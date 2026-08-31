/*
 * ============================================================================
 *  SP-1 LOOPER  —  custom firmware for the Teenage Engineering SP-1
 * ============================================================================
 *  A four-track, hold-to-record audio looper / sketchpad. Audio comes in over
 *  USB-C (the SP-1 appears as a USB sound card); you record loops by holding
 *  the track buttons, and they play back layered together out of the speaker
 *  or headphones. Loops are stored on the SP-1's internal 4 GB flash, so they
 *  survive power-off and even re-flashing the firmware.
 *
 *  ---- HOW THE AUDIO FLOWS ----
 *    USB-C in  ->  [USB ring]  ->  audio engine  ->  I2S bus  ->  speaker / HP
 *                                       |  ^
 *                              record  v  |  play
 *                                  [ eMMC flash, 1 region per track ]
 *
 *  ---- THE THREADS (highest audio priority first) ----
 *    audio_thread   : runs every I2S block (256 frames). Mixes the 4 playback
 *                     tracks + the live USB monitor, and decimates the live
 *                     input down into the track being recorded. Never blocked.
 *    streamer_thread: the only thing that touches the flash. Flushes the
 *                     track being recorded TO flash, and reads the playing
 *                     tracks back FROM flash into their ring buffers ahead of
 *                     the playhead. (sp1_emmc.c is the flash driver.)
 *    midi_thread    : (optional) MIDI clock housekeeping.
 *    main           : ~8 ms control loop — buttons, faders, LEDs, power, the
 *                     USB-serial status line (controls_diag).
 *
 *  ---- KEY DESIGN POINTS ----
 *    * Clocking: the board's 3.072 MHz oscillator drives the I2S bit clock and
 *      the CS42L42 headphone codec masters a true 48 kHz frame; the nRF and the
 *      speaker amp are clock slaves (see the "I2S audio bus" section).
 *    * Loops play at full 48 kHz; recording is mono and decimated by DECIM (see
 *      the LOOPER ENGINE section) — the flash write speed sets that ceiling.
 *    * Storage uses the nRF's SPIM3 SPI engine at 32 MHz (a calculated overclock
 *      above the 26 MHz default-speed max) with hardware CRC checking + retry,
 *      so the flash bus is fast and self-correcting. The card's internal write
 *      cache is enabled to absorb record bursts; it's flushed only at power-off.
 *
 *  ---- BOOTLOADER SAFETY (the SP-1 "BIG FIVE") ----
 *    app lives at 0x20000; watchdog fed < 5 s; we do NOT re-init bootloader-
 *    owned clocks/peripherals; SYSTEM_OFF returns to the bootloader; RESETREAS
 *    is cleared on boot and before SYSTEM_OFF. (There is no hardware reset pin
 *    on the SP-1, so a clean path back to the bootloader is mandatory.)
 *
 *  See README.md in this folder for the player's controls and a fuller tour.
 * ============================================================================
 */

#include <zephyr/kernel.h>
#include <zephyr/irq.h>
#include <zephyr/device.h>
#include <zephyr/drivers/watchdog.h>
#include <zephyr/drivers/adc.h>
#include <zephyr/drivers/uart.h>
#include <zephyr/drivers/i2c.h>
#include <zephyr/drivers/i2s.h>
#include <zephyr/usb/usbd.h>
#include <zephyr/usb/class/usbd_uac2.h>
#include <zephyr/sys/ring_buffer.h>
#include <sample_usbd.h>

/* From the patched Zephyr UAC2 class (zephyr-patches/): selects the Full-Speed
 * explicit-feedback wire format at runtime. false = 3-byte Q10.14 (USB spec —
 * what Apple hosts require), true = 4-byte Q16.16 (what Microsoft's
 * usbaudio2.sys requires). The two are mutually incompatible per host, so the
 * main loop auto-negotiates: see the feedback-format watchdog in main(). */
extern bool uac2_fs_fb_windows_fmt;
#include <soc.h>
#include <math.h>
#include <string.h>
#include <zephyr/fatal.h>
#include <zephyr/sys/reboot.h>
#include "sp1_emmc.h"

/* FAILSAFE: turn ANY unrecoverable fault (bad pointer, stack overflow, kernel
 * panic, failed assert) into a clean reboot instead of a dead hang, so the
 * device can never get stuck in a bricked-looking state.
 * CRASH FORENSICS: this silent reboot is also why crashes left no trail —
 * stash the fault reason + faulting PC in __noinit RAM (survives the soft
 * reboot); the next boot prints them in the diag line as flt=reason@pc. */
static __noinit uint32_t g_fault_key;            /* 0xFA17FA17 = breadcrumb valid */
static __noinit uint32_t g_fault_reason;
static __noinit uint32_t g_fault_pc;
static uint32_t g_resetreas;                     /* NRF_POWER->RESETREAS at boot */
static uint32_t g_last_fault_reason = 0xFFFFFFFFu; /* from the PREVIOUS boot (diag) */
static uint32_t g_last_fault_pc;
void k_sys_fatal_error_handler(unsigned int reason, const struct arch_esf *esf)
{
	g_fault_reason = reason;
	g_fault_pc = esf ? esf->basic.pc : 0u;
	g_fault_key = 0xFA17FA17u;
	sys_reboot(SYS_REBOOT_COLD);
	CODE_UNREACHABLE;
}

#define WDT_NODE DT_ALIAS(watchdog0)

/* ---- the 4 playback LEDs (center row, verified pin map) ---- */
struct led { NRF_GPIO_Type *port; uint32_t pin; };
static const struct led leds[] = {
	{ NRF_P1, 13 }, { NRF_P0, 0 }, { NRF_P1, 12 }, { NRF_P0, 1 },
};
#define NUM_LEDS (sizeof(leds) / sizeof(leds[0]))

/* ---- the 4 TRACK LEDs (directly above buttons 1-4) ---- */
static const struct led track_leds[] = {
	{ NRF_P0, 29 }, { NRF_P0, 26 }, { NRF_P1, 15 }, { NRF_P1, 14 },
};
#define NUM_TRACK_LEDS (sizeof(track_leds) / sizeof(track_leds[0]))

/* 1 = dim LEDs (soft-PWM render), 0 = full brightness. Toggled by the
 * FUNCTION+PLAY double-tap; persisted in the song index tail (led_full).
 * Declared here (not with the dimmer) because xfer_commit persists it. */
static volatile uint8_t g_led_dim = 1;

static void track_led_on(int i);
static void track_all_off(void);
static bool usb_present(void);
static bool charging(void);

/* ---- power / function button: P0.27, active-low with pull-up ---- */
#define PWR_PORT        NRF_P0
#define PWR_PIN         27u

/* ---- BQ24232 battery charger control (verified pins from TimK pinout) ---- */
#define BQ_PORT         NRF_P0
#define BQ_NCE_PIN      21u   /* charge enable, ACTIVE-LOW: drive low = charging on */
#define BQ_NCHG_PIN     22u   /* charge status, open-drain, LOW = charging now      */
#define BQ_NPGOOD_PIN   24u   /* power good,    open-drain, LOW = USB power present  */

/* hold this long (ms) to power off - "a few seconds" like the real device */
#define HOLD_MS_TO_OFF  2500
/* M27: how long TRACK 1 + TRACK 4 must be held before we reset into the
 * bootloader. Was 1200 ms, which collided with using 1+4 as a musical
 * gesture; a mute tap is 100-200 ms, so 3000 gives ~15x margin and lines
 * up with the power-off hold above. */
#define DFU_HOLD_MS     3000

/* ---- button ladders (Milestone 1: read + report the controls) ----
 * The PLAY/track and Vol/FWD/RWD buttons are resistor ladders read on the
 * SAADC. They are only powered when BTN_COM (P1.10) is driven high, so we
 * raise that rail before sampling. Raw 12-bit codes are streamed over the
 * USB serial console so we can map each button press to a voltage band. */
#define BTN_COM_PORT    NRF_P1
#define BTN_COM_PIN     10u

static const struct adc_dt_spec adc_ladder[] = {
	ADC_DT_SPEC_GET_BY_IDX(DT_PATH(zephyr_user), 0),  /* AIN0: PLAY + tracks   */
	ADC_DT_SPEC_GET_BY_IDX(DT_PATH(zephyr_user), 1),  /* AIN1: Vol + FWD/RWD   */
	ADC_DT_SPEC_GET_BY_IDX(DT_PATH(zephyr_user), 2),  /* AIN3: Fader 1 (track1 vol) */
	ADC_DT_SPEC_GET_BY_IDX(DT_PATH(zephyr_user), 3),  /* AIN6: Fader 2 (track2 vol) */
	ADC_DT_SPEC_GET_BY_IDX(DT_PATH(zephyr_user), 4),  /* AIN2: Fader 3 (track3 vol) */
	ADC_DT_SPEC_GET_BY_IDX(DT_PATH(zephyr_user), 5),  /* AIN7: Fader 4 (track4 vol) */
	ADC_DT_SPEC_GET_BY_IDX(DT_PATH(zephyr_user), 6),  /* AIN4: battery level (divider) */
};
#define LAD_TRACKS 0
#define LAD_VOL    1
#define LAD_FADER0 2     /* faders are ladder indices 2..5 */
#define LAD_BATT   6     /* battery voltage via on-board divider (AIN4) */
#define NUM_LADDERS (sizeof(adc_ladder) / sizeof(adc_ladder[0]))

/* the USB CDC ACM serial console (chosen,console in the devicetree) */
static const struct device *const cdc =
	DEVICE_DT_GET(DT_CHOSEN(zephyr_console));

static int16_t adc_sample;

/* ---- audio codecs over I2C (Milestone 2a: just confirm they answer) ----
 *   CS42L42 headphone codec @ 0x48   (reset: P0.15, active-low)
 *   TAS2505 speaker amp     @ 0x18   (reset: P0.09 / NFC1, active-low)
 * We release both resets, then scan the bus and report what ACKs.
 * (Verified on hardware 2026-06-05: both ACK; CS42L42 straps to 0x48.) */
#define CS42_RST_PORT   NRF_P0
#define CS42_RST_PIN    15u
#define TAS_RST_PORT    NRF_P0
#define TAS_RST_PIN     9u
#define CS42L42_ADDR    0x48u
#define TAS2505_ADDR    0x18u

static const struct device *const i2c_bus = DEVICE_DT_GET(DT_NODELABEL(i2c0));

static uint8_t i2c_found[16];
static int     i2c_found_n;
static bool    cs42_ok, tas_ok;
static bool    i2c_scanned;

/* Oversampled ladder read: average 2 conversions. Audio/USB activity couples
 * noise into the shared BTN_COM rail, so a single 12-bit sample can land a band
 * boundary off; averaging quietens every ladder, and the sticky debounce does
 * the rest. CAREFUL with the count: blocking ADC reads run on the main thread,
 * which PREEMPTS the eMMC streamer — at 4x across 6 ladders the stolen CPU
 * slowed the bit-banged card below the ~26.6 blk/s a take produces and brought
 * back record-ring overflows (corrupt loops). 2x + round-robin faders keeps the
 * main loop's ADC cost at the level the working builds had.
 * Returns -1 on ADC error (callers treat <0 as "no change / hold last"). */
static int ladder_read(const struct adc_dt_spec *spec)
{
	struct adc_sequence seq = {
		.buffer      = &adc_sample,
		.buffer_size = sizeof(adc_sample),
	};
	if (adc_sequence_init_dt(spec, &seq) < 0)
		return -1;
	int32_t acc = 0;
	for (int n = 0; n < 2; n++) {
		if (adc_read_dt(spec, &seq) < 0)
			return -1;
		acc += adc_sample;
	}
	return (int)(acc / 2);
}

/* Power the ladder rail, set up the ADC channels, bring USB up. Safe to call
 * once at boot; never blocks waiting for a host. */
static void controls_init(void)
{
	BTN_COM_PORT->OUTSET = (1u << BTN_COM_PIN);
	BTN_COM_PORT->PIN_CNF[BTN_COM_PIN] =
		(GPIO_PIN_CNF_DIR_Output    << GPIO_PIN_CNF_DIR_Pos)   |
		(GPIO_PIN_CNF_DRIVE_S0S1    << GPIO_PIN_CNF_DRIVE_Pos) |
		(GPIO_PIN_CNF_INPUT_Connect << GPIO_PIN_CNF_INPUT_Pos);
	BTN_COM_PORT->OUTSET = (1u << BTN_COM_PIN);

	for (int i = 0; i < NUM_LADDERS; i++) {
		if (device_is_ready(adc_ladder[i].dev))
			adc_channel_setup_dt(&adc_ladder[i]);
	}

	/* USB is brought up later in main() on the device_next stack (UAC2 audio
	 * + CDC console composite); nothing to enable here anymore. */
}

/* Drive one bare-metal GPIO high (used to release the codec reset lines). */
static void gpio_drive_high(NRF_GPIO_Type *port, uint32_t pin)
{
	port->OUTSET = (1u << pin);
	port->PIN_CNF[pin] =
		(GPIO_PIN_CNF_DIR_Output    << GPIO_PIN_CNF_DIR_Pos)   |
		(GPIO_PIN_CNF_DRIVE_S0S1    << GPIO_PIN_CNF_DRIVE_Pos) |
		(GPIO_PIN_CNF_INPUT_Connect << GPIO_PIN_CNF_INPUT_Pos);
	port->OUTSET = (1u << pin);
}

static void gpio_drive_low(NRF_GPIO_Type *port, uint32_t pin)
{
	port->OUTCLR = (1u << pin);
}

/* Release the codec resets, then probe every I2C address once and record
 * which devices answer. Reading a single byte is a harmless presence test. */
static void codec_init(void)
{
	gpio_drive_high(CS42_RST_PORT, CS42_RST_PIN);   /* un-reset CS42L42 */
	gpio_drive_high(TAS_RST_PORT,  TAS_RST_PIN);    /* un-reset TAS2505 */
	k_msleep(20);

	if (!device_is_ready(i2c_bus))
		return;

	i2c_found_n = 0;
	cs42_ok = tas_ok = false;
	for (uint8_t a = 0x08; a <= 0x77; a++) {
		uint8_t b;
		if (i2c_read(i2c_bus, &b, 1, a) == 0) {
			if (i2c_found_n < (int)sizeof(i2c_found))
				i2c_found[i2c_found_n++] = a;
			if (a == CS42L42_ADDR) cs42_ok = true;
			if (a == TAS2505_ADDR) tas_ok = true;
		}
	}
	i2c_scanned = true;
}

/* ========================= I2S audio bus =================================
 * CLOCK TOPOLOGY (the way Teenage Engineering wired the board — see the
 * SP-1-dev wiki): the on-board 3.072 MHz oscillator (enabled via OSC_EN
 * P0.13) drives the shared I2S bit clock, and the CS42L42 headphone codec is
 * the FRAME master — it divides that oscillator by 64 to make a LRCK of
 * exactly 3.072 MHz / 64 = 48000 Hz. The nRF52840 I2S peripheral and the
 * TAS2505 speaker amp are both CLOCK SLAVES on this bus.
 *
 * (Pins: SCLK P0.12, LRCK P0.11, DOUT P1.09.)
 *
 * An earlier design had the nRF master the clocks at ~47619 Hz instead — it
 * crackled on the speaker and produced only noise on the headphones, because
 * the CS42L42 was never given the clock it was built to run from. Driving the
 * board the way TE intended fixed both, so everything below assumes a true,
 * codec-mastered 48.000 kHz. */
#define OSC_EN_PORT     NRF_P0
#define OSC_EN_PIN      13u

#define I2S_SR          48000
#define I2S_TRUE_HZ     48000u   /* real LRCK = osc / 64, CS42L42 is frame master */
#define BLK_FRAMES      256
#define BLK_BYTES       (BLK_FRAMES * 2 * (int)sizeof(int16_t))   /* stereo 16-bit slots */

K_MEM_SLAB_DEFINE(tx_slab, BLK_BYTES, 10, 4);   /* 10 blks ~106ms DMA cushion — the PROVEN WORKING.bin
                                                 * value. (A codec-era trim to 4 was never validated on
                                                 * hardware and rode along in every failed build.) */
static const struct device *const i2s_dev = DEVICE_DT_GET(DT_NODELABEL(i2s0));

static int  audio_cfg_rc = 1;        /* i2s_configure() result, for serial diag */
static bool tas_cfg_ok;              /* did the TAS2505 register writes all ACK?  */
static volatile bool audio_started;  /* did i2s START trigger fire?               */

/* ---- TAS2505 speaker-amp setup (ported from TimK SP-1-dev, 16-bit I2S) ---- */
static int tas_wr(uint8_t reg, uint8_t val)
{
	return i2c_reg_write_byte(i2c_bus, TAS2505_ADDR, reg, val);
}
static void tas_page(uint8_t p) { (void)tas_wr(0x00, p); }

/* Power the speaker amp on/off (page-1 reg 0x2D: 0x02 = driver up, 0x00 = off).
 * Used by the headphone auto-mute. Main-thread only (audio thread never touches
 * I2C after init), so no locking needed. */
static void tas_set_speaker(int on)
{
	tas_page(0x01);
	(void)tas_wr(0x2D, on ? 0x02 : 0x00);
	tas_page(0x00);
}

/* TAS2505 speaker bring-up, following TI Application Reference Guide SLAU472C
 * Section 5.1 ("Play Digital Data Through DAC and Headphone/Speaker Outputs").
 *
 * CLOCKING: the speaker DAC is clocked from a PLL locked to the I2S bit clock
 * (BCLK = the 3.072 MHz oscillator). The PLL multiplies BCLK so the DAC's
 * internal rates land where the sigma-delta modulator wants them:
 *   f_PLL  = BCLK x J = 3.072 MHz x 32 = 98.304 MHz
 *   DAC_FS = f_PLL / (NDAC2 x MDAC8 x DOSR128) = 48000 Hz  (exact)
 * Locking to BCLK (not a free-running MCLK) means the DAC tracks the bus
 * exactly, so the speaker never slips or crackles. BCLK must be running before
 * the PLL can lock, so the I2S stream is started before this runs. */
static bool tas2505_configure(void)
{
	int rc = 0;

	tas_page(0x00);
	rc |= tas_wr(0x01, 0x01);          /* software reset */
	k_msleep(5);

	/* Page 1: LDO output 1.8 V, analog level shifters powered up */
	tas_page(0x01);
	rc |= tas_wr(0x02, 0x00);

	/* Page 0: clocking (PLL locked to BCLK) + interface */
	tas_page(0x00);
	rc |= tas_wr(0x04, 0x07);          /* PLL_CLKIN = BCLK, CODEC_CLKIN = PLL */
	rc |= tas_wr(0x05, 0x91);          /* PLL powered, P=1, R=1 */
	/* TE-native bus: BCLK = the 3.072 MHz oscillator, WCLK = 48000 (64 SCLK per
	 * frame, CS42L42 frame master). PLL J=32 puts f_PLL = 3.072M x 32 = 98.304
	 * MHz (inside the ~80-110 MHz lock range); NDAC=2 x MDAC=8 x DOSR=128 = 2048
	 * brings DAC_FS = 98.304M/2048 = 48000 = WCLK exactly. */
	rc |= tas_wr(0x06, 0x20);          /* PLL J = 32  -> f_PLL = 98.304 MHz */
	rc |= tas_wr(0x07, 0x00);          /* PLL D = 0 (MSB) */
	rc |= tas_wr(0x08, 0x00);          /* PLL D = 0 (LSB) */
	k_msleep(15);                      /* wait for PLL to lock */
	rc |= tas_wr(0x0B, 0x82);          /* NDAC = 2, powered */
	rc |= tas_wr(0x0C, 0x88);          /* MDAC = 8, powered */
	rc |= tas_wr(0x0D, 0x00);          /* DOSR MSB */
	rc |= tas_wr(0x0E, 0x80);          /* DOSR = 128 -> DAC_FS = 48000 */
	rc |= tas_wr(0x1B, 0x00);          /* I2S, 16-bit, slave (matches nRF Philips I2S) */
	rc |= tas_wr(0x1C, 0x00);          /* data slot offset 0 */
	rc |= tas_wr(0x3C, 0x02);          /* DAC processing block PRB_P2 (mono) */

	/* DAC power + digital volume — these live on PAGE 0 */
	rc |= tas_wr(0x3F, 0x90);          /* DAC powered, left data -> left, soft-step */
	rc |= tas_wr(0x41, 0x00);          /* DAC digital gain 0 dB */
	rc |= tas_wr(0x40, 0x04);          /* DAC not muted */

	/* Page 1: analog reference, routing, speaker driver */
	tas_page(0x01);
	rc |= tas_wr(0x01, 0x10);          /* master analog reference powered ON */
	rc |= tas_wr(0x0A, 0x00);          /* output common mode 0.9 V */
	rc |= tas_wr(0x0C, 0x04);          /* Mixer P out -> output mixer (DAC routed) */
	rc |= tas_wr(0x16, 0x00);          /* HP volume 0 dB */
	rc |= tas_wr(0x18, 0x00);          /* AINL volume / mixer */
	rc |= tas_wr(0x09, 0x20);          /* power up HP driver */
	rc |= tas_wr(0x10, 0x00);          /* unmute HP, 0 dB */
	rc |= tas_wr(0x2E, 0x00);          /* speaker attenuation 0 dB (max) */
	/* Class-D driver gain, P1/R48 bits D6-D4: 000=mute 001=6dB 010=12dB
	 * 011=18dB 100=24dB. Was 6 dB — user wants a fair bit louder; 18 dB is
	 * one step below the chip's max (24 dB = 0x40 if ever needed). */
	rc |= tas_wr(0x30, 0x30);          /* speaker driver gain +18 dB */
	rc |= tas_wr(0x2D, 0x02);          /* speaker driver powered up */

	tas_page(0x00);
	k_msleep(10);

	tas_cfg_ok = (rc == 0);
	return tas_cfg_ok;
}

/* ---- HEADPHONE output (always on), SELF-SELECTING driver ---------------------
 * Probes the codec and picks the right register scheme at boot:
 *   PATH 1 (expected): a real CS42L42/CS42L83 — our chip ACKs 0x48, the genuine
 *     CS42L42 address. Full 16-bit paged init taken VERBATIM from the Linux
 *     kernel driver (sound/soc/codecs/cs42l42.c): PLL from SCLK using the
 *     1.536 MHz pll_ratio_table row {prediv 0, div_int 0x7D, frac 0, mode 3,
 *     divout 0x10 x n 2, cal 125, mclk_int 12 MHz}. Our SCLK is 1.5238 MHz
 *     (-0.8%), so every derived clock scales with the bus = self-consistent.
 *     CRITICALLY this path needs NO MCLK: the 3.072 MHz oscillator stays OFF —
 *     turning it on permanently was what made the speaker crackle (the comment
 *     in audio_init predicted exactly that).
 *   PATH 2 (fallback): TimK's 8-bit-register variant (SP-1-dev repo, forum-
 *     confirmed on his unit at 0x4A). Only this path powers the oscillator,
 *     since his CLK_CTL 0x04 is MCLK auto-detect.
 * No jack detect — headphones simply run alongside the speaker. */
static volatile int g_hp_on;     /* diag: 0=none, 1=CS42L42 16-bit, 2=TimK 8-bit */
static uint8_t g_cs42_addr = CS42L42_ADDR;
static uint8_t g_cs42_id8;       /* diag: 8-bit-scheme reg 0x01 readback */
static uint8_t g_cs42_dev[3];    /* diag: 16-bit DEVID A/B, C/D, E (0x42 0xA4 x = CS42L42) */
static uint8_t g_hp_pll;         /* diag: PLL lock status readback */
static volatile int g_hp_in = -1;   /* headphones detected in jack: 1 yes, 0 no, -1 unknown */
static bool cs42_wr8(uint8_t reg, uint8_t val)
{
	uint8_t b[2] = { reg, val };
	return i2c_write(i2c_bus, b, 2, g_cs42_addr) == 0;
}
static bool cs42_rd8(uint8_t reg, uint8_t *val)
{
	return i2c_write_read(i2c_bus, g_cs42_addr, &reg, 1, val, 1) == 0;
}
static bool cs42_wr16(uint16_t reg, uint8_t val)
{
	uint8_t b[3] = { (uint8_t)(reg >> 8), (uint8_t)reg, val };
	return i2c_write(i2c_bus, b, 3, g_cs42_addr) == 0;
}
static bool cs42_rd16(uint16_t reg, uint8_t *val)
{
	uint8_t a[2] = { (uint8_t)(reg >> 8), (uint8_t)reg };
	return i2c_write_read(i2c_bus, g_cs42_addr, a, 2, val, 1) == 0;
}
/* HP_TIM_TEST 1 builds the SEPARATE headphone test binary: the exact init from
 * Tim Knapen's wiki (github.com/timknapen/SP-1-dev/wiki/I2C — proven on real
 * SP-1 hardware, and it uses the page-select protocol we independently
 * confirmed), adapted to OUR clock topology: nRF stays I2S master, the 3.072 MHz
 * oscillator stays OFF (TE's design has the osc drive the shared SCLK line —
 * enabling it against the nRF master is what caused the crackle), PLL row for
 * our 1.524 MHz SCLK, 16-bit channels. Key registers Tim has that we never
 * wrote: 0x1007 (Serial Port SRC routing), 0x2601/0x2609 (SRC rates), 0x240E
 * (EQ input unmute), 0x1121 (headset switch). The main binary keeps 0. */
#ifndef HP_TIM_TEST
#define HP_TIM_TEST 1     /* Tim-wiki headphone init is now the NORMAL build */
#endif
#if HP_TIM_TEST
static bool tpw(uint16_t reg, uint8_t val)   /* paged write: page reg 0x00 first */
{
	uint8_t p[2] = { 0x00, (uint8_t)(reg >> 8) };
	uint8_t b[2] = { (uint8_t)reg, val };
	if (i2c_write(i2c_bus, p, 2, g_cs42_addr) != 0) return false;
	return i2c_write(i2c_bus, b, 2, g_cs42_addr) == 0;
}
static bool tpr(uint16_t reg, uint8_t *val)  /* paged read */
{
	uint8_t p[2] = { 0x00, (uint8_t)(reg >> 8) };
	uint8_t o = (uint8_t)reg;
	if (i2c_write(i2c_bus, p, 2, g_cs42_addr) != 0) return false;
	return i2c_write_read(i2c_bus, g_cs42_addr, &o, 1, val, 1) == 0;
}

/* Headphone presence from the CS42L42: DET_STATUS1 (page 0x1B reg 0x77) bit7,
 * per Tim's wiki "request headphone status". 1=plugged, 0=unplugged, -1=read failed. */
static int hp_detect_connected(void)
{
	uint8_t st;
	if (!tpr(0x1B77, &st)) return -1;
	return (st >> 7) & 1;
}
#endif

static void hp_codec_init(int pllcfg)
{
	static const uint8_t addrs[2] = { 0x48u, 0x4Au };
	(void)pllcfg;                /* unused when the HP graft is compiled out */
	g_hp_on = 0;

#if HP_TIM_TEST
	/* hard reset pulse — without it the codec is wedged and NAKs everything */
	gpio_drive_low(CS42_RST_PORT, CS42_RST_PIN);
	k_msleep(5);
	gpio_drive_high(CS42_RST_PORT, CS42_RST_PIN);
	k_msleep(10);

	g_cs42_addr = 0x48u;
	(void)tpr(0x1001, &g_cs42_dev[0]);            /* DEVID_AB (0x42 = CS42L42) */
	(void)tpr(0x1002, &g_cs42_dev[1]);
	(void)tpr(0x1003, &g_cs42_dev[2]);
	if (g_cs42_dev[0] != 0x42) return;            /* not answering -> leave alone */

	/* ===== TIM'S WIKI SEQUENCE, VERBATIM — native TE topology. =====
	 * The CS42L42 is the I2S frame MASTER here (its designed role on this
	 * board): PLL referenced from the oscillator-driven 3.072 MHz SCLK, LRCK
	 * generated at exactly 48 kHz, the nRF and TAS2505 follow as slaves.
	 * Every value below is from github.com/timknapen/SP-1-dev/wiki/I2C, the
	 * config proven to play headphone audio on this exact hardware. The ONLY
	 * deviation was mixer volume -19 dB; RESTORED to his full-scale 0x00 —
	 * the -19 dB pad capped max headphone loudness ~1/9th of stock. The
	 * digital path already soft-limits before the codec, so 0 dB is safe. */
	(void)tpw(0x1508, 0x10);   /* PLL Control 3                         */
	(void)tpw(0x1504, 0x80);   /* PLL Division Fractional Byte 2        */
	(void)tpw(0x1505, 0x3E);   /* PLL Division Integer                  */
	(void)tpw(0x150A, 0x7D);   /* PLL Calibration Ratio                 */
	(void)tpw(0x1009, 0x00);   /* MCLK Control                          */
	(void)tpw(0x1201, 0x01);   /* MCLK Source Select                    */
	(void)tpw(0x120A, 0x01);   /* Input ASRC Clock Select               */
	(void)tpw(0x120B, 0x01);   /* Output ASRC Clock Select              */
	(void)tpw(0x1501, 0x01);   /* PLL Control 1: start                  */
	(void)tpw(0x1107, 0x01);   /* Oscillator Switch (SCLK is running —
	                              the 3.072 MHz osc drives it)          */
	for (int t = 0; t < 10; t++) {   /* wait for "SCLK selected" (0x02) */
		k_msleep(1);
		if (tpr(0x1109, &g_hp_pll) && g_hp_pll == 0x02) break;
	}
	(void)tpw(0x1007, 0x13);   /* Serial Port SRC Control               */
	(void)tpw(0x1203, 0x1F);   /* FSYNC Pulse Width Lower (64-SCLK frame) */
	(void)tpw(0x1205, 0x3F);   /* FSYNC Period Lower                    */
	(void)tpw(0x1207, 0x34);   /* ASP Clock Config: MASTER              */
	(void)tpw(0x1208, 0x1A);   /* ASP Frame Configuration               */
	(void)tpw(0x2A02, 0x02);   /* Channel 1: 24-bit                     */
	(void)tpw(0x2A05, 0x42);   /* Channel 2: phase + 24-bit             */
	(void)tpw(0x2601, 0x4C);   /* SRC Input Sample Rate                 */
	(void)tpw(0x2609, 0x4C);   /* SRC Output Sample Rate                */
	(void)tpw(0x2A01, 0x0C);   /* ASP Receive Enable                    */
	(void)tpw(0x240E, 0x01);   /* Equalizer Input Mute Control          */
	(void)tpw(0x2301, 0x00);   /* Mixer A vol 0 dB (Tim's full scale)   */
	(void)tpw(0x2303, 0x00);   /* Mixer B vol                           */
	(void)tpw(0x1101, 0x96);   /* power up the codec                    */
	k_msleep(10);              /* HP amp operational after 10 ms        */
	(void)tpw(0x1121, 0x41);   /* Headset switch control                */
	(void)tpw(0x1B74, 0x03);   /* Miscellaneous detect control          */
	(void)tpw(0x1129, 0x01);   /* Headset clamp disable                 */
	(void)tpw(0x2001, 0x0D);   /* HP Control: mute all                  */
	(void)tpw(0x1F06, 0x84);   /* DAC Control 2                         */
	(void)tpw(0x2301, 0x00);   /* Mixer A vol again                     */
	(void)tpw(0x2303, 0x00);   /* Mixer B vol again                     */
	(void)tpw(0x1B73, 0xC2);   /* Tip Sense Control                     */
	(void)tpw(0x1B75, 0x9F);   /* Mic detect control 1                  */
	(void)tpw(0x2001, 0x01);   /* UNMUTE headphones                     */
	g_hp_on = 1;
	return;
#endif

	for (int a = 0; a < 2; a++) {
		g_cs42_addr = addrs[a];

		/* read both ID schemes (8-bit read first: harmless on either chip) */
		uint8_t id8 = 0;
		if (!cs42_rd8(0x01, &id8)) continue;          /* nothing ACKs here */
		g_cs42_id8 = id8;
		(void)cs42_rd16(0x1001, &g_cs42_dev[0]);      /* CS42L42_DEVID_AB */
		(void)cs42_rd16(0x1002, &g_cs42_dev[1]);      /* CS42L42_DEVID_CD */
		(void)cs42_rd16(0x1003, &g_cs42_dev[2]);      /* CS42L42_DEVID_E  */

		if (g_cs42_dev[0] == 0x42) {
			/* ---- PATH 1: genuine CS42L42/L83, kernel-exact init ---- */
			/* clocking: internal-FS = 12 MHz family (mclk_int 12000000) */
			(void)cs42_wr16(0x1009, 0x00);  /* MCLK_CTL: INTERNAL_FS=0     */
			/* PLL dividers — pll_ratio_table row for SCLK 1.536 MHz      */
			(void)cs42_wr16(0x120C, 0x00);  /* PLL_DIV_CFG1: SCLK_PREDIV /1 */
			(void)cs42_wr16(0x1505, 0x7D);  /* PLL_DIV_INT   0x7D (125)    */
			(void)cs42_wr16(0x1502, 0x00);  /* PLL_DIV_FRAC0               */
			(void)cs42_wr16(0x1503, 0x00);  /* PLL_DIV_FRAC1               */
			(void)cs42_wr16(0x1504, 0x00);  /* PLL_DIV_FRAC2               */
			(void)cs42_wr16(0x151B, 0x03);  /* PLL_CTL4: mode 3            */
			(void)cs42_wr16(0x1508, 0x20);  /* PLL_CTL3: DIVOUT 0x10 * n=2 */
			(void)cs42_wr16(0x150A, 0x7D);  /* PLL_CAL_RATIO 125           */
			/* serial port: slave I2S, 50/50 frame, 1.0-cycle FSD, 16-bit  */
			(void)cs42_wr16(0x1207, 0x20);  /* ASP_CLK_CFG: SCLK_EN, slave */
			(void)cs42_wr16(0x1208, 0x0A);  /* ASP_FRM_CFG: 5050 | FSD_1_0 */
			(void)cs42_wr16(0x2A02, 0x01);  /* RX CH1: AP low,  RES 16-bit */
			(void)cs42_wr16(0x2A03, 0x00);  /* CH1 bit offset MSB          */
			(void)cs42_wr16(0x2A04, 0x00);  /* CH1 bit offset LSB          */
			(void)cs42_wr16(0x2A05, 0x41);  /* RX CH2: AP high, RES 16-bit */
			(void)cs42_wr16(0x2A06, 0x00);  /* CH2 bit offset MSB          */
			(void)cs42_wr16(0x2A07, 0x00);  /* CH2 bit offset LSB          */
			(void)cs42_wr16(0x2A01, 0x0C);  /* ASP_RX_DAI0_EN: CH1+CH2     */
			(void)cs42_wr16(0x1209, 0x03);  /* FS_RATE_EN: IASRC+OASRC 96K */
			(void)cs42_wr16(0x120A, 0x00);  /* IN_ASRC_CLK: IASRC_SEL_6    */
			(void)cs42_wr16(0x2301, 0x00);  /* MIXER_CHA_VOL: 0 dB         */
			(void)cs42_wr16(0x2303, 0x00);  /* MIXER_CHB_VOL: 0 dB         */
			/* power up: keep ASP-TX, EQ, ADC down; enable DAI+MIXER+HP    */
			(void)cs42_wr16(0x1101, 0x94);  /* PWR_CTL1                    */
			k_msleep(5);
			/* start the PLL (reference = SCLK, runs whenever I2S runs)    */
			(void)cs42_wr16(0x1501, 0x01);  /* PLL_CTL1: PLL_START         */
			for (int t = 0; t < 40; t++) {  /* poll PLL_LOCK_STATUS 0x130E */
				k_msleep(1);
				if (cs42_rd16(0x130E, &g_hp_pll) && (g_hp_pll & 1))
					break;
			}
			(void)cs42_wr16(0x1201, 0x01);  /* MCLK_SRC_SEL: PLL           */
			(void)cs42_wr16(0x1107, 0x01);  /* OSC_SWITCH: SCLK present    */
			k_msleep(2);
			(void)cs42_wr16(0x2001, 0x00);  /* HP_CTL: unmute A+B          */
			g_hp_on = 1;
			return;
		}
		if ((id8 & 0xF8) == 0x20) {
			/* ---- PATH 2: TimK's 8-bit variant (needs the MCLK osc) ---- */
			gpio_drive_high(OSC_EN_PORT, OSC_EN_PIN);
			k_msleep(5);
			(void)cs42_wr8(0x1D, 0x00);   /* out of hibernate            */
			(void)cs42_wr8(0x1B, 0x04);   /* CLK_CTL: MCLK auto-detect   */
			(void)cs42_wr8(0x2F, 0x01);   /* ASP RX: slave, I2S          */
			(void)cs42_wr8(0x30, 0x60);   /* ASP RX fmt                  */
			(void)cs42_wr8(0x1C, 0x07);   /* signal path: ASP->DAC->HP   */
			(void)cs42_wr8(0x19, 0x00);   /* power on                    */
			(void)cs42_wr8(0x1D, 0x00);   /* unmute HP                   */
			(void)cs42_wr8(0x35, 19);     /* vol A                       */
			(void)cs42_wr8(0x36, 19);     /* vol B                       */
			k_msleep(10);
			g_hp_on = 2;
			return;
		}
	}
}

static void hp_init(void)
{
	hp_codec_init(0);
}

/* ---- continuous I2S TX thread ---- */
static K_THREAD_STACK_DEFINE(audio_stack, 1536);  /* RD-474: was 3072. 473 U4S measured 408 B peak over a 76.6 s corner with the audio thread fully exercised -> 3.8x margin. */  /* +1K margin over the historical 2048: the
                                                   * PREEMPT(0) mixer takes USB-thread
                                                   * preemptions (incl. FPU lazy-stacking
                                                   * frames) on top of its own worst case —
                                                   * the top-ranked candidate for the
                                                   * unexplained record-start crash */
static struct k_thread audio_tcb;

/* Fill one stereo I2S block with silence. Used to prime the I2S DMA at start-up
 * and after an underrun recovery, before the looper engine takes over. */
static void fill_block(int16_t *s)
{
	memset(s, 0, BLK_FRAMES * 2 * sizeof(int16_t));
}

/* ================== Milestone 3: USB-C audio in (UAC2) ==================
 * The host streams 48 kHz / 16-bit / stereo PCM into the SP-1 over a USB
 * isochronous OUT endpoint. The UAC2 data callback (USB thread) pushes those
 * 16-bit frames into this lock-free SPSC ring; audio_thread (below) drains the
 * ring, expands each sample into the existing 24-bit I2S word, and clocks it out
 * to the TAS2505 speaker. The ring is the elastic buffer that absorbs the gap
 * between the host's 48000 Hz send rate and the SP-1's 48000 Hz I2S rate; the
 * explicit-feedback regulator keeps it centred (see feedback_update). */
#define USB_FRAME_BYTES   4u                 /* 2 ch * 16-bit */
#define USB_RING_FRAMES   2048u              /* RD-474: was 4096 (~85 ms). This ring buffers the
                                              * host's UAC2 stream, i.e. the RECORD SOURCE.
                                              * The old note warned the 2048 trim "was never
                                              * validated and rode along in every failed build".
                                              * It is validated now: cumulative-since-boot peak
                                              * fill was 1262/4096 (471) and 1199/4096 (473),
                                              * with uo=0 uu=0 both runs. FB_SETPOINT is 1024,
                                              * so at 2048 the regulator sits DEAD CENTRE with
                                              * 1024 frames each way vs a worst measured
                                              * excursion of +238 -- a better-shaped elastic
                                              * buffer than 4096, where 75%% of it sat above the
                                              * setpoint and was unreachable when regulated.
                                              * FALSIFIERS: uo>0, ufl climbing, U3B ringhi
                                              * near 2048, or input glitching by ear. Any of
                                              * those and this goes back to 4096. */
/* Target ring fill (frames, ~21 ms). Used both as the prebuffer target before
 * the consumer starts draining a freshly-enabled stream, and as the feedback
 * regulator's setpoint, so the hand-off from prebuffering to draining is smooth. */
#define FB_SETPOINT       1024
RING_BUF_DECLARE(usb_audio_ring, USB_RING_FRAMES * USB_FRAME_BYTES);

static volatile bool g_usb_streaming;        /* host has enabled the UAC2 terminal */

/* Diagnostics streamed over the CDC console (controls_diag): if the ring keeps
 * underrunning (drain faster than host delivers) or overflowing (host faster),
 * the rate-matching is off and audio will glitch. If both stay ~0 but it still
 * sounds wrong, the problem is NOT the buffer (look at level/codec instead). */
static volatile uint32_t g_ring_underruns;
static volatile uint32_t g_ring_overflows;
static volatile uint32_t g_usb_pkts;               /* diag: ISO packets received (~1000/s streaming) */
static volatile uint32_t g_usb_frames;             /* diag: audio frames received (~48000/s streaming) */
static volatile uint32_t g_sof_cnt;                /* diag: SOFs seen by the feedback regulator (1000/s) */
static volatile uint32_t g_zero_pad;               /* diag: silence frames padded into short blocks */
static volatile uint32_t g_rx_nobuf;               /* diag: ISO packets DROPPED — rx pool empty (the
                                                    * exact mechanism: ISO never retries a NAKed buffer) */
static volatile uint32_t g_rx_slab_min = 0xFFFF;   /* diag: window MIN free rx buffers */
static volatile int32_t  g_usb_lowat = 0x7FFFFFFF; /* diag: window MIN usb-in ring fill, frames */
static volatile uint32_t g_usb_hiwat;              /* diag: window MAX usb-in ring fill, frames */
/* U3-471 (RAM/U-diet grounding): CUMULATIVE peaks -- never reset, so a
 * blind Protocol-A run can be read afterwards. Capacities for reference:
 * usb_audio_ring 4096 frames, tx_slab 10 blocks, uac2 rx slab (Zephyr). */
static volatile uint32_t g_u3_ring_hi;             /* max usb-in fill, frames */
static volatile uint32_t g_u3_ring_lo = 0xFFFFFFFFu;/* min usb-in fill while primed */
static volatile uint32_t g_u3_tx_hi;               /* max tx_slab blocks in use */
static volatile uint32_t g_u3_rx_lo = 0xFFFFu;     /* min FREE uac2 rx buffers */

/* Drain up to BLK_FRAMES stereo frames from the USB ring into one I2S block,
 * expanding each 16-bit sample into the 24-in-32-bit I2S word with the same <<8
 * left-justify the sine path uses. Underrun (ring empty) -> silence. */
/* Output volume / headroom, Q8 (256 = unity). The PLAY test tone that sounds
 * clean is generated at amplitude 6000/32768 ~= 0.18 of full scale (~-15 dB); the
 * little speaker + TAS2505 +6 dB driver distort well below full scale. So play
 * USB music at the SAME proven-clean level as that tone: 48/256 ~= 0.1875.
 * 32767 * 48 == tone peak. Raise toward 64/96 for more volume IF it stays clean;
 * lower if loud passages still distort. */
#define SPK_VOL_Q8     48

/* ================== LOOPER ENGINE (4 tracks, eMMC-streamed) ==============
 * Loops are mono int16 decimated from the 48000 Hz live input by DECIM and
 * stored on the eMMC (one region per track). A background streamer thread does
 * the blocking eMMC reads/writes into per-track SPSC rings; THIS audio code only
 * touches RAM. Playback is interpolated back up to the I2S rate; the 4 tracks
 * are mixed with per-track (fader) + master volume over the live monitor.
 * Recording is HOLD-to-record, UNQUANTIZED: the FIRST take you hold sets the
 * master length — exactly what you held, rounded only to the 256-sample storage
 * block (~±19 ms; works for podcasts/speech, nothing snaps or jumps). Overdubs
 * start at the next block (~38 ms = effectively instant) and record exactly one
 * loop, wrapping. "BPM" is just the varispeed label (80 = 1.0x); there is NO
 * tempo grid — the beat constants below only pace the LED pulse + MIDI clock. */
#if SP1_BUILD_24K
#define DECIM            2u                               /* 24 kHz build (see SP1_BUILD_24K) */
#else
#define DECIM            1u                               /* 48 kHz build (default) */
#endif
#define LOOP_RATE        (I2S_TRUE_HZ / DECIM)             /* 48000/DECIM Hz mono */
/* ===== STORAGE CODEC TOGGLE (compile-time) ===============================
 * Loop audio is stored COMPRESSED on flash to cut the WRITE+READ traffic that
 * is the eMMC reliability bottleneck. The audio engine is UNCHANGED: the rec
 * ring (g_rring) and play rings (trk[].pring) and the whole mix stay int16.
 * We ONLY encode on the flash write and decode on the flash read, at the three
 * flush-boundary sites (codec_pack / codec_unpack). SAMP_PER_BLK = int16
 * samples represented by ONE 512-byte flash block; it is codec-conditional.
 *   PCM   (0): 16-bit, 256 samp/blk, 1:1  (current format, memcpy-equivalent)
 *   ULAW  (1):  8-bit G.711 u-law, 512 samp/blk, 2:1
 *   ADPCM (2):  4-bit IMA, self-contained blocks: 4-byte header (predictor
 *               int16 + step-index uint8 + 1 pad) + 508 nibble-bytes = 1016
 *               samp/blk, ~4:1. Predictor RESETS at the start of every block so
 *               any block decodes standalone (random-access loop seeks work).
 * NOTE: 256 and 512 are powers of two; 1016 is NOT. The only bitmask use of
 * SAMP_PER_BLK (the prime align at the promotion site) is converted to a
 * division-based align so the non-power-of-two ADPCM value is correct. All
 * other SAMP_PER_BLK uses are already /,*,%  (block-domain). The int16 ring
 * masks (RING_MASK / RRING_MASK) are sample-domain and stay powers of two. */
#define SP1_CODEC_PCM    0
#define SP1_CODEC_ULAW   1
#define SP1_CODEC_ADPCM  2
#define SP1_CODEC_A7    3u   /* M63b: SP1-ADPCM7, the FROZEN 3.0 codec */
#ifndef SP1_CODEC
#define SP1_CODEC        SP1_CODEC_A7    /* FULL 16-BIT PCM — the proven WORKING.bin
                                           * format (magic SE4A). The u-law/ADPCM
                                           * compressed builds never worked right on
                                           * the user's hardware; do not rebase on
                                           * them again. */
#endif
#if   SP1_CODEC == SP1_CODEC_PCM
#define SAMP_PER_BLK     (EMMC_BLOCK_SIZE / 2u)            /* 256 int16 / block */
#elif SP1_CODEC == SP1_CODEC_ULAW
#define SAMP_PER_BLK     (EMMC_BLOCK_SIZE)                 /* 512 samp / block (8-bit) */
#elif SP1_CODEC == SP1_CODEC_ADPCM
#define SAMP_PER_BLK     1016u                             /* 4B hdr + 508 nibble-bytes = 1016 samp / block (4-bit IMA) */
#elif SP1_CODEC == SP1_CODEC_A7
#define SAMP_PER_BLK     280u   /* FRAMES/block: 16 B hdr + 70x7 B payload (spec 4.1b) */
#else
#error "SP1_CODEC must be 0 (PCM), 1 (ULAW), 2 (ADPCM) or 3 (A7)"
#endif
/* ---- storage codec pack/unpack (full bodies just before streamer_thread) ----
 * codec_pack:   int16 ring -> flash bytes  (encode), one CMD25 burst of n blocks
 * codec_unpack: flash bytes -> int16 ring  (decode), one CMD18 burst of n blocks
 * Both take (ring, ring_mask, ring_start_sample, flashbuf, nblocks) and handle
 * the power-of-two ring wrap internally. PCM = memcpy-equivalent. */
static void codec_pack(const int16_t *ring, uint32_t ring_mask, uint32_t start,
                       uint8_t *flash, uint32_t nblk);
static void codec_unpack(int16_t *ring, uint32_t ring_mask, uint32_t start,
                         const uint8_t *flash, uint32_t nblk);
#define LOOP_BPM_BASE    80u                               /* BPM label for 1.0x varispeed */
/* FULL-RATE LOOPS: the SPIM3 hardware eMMC path measures 1333 blk/s sustained
 * REWRITE (2026-06-12 capture) — 48 kHz mono needs 187.5 blk/s write + 750
 * blk/s read (4 tracks): ~14% / ~60% of capacity. DECIM=1 also means the
 * decimator/interpolator is bit-transparent — loops record and play exactly
 * what the engine hears. Mono remains the only compromise. */
#define BEAT_SAMPLES_I2S 35840u                            /* I2S frames / beat (140 blocks ÷256) */
#define BEAT_SAMPLES_L   (BEAT_SAMPLES_I2S / DECIM)        /* 35840 = 140 blocks (÷256) */
#define BAR_SAMPLES      (BEAT_SAMPLES_L * 4u)             /* 4 beats — for display / phrasing */
#define MAX_BEATS        643u                              /* longest loop 8:00 at 1.0x (the 2.0 long-
                                                            * take bump): 16 songs x 4 tracks = 76.4% of
                                                            * the 4 GB card (7,553,024 blocks), ~912 MB
                                                            * spare. Recording follows tape speed, so a
                                                            * slowed tape holds proportionally more. */
#define MAX_LOOP_SAMPLES (BEAT_SAMPLES_L * MAX_BEATS)
/* eMMC blocks for the longest loop. At 800 beats the 4 songs × 4 tracks use ~452 MB
 * (12 kHz) / ~301 MB (8 kHz) of the 4 GB card. RAM is unchanged (always streamed). */
#define MAX_LOOP_BLOCKS  (MAX_LOOP_SAMPLES / SAMP_PER_BLK)
#define MIDI_DIV         ((BEAT_SAMPLES_L + 12u) / 24u)    /* loop samples per 24-PPQN clock (rounded) */
#define NTRK             4
/* eMMC region per track, rounded UP to a 16-block (8 KB) multiple: the card's
 * internal pages are 8 KB (TE's own format writes 8 KB sectors — see the wiki's
 * Data-Structure page). With regions 8KB-ALIGNED, every 16-block flush burst
 * lands exactly on one internal page and the card can program it without a
 * read-modify-write, which is far slower than a clean page-aligned burst. */
/* round the per-track region UP to a 4096-block (2MB) multiple so every track
 * region stays 2MB-aligned. (The original reason was a pre-erase pass that has
 * since been removed; the alignment is harmless and is kept so the on-card
 * layout / META_MAGIC do not change.) */
#define TRACK_BLOCKS     ((((MAX_LOOP_BLOCKS + 8u) + 4095u) / 4096u) * 4096u)
#define RING_SAMPLES     8192u   /* M63a: STEREO FRAMES (~170 ms @48k; was 16384 mono) */                            /* ~341 ms read-ahead @48k (reverted 8192->16384 to give the compressed codecs comfortable play-ring margin) */
#define RING_MASK        (RING_SAMPLES - 1u)
/* RA-491: how full a STARVED track's ring must get before it is
 * audible again. Was RING_SAMPLES/2 = 4096 frames = 14.6 blocks =
 * ~85 ms of SILENCE on that track for a ring that ran dry by TWO
 * frames. The starve COUNT was never the audible thing -- the HOLE
 * each starve opens is. /8 = 1024 frames = ~21 ms, still 4x the
 * 5 ms fade-in ramp, so there is real hysteresis left.
 * TE's own engine holds the last good frame on a late read
 * (KB references/12-audio-engine-internals.md: held_frame_), i.e.
 * it never opens a hole at all. This is the cheap half of that. */
#define PLAY_REARM_FRAMES (RING_SAMPLES / 8u)
/* Play-ring critical margin for scheduling decisions: 128 ms expressed in
 * samples at the loop rate — EXPLICIT and codec-independent (the old
 * 24u*SAMP_PER_BLK silently varied 2.5x across codec block sizes). */
#define PLAY_CRIT_SAMPLES (128u * (LOOP_RATE / 1000u))

/* ---- SONG SLOTS + eMMC layout ----------------------------------------------
 * The looper owns the whole eMMC starting at block 0: block 0 holds the slot
 * metadata (this OVERWRITES the original TE "ALBUM_PR" index, deleting the songs
 * and reclaiming the space — they couldn't be played anyway), tracks follow.
 * NUM_SLOTS independent songs, each with its own saved BPM + 4 tracks. There are
 * 16 songs shown on the 4 status LEDs with TWO lights: the POSITION LED
 * (song % 4) is solid and the BANK LED (song / 4) blinks ~2 Hz. When the two
 * roles land on the same LED (songs 1, 6, 11, 16) it flutters fast (~4 Hz). */
#define NUM_SLOTS        16u
#define META_BLOCK       0u
#define META_BLOCKS      2u     /* 16-song index = 972 B — the exact 2-block maximum */
#define SLOT0_BLOCK      4096u  /* 2MB-aligned (block 0 = meta, 1-4095 spare) so every trk_blk stays 2MB-aligned */
/* FIXED storage signature: reflashing KEEPS the saved songs (the earlier
 * wipe-on-reflash build stamp is gone — user prefers persistence; double-tap a
 * track to delete it instead). Storage only re-formats if this constant or the
 * layout ever changes. */
/* The two sample-rate builds use different on-flash layouts (TRACK_BLOCKS
 * scales with DECIM), so each gets its own magic: switching builds is detected
 * as "unformatted" and reformats, rather than reading the other rate's data. */
/* The on-flash byte format now depends on BOTH the sample-rate build (DECIM)
 * AND the storage codec (SP1_CODEC): a different codec packs the same loop into
 * a different number of bytes/block, so the two are not interchangeable. Give
 * each (rate,codec) pair its own magic; switching either is detected as
 * "unformatted" and triggers a one-time reformat instead of mis-reading the
 * other format's bytes. */
#if DECIM == 1u
#  if   SP1_CODEC == SP1_CODEC_PCM
#define META_MAGIC       0x53453341 /* 'SE3A' (was 'S816'): a build switch reformats */u                       /* 'S816' — 48 kHz PCM, 16-song 2-block index,
                                                            * 643-beat (8:00) regions. TRACK_BLOCKS
                                                            * differs from earlier layouts, so this is a
                                                            * format break: any other index reads as
                                                            * unformatted and loop storage reformats on
                                                            * first boot — export loops as WAVs first,
                                                            * re-upload after. Grids (block 2) survive,
                                                            * same as site uploads today. */
#  elif SP1_CODEC == SP1_CODEC_ULAW
#define META_MAGIC       0x53455534u                       /* 'SEU4' — 48 kHz, u-law 8-bit */
#  else
#define META_MAGIC       0x53453341u   /* 'SE3A' 3.0 two-tier. MG-509: was
 * 0x53454134 'SEA4', which is the 48 kHz IMA-ADPCM magic AND is listed
 * in SP1-3.0-FORMAT-BREAK-SPEC section 7 among the magics 3.0 must
 * REFUSE. 500 edited the 'S816' literal instead -- but that lives in the
 * SP1_CODEC_PCM arm, which the same script kills by selecting A7, so the
 * edit landed on dead code and the log printed a magic we never built.
 * THIS line is the live #else arm. Verified from the shipped binary. */                       /* 'SEA4' — 48 kHz, IMA-ADPCM 4-bit */
#  endif
#else
#  if   SP1_CODEC == SP1_CODEC_PCM
#define META_MAGIC       0x53453241u                       /* 'SE2A' — 24 kHz, PCM 16-bit */
#  elif SP1_CODEC == SP1_CODEC_ULAW
#define META_MAGIC       0x53455532u                       /* 'SEU2' — 24 kHz, u-law 8-bit */
#  else
#define META_MAGIC       0x53454132u                       /* 'SEA2' — 24 kHz, IMA-ADPCM 4-bit */
#  endif
#endif
static inline uint32_t trk_blk(uint32_t slot, uint32_t t)
{
	return SLOT0_BLOCK + (slot * NTRK + t) * TRACK_BLOCKS;
}
/* loop_len = this song's loop length in loop-samples (a whole number of bars,
 * 0 = empty/no loop yet). Saved so a song resumes at its own length + tempo. */
/* SEGMENT looper: each track also remembers its own length (a whole multiple of
 * the base loop_len) and its phase anchor, so a song reloads with the same
 * per-track loop lengths it was recorded with. */
struct slot_state {
	uint32_t speed_q16;
	uint32_t loop_len;
	uint8_t  present[NTRK];
	uint32_t trk_len[NTRK];      /* per-track length in eMMC blocks (0 -> base) */
	uint32_t trk_start[NTRK];    /* per-track segment-0 transport-block anchor */
};
struct meta_blk {
	uint32_t magic;
	uint32_t cur_slot;
	struct slot_state slot[NUM_SLOTS];
	uint32_t fixed_len;        /* persisted loop-length mode (0=variable, 1=fixed).
	                            * APPENDED after the slots: old metas read 0 here
	                            * (the format zeroes the block), and the transfer
	                            * site reads only the slots, so this is layout-safe. */
	uint32_t trk_content[NUM_SLOTS][NTRK]; /* per-track recorded content length in blocks; 0 = whole
	                                        * track. Also appended in the tail -> layout-safe; a website
	                                        * upload zeroes it (0 = full track = correct for uploads). */
	uint32_t led_full;         /* SETTINGS WORD, site-owned (adopted in
	                            * xfer_commit like fixed_len; tail-appended
	                            * -> layout-safe). BIT 0: 1 = full LED
	                            * brightness (0 = dim, the default). BIT 1
	                            * (M41-r5): 1 = CLASSIC record arm (no head
	                            * recovery), i.e. head recovery is the
	                            * DEFAULT and bit 1 opts out. The struct is
	                            * exactly 1024 B (the 2-block maximum), so
	                            * new settings ride spare bits here. Old
	                            * indexes/sites write 0/1 -> bit 1 = 0. */
	uint8_t  chop[NUM_SLOTS][2]; /* M7a: per-song chop window: [0]=div (0/1=none,
	                              * 2..64), [1]=offset. Zeros = unchopped. */
	uint8_t  song_mode[NUM_SLOTS]; /* LOW nibble, M7c: recorded-with mode stamp:
	                                * 0 = unset (inherit the global preference),
	                                * 1 = variable, 2 = fixed.
	                                * HIGH nibble, M7-r4: per-track MUTE bits
	                                * (bit4 = track 1 .. bit7 = track 4) — a
	                                * song's muted tracks come back muted. Old
	                                * indexes read 0 = no mutes; same 'SE16'. */
};
/* The index must fit its reserved blocks: 16 songs = 972 of 1024 bytes — the
 * exact maximum of a 2-block index (17 would need three). Compile error here
 * beats storage corruption there. */
BUILD_ASSERT(sizeof(struct meta_blk) <= META_BLOCKS * EMMC_BLOCK_SIZE,
	     "meta_blk outgrew its reserved index blocks");
static struct meta_blk   g_meta;
/* ==== M72: the v3 PER-TRACK EXTENDED TABLE (blocks 3-5), M61-proven.
 * Self-validating (magic+sum): stale stock bytes read as "no table".
 * Carries SAMPLE-EXACT anchors/lengths across power cycles — closes
 * the <=2.7 ms block-rounding reload limit (Phase-B), which the v3
 * codec's bigger blocks would have widened to 5.83 ms. Streamer owns
 * writes; audio reads with a consistency cross-check, so a torn or
 * stale entry degrades to the block-derived value, never worse. ==== */
#define X3_MAGIC   0x53453358u        /* 'SE3X' */
#define X3_VER     1u
/* Card-table codec numbering (FREEZES AT SHIP -- see 414 header).
 * 0 PCM16, 1 u-law, 2 IMA4, 3 SP1-ADPCM5, 4 SP1-ADPCM7.
 * NOT the same namespace as the build-time SP1_CODEC_* selector,
 * where A7 == 3. Do not merge them. */
#define X3_CODEC_A7 4u
#define X3_BLK     3u
#define X3_NBLK    3u
struct x3_trk {
	uint32_t start_samps;
	uint32_t len_samps;
	uint32_t content_blocks;
	uint8_t  codec_id;            /* 0 PCM16 1 u-law 2 IMA4 3 A5 4 A7 */
	uint8_t  flags;               /* bit0 stereo content */
	uint8_t  pan;
	uint8_t  rsv;
};
struct x3_tab {
	uint32_t magic;
	uint16_t ver;
	uint16_t sum;                 /* over the entry bytes only */
	uint32_t rsv0, rsv1;
	struct x3_trk t[NUM_SLOTS][NTRK];
};
static struct x3_tab g_x3;
static volatile uint8_t g_x3_ok;
static uint16_t x3_sum(const struct x3_tab *tb)
{
	const uint8_t *p = (const uint8_t *)&tb->t[0][0];
	uint32_t n = (uint32_t)sizeof(tb->t), i;
	uint16_t s = 0;
	for (i = 0; i < n; i++) s = (uint16_t)(s + p[i]);
	return s;
}
static int x3_valid(const struct x3_tab *tb)
{
	return tb->magic == X3_MAGIC && tb->ver == X3_VER &&
	       tb->sum == x3_sum(tb);
}
static volatile uint32_t g_slot;
static volatile int      g_slot_switch_req;   /* main -> audio: reload tracks for the new slot */
static volatile int      g_meta_save_req;     /* -> streamer: persist g_meta to eMMC */
/* ---- TAPPED GRID (M8a): per-song tempo grid taught by FN-taps ----
 * 4+ taps in rhythm set it (first tap = downbeat); independent of the tape.
 * bpm persists in flash block 2 — unused spare, self-validating 'GRD1' tag +
 * sum, so NO format break, the site never touches it (blocks 0-1 only), and
 * older firmware simply ignores it. Phase is session-only by design: after
 * boot it re-anchors to the next tap run (or provisionally to "now"). */
#define GRID_EXT_BLOCK  2u
#define GRID_EXT_MAGIC  0x31445247u   /* 'GRD1' */
struct grid_ext {
	uint32_t magic;
	uint16_t bpm_q8[NUM_SLOTS];   /* Q8.8 BPM per song, 0 = no grid */
	uint16_t sum;                 /* 16-bit sum of bpm_q8[] (torn-write guard) */
};
BUILD_ASSERT(sizeof(struct grid_ext) <= 512, "grid ext must fit one block");
static volatile uint16_t g_grid_bpm_q8[NUM_SLOTS];
static volatile uint64_t g_grid_anchor;       /* sample-clock frame of a downbeat */
static volatile uint32_t g_grid_beat_frames;  /* I2S frames per grid beat (current song) */
static volatile uint64_t g_grid_next_tick;
static uint64_t          g_grid_tick_base;      /* M22-A: exact tick schedule base */
static uint64_t          g_grid_tick_base_sync; /* M22-A: last value WE wrote to next_tick */
static uint32_t          g_grid_tick_idx;       /* M22-A: ticks since the base */
/* M22b-r2 INSTRUMENTATION (diagnostic only): every quantity the -62 ms bench
 * anomaly could implicate, captured at the moments they are decided. */
static volatile uint32_t g_dbg_tap_bs;     /* stored beat at tap commit (frames=samples at 1.0x) */
static volatile uint32_t g_dbg_rf;         /* F8's refined beat (0 = declined) */
static volatile uint32_t g_dbg_bf;         /* g_grid_beat_frames after the stop */
static volatile uint32_t g_dbg_lens;       /* len_samps the take got */
static volatile uint32_t g_dbg_lenb;       /* len_blocks the take got */
static volatile int32_t  g_dbg_punch_ph;   /* punch phase vs grid, frames (should be ~0) */
static volatile uint32_t g_dbg_punch_sp;   /* start_samps at punch */
/* M25-r5: the anchor decision, exactly as it is made. The stored anchor is
 * consume_pos MINUS the pre-roll backfill, and the suspicion is that those two
 * do not leave it on a grid line even when pph says the punch did. Printing
 * all three settles it without another guess: cp = consume_pos at the trigger,
 * bkf = samples reached back, and the anchor's own phase against the beat,
 * which should read the SAME for every take if the anchors are beat-aligned. */
static volatile uint32_t g_dbg_anc_cp;     /* consume_pos at the trigger */
static volatile uint32_t g_dbg_anc_bkf;    /* pre_backfill applied */
static volatile uint32_t g_dbg_anc_mod;    /* start_samps % beat */
/* M25-r9: the overdub anchors read 264 and 336 samples EARLY against the beat
 * while pph says the punch landed exactly on the line. Both cannot be right —
 * but "early against a grid line" and "early against an origin that was never
 * on one" are indistinguishable in the log without the anchor to measure from.
 * Low 32 bits is plenty: the question is a phase, not an absolute. */
static volatile uint32_t g_dbg_ganc;       /* g_grid_anchor at the punch */
static volatile uint32_t g_dbg_pat;        /* g_grid_punch_at at the punch */
/* M25-r6 THE CHAIN. bf ended at 22504 while rf measured 22612 — the loop was
 * built on one beat and the grid ran on another, 0.48% apart, which walks the
 * first take ~290 ms/min away from everything recorded after it. At the punch
 * the two are tied by an identity at 1.0x speed, and refine calls grid_retune,
 * so bf SHOULD come out equal to rf. It does not. These three snapshots bracket
 * the whole path so the step that moves it is visible instead of deduced. */
static volatile uint32_t g_dbg_gbf0;       /* grid beat at TAP commit */
static volatile uint32_t g_dbg_grs0;       /* rec beat at the PUNCH */
static volatile uint32_t g_dbg_gbf1;       /* grid beat AFTER refine's retune */
static volatile uint32_t g_dbg_speed;      /* speed_q16 at punch */
/* M22c CONVERGENCE: the tempo TRUTH accrues with observation time. One take
 * of 8 beats bounds F8 at +-10-20 samples/beat (detector jitter over a short
 * span). But every gridded take leaves a fixed landmark — its first onset, at
 * an absolute stored position — and the music runs at ONE tempo through all
 * of them. Two landmarks a minute apart measure the beat to <1 sample. At
 * each gridded stop the drift between the newest landmark and the session's
 * first is folded into a per-beat correction, the grid retunes, and (the door
 * Phase B opened) every gridded track's len_samps rescales with it — the
 * loops CONVERGE onto the source instead of freezing the first estimate. */
static uint32_t g_cnv_ref;                 /* first landmark, absolute stored samples */
static uint8_t  g_cnv_set;
static uint32_t g_cnv_speed;               /* speed the landmark was laid at */
static volatile int32_t  g_dbg_cnv_beats;  /* diag: baseline length, beats */
static volatile int32_t  g_dbg_cnv_corr;   /* diag: per-beat correction applied */
/* M43 GRID FREEZE. A grid is a trust contract: loose punches are absorbed
 * by a FIXED clock. Once set — tapped, rounded, or detected — the grid
 * does not move; re-tap to change it. 0 gates the two CONTENT-CHASING
 * retunes (F8 refine at the first gridded stop; M22-C convergence at
 * every gridded stop). KEPT: the M22-A achieved-length retune (the grid
 * following the LOOP's own quantization — removing that would bring back
 * the v2.5.0 grid-vs-loop slide) and the explicit snap gesture. The
 * chase's one deliverable was multi-minute lock to an external AUDIO
 * source: zero field requests in the corpus, two maintainer-found bugs
 * in 48 h (rows 81, 82); external-sync users ask for MIDI clock IN
 * (3.0). The estimator + refine still RUN — g_dbg_rf / g_dbg_cnv_*
 * record what WOULD have been applied, field data for the 3.0 call. */
#define SP1_GRID_FOLLOW 0
/* M23 INTEGER-BPM SNAP (session-only, opt-in). Phase B is what makes this
 * worth having: with block-quantized lengths the flash grid dominated and
 * rounding the BPM changed nothing (at 128 BPM an 8-beat loop was 703.125
 * blocks either way). Sample-exact loops mean an integer BPM lands EXACTLY —
 * 2880000/128 = 22500 frames, no residual — so when the source really is a
 * whole number, snapping puts the grid on truth immediately, instead of
 * waiting for the convergence to walk there. It is opt-in because DJs pitch
 * their decks: a mix sitting at 122.2 is hurt by being forced to 122, which
 * is exactly the call the player has to make, not the machine. */
static volatile uint8_t  g_snap_sweep;     /* LED confirm: 0=idle, else frames left */
static volatile uint8_t  g_snap_took;      /* diag: the last nudge actually moved */
#define SNAP_GATE_BPM100 40u   /* 0.40 BPM, in hundredths — see bpm_snap */
/* Round a beat length (frames) to the nearest WHOLE BPM, if it is close
 * enough to be a rounding rather than a reinterpretation. Applied LAST at
 * every point the beat is decided (tap commit, F8 refine, convergence) — if
 * it ran anywhere else the two would fight, one rounding to 122 while the
 * other measures 122.2. */
static uint32_t bpm_snap(uint32_t bf)
{
	if (!bf) return bf;
	uint32_t bpm100 = (uint32_t)(((uint64_t)48000u * 60u * 100u + bf / 2u) / bf);
	uint32_t whole  = (bpm100 + 50u) / 100u;
	if (whole < 50u || whole > 200u) return bf;
	/* M25-r10 DISTANCE GATE. The nearest whole number is never more than
	 * 0.5 BPM away, so this window only ever rejects the outer part of
	 * that range — at 0.35 it passes 70% of it. The point is not safety,
	 * it is HONESTY: past the gate the machine says "that is not a whole
	 * tempo" with a shrug instead of silently inventing one. Convergence
	 * would walk a wrong snap back anyway, so a decline costs nothing.
	 * The number is set by TAP SCATTER, not by taste. marc's bench taps
	 * against a 128.000 click landed 0.02-0.45 from whole; at 0.35 five
	 * of fourteen would have shrugged at a genuinely whole tempo, which
	 * is the machine arguing with his finger. 0.40 passes thirteen of the
	 * fourteen and still declines a deliberately pitched 122.2, which is
	 * the only case the gate was ever for. Adjust only against real taps:
	 * the bench ones are the evidence, not a preference. */
	uint32_t w100 = whole * 100u;
	uint32_t d100 = (bpm100 > w100) ? (bpm100 - w100) : (w100 - bpm100);
	if (d100 > SNAP_GATE_BPM100) return bf;   /* too far: the caller shrugs */
	uint32_t nf = (uint32_t)(((uint64_t)48000u * 60u + whole / 2u) / whole);
	if (!nf) return bf;
	g_snap_took = (nf != bf);
	return nf;
}    /* next 24-PPQN tick, sample-clock domain */
static volatile uint8_t  g_grid_active;       /* current song has a live grid */
static volatile uint8_t  g_grid_save_req;     /* control -> streamer: write block 2 */
/* M8b quantized capture: with a grid, arming PUNCHES IN on the next bar line
 * (auto-start-on-sound is bypassed) and the stop rounds to the nearest grid
 * BEAT — reusing fixed mode's run-on/snap-back machinery with the tapped beat
 * as the base. Lengths quantize to a block-rounded beat so all grid takes are
 * multiples of the SAME base = mutually locked forever. */
static volatile uint64_t g_grid_punch_at;      /* sample-clock of the scheduled punch-in (0 = none) */
/* M20 F1: grid phase is TRUTH only when it came from taps THIS session on
 * THIS song ("fresh") — tapping means "I'm syncing to something external",
 * so the first take punches ON the tapped grid instead of re-anchoring it
 * (bench: instant starts planted downbeats 21-82 ms off the source).
 * Grid-from-first-take songs keep the classic your-take-IS-the-"1" feel. */
static volatile uint8_t  g_grid_fresh;
static volatile uint64_t g_arm_press_sclk;  /* A-r2: sample-clock of the
                                             * PRESS behind the current arm
                                             * (first-take punch schedules
                                             * from the finger, not the arm) */
static volatile uint8_t  g_gridrec;            /* current take was grid-punched */
static volatile uint32_t g_gridrec_beat_samps; /* grid beat in STORED samples at punch speed */
/* M20 F7: the BASE of a gridded song — beat count and block length of its
 * first grid take. Loop lengths live in whole flash blocks (256 samples,
 * 5.33 ms), and the old code rounded EACH BEAT to blocks before multiplying:
 * at 120 BPM a beat is 93.75 blocks, forced to 94, so a PERFECT tap still
 * recorded a loop that plays at 119.68 BPM — +1.33 ms every beat, compounding
 * every lap (marc's bench: 10.7 ms per 8-beat lap, 160 ms after a minute; the
 * metronome LEDs run off the unquantized grid clock, which is exactly why the
 * lights looked locked while the audio slid). Now the WHOLE take is rounded
 * once, and every later take is referenced to this base, so lengths stay exact
 * multiples of each other AND track the true tempo. */
static volatile uint32_t g_grid_base_beats;
static volatile uint32_t g_grid_base_blocks;

/* GP-518 (GEOM-PREP): per-track block-geometry accessors. In THIS build
 * they are CONSTANT 280 -- value-identical to SAMP_PER_BLK, zero new
 * state -- so this bin must BEHAVE EXACTLY like 514. The P16M codec
 * build redefines them to read the track's codec geometry. The (void)
 * arg keeps every call site compile-checked NOW, so the later flip
 * cannot surface ~70 latent argument errors at once. */
#define TSPB(tp)   ((uint32_t)((tp)->p16m ? 496u : 280u))   /* P16-522: LIVE per-track geometry */
#define TSPBI(ix)  ((uint32_t)(trk[ix].p16m ? 496u : 280u))
#define TLOOPB(ix) ({ uint32_t _ll = g_loop_len;   /* VF-523: ONE volatile read */ \
		      _ll ? (uint32_t)((_ll + TSPBI(ix) / 2u) / TSPBI(ix)) : 0u; })
#define P16M_DEFAULT 0u   /* GS-531: STEREO default; double-tap a track to
                           * toggle its record mode (gesture map v2). */

/* Blocks for n grid beats. Base-referenced when the song has one at the same
 * tempo (siblings then lock exactly); otherwise the whole run is rounded once
 * — error <= half a block per TAKE instead of half a block per BEAT. */
static uint32_t grid_len_blocks(uint32_t nbeats, uint32_t spb)   /* GP-518 */
{
	uint32_t bs = g_gridrec_beat_samps;
	if (nbeats < 1u) nbeats = 1u;
	if (!bs) return nbeats;
	if (g_grid_base_beats && g_grid_base_blocks) {
		uint32_t bb = (uint32_t)(((uint64_t)g_grid_base_blocks *
					  spb) / g_grid_base_beats);
		uint32_t d = (bb > bs) ? (bb - bs) : (bs - bb);
		if ((uint64_t)d * 100u <= (uint64_t)bs)   /* same tempo (<1%) */
			return (uint32_t)(((uint64_t)nbeats * g_grid_base_blocks +
					   g_grid_base_beats / 2u) / g_grid_base_beats);
	}
	return (uint32_t)(((uint64_t)nbeats * bs + spb / 2u) / spb);
}
/* M8c: performance layer. Mute/unmute WAITS for the bar line on gridded songs
 * (launch quantize); a tap run over EXISTING loops beatmatches (retunes the
 * tape + resyncs the loop start to the tapped downbeat at the next bar). */
static volatile uint64_t g_grid_next_bar;      /* next bar line, sample-clock domain */
static volatile uint64_t g_grid_resync_at;     /* pending loop-restart at this bar (0 = none) */
/* PASS 2 forensics (printed + zeroed each diag window): blocks delivered per
 * track, dead-history snaps per track, and round aborts (rec yield / read fail). */
static volatile uint32_t g_p2blk[4];
static volatile uint32_t g_p2snap[4];
static volatile uint32_t g_p2yield, g_p2rfail;
static volatile uint32_t g_prime_ovf;   /* M63b-r2: prime room clip bit */
/* M63b-r4 PHASE TIMING: cycles spent per streamer phase, so the
 * codec cost stops being an argument and becomes a number.
 *
 * Use DWT->CYCCNT (64 MHz core), NOT k_cycle_get_32(). The tree
 * says at the eMMC CRC counters that k_cycle_get_32 runs on the
 * 32768 Hz RTC, ~30.5 us resolution -- coarser than a whole block
 * decode. The audio engine already profiles with DWT for exactly
 * this reason ('(DWT->CYCCNT - _c0) / 64u; 64 MHz -> us'), and
 * CYCCNT is enabled once at init. 1000x the resolution, and it
 * kills the 32768/1000 = 32 integer-division bias too.
 *
 * Accumulate in uint64_t: at 64 MHz a uint32_t of CYCLES saturates
 * after only 67 s of accumulated phase time, which a real run
 * exceeds. The per-call DELTA is always short, so it stays 32-bit
 * and wraps correctly. */
/* M95-B: the inner-loop probes run 384x/block at 1.5x and cost an
 * estimated 220-500 us -- six DWT->CYCCNT PPB loads plus two volatile
 * uint64 RMWs per iteration, and they pin r11 hard enough to force two
 * stack spills, partly undoing the M93 hoist. Set to 1 to profile
 * PASS A's interior again. M81/M8X/M8Y are BLOCK-level and unaffected,
 * so `a=` still measures PASS A either way. */
#define M82_PROBES 0
static volatile uint64_t g_t_rd, g_t_dc, g_t_en, g_t_wr;
/* M95-A: CORNER-GATED twins of the M73 phase timers.
 * The originals are cumulative-since-boot, which dilutes the corner
 * across all the idle time around it -- artifact #6, the same defect
 * that made `CPU aud=` disagree with the 1 ms census. These accumulate
 * ONLY while the corner condition holds, so they answer the question
 * the ~35%% design target never actually answered.
 * Counts ride alongside so cost-per-unit is derivable, which is what
 * turns "what the streamer GOT" into "what the streamer NEEDS". */
static volatile uint64_t g_t_rd_cx, g_t_dc_cx, g_t_en_cx, g_t_wr_cx;
static volatile uint32_t g_t_rd_cxn, g_t_dc_cxn, g_t_en_cxn, g_t_wr_cxn;
/* CY-475: the same four phases under the INPUT-corner gate
 * (high speed + audio in, recording NOT required) -- the W4Y gate,
 * one layer down. */
static volatile uint64_t g_t_rd_cy, g_t_dc_cy, g_t_en_cy, g_t_wr_cy;
static volatile uint32_t g_t_rd_cyn, g_t_dc_cyn, g_t_en_cyn, g_t_wr_cyn;
/* UP-476: the PCM14S unpack, nested. ps is inside pk. */
static volatile uint64_t g_t_pk, g_t_pk_cx, g_t_pk_cy;
static volatile uint32_t g_t_pk_cxn, g_t_pk_cyn;
static volatile uint64_t g_t_ps, g_t_ps_cx, g_t_ps_cy;
static volatile uint32_t g_t_ps_cxn, g_t_ps_cyn;
/* blocks unpacked at the corner -- turns cycles into cycles/block
 * and cycles/sample without any arithmetic on the reader's part. */
static volatile uint32_t g_pk_blk;
/* RB-475: read-burst size histogram at the live PASS-2 read.
 * The burst is NOT set by a constant -- it is whatever ring headroom
 * allows, so its distribution is the only honest way to know how big
 * reads actually are at the corner. Buckets: 1-2,3-4,5-8,9-16,17-32. */
static volatile uint32_t g_rb_n[5];
static volatile uint32_t g_rb_blk, g_rb_cnt;
static volatile uint32_t g_dcc;   /* M75: a7_decode_block calls */
static volatile uint32_t g_dcu, g_dcp, g_dcr; /* M76: by caller */
static volatile uint8_t g_cap_stereo = 1u;  /* M63b-2 step 1: R=L
                                              * capture. Ring is mono
                                              * (M91); the encoder's
                                              * stereo branch reads
                                              * ring[fi] for BOTH L and
                                              * R by construction, so
                                              * setting this flag stamps
                                              * takes stereo with R = L
                                              * identical. Step 2 will
                                              * add a real R source. */
/* M80: cumulative DWT time inside the two UAC2 callbacks. */
static volatile uint64_t g_t_cb, g_t_sof;
/* M81: per-phase time in looper_audio_block. Cumulative + max. */
static volatile uint64_t g_ph[4];
static volatile uint32_t g_phmax[4];
/* M8X: the same four phases, but advancing ONLY at the corner.
 * g_ph[] is cumulative from boot and a 58 s corner vanishes into
 * the average -- the same dilution that made W4C useless until
 * W4X gated it. Gate the instrument on the condition. */
static volatile uint64_t g_cph[4];
static volatile uint32_t g_cph_n, g_cph_blk;
/* M8Y: identical to M8X except the gate -- high speed but NOT
 * recording. Differencing the two isolates the record path's cost
 * at speed from the speed-scaled walk itself. */
static volatile uint64_t g_dph[4];
static volatile uint32_t g_dph_blk;
static volatile uint64_t g_pa82[2];  /* M82: PASS A sub-spans */
static volatile uint32_t g_t1min = 0xFFFFFFFFu; /* M86 min cyc/call */
static volatile uint32_t g_enmin = 0xFFFFFFFFu; /* M88 min cyc/emit */
static volatile uint32_t g_dbg_rw, g_dbg_rr, g_dbg_rc; /* M86-r2 raw */
static volatile uint32_t g_w4_pk, g_w4_pb, g_w4_sq, g_w4_tq; /* W4P */
/* ==== S1: SHADOW CACHE state (design doc SP1-SHADOW-CACHE-DESIGN) ====
 * Shadow region: past the layout tail, SEC_COUNT-gated at boot.
 * 256 ring samples per 512-B shadow block; per-track watermark in
 * FRAMES (multiple of 256), contiguous-from-0. Disposable. */
#define SHW_BASE        (SLOT0_BLOCK + (uint32_t)NUM_SLOTS * NTRK * TRACK_BLOCKS + 131072u)
#define SHW_TRK_BLOCKS  (TRACK_BLOCKS * 3u)
#define SHW_TRK(t)      (SHW_BASE + (uint32_t)(t) * SHW_TRK_BLOCKS)
/* ==== S8Q: 8-bit stereo shadow codec (Stage 1) =====================
 * Sector: 512 B = 12 B header + 250 stereo frames x 2 B.
 * Header: tag 0x38 | u16 idx | bases (baseL<<4|baseR) | 32x2-bit offs.
 * s8q_sub[] is the ONE source of truth for sub-block sizes on both
 * the encode and decode side: divmod(250,16) -> 10x16 then 6x15.
 * Headroom 4 is the PROVABLE no-clip bound: the shaper clamp is
 * 4<<sh, so a sample lands at most 4 steps over its peak; 127-4=123.
 * e1 RESETS at every sub-block boundary -- carrying it across a
 * step-size change is invalid (bit three times on 2026-08-25).
 * Host reference + verifier: 454-s8q-packer-check.command. */
static const uint8_t s8q_sub[16] = {16,16,16,16,16,16,16,16,16,16,
                                    15,15,15,15,15,15};

static void s8q_enc_sector(const int16_t *sp, uint32_t mask, uint32_t f0,
                           uint16_t idx, uint8_t *out)
{
	uint8_t offs[32];
	out[0] = 0x38u; out[1] = (uint8_t)idx; out[2] = (uint8_t)(idx >> 8);
	out[3] = 0u;
	for (uint32_t c = 0; c < 2u; c++) {
		uint8_t want[16]; uint8_t wmax = 0u; uint32_t f = f0;
		for (uint32_t b = 0; b < 16u; b++) {
			uint32_t pk = 0u;
			for (uint32_t i2 = 0; i2 < s8q_sub[b]; i2++, f++) {
				int32_t v = sp[(f & mask) * 2u + c];
				if (v < 0) v = -v;
				if ((uint32_t)v > pk) pk = (uint32_t)v;
			}
			uint8_t sh = 0u;
			while ((pk >> sh) > 123u) sh++;
			want[b] = sh; if (sh > wmax) wmax = sh;
		}
		uint8_t base = (wmax > 3u) ? (uint8_t)(wmax - 3u) : 0u;
		out[3] |= (c == 0u) ? (uint8_t)(base << 4) : base;
		f = f0;
		for (uint32_t b = 0; b < 16u; b++) {
			uint8_t sh = (want[b] < base) ? base :
			             ((want[b] > (uint8_t)(base + 3u)) ?
			              (uint8_t)(base + 3u) : want[b]);
			offs[c * 16u + b] = (uint8_t)(sh - base);
			int32_t e1 = 0, lim = 4 << sh, half = (1 << sh) >> 1;
			for (uint32_t i2 = 0; i2 < s8q_sub[b]; i2++, f++) {
				int32_t v = (int32_t)sp[(f & mask) * 2u + c] - e1;
				if (v > 32767) v = 32767; else if (v < -32768) v = -32768;
				int32_t q = (v + half) >> sh;
				if (q > 127) q = 127; else if (q < -128) q = -128;
				e1 = (q << sh) - v;
				if (e1 > lim) e1 = lim; else if (e1 < -lim) e1 = -lim;
				out[12u + (f - f0) * 2u + c] = (uint8_t)q;
			}
		}
	}
	for (uint32_t j = 0; j < 8u; j++)
		out[4u + j] = (uint8_t)((offs[j*4u] << 6) | (offs[j*4u+1u] << 4) |
		                        (offs[j*4u+2u] << 2) |  offs[j*4u+3u]);
}

/* Decode cnt frames starting at frame li of sector sec into the
 * stereo ring dst at write head dw. Walks sectors; NO divides in the
 * sample loop. Stateless per sector (seek-safe). */
static void s8q_dec_span(const uint8_t *sec, uint32_t li, uint32_t cnt,
                         int16_t *dst, uint32_t mask, uint32_t dw)
{
	while (cnt) {
		uint8_t baseL = (uint8_t)(sec[3] >> 4);
		uint8_t baseR = (uint8_t)(sec[3] & 0x0Fu);
		uint32_t f = 0u, b = 0u;
		while (f + s8q_sub[b] <= li) { f += s8q_sub[b]; b++; }
		uint32_t rem = f + s8q_sub[b] - li;
		f = li;
		while (f < 250u && cnt) {
			uint32_t jr = 16u + b;
			uint8_t shL = (uint8_t)(baseL +
			    ((sec[4u + (b  >> 2)] >> (6u - 2u * (b  & 3u))) & 3u));
			uint8_t shR = (uint8_t)(baseR +
			    ((sec[4u + (jr >> 2)] >> (6u - 2u * (jr & 3u))) & 3u));
			while (rem && cnt) {
				int32_t yl = (int32_t)(int8_t)sec[12u + f * 2u]      << shL;
				int32_t yr = (int32_t)(int8_t)sec[12u + f * 2u + 1u] << shR;
				if (yl > 32767) yl = 32767; else if (yl < -32768) yl = -32768;
				if (yr > 32767) yr = 32767; else if (yr < -32768) yr = -32768;
				uint32_t _di = (dw & mask) * 2u;
				dst[_di]      = (int16_t)yl;
				dst[_di + 1u] = (int16_t)yr;
				dw++; f++; cnt--; rem--;
			}
			b++;
			if (b < 16u) rem = s8q_sub[b];
		}
		sec += 512u; li = 0u;
	}
}

#define X3_CODEC_P14S 5u
#define X3_CODEC_P16M 6u   /* P16-522: PCM16-mono take -- 496 engine fr / 248 stored samp per block */
#define P14S_MARK     0x5Bu
static uint8_t  g_p14s_mask;              /* bit i: track i is P14S (shadow OFF) */
static int32_t  g_p14s_e1[2];             /* encode shaper, carried within a take */
static int16_t  g_p14s_prev[NTRK][2];     /* decode continuity per track */
static uint32_t g_p14s_sh;                /* BG-470: encoder's current block-gain shift */
static volatile uint32_t g_shw_wm[NTRK];
/* #116: the shadow region is addressed by TRACK INDEX ONLY --
 * SHW_TRK(i) has no slot in it -- so every song shares the same
 * four regions and a slot change makes all four stale. */
static volatile uint32_t g_shw_slot = 0xFFFFFFFFu;
static volatile uint32_t g_shw_inv;    /* stale shadow actually discarded */
static volatile uint32_t g_shw_stale;  /* serve passed on a stale slot -- MUST STAY 0 */
static volatile uint32_t g_shw_blk, g_shw_skip, g_shw_hit;
static uint8_t g_shw_armed;
/* W4C: 1 ms statistical census — the timer ISR samples the
 * INTERRUPTED thread. Cumulative per-tid counts (Protocol A:
 * deltas belong to the analysis, not the firmware). */
static struct k_timer g_w4c_tmr;
static struct { void *tid; uint32_t n; } g_w4c_tab[8];
static volatile uint32_t g_w4c_miss;
/* CX: the corner census. g_w4c_tab is cumulative from boot and is
 * diluted by every idle second; these tick ONLY while the transport
 * is at high speed AND a take is recording -- the corner's defining
 * condition. Indices match g_w4c_tab, so no second tid table. */
#define CX_SPEED_MIN 90000u   /* ~1.373x (1.5x == 98304) */
/* g_rec_track is DEFINED further down the file than the census
 * tick that reads it -- the first CX build failed to compile on
 * exactly this, the same ordering class as the batchbuf bug in
 * 432. A tentative definition here is legal C at file scope and
 * binds to the real one below. */
static volatile int g_rec_track;
static uint32_t g_cur_speed_q16;
static volatile uint32_t g_cx_n[8];
static volatile uint32_t g_cx_tot, g_cx_hs;
/* CXW-473: the INPUT corner. Same 8 indices, a WIDER gate: high
 * speed AND the host is streaming audio in -- recording NOT
 * required. This is the condition marc actually reproduces. */
static volatile bool g_usb_streaming;
static volatile uint32_t g_cy_n[8];
static volatile uint32_t g_cy_tot;
/* RC-484: the RECORD corner at ANY speed -- marc's real workflow.
 * Same 8 indices; the only gate is that a take is recording. */
static volatile uint32_t g_cz_n[8];
static volatile uint32_t g_cz_tot;
/* EP-484: the PCM14S packer, gated on the record corner. */
static volatile uint64_t g_t_ep;
static volatile uint32_t g_t_epn, g_ep_blk;
static volatile uint32_t g_gap_max;   /* W4N: worst rec-ring gap this boot */
static uint8_t g_w4n_once;
static uint8_t g_w4c_on;
static void w4c_tick(struct k_timer *t)
{
	ARG_UNUSED(t);
	void *cur = (void *)k_current_get();
	int _cxhs = (g_cur_speed_q16 >= CX_SPEED_MIN);
	int _cx = _cxhs && (g_rec_track >= 0);
	int _cy = _cxhs && g_usb_streaming;   /* CXW-473: input corner */
	int _cz = (g_rec_track >= 0);         /* RC-484: record, ANY speed */
	if (_cxhs) g_cx_hs++;
	for (int i = 0; i < 8; i++) {
		if (g_w4c_tab[i].tid == cur) { g_w4c_tab[i].n++;
			if (_cx) { g_cx_n[i]++; g_cx_tot++; }
			if (_cy) { g_cy_n[i]++; g_cy_tot++; }
			if (_cz) { g_cz_n[i]++; g_cz_tot++; } return; }
		if (!g_w4c_tab[i].tid) { g_w4c_tab[i].tid = cur; g_w4c_tab[i].n = 1;
			if (_cx) { g_cx_n[i] = 1; g_cx_tot++; }
			if (_cy) { g_cy_n[i] = 1; g_cy_tot++; }
			if (_cz) { g_cz_n[i] = 1; g_cz_tot++; } return; }
	}
	g_w4c_miss++;
}
#define M81_LAP(K) do { uint32_t _n81 = DWT->CYCCNT, _d81 = _n81 - _lt81; \
	g_ph[K] += _d81; uint32_t _u81 = _d81 / 64u; \
	if (_u81 > g_phmax[K]) g_phmax[K] = _u81; \
	if (_cx81) g_cph[K] += _d81; \
	if (_dx81) g_dph[K] += _d81; \
	_lt81 = _n81; } while (0)
#define M73_T0() uint32_t _t73 = DWT->CYCCNT
/* M95-A: same accumulate, plus a corner-gated twin. The gate reads
 * g_play_speed_q16 (volatile, rocker-set) rather than g_cur_speed_q16
 * -- the latter is documented audio-thread-only and M73_ADD runs on
 * the STREAMER thread. */
#define M73_CX_NOW() (g_play_speed_q16 >= CX_SPEED_MIN && g_rec_track >= 0)
/* CY-475: the input-corner gate. Same shape as M73_CX_NOW, but keyed
 * on the host streaming audio IN rather than on recording. */
#define M73_CY_NOW() (g_play_speed_q16 >= CX_SPEED_MIN && g_usb_streaming)
#define M73_ADD(acc) do { uint32_t _dcx73 = (uint32_t)(DWT->CYCCNT - _t73); \
        (acc) += _dcx73; \
        if (M73_CX_NOW()) { (acc##_cx) += _dcx73; (acc##_cxn)++; } \
        if (M73_CY_NOW()) { (acc##_cy) += _dcx73; (acc##_cyn)++; } } while (0)
static volatile int      g_meta_loaded;       /* streamer -> main: g_meta read at boot */

/* Persist the 2-block song index MAGIC-LAST: block 1 (songs 9-16 + tail)
 * first, then block 0 (magic + songs 1-8). A power cut between the two
 * writes leaves the old block 0 — the old index stays fully authoritative —
 * so a torn half-new index is impossible by ordering. (Both writes usually
 * land in the card's write cache and flush together anyway; this closes the
 * rare flush-between window. See SP1-SIDE-EFFECTS-AUDIT.md §1.1.) */
static bool meta_write_blocks(const uint8_t *buf)
{
	bool ok1 = emmc_write_blocks(META_BLOCK + 1u, buf + EMMC_BLOCK_SIZE, 1);
	bool ok0 = emmc_write_blocks(META_BLOCK, buf, 1);
	return ok0 && ok1;
}

enum trk_state { TS_EMPTY, TS_ARMED, TS_REC, TS_DONE, TS_PLAY };

struct looptrk {
	volatile uint8_t  state;
	uint8_t  p16m_next;                  /* GS2-532: record mode for the NEXT take --
	                                      * the double-tap toggles THIS, never p16m,
	                                      * so a loaded take's live geometry can
	                                      * never flip under the streamer (the
	                                      * half-plugged-guitar noise, W147). */
	uint8_t  p16m;                       /* P16-522, VF-523: NOT volatile -- see W141.
	                                      * Written only at take-create/load; a stale
	                                      * read for one pass is harmless, and volatile
	                                      * reads at the ~70 geometry sites reproduce
	                                      * the W139 uniform-stall corner regression. */
	volatile uint16_t vol_q8;            /* fader volume, 256 = unity */
	int16_t  pring[RING_SAMPLES * 2u] __attribute__((aligned(4)));
	                                     /* M63a play ring: STEREO frames (L,R int16
	                                      * pairs); RING_SAMPLES counts FRAMES.
	                                      * streamer writes, audio reads */
	volatile uint32_t p_w;               /*   streamer fill frontier (loop samples) */
	volatile uint32_t r_w;               /*   rec ring: audio produce (into g_rring) */
	volatile uint32_t r_r;               /*   rec ring: streamer consume */
	volatile uint32_t rec_count;         /* samples recorded so far (audio) */
	volatile uint32_t rec_target;        /* stop after this many samples (0 = open, first loop) */
	volatile uint8_t  rec_silence;       /* live phrase ended; pad silence to rec_target */
	volatile uint8_t  muted;             /* tap-to-mute: track silenced but kept */
	volatile uint8_t  starved;           /* ring underran; silent until half-refilled */
	uint16_t          fade;              /* starve-recovery fade-in position (256 = full; mixer-only) */
	uint16_t          vol_now;           /* gain actually applied last block (mixer-only; ramps toward fader/mute target) */
	uint8_t           rec_fade;          /* stop-pad fade-down remaining, of 128 (recorder-only) */
	uint8_t           rec_fstep;         /* fade decrement per sample (fits the fade inside the pad) */
	uint32_t flush_blk;                  /* streamer: next loop block to write */
	uint32_t flush_mod;                  /* wrap the flush at this many blocks (overdub = loop len) */
	/* SEGMENT looper: a track's length is a whole multiple of the base loop. The
	 * first take sets the base; an overdub records ONE base-length segment as a
	 * bounded take, and if the button is still held when the segment boundary is
	 * reached it appends another base-length segment (and another), each one a
	 * bounded take through the same proven flush path -- never the old open-ended
	 * "record until release, then figure out the length". len_blocks is the
	 * track's total length; start_blk is the transport block where its segment 0
	 * began (the phase anchor used to line playback up with where it was cut). */
	uint32_t len_blocks;                 /* this track's total LOOP length in eMMC blocks (N * base) */
	uint32_t content_blocks;             /* blocks actually recorded; [content_blocks, len_blocks) plays
	                                      * as SILENCE synthesised on read (never written to flash), so a
	                                      * fixed-mode take finalises INSTANTLY instead of real-time-
	                                      * padding a bar of zeros. 0 == whole track (old/variable/uploaded). */
	uint32_t start_blk;                  /* transport block of this take's segment 0 (playback anchor) */
	uint32_t len_samps;                  /* M22-B: loop length in SAMPLES (the wrap the
	                                      * streamer honours on a plain, unchopped loop).
	                                      * 0 or a block multiple = classic behaviour. */
	uint32_t start_samps;                /* M22-B: playback anchor in SAMPLES */
	/* AUTO-START-ON-SOUND: a take ARMS on the button hold and the recorder only
	 * begins capturing at the first input past SOUND_THRESHOLD (armed waits
	 * as a fallback), so dead air before the first note never lands in the loop. */
	volatile int32_t  wait_peak;
	volatile uint32_t wait_ticks;
};
static struct looptrk trk[NTRK];

/* ONE SHARED record ring. Only one take is ever in flight (the press handler
 * refuses to arm while any track is ARMED/REC/DONE), so the four per-track rec
 * rings were waste: one ring TWICE the size costs 32 KB less RAM and absorbs
 * twice the eMMC-write transient (~2.4 s at the loop rate) before overflowing.
 * Overflow = a permanently corrupted take, so headroom here is what matters. */
#define RRING_SAMPLES    8192u   /* CD-463: STORED 24 kHz stereo frames.
 * Byte-identical ring (8192 x 2ch x 2B = 32,768 B) but each stored frame
 * covers TWO engine frames -> the ring spans 16,384 engine frames of time:
 * 341 ms @1.0x, ~248 ms at max (1.373x) -- the 104 ms worst write-cache
 * stall fits with margin (scenario-2 fix, watchlist W1). Counters (r_w,
 * r_r, rec_count) stay ENGINE-based; only the store/read is half-rate.
 * rhw= on the STV line is the meter; overrun line is now 2x RRING. */  /* M91: MONO frames -- capture is a mono downmix; the stereo-frame ring stored every sample twice. 341 ms backlog, the PCM-era headroom back */   /* M63a: STEREO FRAMES (~170 ms backlog; was 16384 mono) */   /* ~341 ms record backlog (reverted 32768->16384): the compressed codecs cut flush traffic, so the doubled rec ring is no longer needed; this reclaims RAM for the play-ring revert */
#define RRING_MASK       (RRING_SAMPLES - 1u)
static int16_t g_rring[RRING_SAMPLES * 2u]  /* CD-463: STORED 24k stereo frames (each = 2 engine frames; ring spans RRING_SAMPLES*2 engine frames of time) */ __attribute__((aligned(4)));
/* CD-463: capture-side boxcar hold. The pair grid is ABSOLUTE (bit0 of the
 * engine counter): even frame -> hold, odd frame -> store (hold+cur+1)>>1 at
 * physical index (counter>>1). Audio-thread only; shared by the TS_REC writer
 * and both pre-roll writers because they are one sequential stream. */
static int16_t g_cd_holdL, g_cd_holdR;
/* DMP-466: one-shot take dump state (diagnostic build only) */
static volatile uint8_t g_dmp_arm, g_dmp_state;
static uint32_t g_dmp_blk, g_dmp_n;
/* M63a: stereo frames; g_pre_w / r_w / r_r count FRAMES as before */
/* M20 PRE-ROLL: the record ring sits IDLE whenever nothing is being captured,
 * so the input is written into it continuously — the machine always remembers
 * the last stretch of what it heard. A punch that arrives LATE can then start
 * exactly on the grid line it missed, filled in from that memory: you cannot
 * record the past, but you can remember it. Costs zero RAM (the buffer already
 * existed) and one store per sample while idle. Capped at half the ring so a
 * backfilled take never starts the flush against a full buffer. */
#define PREROLL_MAX      (RRING_SAMPLES * 3u / 2u)  /* CD-463: engine frames; 3/4 of the
                                                     * 2x-engine ring = ~256 ms reach again */
/* M20b-r2: how far back a punch may REACH. Human lateness is measured in
 * milliseconds, not in beats, so the reach window is a quarter of a beat
 * CAPPED here — see the rescue site for why half a beat was too generous. */
#define PREROLL_REACH_MS 180u
static volatile uint32_t g_pre_w;         /* pre-roll write frontier (ring index) */
static volatile uint32_t g_pre_valid;     /* consecutive valid pre-rolled samples */
static volatile uint32_t g_pre_phase;     /* decimator phase while the transport is idle */
static volatile uint32_t g_pre_speed;     /* tape speed the idle ring was filled at */
static volatile uint8_t  g_done_pending;  /* a take is still flushing: ring is BUSY */
/* M41 HEAD RECOVERY (row 79), ON BY DEFAULT. The start rules are
 * unchanged (ungridded = first sound, gridded = on the line); when set,
 * an ungridded trigger scans the pre-roll ring back to the sound's
 * ONSET (capped at the press) so the 100/180 ms arm window never eats
 * the head. Clear = the exact shipped slight-hold feel. Opt-out lives
 * in BIT 1 of the index settings word (led_full): SET = classic. Set
 * on the transfer site; adopted in xfer_commit and at the boot index
 * load, like brightness (M8c). Old indexes read bit 1 = 0 -> instant,
 * so the default reaches every existing device. */
static volatile uint8_t  g_instant_rec = 1;
static volatile uint32_t g_rec_overruns;         /* diag: rec ring overflow events */
static volatile uint32_t g_starve_cnt[NTRK];     /* diag: per-track play-ring underrun episodes */
/* M98: g_starve_cnt is cumulative-since-boot, and Protocol A connects
 * the capture AFTER the run -- so every stv we have ever read is a
 * single end-of-session snapshot. Slicing the captures by tick shows
 * flat lines: identical on all 269 ticks of one run. Four snapshots
 * from four differently-shaped sessions cannot answer WHERE the
 * dropouts happen. Same defect as artifact #6, same fix as W4X:
 * gate by phase. Both bump sites are in PASS B on the audio thread,
 * so the gate reads variables already in hand and only runs when a
 * ring has ALREADY underrun -- it cannot perturb what it measures. */
static volatile uint32_t g_stv_lo;   /* below high speed              */
static volatile uint32_t g_stv_up;   /* high speed, NOT recording     */
static volatile uint32_t g_stv_cx;   /* high speed AND recording      */
static volatile uint32_t g_stv_pf;   /* a take still flushing         */
static volatile uint32_t g_stv_re;   /* RA-491: starve DURING fade-in */
#define STV_BUMP() do { \
        if (trk[i].fade < 256u) g_stv_re++;   /* RA-491 thrash */ \
        if (g_cur_speed_q16 < CX_SPEED_MIN) g_stv_lo++; \
        else if (g_rec_track >= 0)          g_stv_cx++; \
        else if (g_done_pending)            g_stv_pf++; \
        else                                g_stv_up++; \
} while (0)
/* ---- M46d: duty-cycled streamer priority boost (the TL-3 dropout fix).
 * USB interrupt load dilates the CPU-paced eMMC reads ~2x (measured:
 * cmd 455->857 us, data 474->847 us per 512 B block). When a playing
 * ring runs low the streamer briefly outranks everything but audio so
 * reads finish on time; a governor keeps main feeding the bootloader's
 * 5 s watchdog. Constants measured on hardware 2026-08-16. ---- */
volatile uint8_t g_emmc_sprint;      /* audio -> streamer: ring is low */
struct k_thread *g_str_tid;          /* the streamer, for the wrapper */
int g_pb_orig = 12345;               /* streamer's normal priority */
volatile uint8_t g_pb_on;            /* boost currently applied */
volatile uint32_t g_pb_t0;           /* boost burst start (cycles) */
static volatile uint32_t g_stored_glitch_cnt;    /* diag: wfail advance-anyway commits — a STORED glitch
                                                  * replays at the same loop spot every pass (vs a live
                                                  * underrun, which is one-shot). Separating the two is
                                                  * what previous crackle hunts were missing. */
static volatile uint32_t g_i2s_wfail_cnt;        /* diag: I2S write failures (audio-path exoneration) */
static volatile uint32_t g_audio_us_max;         /* diag: worst looper_audio_block exec time, us (DWT, session) */
static volatile int32_t  g_play_lowat = 0x7FFFFFFF; /* diag: window MIN play-ring margin, samples */
static volatile uint32_t g_rec_hiwat;            /* diag: window MAX rec-ring fill, samples */
static volatile uint8_t  g_extcsd_dump[9];       /* diag: EXT_CSD[167,166,231,502,503,198,246,192,175] */
static volatile uint8_t  g_hpi_on;               /* 1 = HPI enabled (abort lever for maintenance ops; also proves
                                                  * the card's HPI works, for a possible future write-path V4) */
static volatile uint8_t  g_emmc_quiesce;         /* 1 = shutdown flush done: park the eMMC bus */
/* eMMC internal write cache: enabled at boot if the card has one. It absorbs the
 * record write-bursts so an overdub doesn't overflow the rec ring. The cache is
 * volatile, so it is flushed to NAND once at power-off (via g_cache_flush_req) to
 * keep the loops -- never during play, which would stall the bus. */
static volatile uint8_t  g_cache_on;           /* 1 = card write cache enabled */
static volatile uint32_t g_cache_kb;           /* diag: EXT_CSD CACHE_SIZE (KB) the card reports */
static volatile int      g_cache_flush_req;    /* power-off: streamer, flush the cache now */

/* ---- USB block-transfer mode (the file-transfer website talks to this) -----
 * A tiny binary protocol over the CDC serial console lets a WebSerial page
 * read/write raw eMMC blocks, so loops can be up/downloaded as WAV. The host
 * sends an 8-byte magic to ENTER; the streamer (the only eMMC user) then pauses
 * audio and services one command at a time. Auto-exits on 'X' or a 15 s idle. */
#define SP1_XFER_ENABLE 1                      /* 1 = USB loop-transfer (website upload/download) enabled */
#if SP1_XFER_ENABLE
static volatile uint8_t  g_xfer_mode;          /* 1 = in block-transfer mode (audio paused) */
RING_BUF_DECLARE(g_cdc_rx, 1024);              /* CDC serial RX bytes, filled by the ISR */
#else
#define g_xfer_mode 0u                         /* transfer out: constant 0 so every g_xfer_mode branch drops */
#endif

static volatile uint32_t g_consume_pos;          /* shared playhead (loop samples, free-running) */
static volatile uint8_t  g_loop_active;          /* a loop exists / master clock running */
static volatile uint32_t g_loop_len;             /* master loop length, loop-samples (0 = unset) */
static volatile uint32_t g_loop_blocks;          /* g_loop_len / SAMP_PER_BLK (streamer wrap) */
static volatile int      g_rec_track = -1;       /* the one track currently recording, or -1 */
/* Master volume Q8. Default = the proven-clean speaker level (the audio firmware's
 * SPK_VOL_Q8 = 48 ~= 0.19 full-scale): the little TAS2505-driven speaker distorts
 * well below full scale, and the looper sums up to 4 tracks + the live monitor, so
 * this also keeps the mix from hard-clipping. Adjustable up to 256 via the buttons. */
/* Master volume Q8 (256 = unity). The VOL +/- buttons step a perceptual curve
 * (~3 dB/step) so each press is an equal-loudness change, smooth from full down
 * to silence. g_vol_idx = current position. (Per-track faders set vol_q8 directly.) */
static const uint16_t g_vol_table[] = {
	0, 2, 3, 4, 6, 8, 11, 16, 23, 32, 45, 64, 90, 128, 181, 256,
};
#define VOL_STEPS ((int)(sizeof(g_vol_table) / sizeof(g_vol_table[0])) - 1)  /* 15 */
static volatile int      g_vol_idx = 10;          /* -> 45 */
static volatile uint16_t g_master_vol_q8 = 45;
static volatile int      g_arm_req[NTRK];         /* main -> engine: track i pressed (start rec) */
static volatile int      g_stop_req;               /* main -> engine: track released (stop rec) */
static volatile int      g_del_req[NTRK];          /* main -> engine: double-tap = delete track i */
static volatile int      g_restart_req;            /* main -> engine: hold PLAY = jump to song start */
/* GLOBAL LOOP CHOP (performance window, scheme A'): play only 1/div of every
 * track's loop — the off'th slice. Non-destructive playback-window remap in
 * the streamer's fill math only: recorded audio, loop lengths, beat grid and
 * MIDI clock are untouched; div=1/off=0 is bit-identical to the original
 * math. Persisted per song since M7a (index chop[] bytes). */
static volatile uint32_t g_chop_div = 1;           /* 1,2,4,... 64 (1 = full loop) */
static volatile uint32_t g_chop_off = 0;           /* window index: 0..div-1 */
static volatile int      g_chop_req;               /* main -> engine: window changed, snap rings */
static volatile uint8_t  g_chop_defer;             /* M24: a CONTINUOUS window gesture is in
                                                    * progress — accumulate the edits and pay
                                                    * for them ONCE when the finger lifts. See
                                                    * the FUNCTION-release hook. */
static volatile int64_t  g_defer_t;                /* r3: last deferred edit (ms) — gates the release settle */
/* M13 HEADS MODE (prototype, session-only): FN+PLAY TRIPLE-tap toggles it.
 * Tracks 2-4 stop playing their own loops and become three extra TAPE HEADS
 * on track 1's loop, offset by quarters of its audible cycle (Count-to-Five
 * style): same audio, four phases. Faders and mutes act per head, so one
 * loop becomes a canon/texture instrument. Recording and delete are blocked
 * while active (toggle off to record); the heads' own hidden content is
 * untouched and returns when the mode ends. */
static volatile uint8_t  g_heads_mode;
/* M19a: the heads SOURCE is any track (bharris22/JustyB) — g_head_src.
 * Entry picks the lowest playing track (so heads work when track 1 is
 * empty); holding a LOADED track in heads mode makes IT the tape. */
static volatile uint8_t  g_head_src;
static uint8_t           g_head_mute_save;   /* song mutes across heads mode */
/* M19b BOUNCE: print the heads performance into an empty track as an OFFLINE
 * RENDER — the heads mix repeats exactly once per audible cycle, so one
 * rendered cycle is a seamless loop by construction, phase-locked to its
 * source and speed-independent. Snapshotted at request (gains/mutes/
 * positions/directions/window); rendered by the streamer 4 blocks per round
 * while the heads keep playing; index written ONLY after every audio block
 * (torn-write doctrine: an abort or power cut leaves an empty track).
 * On completion: promote dst, restore the song's mutes, AUTO-EXIT heads —
 * you immediately hear what you printed, in phase (locked decision). */
static volatile int8_t   g_bnc_req = -1;   /* dst track; -1 = idle */
static volatile uint8_t  g_bnc_active;
static volatile uint8_t  g_bnc_done;
static volatile uint8_t  g_bnc_abort;
static volatile uint8_t  g_led_shrug;      /* track row "no" double-blink */
static volatile uint8_t  g_pg_open;        /* PG-533: T4 MODE PAGE open (FN held) */
static uint8_t  bnc_src, bnc_dst;
static uint8_t  bnc_pos[NTRK], bnc_rev[NTRK], bnc_mut[NTRK];
static uint16_t bnc_vol[NTRK];
static uint8_t  bnc_wfree, bnc_wrev;
static uint32_t bnc_cyc, bnc_win, bnc_wbase, bnc_wper, bnc_start, bnc_content;
static uint32_t bnc_done_blocks;
static int32_t  bnc_acc[4u * 256u];        /* 4 KB chunk accumulator */
static uint8_t  bnc_rdbuf[512];            /* one source block */
#define head_active(i) (g_heads_mode && (i) != g_head_src && \
			trk[g_head_src].state == TS_PLAY)
/* M14 HEADS v2: each head's position on the loop is a live Q8 phase (0-255
 * of the audible cycle). Quarters at entry = the v1 sound; FUNCTION+fader
 * scrubs them (all four — track 1's own phase slides too, locked decision).
 * g_head_blip asks the mixer for a ~16 ms per-track dip masking a head's
 * ring re-anchor — the master is never ducked for a one-head edit. */
static volatile uint8_t  g_head_pos[NTRK];
/* M15: per-head DIRECTION (heads mode double-tap — delete is blocked there,
 * so the gesture was free). Gated on heads_engaged(): normal playback can
 * never see it; reset forward at every heads entry. Session-only. */
static volatile uint8_t  g_head_rev[NTRK];
static volatile uint8_t  g_head_blip[NTRK];
/* M16 FREE WINDOW (session-only): while FUNCTION is held OUTSIDE heads mode,
 * fader1 = window START, fader2 = END (free Q8 fractions of the chop period
 * — any width, any place, not just the stepped div/off), fader3 = SHIFT
 * (width and order kept), fader4 = nothing (the fx slot stays pended). If
 * START crosses past END the window plays in REVERSE (nervouskidz), riding
 * the M15 reverse engine. Any chop BUTTON press reclaims the stepped world
 * (clears the flag); song switch and power-off clear it too. */
static volatile uint8_t  g_win_free;
static volatile uint8_t  g_win_s8;
static volatile uint8_t  g_win_e8 = 255;
static volatile uint8_t  g_win_rev;
/* M17 DJ FILTER (session-only, M11 decisions finally cashed in): while
 * FUNCTION is held outside heads mode, FADER 4 is a center-neutral DJ
 * filter on the master sum — center = clean bypass (wide 12% notch),
 * below = LP sweep down to ~80 Hz, above = HP sweep up to ~4.5 kHz.
 * One 2-pole state-variable filter in PASS C (after the mix, before the
 * limiter — colors everything, the DJ-correct spot), Q14 coefficients
 * from the tables below, per-block smoothed so sweeps never zipper.
 * Latches where the fader leaves it; resets to neutral at power-on. */
static volatile uint8_t  g_flt_pos = 128;
static const int16_t flt_lp_tab[14] = {   /* 80 Hz .. 6.5 kHz, exp */
	172, 241, 337, 473, 664, 931, 1306, 1831,
	2566, 3595, 5033, 7032, 9788, 13524 };
static const int16_t flt_hp_tab[14] = {   /* 30 Hz .. 4.5 kHz, exp */
	64, 95, 139, 204, 301, 442, 650, 955,
	1404, 2064, 3032, 4451, 6520, 9512 };
static uint8_t           g_fh_latch[NTRK];   /* fader owes a volume re-cross */
static int               g_fh_lastq[NTRK];   /* last raw read while latched */
#define heads_engaged() (g_heads_mode && trk[g_head_src].state == TS_PLAY)
static volatile uint8_t  g_dip_req;                /* M10: controls -> mixer, declick dip at a chop edit */
static volatile uint8_t  g_off_fade;               /* M10: power-off fade — master to 0 and HOLD */
static volatile uint32_t g_beat_phase;            /* phase within a beat (loop samples), for LEDs */
static volatile int      g_emmc_ready;
static volatile int      g_dbg_beat;              /* current beat number (diag) */
static volatile int      g_dbg_btn = -1;          /* committed track button (diag) */
static uint64_t          g_sample_clock;          /* free-running I2S frames (idle metronome) */
static int64_t           g_dec_acc;
static int64_t           g_dec_accR;               /* S2CAP: R-channel decimator */
static volatile uint32_t g_rw_hw;                  /* S2CAP: rec-ring fill high-water (frames) */                /* live accumulator for record decimation (int64: cannot overflow when the transport is stopped / step rounds to 0) */
static uint32_t          g_frames_since;           /* I2S frames since the last loop-sample tick */
static uint32_t          g_pphase;                 /* Q16 playback phase */
static volatile uint32_t g_play_speed_q16 = 65536; /* tape speed when playing (Q16, 65536=1.0x); rocker sets */
static volatile uint8_t  g_fixed_len;              /* EFFECTIVE mode of the CURRENT song (M7c):
                                                    * 0 = variable (independent loop lengths),
                                                    * 1 = fixed (overdubs snap to track 1's base).
                                                    * = the song's recorded-with stamp when set,
                                                    * else the global preference below. */
static volatile uint8_t  g_mode_pref;              /* M7c: global working preference — what empty
                                                    * songs inherit. Toggling FUNCTION+PLAY on an
                                                    * EMPTY song sets this; on a RECORDED song it
                                                    * stamps that song only. Persisted in the
                                                    * index's fixed_len field. */
/* Tempo as an INTEGER BPM (rocker steps it 1 BPM per click for fine control).
 * Speed is derived exactly: speed = bpm * 65536 / LOOP_BPM_BASE, so 80 BPM is
 * exactly 1.0x — no detent/snap logic needed. Range 40..120 = 0.5x..1.5x. */
#define BPM_MIN 40
#define BPM_MAX 120
static volatile int g_play_bpm = 80;
/* auto-start thresholds (loop-sample domain @ LOOP_RATE) */
#define SOUND_THRESHOLD  1000              /* int16 level (~ -30 dBFS) */
#define SOUND_WAIT_TICKS (LOOP_RATE * 4u)  /* ~4 s fallback */
/* PERFECT-LOOP R2: the stop gesture's CONSTANT pipeline latency — ladder
 * debounce (~24 ms) + sustained-commit gate (~24 ms) + control pass (~8 ms)
 * ~= 55 ms — backdated out of every take so the captured end lands where the
 * finger did, not where the pipeline noticed. */
#define STOP_COMP_SAMPLES 2600u             /* ~55 ms at 48 kHz */
/* M96: the stop gesture's latency is NOT constant. The debounce below
 * was PASS-COUNTED, and the control pass stretches when main is starved
 * (4.60%% CPU at the corner), so the real latency scales with load. We
 * now MEASURE it: g_stop_lat_ms is the wall time from first sighting of
 * a new ladder value to its commit. Used for the backdate and printed
 * as BTN, so the stretch is visible instead of merely felt. */
#define BTN_DEBOUNCE_MS   24
static volatile uint32_t g_stop_lat_ms;
static volatile uint32_t g_stop_lat_max;
/* M44 PRESS side of the same budget: ladder debounce (~24 ms) + control
 * pass (~8 ms) ~= 32 ms between skin-on-button and the committed press.
 * Added to the A-r2 press stamp so head recovery (M41) and the gridded
 * punch schedule reach the PHYSICAL touchdown, not the commit. */
#define PRESS_COMP_MS    32
/* track-button gesture timing */
#define HOLD_RECORD_MS   180   /* physical button-down this long (ms) => RECORD; shorter => TAP */
/* M44 INSTANT ARM: an EMPTY track arms at 48 ms — above the 40 ms
 * transit/graze bound (a finger sweeping to a higher button can commit
 * a lower band for ~24-32 ms; arming on that would steal the take from
 * the button actually pressed), below any real tap's finger-down time.
 * A tap means nothing on an empty track, so there is nothing else to
 * disambiguate. Fresh-tapped-grid empty keeps 0 (A-r2). */
#define EMPTY_ARM_MS     48
#define DTAP_GAP_MS      420   /* 2nd tap within this of the 1st tap's release => DOUBLE-TAP */
#define DTAP_DEL_HOLD_MS 400   /* GS-531 (map v2 row 99): the 2nd tap HELD this long = DELETE.
                                * A QUICK 2nd tap = the mono/stereo record toggle -- the
                                * destructive gesture gets the dwell, the safe one the tap. */

/* BEAT GRID for the LED pulse + MIDI clock — defaults to the nominal beat, but
 * the first-track TEMPO ESTIMATOR replaces it with the detected beat period so
 * the lights/clock track the music. It does NOT change playback speed/pitch
 * (the rocker still does tape varispeed); it's the metronome grid only. */
static volatile uint32_t g_beat_samples = BEAT_SAMPLES_L;
static volatile int      g_det_bpm;       /* diag: last detected BPM (0 = none) */
/* PRECOMPUTED MIDI-clock divisor: loop-samples per 24-PPQN tick = g_beat_samples/24.
 * Recomputed ONLY when the tempo is (re)detected, NOT per audio sample -- so the
 * detected tempo costs one divide once, not a runtime divide 48000x/sec on every
 * track (that per-sample divide was a big part of why this build lost v2's
 * headroom). The per-sample path just runs a cheap counter (g_midi_cnt). */
static volatile uint32_t g_midi_div = (BEAT_SAMPLES_L + 12u) / 24u;
static uint32_t          g_midi_cnt;      /* counts loop-samples toward the next MIDI tick */

/* Lightweight integer onset/tempo estimator, run only over the FIRST take of an
 * empty song. Envelope follower flags onsets (energy past half the running
 * peak); the median inter-onset gap is the beat period, folded to a musical
 * range. No FFT. */
#define TEMPO_MAX_ONSETS 48u
static struct {
	int      active;
	int32_t  env;
	int32_t  peak;
	int      above;
	uint32_t first_onset;
	uint32_t last_onset;
	uint32_t ioi[TEMPO_MAX_ONSETS];
	uint32_t n;
} g_tempo;
static void tempo_reset(void)
{
	memset((void *)&g_tempo, 0, sizeof(g_tempo));
	g_tempo.active = 1;
}
static inline void tempo_feed(int16_t sv, uint32_t pos)
{
	if (!g_tempo.active) return;
	int32_t a = sv < 0 ? -sv : sv;
	g_tempo.env += (a - g_tempo.env) >> 6;
	if (g_tempo.env > g_tempo.peak) g_tempo.peak = g_tempo.env;
	int32_t thr = g_tempo.peak >> 1;
	if (!g_tempo.above && g_tempo.env > thr && thr > 200) {
		g_tempo.above = 1;
		/* M42 (row 81): advance the IOI reference ONLY on a beat-scale
		 * gap. Near-sine hits sag the envelope between half-cycles and
		 * fire 2-3 crossings per hit; the <1/8 s gaps were already
		 * dropped, but the reference still moved to the LAST SPUTTER,
		 * so every real gap measured short — a uniform ~1-3% bias the
		 * agreement guards could not see (grid retuned after a gridded
		 * take; sim-reproduced on the narrowband corpus). Rolls and
		 * fast subdivisions now accumulate into beat-multiples instead,
		 * which the musical fold already handles. */
		if (g_tempo.last_onset) {
			uint32_t d = pos - g_tempo.last_onset;
			if (d > LOOP_RATE / 8u) {
				if (g_tempo.n < TEMPO_MAX_ONSETS)
					g_tempo.ioi[g_tempo.n++] = d;
				g_tempo.last_onset = pos;
			}
		} else {
			g_tempo.last_onset = pos;
		}
		if (!g_tempo.first_onset) g_tempo.first_onset = pos ? pos : 1u;
	} else if (g_tempo.above && g_tempo.env < (thr * 3 >> 2)) {
		g_tempo.above = 0;
	}
}
static void tempo_finish(void)
{
	g_tempo.active = 0;
	if (g_tempo.n < 2u) return;
	for (uint32_t i = 1; i < g_tempo.n; i++) {
		uint32_t v = g_tempo.ioi[i]; int j = (int)i - 1;
		while (j >= 0 && g_tempo.ioi[j] > v) { g_tempo.ioi[j + 1] = g_tempo.ioi[j]; j--; }
		g_tempo.ioi[j + 1] = v;
	}
	uint32_t beat = g_tempo.ioi[g_tempo.n / 2];
	uint32_t lo = (uint32_t)((uint64_t)LOOP_RATE * 60u / 176u);
	uint32_t hi = (uint32_t)((uint64_t)LOOP_RATE * 60u / 70u);
	while (beat > hi) beat >>= 1;
	while (beat && beat < lo) beat <<= 1;
	if (beat < lo || beat > hi) return;
	g_beat_samples = beat;
	g_midi_div = (beat + 12u) / 24u;          /* precompute once: no per-sample divide */
	g_det_bpm = (int)(((uint64_t)LOOP_RATE * 60u + beat / 2u) / beat);
}
/* M20 F8: CONTENT-DERIVED TEMPO REFINEMENT — the loop learns the source's real
 * tempo from the audio it just recorded. The onset estimator above has always
 * run through every first take (tempo_reset at the punch, tempo_feed per
 * sample); on a TAPPED grid its answer was simply discarded. But human tapping
 * lands ~0.2-1% off, and that error is exactly what walks a loop off the track
 * it was recorded from (marc's bench: a 0.27% error = 1.3 ms per beat = 160 ms
 * of slide per minute). The content knows better: measure the span between the
 * first and last onset, work out how many half-beats it covers using the tap as
 * the hypothesis (it is close enough to make that unambiguous), and divide.
 *
 * Guards, so this can only ever help: at least 4 onsets; span >= 2 beats;
 * the span is CAPPED at 24 beats so that miscounting the beats by one always
 * lands >2% away and gets rejected; and the refined beat must sit within 2% of
 * the tap. Anything ambiguous (pads, drones, rubato) keeps the tapped value. */
static uint32_t tempo_span(uint32_t cap)
{
	uint32_t acc = 0u, span = 0u;
	for (uint32_t i = 0; i < g_tempo.n; i++) {
		if (acc + g_tempo.ioi[i] > cap) break;
		acc += g_tempo.ioi[i];
		span = acc;
	}
	return span;
}
/* Median gap between onsets. Sorts the list, so it must be the LAST thing to
 * read it (the span walk above needs chronological order). */
static uint32_t tempo_median_ioi(void)
{
	if (g_tempo.n < 2u) return 0u;
	for (uint32_t i = 1; i < g_tempo.n; i++) {
		uint32_t v = g_tempo.ioi[i]; int j = (int)i - 1;
		while (j >= 0 && g_tempo.ioi[j] > v) {
			g_tempo.ioi[j + 1] = g_tempo.ioi[j]; j--;
		}
		g_tempo.ioi[j + 1] = v;
	}
	return g_tempo.ioi[g_tempo.n / 2u];
}
static uint32_t tempo_refine(uint32_t bs)
{
	if (!bs || g_tempo.n < 4u) return 0u;
	if (!g_tempo.first_onset || g_tempo.last_onset <= g_tempo.first_onset)
		return 0u;
	/* M42 GATES: refinement can move a TAPPED grid, so the content must
	 * actually be discrete, regular onsets. The old code got that
	 * protection BY ACCIDENT — retrigger-corrupted gap lists failed the
	 * span checks. With true references (M42) a wobbling pad logs gaps
	 * pinned just above the 1/8 s floor, perfectly regular, plausible
	 * enough to move the tap 4%+ (caught in offline sim). Deliberate now:
	 *  - FLOOR CLEARANCE: median gap > 1.5x the floor — continuous
	 *    envelope wobble piles up at floor+eps, real onsets do not;
	 *  - REGULARITY: at least half the gaps within 12.5% of their
	 *    median — rubato and mixed material keep the tap. */
	{
		uint32_t tmp[TEMPO_MAX_ONSETS];
		memcpy(tmp, g_tempo.ioi, g_tempo.n * sizeof(tmp[0]));
		for (uint32_t i = 1; i < g_tempo.n; i++) {
			uint32_t v = tmp[i]; int j = (int)i - 1;
			while (j >= 0 && tmp[j] > v) {
				tmp[j + 1] = tmp[j]; j--;
			}
			tmp[j + 1] = v;
		}
		uint32_t med = tmp[g_tempo.n / 2u];
		if (med * 2u <= (LOOP_RATE / 8u) * 3u) return 0u;
		uint32_t good = 0;
		for (uint32_t i = 0; i < g_tempo.n; i++) {
			uint32_t d = (g_tempo.ioi[i] > med)
				   ? g_tempo.ioi[i] - med : med - g_tempo.ioi[i];
			if (d * 8u <= med) good++;
		}
		if (good * 2u < g_tempo.n) return 0u;
	}
	/* STAGE 1 — COARSE, over a SHORT span (<=4 beats). Counting half-beats
	 * here needs the hypothesis only to be better than ~6%, so even a badly
	 * tapped grid (marc's bench had one 3% out) still counts correctly. */
	uint32_t s1 = tempo_span(bs * 4u);
	if (s1 < bs * 2u) return 0u;
	uint32_t h1 = (uint32_t)(((uint64_t)s1 * 2u + bs / 2u) / bs);
	if (h1 < 4u) return 0u;
	uint32_t r1 = (uint32_t)(((uint64_t)s1 * 2u + h1 / 2u) / h1);
	uint32_t d1 = (r1 > bs) ? (r1 - bs) : (bs - r1);
	if ((uint64_t)d1 * 20u > (uint64_t)bs) return 0u;  /* >5% from the tap:
	                                                    * not the same tempo,
	                                                    * and past the count-
	                                                    * safety limit — keep
	                                                    * what was tapped */
	/* STAGE 2 — FINE, over the long span, counted with STAGE 1 (~0.15%
	 * accurate) as the hypothesis instead of the hand. A miscount here would
	 * need >1% of hypothesis error, so it cannot happen; the 24-beat cap plus
	 * the 2% agreement check make it safe twice over. Precision scales with
	 * the span: ~0.06% on percussive material. */
	uint32_t out = r1;
	uint32_t s2 = tempo_span(r1 * 24u);
	if (s2 >= r1 * 4u) {
		uint32_t h2 = (uint32_t)(((uint64_t)s2 * 2u + r1 / 2u) / r1);
		if (h2 >= 8u) {
			uint32_t r2 = (uint32_t)(((uint64_t)s2 * 2u + h2 / 2u) / h2);
			uint32_t d2 = (r2 > r1) ? (r2 - r1) : (r1 - r2);
			if ((uint64_t)d2 * 50u <= (uint64_t)r1) out = r2;
		}
	}
	/* SUBDIVISION SANITY. Both stages can share one mistake: if the onset
	 * that ends a measuring window sits on a TRIPLET or swung subdivision,
	 * the half-beat count lands wrong and the two stages agree with each
	 * other on the wrong answer (~5% out). So cross-check against a
	 * statistic that does not depend on the count at all — the typical gap
	 * between hits must be a simple fraction or multiple of the result
	 * (1/4, 1/3, 1/2, 1, 2, 3, 4). Straight material passes trivially; a
	 * triplet-corrupted answer misses every ratio and the tapped tempo is
	 * kept instead. */
	{
		uint32_t med = tempo_median_ioi();
		if (med) {
			static const uint8_t rn[7] = { 1u, 1u, 1u, 1u, 2u, 3u, 4u };
			static const uint8_t rd[7] = { 4u, 3u, 2u, 1u, 1u, 1u, 1u };
			int ok = 0;
			for (int k = 0; k < 7; k++) {
				uint32_t want = (uint32_t)(((uint64_t)out * rn[k] +
							    rd[k] / 2u) / rd[k]);
				if (!want) continue;
				uint32_t dm = (med > want) ? (med - want) : (want - med);
				if ((uint64_t)dm * 33u <= (uint64_t)want) { ok = 1; break; }
			}
			if (!ok) return 0u;   /* nothing musical fits: keep the tap */
		}
	}
	return out;
}

/* Apply a refined beat to the SONG GRID as well, so the metronome, the MIDI
 * clock and every later punch follow the corrected tempo instead of the tapped
 * one (otherwise overdubs would quantize to a grid the base loop no longer
 * agrees with). Phase is untouched — only the spacing changes. */
/* Forward tentative declaration: the smoothed tape speed is defined further
 * down (audio thread only) but beat_set has to derive the recording beat from
 * it, and it must be the SAME variable the punch uses — g_play_speed_q16 is
 * the rocker's setting, not the settled value, and picking a different one
 * here would reintroduce exactly the inconsistency this change removes. */
static uint32_t g_cur_speed_q16;

/* M25-r7 THE ONE OWNER. The beat lived in three variables written from twelve
 * places, tied together only by a convention asserted once at the punch and
 * never re-checked. That is how the loop and the grid ended up on tempos 0.48%
 * apart (rf=22612 vs bf=22504) and walked the first take ~290 ms/min away from
 * everything recorded after it — a divergence no read of the code could
 * explain, because nothing in the code forbade it.
 * Now: every mechanism PROPOSES a beat in grid-domain frames and calls this.
 * This is the only writer. The grid/recording identity is structural instead of
 * conventional, so the divergence is no longer expressible. */
static void beat_set(uint32_t nf)
{
	if (!nf) return;
	g_grid_beat_frames = nf;
	/* recording domain follows the tape, exactly as the punch derived it */
	uint32_t rs = (uint32_t)(((uint64_t)nf * g_cur_speed_q16) >> 16);
	if (!rs) rs = nf;
	g_gridrec_beat_samps = rs;
	g_beat_samples       = rs;
	g_midi_div           = rs / 24u;
	if (g_slot < NUM_SLOTS) {
		g_grid_bpm_q8[g_slot] = (uint16_t)((48000ULL * 60u * 256u) / nf);
		g_grid_save_req = 1;
	}
	{ uint64_t _bar = (uint64_t)nf * 4u;
	  g_grid_next_bar = g_grid_anchor +
		(((g_sample_clock - g_grid_anchor) / _bar) + 1u) * _bar; }
}

/* Convert a RECORDING-domain beat to grid domain and hand it to beat_set. The
 * three estimator paths (refine, achieved-length, convergence) all measure in
 * stored samples, so they come through here; the snap already has a grid-domain
 * number and calls beat_set directly. Same ratio maths as before — but it no
 * longer WRITES anything, so it can no longer preserve a divergence. */
static void grid_retune(uint32_t old_bs, uint32_t new_bs)
{
	if (!old_bs || !new_bs || !g_grid_beat_frames) return;
	beat_set((uint32_t)(((uint64_t)g_grid_beat_frames * new_bs +
			     old_bs / 2u) / old_bs));
	g_grid_next_tick = g_sample_clock;
}

/* Boot STOPPED (no auto-play): the saved song loads paused; PLAY (tap=resume,
 * hold=from the top) or recording starts the tape. The device used to blast the
 * last loop the instant it powered up — annoying after a flash or plug-in. */
static volatile uint8_t  g_playing = 0;            /* PLAY/STOP: target speed ramps to 0 when stopped */
static uint32_t          g_cur_speed_q16 = 0;      /* smoothed actual speed Q16 (audio thread only) */
static volatile int      g_midi_stop_pending;      /* send MIDI Stop on pause */
/* 24-PPQN clock: SINGLE-WRITER counters (audio produces, midi consumes its own
 * count). A shared pending counter with ++/-- from two threads loses pulses on
 * ARM (volatile is not atomic), drifting any synced external gear. */
static volatile uint32_t g_midi_clk_produced;      /* audio thread writes ONLY */
static volatile int      g_midi_start_pending;     /* send MIDI Start on loop activation */

static inline int16_t clamp16(int32_t x)
{
	if (x > 32767) return 32767;
	if (x < -32768) return -32768;
	return (int16_t)x;
}

/* SOFT LIMITER for the mix bus: 4 tracks at unity + the live monitor easily sum
 * past full-scale, and a hard clamp turns every peak into harsh square-wave
 * crunch ("bit-crushing" / distortion when channels stack). Below TH the signal
 * is untouched; above it the excess is compressed along a hyperbolic knee that
 * asymptotes to full-scale, so loud sums round off smoothly instead of clipping.
 * Integer, branch-light, ~no cost. */
static inline int16_t soft_limit(int32_t x)
{
	const int32_t TH = 26000;        /* ~0.8 FS linear region */
	const int32_t HEAD = 32767 - TH; /* room above the knee   */
	int32_t s = (x < 0) ? -1 : 1;
	int32_t a = x * s;               /* |x| */
	if (a > TH) {
		int32_t over = a - TH;       /* compress: y = TH + HEAD*over/(over+HEAD) */
		/* M95-C: the int64 form compiles to bl __aeabi_uldivmod, called
		 * 2x per output frame -- up to 512 library divisions per block on
		 * loud material. HEAD is 6767, so HEAD*over stays under 2^31 for
		 * over < 317346; below that the whole expression fits in uint32
		 * and becomes ONE hardware udiv. The 64-bit arm is kept so this
		 * is bit-exact for every input, not merely for reachable ones:
		 * clamping instead of branching diverges from |x| = 344002 up.
		 * Verified 0 differing samples over +/-2,000,000. Reachable max
		 * over = 137835 (4 tracks + monitor, full scale) -- 2.3x inside. */
		if (over < 317000)
			a = TH + (int32_t)(((uint32_t)HEAD * (uint32_t)over) / (uint32_t)(over + HEAD));
		else
			a = TH + (int32_t)(((int64_t)HEAD * over) / (over + HEAD));
	}
	return (int16_t)(s * a);         /* a <= 32767 by construction */
}
/* mix-only -O2: the audio hot path. Safe here (unlike global -O2): the two signed-
 * overflow UB sites are fixed with int64 casts, -fno-strict-aliasing is global, and
 * this function contains NO flash-write code -- same per-function -O2 already proven
 * werr-safe on the eMMC read path. Speeds the per-frame interp/volume/limit work. */
/* M85-r2: the rec-write chain, machine-extracted from the tree
 * (M84) with a MECHANICAL field-pointer transform. Do not edit
 * by hand; r1 hand-transcription broke the stereo ring store. */
__attribute__((optimize("O2"), noinline))
static void rec_write_sample(int16_t lsamp, int16_t rsamp)
{
					struct looptrk *rt = &trk[g_rec_track];
					/* M85-r2: one address computation per field per CALL --
					 * struct looptrk is 32,840 B with control fields past
					 * +0x8000 (beyond Thumb-2 imm12); naive access pays
					 * movw+mla per field per sample (M84 disasm). Volatile
					 * semantics, store order, per-sample publish: UNCHANGED. */
					volatile uint32_t * const prw = &rt->r_w;
					volatile uint32_t * const prr = &rt->r_r;
					volatile uint32_t * const prc = &rt->rec_count;
					volatile uint32_t * const ptg = &rt->rec_target;
					if (((*prw) - (*prr)) >= (RRING_SAMPLES * 2u))  /* CD-463: 2x engine capacity */
						g_rec_overruns++;   /* take corrupting: flush too slow */
					int16_t wsamp = lsamp;
					int16_t wsampR = rsamp;
					if (rt->rec_silence) {
						uint8_t fg = rt->rec_fade;
						if (fg) {
							wsamp  = (int16_t)(((int32_t)lsamp * fg) >> 7);
							wsampR = (int16_t)(((int32_t)rsamp * fg) >> 7);
							uint8_t st = rt->rec_fstep ? rt->rec_fstep : 1u;
							rt->rec_fade = (fg > st) ? (uint8_t)(fg - st) : 0u;
						} else {
							wsamp = 0; wsampR = 0;
						}
					} else if ((*ptg)) {
						/* fixed-mode run-to-the-bar: fade the final ~2.7 ms
						 * into the bar line so the loop seam can't click */
						uint32_t rem = (*ptg) - (*prc);
						if (rem <= 128u) {
							wsamp  = (int16_t)(((int32_t)lsamp *
									   (int32_t)rem) >> 7);
							wsampR = (int16_t)(((int32_t)rsamp *
									   (int32_t)rem) >> 7); }
					}
					{ /* CD-463: 24k store — boxcar pairs; counters stay engine-based */
					  if (((*prw) & 1u) == 0u) { g_cd_holdL = wsamp; g_cd_holdR = wsampR; }
					  else { uint32_t _fi = (((*prw) >> 1) & RRING_MASK);
					    g_rring[_fi * 2u]      = (int16_t)(((int32_t)g_cd_holdL + (int32_t)wsamp  + 1) >> 1);
					    g_rring[_fi * 2u + 1u] = (int16_t)(((int32_t)g_cd_holdR + (int32_t)wsampR + 1) >> 1); } }
					(*prw)++;
					(*prc)++;
					{ uint32_t _bl = (*prw) - (*prr);   /* S2CAP meter */
					  if (_bl > g_rw_hw) g_rw_hw = _bl; }
					/* RP: the per-sample pre-roll frontier store is DELETED
					 * 72,000/s. Its only reader is at block START and the
					 * block TAIL republishes that global regardless,
					 * so nothing could ever observe it. (It also means
					 * "pre-roll follows the take" has not worked since
					 * M90 -- a real bug, logged, NOT fixed here.) */
					if (g_tempo.active) tempo_feed(lsamp, (*prc));
					if ((*ptg) == 0u) {
						/* OPEN take (first take AND independent overdubs):
						 * force-stop at the maximum length. Only a FIRST
						 * take defines the song grid/BPM. */
						if ((*prc) >= MAX_LOOP_SAMPLES) {
							if (g_loop_len == 0u) {
								g_loop_len = MAX_LOOP_SAMPLES;
								g_loop_blocks = (g_loop_len + SAMP_PER_BLK / 2u) / SAMP_PER_BLK;
								tempo_finish();
								if (g_slot < NUM_SLOTS) {
									g_meta.slot[g_slot].loop_len = g_loop_len;
									g_meta_save_req = 1;
								}
							}
							(*ptg) = MAX_LOOP_SAMPLES;
							rt->len_blocks = MAX_LOOP_BLOCKS;
							rt->len_samps = MAX_LOOP_SAMPLES;
							rt->content_blocks = MAX_LOOP_BLOCKS;  /* all content */
							rt->state = TS_DONE; g_rec_track = -1;
							g_done_pending = 1;   /* M20: ring busy */
						}
					} else if ((*prc) >= (*ptg)) {
						/* Take FINALIZE: rec_target is set by the stop tap
						 * (free-length, block-rounded) — the recorder pads
						 * the sub-block remainder with silence and lands
						 * here. The take now loops at its own length. */
						rt->state = TS_DONE; g_rec_track = -1;
							g_done_pending = 1;   /* M20: ring busy */
					}
}
__attribute__((optimize("O2")))
static void looper_audio_block(int16_t *s)
{
	static int16_t tmp[BLK_FRAMES * 2];
	if (g_xfer_mode) { memset(s, 0, BLK_BYTES); return; }   /* USB transfer: silence out */
	uint32_t _lt81 = DWT->CYCCNT;   /* M81 phase clock */
	/* M8X: one predicate per BLOCK, not per frame. Same gate as W4X. */
	const int _cx81 = (g_cur_speed_q16 >= CX_SPEED_MIN) && (g_rec_track >= 0);
	const int _dx81 = (g_cur_speed_q16 >= CX_SPEED_MIN) && (g_rec_track < 0);
	if (_cx81) g_cph_blk++;
	if (_dx81) g_dph_blk++;
	{ /* M46d: sprint flag with hysteresis — ON under 4096 smp (~85 ms),
	   * OFF at 4800 smp (~100 ms); steady-state fill is ~110 ms. */
	  uint32_t _sp_c = g_consume_pos; int _sp_low = 0;
	  for (int _sp_i = 0; _sp_i < NTRK; _sp_i++)
	    if (trk[_sp_i].state == TS_PLAY &&
	        (int32_t)(trk[_sp_i].p_w - _sp_c) <
	            (g_emmc_sprint ? (int32_t)4800 : (int32_t)4096)) {
	      _sp_low = 1; break;
	    }
	  { /* M87: the rec-ring flush needs the SAME storm immunity the
	     * play rings got in 2.7.2. Measured (M86-r2, raw indices):
	     * flush sustains ~160 blk/s under USB vs 171.4 demand; the
	     * 8,192-frame ring is lapped ~1 s into a take and capture
	     * corrupts. M55-r3 proved 376 blk/s at sprint priority under
	     * the same storm. Pressure = >2 pages (2x16 blocks) queued;
	     * the existing 150/15 duty cycle bounds the boost. */
	    int _rt87 = g_rec_track;
	    if (_rt87 >= 0 && trk[_rt87].state == TS_REC &&
	        (trk[_rt87].r_w - trk[_rt87].r_r) > 2u * 16u * TSPBI(_rt87))
		_sp_low = 1;
	  }
	  g_w4_tq++; if (_sp_low) g_w4_sq++;   /* W4P */
	  g_emmc_sprint = (uint8_t)_sp_low;
	}
	/* PREBUFFER: do not start draining a freshly-(re)enabled stream until the
	 * ring holds FB_SETPOINT frames — the feedback regulator over-delivers to
	 * fill it in ~20 ms. Without this gate the consumer races the empty ring and
	 * the first moments of every host play start dribble out as choppy fragments
	 * (this gate existed in the old direct path but was lost in the looper). */
	static bool primed;
	/* SCHED-LOCKED cluster: the mixer is PREEMPT(0) now, so the COOP USB
	 * threads can preempt it mid-ring_buf_get — and the terminal-toggle
	 * callback resets this ring (documented unsafe against a concurrent
	 * get). The lock (~tens of us) restores exactly the atomicity the old
	 * COOP(7) mixer had for this cluster; USB ISO service only needs to
	 * preempt the ~ms-scale MIX work below, never this copy. */
	k_sched_lock();
	if (!g_usb_streaming)
		primed = false;
	else if (!primed &&
		 ring_buf_size_get(&usb_audio_ring) >= FB_SETPOINT * USB_FRAME_BYTES)
		primed = true;
	if (primed) {
		/* diag: usb-in ring fill watermarks — the LIVE INPUT is the record
		 * source, and none of the eMMC counters can see it starve. */
		int32_t _uf = (int32_t)(ring_buf_size_get(&usb_audio_ring) / USB_FRAME_BYTES);
		if (_uf < g_usb_lowat) g_usb_lowat = _uf;
		if (_uf > (int32_t)g_usb_hiwat) g_usb_hiwat = (uint32_t)_uf;
		/* U3-471: same sample, cumulative (survives the blind run) */
		if ((uint32_t)_uf > g_u3_ring_hi) g_u3_ring_hi = (uint32_t)_uf;
		if ((uint32_t)_uf < g_u3_ring_lo) g_u3_ring_lo = (uint32_t)_uf;
	}
	uint32_t bytes = primed ?
		ring_buf_get(&usb_audio_ring, (uint8_t *)tmp, sizeof(tmp)) : 0;
	k_sched_unlock();
	uint32_t got = bytes / USB_FRAME_BYTES;
	if (primed && got < BLK_FRAMES) {
		g_ring_underruns++;
		g_zero_pad += BLK_FRAMES - got;   /* silence frames injected (and recorded) */
	}

	/* FAILSAFE — exactly one recorder. Every block, find the single ARMED/REC
	 * track and make g_rec_track the one source of truth; if a second recorder
	 * somehow appeared, demote it back to play/empty. This guarantees recording
	 * can only ever touch one track at a time, no matter what races upstream. */
	{
		int only = -1;
		for (int i = 0; i < NTRK; i++) {
			uint8_t st = trk[i].state;
			if (st != TS_ARMED && st != TS_REC) continue;
			if (only < 0) only = i;
			else trk[i].state = (g_slot < NUM_SLOTS &&
					     g_meta.slot[g_slot].present[i]) ? TS_PLAY : TS_EMPTY;
		}
		g_rec_track = only;
	}

	/* PROVISIONAL AUTO-CONFIRM (engine-side, control-loop-independent): once
	 * a provisional take has captured ~150 ms of real material it is clearly
	 * not a transit graze (grazes abort within ~100 ms via the press-edge
	 * guard) — confirm it so the streamer starts flushing well inside the
	 * rec ring's ~341 ms horizon even if the control loop is frozen
	 * (FUNCTION page / USB transfer) before its own confirm could run.
	 * Without this a frozen control loop left a zombie RAM-only take that
	 * overflowed its ring and was discarded at the eventual stop tap. */
	/* DOUBLE-TAP DELETE: clear the track — abort any take it has in flight,
	 * drop it from the song, persist. If it was the song's only content, the
	 * song resets to empty (the next take sets a fresh loop length). Ring
	 * indices are NOT touched here: a mid-flush streamer pass may still be
	 * draining them (finite, writes land in the deleted track's own region);
	 * every take start re-zeroes them anyway. */
	for (int i = 0; i < NTRK; i++) {
		if (!g_del_req[i]) continue;
		g_del_req[i] = 0;
		if (g_rec_track == i) g_rec_track = -1;
		if (trk[i].state == TS_DONE)
			g_done_pending = 0;   /* M22-A: deleting a still-flushing take
			                       * must free the rec ring, or pre-roll is
			                       * silently OFF for the session (the only
			                       * other clear is the promotion, which
			                       * needs TS_DONE to still be true). Only
			                       * one take can flush at a time, so there
			                       * is never a second one to protect. */
		trk[i].state = TS_EMPTY;
		trk[i].rec_silence = 0; trk[i].rec_target = 0; trk[i].rec_count = 0; trk[i].muted = 0;
		trk[i].len_blocks = 0; trk[i].start_blk = 0; trk[i].content_blocks = 0;  /* drop all its segments */
		trk[i].len_samps = 0; trk[i].start_samps = 0;
		if (g_slot < NUM_SLOTS) {
			g_meta.slot[g_slot].present[i] = 0;
			g_meta.slot[g_slot].trk_len[i] = 0;
			g_meta.slot[g_slot].trk_start[i] = 0;
			g_meta.trk_content[g_slot][i] = 0;   /* keep the on-flash block self-consistent */
			{	/* FX3-537: the x3 row dies with the take (the removed
				 * save-service refresh used to do this). rsv survives:
				 * the per-song preference outlives its takes. */
				struct x3_trk *_xe = &g_x3.t[g_slot][i];
				_xe->start_samps = 0; _xe->len_samps = 0;
				_xe->content_blocks = 0;
				_xe->codec_id = 0; _xe->flags = 0; _xe->pan = 128u;
			}
			g_meta.song_mode[g_slot] &= (uint8_t)~(uint8_t)(0x10u << i); /* M7-r4: unmute */
		}
		int any = 0;
		for (int k = 0; k < NTRK; k++)
			if (trk[k].state != TS_EMPTY ||
			    (g_slot < NUM_SLOTS && g_meta.slot[g_slot].present[k]))
				any = 1;
		if (!any) {
			g_loop_len = 0; g_loop_blocks = 0; g_loop_active = 0;
			g_grid_base_beats = 0; g_grid_base_blocks = 0;   /* M20 F7 */
			if (g_slot < NUM_SLOTS) {
				g_meta.slot[g_slot].loop_len = 0;
				g_meta.song_mode[g_slot] = 0;   /* M7c: unstamp */
				g_meta.chop[g_slot][0] = 0;     /* M7a: unchop  */
				g_meta.chop[g_slot][1] = 0;
			}
			g_chop_div = 1; g_chop_off = 0;
			g_win_free = 0; g_win_rev = 0;          /* M16 */
			g_fixed_len = g_mode_pref;              /* rejoin global */
		}
		g_meta_save_req = 1;
	}

	/* HOLD-TO-RECORD. A track button held down records that track; releasing it
	 * stops. The FIRST take starts immediately and its hold duration sets the
	 * master length (snapped to whole bars on release); later tracks (overdubs)
	 * arm and begin on the next beat, in sync. Only one track records at a time. */

	/* RELEASE -> stop the current take */
	if (g_stop_req) {
		g_stop_req = 0;
		int i = g_rec_track;
		if (i >= 0 && i < NTRK) {
			if (trk[i].state == TS_ARMED) {
				/* cancelled before any sound — or while still PROVISIONAL
				 * (an empty-track instant arm whose press turned out to be
				 * a transit graze toward a higher button). A provisional
				 * take has only captured into RAM (PASS 1 skips its flush),
				 * so aborting leaves NO trace: no flash write, no junk
				 * take, no grid/BPM hijack on an empty song, and the
				 * transport state the arm forced is put back. */
				/* -> back to PLAY/EMPTY. */
				trk[i].state = (g_slot < NUM_SLOTS && g_meta.slot[g_slot].present[i])
					       ? TS_PLAY : TS_EMPTY;
				g_rec_track = -1;
				g_grid_punch_at = 0;   /* M8b: cancel the scheduled punch */
				if (g_loop_len == 0u) {
					/* A sole-track re-record ARM reset the song grid and the
					 * playhead. A cancel must UNDO that damage: restore the
					 * saved grid, and re-anchor every playing ring to the
					 * (reset) playhead — without this the track replays one
					 * stale ~341 ms ring chunk for as long as the song had
					 * been running (PASS 2 believes the ring is pinned full)
					 * and the NEXT take hijacks the song grid. */
					if (g_slot < NUM_SLOTS && g_meta.slot[g_slot].loop_len) {
						g_loop_len = g_meta.slot[g_slot].loop_len;
						g_loop_blocks = (g_loop_len + SAMP_PER_BLK / 2u) / SAMP_PER_BLK;
					}
					int anyp = 0;
					for (int k = 0; k < NTRK; k++)
						if (trk[k].state == TS_PLAY) {
							anyp = 1;
							trk[k].p_w = g_consume_pos;  /* starve -> clean refill */
						}
					if (!anyp) g_loop_active = 0;
				}
			} else if (trk[i].state == TS_REC) {
				/* FREE-LENGTH stop (every take): the loop is EXACTLY what was
				 * recorded — no quantization to the first track's grid, no
				 * silence padding while you hunt for the loop point. Rounded
				 * only to the 256-sample storage block (~±2.7 ms, inaudible)
				 * so the eMMC streaming stays block-aligned. The FIRST take
				 * of a song additionally defines the beat grid + BPM (LEDs,
				 * MIDI clock); later tracks free-run on their own cycles. */
				/* CONTENT length = the audio actually recorded, rounded UP to a
				 * whole block so nothing is lost. rec_target is set to CONTENT,
				 * not the (possibly longer) loop length, so the recorder pads
				 * only this final <1 block and finalises INSTANTLY on the tap. */
				/* R2 (perfect-loop): backdate the stop by the constant
				 * gesture latency so the end lands on the finger, not
				 * on the pipeline. */
				/* M96: the gesture latency is not constant -- it stretches
				 * with main's CPU share, so a fixed 55 ms backdate leaves the
				 * take ending LATE under load. Use the measured value.
				 * FLOORED at the old constant so the healthy case cannot
				 * regress, CEILINGed at 8x so a pathological reading can
				 * never eat the take. 48 samples per ms at 48 kHz. */
				uint32_t _comp96 = g_stop_lat_ms * 48u;
				if (_comp96 < STOP_COMP_SAMPLES)      _comp96 = STOP_COMP_SAMPLES;
				if (_comp96 > STOP_COMP_SAMPLES * 8u) _comp96 = STOP_COMP_SAMPLES * 8u;
				uint32_t rc = trk[i].rec_count;
				if (rc > _comp96 + TSPBI(i))
					rc -= _comp96;
				uint32_t content = (rc + TSPBI(i) - 1u)
						   / TSPBI(i);
				if (content < 1u) content = 1u;
				else if (content > MAX_LOOP_BLOCKS) content = MAX_LOOP_BLOCKS;
				/* M8b QUANTIZED STOP: a grid-punched take rounds to the
				 * NEAREST grid beat. The beat is block-rounded ONCE and
				 * shared by every grid take -> all lengths are multiples
				 * of the same base and stay locked to each other. */
				uint32_t glen = 0, gbb = 0, gbeats = 0;
				if (g_gridrec && g_gridrec_beat_samps) {
					if (g_loop_len == 0u) {
						/* M20 F8: trust the recording over the
						 * tapping — refine the beat from the
						 * onsets this take just captured, and
						 * retune the grid to match. */
						uint32_t rf =
							tempo_refine(g_gridrec_beat_samps);
						g_dbg_rf = rf;             /* r2 diag */
						/* M43: measured, recorded, NOT applied —
						 * the tapped/snapped grid is the clock. */
						if (SP1_GRID_FOLLOW && rf) {
							grid_retune(g_gridrec_beat_samps, rf);
							g_det_bpm = (int)(((uint64_t)LOOP_RATE *
								60u + rf / 2u) / rf);
							/* r7: beat_set already derived the rec beat
							 * from the grid. Re-assigning it here is
							 * exactly what let the two come apart. */
						}
						g_dbg_gbf1 = g_grid_beat_frames;   /* r6 */
					}
					gbb = (g_gridrec_beat_samps + TSPBI(i) / 2u)
					      / TSPBI(i);
					if (gbb < 1u) gbb = 1u;
					/* M20 F7: count beats from the PRECISE beat length,
					 * then ask for that many beats' worth of blocks —
					 * never beats-times-a-rounded-beat. */
					uint64_t csam = (uint64_t)content * TSPBI(i);
					uint32_t gm = (uint32_t)((csam +
						g_gridrec_beat_samps / 2u) / g_gridrec_beat_samps);
					if (gm < 1u) gm = 1u;
					uint32_t nearest = grid_len_blocks(gm, TSPBI(i));
					if (g_loop_len == 0u) {
						/* M8b-r3 FIRST TAKE: TRIM-BACK policy — the
						 * stop is instant and a loop can never
						 * contain silence. Run on only in the
						 * "nailed it" window (last ~15% of a beat);
						 * otherwise snap DOWN to the last whole
						 * beat (overhang stays on flash, unplayed).
						 * Tap-tempo drift made the old run-to-the-
						 * line wait long enough to read as "still
						 * recording" (user report). */
						uint32_t flb = (uint32_t)(csam /
							       g_gridrec_beat_samps);
						uint32_t fl = flb ? grid_len_blocks(flb, TSPBI(i)) : 0u;
						/* M20 F2: round to the NEAREST beat (window
						 * 16% -> 50%), matching the overdub policy.
						 * Bench: the trim-back cost marc a beat at
						 * his best (7 for an intended 8) and left a
						 * 7-vs-8 polymeter. Max run-on = half a beat
						 * with the double-blink cue. */
						uint32_t win = gbb / 2u;
						if (content < gbb) {
							glen = grid_len_blocks(1u, TSPBI(i));
							gbeats = 1u;    /* degenerate: complete 1 beat */
						} else if (nearest > fl &&
						         (nearest - content) <= win) {
							glen = nearest; /* tiny run-on to the line */
							gbeats = gm;
						} else {
							glen = fl;      /* trim back — instant */
							gbeats = flb;
						}
					} else {
						glen = nearest;         /* overdub: fixed-style */
						gbeats = gm;
					}
					if (glen > MAX_LOOP_BLOCKS) glen = 0;  /* fall back free */
				}
				if (g_loop_len == 0u) {
					uint32_t base = glen ? glen : content;
					/* M22-B: a gridded take's loop is EXACTLY its beats
					 * times the true beat — no longer forced onto a
					 * flash-block boundary. 8 beats at 128 BPM is
					 * 180000 samples now, not 179968: the loop and the
					 * source can no longer diverge, which is the whole
					 * mechanism behind "layers drift apart" (bench:
					 * -32 samples/lap = 10.7 ms/min at 128, and worse
					 * elsewhere; 120 BPM was one of only 12 tempos in
					 * 60-200 that could not show it). Blocks stay what
					 * the flash reads; samples are what the loop IS. */
					if (glen && gbeats && g_gridrec_beat_samps)
						g_loop_len = gbeats * g_gridrec_beat_samps;
					else
						g_loop_len = base * TSPBI(i);
					g_loop_blocks = base;
					if (glen && gbb) {
						/* the TAPPED grid defines the beat — exact
						 * stored-domain beat, not the estimator.
						 * The estimator is DONE here: this branch
						 * never called tempo_finish(), so it was
						 * left running for the rest of the session
						 * and kept sampling through every later
						 * overdub for an answer nobody reads. */
						g_tempo.active = 0;
						/* M22-A: THE GRID FOLLOWS THE LOOP. The loop
						 * wraps at a block-quantized length, so the
						 * beat it can actually honour is stored/beats
						 * — up to 128 samples per take away from the
						 * true beat. v2.5.0 kept the TRUE beat on the
						 * grid, so grid lines slid past the loop at
						 * up to ~9 samples a beat and later overdubs
						 * punched visibly off the layers already
						 * down (bench: +16 ms in 85 s at 128 BPM).
						 * The loop is the instrument; the grid now
						 * tunes itself to what the loop plays.
						 * (Residual: the song as a whole still runs
						 * at the quantized tempo vs an external
						 * source — that is M22 Phase B's job.) */
						if (gbeats) {
							/* M22-B: with sample-exact lengths the
							 * achievable beat IS the true beat, so
							 * this Phase-A retune self-disarms; it
							 * still guards the fallback paths. */
							uint32_t ach = (uint32_t)
								((g_loop_len + gbeats / 2u) / gbeats);
							if (ach && ach != g_gridrec_beat_samps) {
								grid_retune(g_gridrec_beat_samps, ach);
								g_det_bpm = (int)(((uint64_t)LOOP_RATE *
									60u + ach / 2u) / ach);   /* r7 */
							}
						}
						g_beat_samples = g_gridrec_beat_samps;
						g_midi_div = g_gridrec_beat_samps / 24u;
						if (gbeats) {   /* M20 F7: the base to lock to */
							g_grid_base_beats = gbeats;
							g_grid_base_blocks = glen;
						}
					} else
					tempo_finish();         /* set the detected beat grid + BPM */
					if (g_slot < NUM_SLOTS) {
						g_meta.slot[g_slot].loop_len = g_loop_len;
						g_meta.song_mode[g_slot] = (uint8_t)
							((g_meta.song_mode[g_slot] & 0xF0u) |
							 (g_fixed_len ? 2u : 1u)); /* M7c stamp */
						g_meta_save_req = 1;
					}
				}
				uint32_t len = content;
				uint32_t tgt = content * TSPBI(i);   /* default: stop now */
				uint8_t  sil = 1;                        /* pad the final sub-block */
				if (trk[i].rec_target && !trk[i].rec_silence) {
					/* SECOND tap while a fixed-mode take is running on to
					 * the bar line (below): stop IMMEDIATELY — the loop
					 * keeps the already-snapped bar length; the unfilled
					 * remainder plays as silence (the old behavior, as an
					 * escape hatch). */
					len = trk[i].len_blocks;
					if (g_gridrec && g_gridrec_beat_samps) {
						/* M8b-r3: on a GRID take the escape trims to
						 * the last WHOLE beat instead of amputating
						 * mid-beat and leaving a silent tail. */
						uint32_t nb2 = (uint32_t)((uint64_t)trk[i].rec_count /
									  g_gridrec_beat_samps);
						uint32_t bb2 = grid_len_blocks(1u, TSPBI(i));
						if (nb2 >= 1u) {
							uint32_t fl2 = grid_len_blocks(nb2, TSPBI(i));
							if (fl2 >= bb2) {
								len = fl2;
								content = fl2;
								tgt = fl2 * TSPBI(i);
							}
						}
					}
				} else if (glen) {
					/* M8b: grid take — same early/late machinery as
					 * fixed mode, with the tapped beat as the base:
					 * EARLY -> run on to the grid line capturing live;
					 * LATE -> snap back (overhang never plays). */
					len = glen;
					if (glen * TSPBI(i) > trk[i].rec_count) {
						content = glen;
						tgt = glen * TSPBI(i);
						sil = 0;
					}
				} else if (g_fixed_len && TLOOPB(i)) {
					/* FIXED mode: round to the NEAREST whole multiple of
					 * the base — ceil-only rounding gapped BOTH ways
					 * (community: stop a hair early and the tail padded
					 * with silence; a hair late and nearly a whole extra
					 * bar of silence was appended).
					 *  - stopped EARLY (before the nearest bar): the tap
					 *    SCHEDULES the stop — recording runs on to the bar
					 *    line capturing live audio, so the loop ends ON
					 *    the bar with real sound in it (the emit path
					 *    fades the final ~2.7 ms into the seam). The track
					 *    LED stays on until the bar; tap again to force an
					 *    immediate stop.
					 *  - stopped LATE (past the nearest bar): snap BACK to
					 *    it — the overhang stays on flash but is never
					 *    played (promotion fades the new seam). */
					uint32_t mult = (content + TLOOPB(i) / 2u) / TLOOPB(i);
					if (mult < 1u) mult = 1u;
					uint32_t nlen = mult * TLOOPB(i);
					if (nlen <= MAX_LOOP_BLOCKS) {
						len = nlen;
						if (nlen * TSPBI(i) > trk[i].rec_count) {
							/* EARLY: run on to the bar, capturing live */
							content = nlen;
							tgt = nlen * TSPBI(i);
							sil = 0;
						}
					}
					/* nlen over the region: len stays = content, stop now */
				}
				trk[i].content_blocks = content;     /* audio ends here */
				trk[i].len_blocks     = len;         /* loop length */
				/* M22-B: the sample-exact wrap. Gridded takes are whole
				 * beats of the TRUE beat; everything else keeps the
				 * block length exactly as before (their loop-vs-grid
				 * question does not exist). */
				trk[i].len_samps = (glen && gbeats && g_gridrec_beat_samps)
						 ? gbeats * g_gridrec_beat_samps
						 : len * TSPBI(i);
				g_dbg_lens = trk[i].len_samps;         /* r2 diag */
				g_dbg_lenb = len;
				g_dbg_bf   = g_grid_beat_frames;
				/* M22c CONVERGENCE (gridded takes with an onset only) */
				if (glen && gbeats && g_gridrec_beat_samps &&
				    g_tempo.first_onset) {
					uint32_t abs_k = trk[i].start_samps +
							 g_tempo.first_onset;
					if (!g_cnv_set) {
						g_cnv_ref = abs_k;
						g_cnv_speed = g_cur_speed_q16;
						g_cnv_set = 1;
						g_dbg_cnv_beats = 0; g_dbg_cnv_corr = 0;
					} else if (g_cur_speed_q16 == g_cnv_speed &&
						   abs_k > g_cnv_ref) {
						uint32_t bs2 = g_gridrec_beat_samps;
						uint32_t el = abs_k - g_cnv_ref;
						uint32_t nb = (el + bs2 / 2u) / bs2;
						g_dbg_cnv_beats = (int32_t)nb;
						g_dbg_cnv_corr = 0;
						if (nb >= 16u) {
							int64_t dev = (int64_t)el -
								(int64_t)nb * bs2;
							int32_t corr = (int32_t)
								((dev >= 0 ? dev + (int64_t)nb / 2
								           : dev - (int64_t)nb / 2)
								 / (int64_t)nb);
							if (corr > 16) corr = 16;
							if (corr < -16) corr = -16;
							uint32_t nbs = corr
								? (uint32_t)((int32_t)bs2 + corr)
								: bs2;
							/* M43: measured, recorded, NOT applied. */
							if (SP1_GRID_FOLLOW && nbs != bs2) {
								grid_retune(bs2, nbs);   /* r7: sole writer */
								g_det_bpm = (int)(((uint64_t)LOOP_RATE *
									60u + nbs / 2u) / nbs);
								/* rescale every gridded loop —
								 * the lengths are just numbers
								 * now (Phase B), and they are
								 * all N x the beat */
								for (int k2 = 0; k2 < NTRK; k2++) {
									uint32_t Lk = trk[k2].len_samps;
									if (!Lk) continue;
									uint32_t Nk = (Lk + bs2 / 2u) / bs2;
									if (!Nk) continue;
									uint32_t Ln = Nk * nbs;
									/* M25-r8: this used to clamp to
									 * content_blocks * 256. content is
									 * the RECORDED AUDIO; len_samps is
									 * the MUSICAL length, and on a
									 * gridded take those differ on
									 * purpose — the stop rounds to the
									 * nearest beat and pads out to the
									 * line, so the loop is legitimately
									 * longer than the audio in it. That
									 * pad is up to HALF A BEAT, and the
									 * clamp threw it away in one step
									 * the first time convergence
									 * retuned — i.e. at the SECOND
									 * take's stop, which is exactly
									 * where marc heard track 1 jump.
									 * It guarded nothing: the rescale is
									 * proportional and corr is capped at
									 * +/-16 per beat, so Ln cannot run
									 * past the allocation. Sanity-bound
									 * the CHANGE instead; refuse absurd
									 * ones rather than truncating. */
									uint32_t dL = (Ln > Lk) ? (Ln - Lk)
											        : (Lk - Ln);
									if (Ln && (uint64_t)dL * 16u <=
									          (uint64_t)Lk)
										trk[k2].len_samps = Ln;
									/* C-r2: the wrap MOVED — the ring
									 * still holds audio fetched under
									 * the old length, and playing it
									 * across the new seam is a hard
									 * splice (marc heard it). Same
									 * cure as every chop edit: drop
									 * the read-ahead, refill under
									 * the new geometry, boundary-fade
									 * covers the joint. */
									if (trk[k2].state == TS_PLAY)
										trk[k2].p_w =
											(g_consume_pos / TSPBI(k2))
											* TSPBI(k2);
								}
								g_dip_req = 1;   /* C-r2: declick, like
								                  * every chop edit */
								{	/* master follows the base */
									uint32_t Nb = (g_loop_len + bs2 / 2u) / bs2;
									if (Nb) g_loop_len = Nb * nbs;
									if (g_slot < NUM_SLOTS) {
										g_meta.slot[g_slot].loop_len = g_loop_len;
										g_meta_save_req = 1;
									}
								}
								g_dbg_cnv_corr = (int32_t)nbs - (int32_t)bs2;
							}
						}
					}
				}
				trk[i].rec_target     = tgt;
				/* end the live phrase. When padding (immediate stops), the
				 * pad used to be hard zeros — a click baked into the seam;
				 * fade the first 128 pad samples (~2.7 ms) down instead. */
				trk[i].rec_silence = sil;
				g_gridrec = 0;
				if (sil) {
					trk[i].rec_fade = 128;
					/* the pad is only rec_target - rec_count samples
					 * (0..255); steepen the slope so the fade always
					 * COMPLETES inside it. */
					uint32_t pad = trk[i].rec_target - trk[i].rec_count;
					trk[i].rec_fstep = (pad && pad < 128u)
						? (uint8_t)((128u + pad - 1u) / pad) : 1u;
				}
			}
		}
	}

	/* PRESS -> start recording that track (if nothing else is recording) */
	for (int i = 0; i < NTRK; i++) {
		if (!g_arm_req[i]) continue;
		g_arm_req[i] = 0;
		if (!g_emmc_ready) continue;
		if (g_rec_track >= 0) continue;                       /* one at a time */
		/* ONE take in flight, device-wide: refuse while ANY track is armed,
		 * recording, or still flushing (TS_DONE). The rec ring is SHARED, so a
		 * second take during a drain would interleave into the same buffer; and
		 * two flushes would also exceed the eMMC write budget. The press becomes
		 * valid the moment the drain finishes (sub-second; LED solid meanwhile). */
		int busy = 0;
		for (int k = 0; k < NTRK; k++) {
			uint8_t st = trk[k].state;
			if (st == TS_REC || st == TS_ARMED || st == TS_DONE) busy = 1;
		}
		if (busy) continue;
		/* sole track in the song -> allow a fresh length (reset only the in-RAM
		 * master; the saved length is rewritten when this new take completes).
		 * ANY non-empty state on another track counts as "others" — including
		 * TS_DONE (a take still flushing to the card): resetting the length while
		 * another take is mid-flush would corrupt it. */
		int others = 0;
		for (int k = 0; k < NTRK; k++)
			if (k != i && (trk[k].state != TS_EMPTY ||
				       (g_slot < NUM_SLOTS && g_meta.slot[g_slot].present[k])))
				others = 1;
		if (!others) { g_loop_len = 0; g_loop_blocks = 0; g_loop_active = 0;
			       g_grid_base_beats = 0; g_grid_base_blocks = 0; }

		if (g_loop_len == 0u) {
			/* FIRST take: start the transport NOW so the recorder can watch the
			 * input, but DON'T capture yet — recording begins at the first sound
			 * (auto-start), at which point the playhead is reset so that sound is
			 * loop position 0. Snap the tape speed so no spin-up ramp is baked in. */
			g_cur_speed_q16 = g_play_speed_q16;   /* snap to the set tape speed */
			g_loop_active = 1; g_consume_pos = 0;
			g_pphase = 0; g_frames_since = 0; g_dec_acc = 0; g_dec_accR = 0;
		}
		/* ARM (first take AND overdub): wait for the first sound, then the tick
		 * handler begins the capture so the loop starts exactly on the audio. */
		trk[i].r_w = 0; trk[i].r_r = 0; trk[i].flush_blk = 0;
		trk[i].flush_mod = MAX_LOOP_BLOCKS;
		trk[i].rec_count = 0; trk[i].rec_silence = 0; trk[i].rec_target = 0; trk[i].muted = 0;
		if (g_slot < NUM_SLOTS)   /* M7-r4: a fresh take is audible — unmute */
			g_meta.song_mode[g_slot] &= (uint8_t)~(uint8_t)(0x10u << i);
		trk[i].wait_peak = 0; trk[i].wait_ticks = 0;
		if (g_grid_active && g_grid_beat_frames) {
			if (g_loop_len == 0u && !g_grid_fresh) {
				/* M8b-r5 (kept for UNTAPPED grids): the first take
				 * punches immediately and places the downbeat —
				 * your take IS the "1". The r2 contradiction (wait
				 * for a phase, then discard it) stays resolved this
				 * way HERE; on fresh-tapped grids it's resolved the
				 * other way below (M20 F1: keep the phase). */
				g_grid_punch_at = g_sample_clock ? g_sample_clock : 1u;
			} else {
				/* M20 F1+F3: overdubs — and FIRST takes on a
				 * FRESHLY TAPPED grid (the taps said "sync to
				 * this") — punch on the next BEAT line. F3: beat,
				 * not bar — the <=2 s bar count-in was the "way
				 * too late" report; the wait is <=1 beat now, and
				 * stops still snap to whole beats so every loop
				 * stays locked. The armed LED fast-blinks. */
				uint64_t unit = (uint64_t)g_grid_beat_frames;
				/* A-r2: the FIRST take on a fresh grid schedules
				 * from the PRESS — pressing before the line catches
				 * that line exactly (the trigger fires the moment
				 * the arm lands if the line just passed: bounded
				 * ~25-30 ms worst case, never a full-beat wait).
				 * Overdubs keep arm-time scheduling: their 180 ms
				 * hold is a deliberate content-track gesture filter,
				 * and arming early achieves line-exact there. */
				uint64_t ref = (g_loop_len == 0u && g_arm_press_sclk &&
						g_arm_press_sclk > g_grid_anchor)
					     ? g_arm_press_sclk : g_sample_clock;
				uint64_t off = ref - g_grid_anchor;
				g_grid_punch_at = g_grid_anchor +
					((off + unit - 1u) / unit) * unit;
			}
			g_arm_press_sclk = 0;
		} else {
			g_grid_punch_at = 0;
		}
		/* NOTE: len_blocks/start_blk are NOT reset here -- they are set when the
		 * first sound lands (TS_REC). Leaving them intact means a re-record that
		 * is cancelled (released before any sound) returns the track to PLAY with
		 * its ORIGINAL length, not a clobbered one. */
		trk[i].state = TS_ARMED;
		g_rec_track = i;
	}

	/* HOLD PLAY -> jump to the start of the song and play. Rewind the shared
	 * playhead to 0 and reset every track's read frontier so the streamer refills
	 * each loop from its first block; they all restart together, in sync. Ignored
	 * while recording (so a take isn't disrupted). */
	if (g_restart_req) {
		g_restart_req = 0;
		if (g_rec_track < 0 && g_loop_active) {
			g_consume_pos = 0; g_pphase = 0; g_frames_since = 0; g_dec_acc = 0; g_dec_accR = 0; g_midi_cnt = 0;
			for (int i = 0; i < NTRK; i++) trk[i].p_w = 0;
			g_playing = 1;
			g_midi_start_pending = 1;
		}
	}

	/* CHOP CHANGE: drop the (old-window) read-ahead so the new window is
	 * audible within one refill round (~20-40 ms, boundary-faded by the
	 * starve machinery) instead of after ~341 ms of stale ring. */
	if (g_chop_req) {
		g_chop_req = 0;
		for (int i = 0; i < NTRK; i++)
			if (trk[i].state == TS_PLAY)
				trk[i].p_w = (g_consume_pos / TSPBI(i)) * TSPBI(i);
	}

	/* SONG SWITCH: reload the tracks for the newly-selected slot. Tracks that the
	 * slot already has recorded -> PLAY (streamer refills from that slot's eMMC
	 * region from block 0); empty tracks -> ready to record. Restart the loop. */
	if (g_slot_switch_req) {
		g_slot_switch_req = 0;
		g_consume_pos = 0; g_pphase = 0; g_frames_since = 0; g_dec_acc = 0; g_dec_accR = 0; g_midi_cnt = 0;
		g_rec_track = -1;
		/* this song's remembered loop length (0 = empty, ready for a fresh take) */
		g_loop_len    = (g_slot < NUM_SLOTS) ? g_meta.slot[g_slot].loop_len : 0;
		g_loop_blocks = (g_loop_len + SAMP_PER_BLK / 2u) / SAMP_PER_BLK;
		int any = 0;
		for (int i = 0; i < NTRK; i++) {
			uint8_t pres = (g_slot < NUM_SLOTS) ? g_meta.slot[g_slot].present[i] : 0;
			trk[i].state = pres ? TS_PLAY : TS_EMPTY;
			trk[i].p_w = 0;
			trk[i].rec_silence = 0; trk[i].rec_target = 0; trk[i].rec_count = 0;
			/* M7-r4: the song's saved mutes come back with it */
			trk[i].muted = (pres && g_slot < NUM_SLOTS &&
			                (g_meta.song_mode[g_slot] & (0x10u << i))) ? 1u : 0u;
			{	/* FX2-536: the per-song NEXT-mode preference loads for
				 * EVERY track -- the old latch sat inside the presence
				 * guard, so empty tracks (the main use case) never
				 * restored it (marc: "songs not saving the settings"). */
				uint8_t _rv = (g_x3_ok && g_slot < NUM_SLOTS)
				            ? g_x3.t[g_slot][i].rsv : 0u;
				if (_rv & 0x80u)
					trk[i].p16m_next = (uint8_t)(_rv & 1u);
				if (!pres) {
					trk[i].p16m = 0;   /* empty: no take, clean geometry */
					if (!(_rv & 0x80u)) trk[i].p16m_next = 0;
				}
			}
			/* SEGMENT: restore this track's own length + phase anchor (older saves
			 * with trk_len==0 fall back to the base length = one segment). */
			if (pres && g_slot < NUM_SLOTS) {
				trk[i].p16m = (g_x3_ok && g_x3.t[g_slot][i].codec_id
				               == X3_CODEC_P16M) ? 1u : 0u;   /* P16-522:
				               * BEFORE the TSPBI(i) length math below */
				{	/* PS-535: per-song NEXT-mode preference. */
					uint8_t _rv = (g_x3_ok && g_slot < NUM_SLOTS)
					            ? g_x3.t[g_slot][i].rsv : 0u;
					trk[i].p16m_next = (_rv & 0x80u)
					                 ? (uint8_t)(_rv & 1u)
					                 : trk[i].p16m;   /* old cards: follow the take */
				}
				uint32_t L = g_meta.slot[g_slot].trk_len[i];
				trk[i].len_blocks = L ? L : TLOOPB(i);
				{	/* M22-B: rebuild the sample length from the stored
					 * master (loop_len is SAMPLES and now carries the
					 * true length). A track is a whole multiple of the
					 * base, so multiple x master = its exact samples.
					 * Anchors reload block-rounded (<=2.7 ms once per
					 * load) — the known Phase-B limit; live sessions
					 * are sample-exact. */
					uint32_t Lb = trk[i].len_blocks;
					uint32_t ms = g_loop_len;
					if (ms && Lb && (ms % TSPBI(i)) != 0u) {
						uint32_t mult = (uint32_t)
							(((uint64_t)Lb * TSPBI(i) +
							  ms / 2u) / ms);
						if (!mult) mult = 1u;
						trk[i].len_samps = mult * ms;
					} else {
						trk[i].len_samps = Lb * TSPBI(i);
					}
				}
				trk[i].start_blk  = g_meta.slot[g_slot].trk_start[i];
				/* M25 BUG FIX: this used to sit one line ABOVE the
				 * load, so it read the anchor belonging to the
				 * PREVIOUSLY loaded song (or 0 at boot) — not the
				 * block-rounded anchor the comment above claims, an
				 * arbitrary one. First takes anchor at block 0 and
				 * survived; overdubs came back at the wrong phase
				 * after a song switch or power-cycle. Introduced by
				 * M22-B, found while planning M25. */
				trk[i].start_samps = trk[i].start_blk * TSPBI(i);
				trk[i].content_blocks = g_meta.trk_content[g_slot][i]; /* 0 = whole track */
				/* M72: adopt the EXACT persisted values when the v3
				 * entry is consistent with the index (torn/stale ->
				 * keep the block-derived fallback above). */
				if (g_x3_ok && g_slot < NUM_SLOTS) {
					const struct x3_trk *xe = &g_x3.t[g_slot][i];
					uint32_t Lb2 = trk[i].len_blocks;
					if (xe->len_samps && Lb2 &&
					    /* r2: the INDEX rounds half-up, not ceil */
					    ((xe->len_samps + TSPBI(i) / 2u) /
					     TSPBI(i)) == Lb2 &&
					    (xe->start_samps / TSPBI(i)) ==
					     trk[i].start_blk) {
						trk[i].len_samps   = xe->len_samps;
						trk[i].start_samps = xe->start_samps;
					}
				}
			} else {
				trk[i].len_blocks = 0; trk[i].start_blk = 0;
				trk[i].len_samps = 0; trk[i].start_samps = 0;
				trk[i].content_blocks = 0;
			}
			if (pres) any = 1;
		}
		g_loop_active = any && (g_loop_len > 0);
	}

	/* ---- TAPE-EFFECT speed smoothing (once per block, like the SP-1) ----
	 * target = the rocker speed when playing, 0 when stopped. A one-pole filter
	 * glides the actual speed toward the target by 2% per block, giving the tape
	 * ramp on play/pause AND on tempo changes. Recording does NOT force 1.0x any
	 * more: capture ticks in the loop-sample domain at the current speed, so an
	 * overdub lands exactly as heard at ANY speed — and there's no pitch JUMP
	 * when record starts/stops. The Q16 step feeds the resampler below. */
	uint32_t target_q16 = g_playing ? g_play_speed_q16 : 0u;
	int32_t sd = (int32_t)target_q16 - (int32_t)g_cur_speed_q16;
	if (sd > -64 && sd < 64) g_cur_speed_q16 = target_q16;                 /* snap when ~there */
	else g_cur_speed_q16 = (uint32_t)((int32_t)g_cur_speed_q16 + sd / 50); /* one-pole ~2%/block */
	/* At exact unity, drop any fractional-phase residue left by the spin-up
	 * ramp (one-time <=1/2-sample jump, inaudible): otherwise frac stays
	 * nonzero forever and every playing track pays the interpolation
	 * multiply per frame despite running at 1.0x. */
	if (g_cur_speed_q16 == 65536u && g_playing && (g_pphase & 0xFFFFu))
		g_pphase &= ~0xFFFFu;
	uint32_t step = g_cur_speed_q16 / DECIM;                              /* Q16 per I2S frame */

	/* Snapshot per-track fader volume once per block. vol_q8 is volatile (reloaded
	 * every frame at -Os), but its only writer is the lower-priority controls path
	 * and the mixer (PREEMPT 0) outranks it, so it is constant
	 * across the 256 frames -- the snapshot is bit-identical and drops ~1024 reloads. */
	uint16_t vol_s[NTRK];
	for (int i = 0; i < NTRK; i++) vol_s[i] = trk[i].vol_q8;

	M81_LAP(0);
	/* ==== M90: PASS A ran on VOLATILES. Every reference was a forced
	 * reload; ~60 of them per inner-loop iteration, which is why the
	 * loop cost 338 cycles (634 recording) for a decimate and one ring
	 * store. Hoist the audio-thread-private ones into locals for the
	 * duration of the block and publish once at the end.
	 *
	 * SAFE because the STREAMER CANNOT RUN INSIDE PASS A: audio is
	 * PREEMPT(0), streamer PREEMPT(5), and PASS A has no blocking call.
	 * The streamer already only ever saw whole-block snapshots.
	 *
	 * NOT hoisted, deliberately: trk[].r_w (g_rring[] is non-volatile,
	 * so hoisting r_w lets the compiler sink array stores past the
	 * publish -- needs a barrier), g_rec_track (needs a finalize
	 * publication point), and trk[].state / trk[].r_r / g_done_pending
	 * (the STREAMER writes those -- read-only, never written back).
	 *
	 * g_dec_acc stays 64-bit: paused with a loop present, step rounds
	 * to 0, the inner while never fires, and it accumulates unbounded
	 * at 48 kHz -- int32 would overflow in ~1.37 s. */
	uint32_t _pphase   = g_pphase;
	int64_t  _dec_acc  = g_dec_acc;
	int64_t  _dec_accR = g_dec_accR;
	uint32_t _fsince   = g_frames_since;
	uint32_t _pre_w    = g_pre_w;
	uint32_t _pre_val  = g_pre_valid;
	uint32_t _cpos     = g_consume_pos;
	const uint8_t _lactive = g_loop_active;
	/* ==== PASS A: transport + record, stashing per-frame positions ====
	 * The old single loop interleaved all four tracks' mixing into every
	 * frame, paying loop + volatile-read overhead 4 x 48000 times a second
	 * even for empty tracks — measured with the kernel's thread stats at
	 * 31% CPU stopped / 40% playing, which starved the eMMC streamer below
	 * the refill rate it needed (the cut-outs while recording track 4).
	 * Restructured into per-block passes: A) advance transport + record
	 * exactly as before, stashing each frame's playhead position + phase;
	 * B) one tight accumulation loop per PLAYING track; C) master volume +
	 * limiter + stereo write-out. Arithmetic, ordering and per-frame starve
	 * semantics are unchanged — the loops are merely inverted so per-track
	 * invariants hoist out of the 48 kHz hot path. */
	static uint32_t posb[BLK_FRAMES];
	static uint16_t fracb[BLK_FRAMES];
	static int32_t  mix32[BLK_FRAMES];   /* LEFT bus */
	static int32_t  mix32R[BLK_FRAMES];  /* M63a RIGHT bus */
	for (uint32_t f = 0; f < BLK_FRAMES; f++) {
		/* The UAC2 input is a stereo pair and always has been; the
		 * engine simply summed it away. liveL/liveR feed the monitor;
		 * `live` keeps the EXACT former value so every record-path
		 * consumer stays bit-exact (asserted in this stage's gate). */
		int32_t liveL = (f < got) ? (int32_t)tmp[2 * f]      : 0;
		int32_t liveR = (f < got) ? (int32_t)tmp[2 * f + 1]  : 0;
		int32_t live  = (liveL + liveR) >> 1;

		/* (the first take is started immediately by the press handler above, and
		 * overdubs are started on the next beat by the wrap logic below) */
		mix32[f] = liveL; mix32R[f] = liveR;    /* the live monitor is STEREO.
		                                         * PASS B and PASS C were already
		                                         * two-channel (M63a stages 2, 3);
		                                         * only this fetch was still mono. */
		posb[f]  = _cpos;
		fracb[f] = (uint16_t)(_pphase & 0xFFFFu);

		/* advance the playback phase; each integer step is one loop-sample tick */
		/* S2CAP: accumulate TRUE channels. `live` (the downmix) still
		 * feeds threshold/tempo consumers; the RECORDED signal is now
		 * the real L and the real R. */
		_dec_acc += liveL; _dec_accR += liveR; _fsince++;
		if (_lactive) {
			_pphase += step;
			while (_pphase >= 65536u) {
				_pphase -= 65536u;
				/* Decimate the live input to the current tape rate.
				 * >1x (frames_since==0, a 2nd+ emit in one input frame):
				 * HOLD the current sample instead of emitting a zero — the
				 * old zero-stuffing was the metallic aliasing/bitcrush. 1x:
				 * the one accumulated sample. <1x: average the frames. */
				int16_t lsamp, rsamp;
				if (_fsince == 0u)    { lsamp = (int16_t)liveL; rsamp = (int16_t)liveR; }
				else if (_fsince == 1u) { lsamp = (int16_t)_dec_acc; rsamp = (int16_t)_dec_accR; }
				else if (_fsince < 65536u)
				{ lsamp = (int16_t)((int32_t)_dec_acc /
							  (int32_t)_fsince); /* hw SDIV, bit-identical */
				  rsamp = (int16_t)((int32_t)_dec_accR /
							  (int32_t)_fsince); }
				else { lsamp = (int16_t)(_dec_acc / (int64_t)_fsince);
				       rsamp = (int16_t)(_dec_accR / (int64_t)_fsince); }
				_dec_acc = 0; _dec_accR = 0; _fsince = 0;

#if M82_PROBES
				uint32_t _r82 = DWT->CYCCNT;   /* M82 */
#endif
				int rt_i = g_rec_track;
				/* RP: ONE address computation for the whole iteration.
				 * rt_i is a local and fixed here, so &trk[rt_i] is
				 * invariant -- this replaces three movw #32840 + mul
				 * sequences. Every state READ below stays exactly where
				 * it was: the arm block changes state mid-iteration and
				 * the third read is what starts recording on the SAME
				 * sample the threshold is crossed. NULL when idle; every
				 * use is short-circuit guarded by rt_i >= 0. */
				struct looptrk *rt_p = (rt_i >= 0) ? &trk[rt_i] : (struct looptrk *)0;
				/* M20 PRE-ROLL: nothing capturing and nothing still
				 * flushing -> the ring is free, so keep the last
				 * PREROLL_MAX samples of input in it. */
				if (!g_done_pending &&
				    (rt_i < 0 || rt_p->state != TS_REC)) {
					{ /* CD-463: 24k pre-roll store (same absolute pair grid) */
					  if ((_pre_w & 1u) == 0u) { g_cd_holdL = lsamp; g_cd_holdR = rsamp; }
					  else { uint32_t _fi = ((_pre_w >> 1) & RRING_MASK);
					    g_rring[_fi * 2u]      = (int16_t)(((int32_t)g_cd_holdL + (int32_t)lsamp + 1) >> 1);
					    g_rring[_fi * 2u + 1u] = (int16_t)(((int32_t)g_cd_holdR + (int32_t)rsamp + 1) >> 1); } }
					_pre_w++;
					if (_pre_val < PREROLL_MAX) _pre_val++;
				}
				if (rt_i >= 0 && rt_p->state == TS_ARMED) {
					/* AUTO-START: hold armed until the input first crosses
					 * the threshold. NO TIMEOUT any more: the old ~4 s
					 * fallback started recording SILENCE on its own
					 * (community: "once armed it should only rely on sound
					 * input... after 8 tics it starts on its own"). An
					 * armed track now waits indefinitely — tap it to
					 * cancel; the blinking LED shows it is armed. */
					struct looptrk *rt = &trk[rt_i];
					int32_t aa = lsamp < 0 ? -lsamp : lsamp;
					int trigger;
					uint32_t pre_backfill = 0u;
					if (g_grid_active && g_grid_beat_frames && g_grid_punch_at) {
						/* M8b PUNCH-IN: start on the scheduled line.
						 * M22-B: SAMPLE-exact — g_sample_clock is the
						 * block START (it advances once per 256-frame
						 * block), so comparing it raw fired every
						 * punch 0-5.33 ms late, quantized to block
						 * edges. The frame index makes it exact; the
						 * bench showed the quantization as per-take
						 * scatter on top of the drift. */
						uint64_t now_f = g_sample_clock + f;
						trigger = (now_f >= g_grid_punch_at);
						/* M20 PRE-ROLL RESCUE: the punch is waiting
						 * for the NEXT line — but if the PREVIOUS one
						 * is less than half a beat back and still
						 * inside the pre-roll memory, start there
						 * instead and fill the gap in. The punch
						 * lands on the NEAREST line either way, so a
						 * press just after the beat is as good as a
						 * press just before it. */
						if (!trigger && _pre_val &&
						    now_f > g_grid_anchor) {
							uint64_t unit = g_grid_beat_frames;
							uint64_t off = now_f - g_grid_anchor;
							/* GP-506: this runs once per EMITTED SAMPLE for the
							 * whole ARMED punch wait -- up to a full beat. The
							 * 64/64 divide compiled to bl __aeabi_uldivmod
							 * (~150-190 cyc incl. 14 stack accesses). Both
							 * operands fit in 32 bits in every reachable case:
							 * `unit` is a beat in frames (72,000 at the 40 BPM
							 * floor) and `off` only reaches 2^32 if the anchor is
							 * more than 24.9 h old. Unsigned division of values
							 * below 2^32 yields the same quotient at either
							 * width, and the 64-bit arm is KEPT for the rest, so
							 * this is bit-exact by construction. */
							uint64_t _q;
							if (!(off >> 32) && !(unit >> 32))
								_q = (uint64_t)((uint32_t)off /
									       (uint32_t)unit);
							else
								_q = off / unit;
							uint64_t prev = g_grid_anchor + _q * unit;
							uint64_t back = now_f - prev;
							uint32_t need = (uint32_t)
								((back * g_cur_speed_q16) >> 16);
							/* M20b-r2 REACH LIMIT: half a beat back
							 * was ambiguous — a press 250 ms after a
							 * line usually MEANT the next line, and
							 * reaching back made the take a whole beat
							 * too long, so its head repeated at its
							 * tail. Only a genuinely LATE finger gets
							 * rescued: a quarter beat, capped in ms. */
							/* M25-r9: a THIRD of a beat. r5 tried this,
							 * r6 reverted it on suspicion, and the bisect
							 * then cleared it outright — the half-beat
							 * jump was a truncating clamp in the
							 * convergence rescale, present since M22-C
							 * and reproducible on M24-R1, which predates
							 * the reach change entirely. So this returns
							 * on its own merits: 156 ms of forgiveness at
							 * 128 instead of 117, still well short of the
							 * half beat that caused the head-repeats. */
							uint64_t reach = unit / 3u;
							uint64_t rcap = (uint64_t)
								(I2S_TRUE_HZ / 1000u) *
								PREROLL_REACH_MS;
							if (reach > rcap) reach = rcap;
							if (back <= reach && need &&
							    need <= _pre_val) {
								pre_backfill = need;
								g_dbg_anc_bkf = need;   /* r6: ANY take */
								g_grid_punch_at = prev;
								trigger = 1;
							}
						}
					} else {
						/* trigger directly on the first sample past
						 * threshold (no running-peak tracking) */
						trigger = (aa >= SOUND_THRESHOLD);
						/* M41 HEAD RECOVERY: the rule above is
						 * UNCHANGED — but the first sound may have
						 * arrived while the button was still in its
						 * 100/180 ms arm window, and shipped code then
						 * started the take mid-note. Scan the pre-roll
						 * ring BACKWARDS in 64-sample windows while
						 * each window's peak stays above the threshold
						 * and adopt that tail: the take begins at the
						 * sound's ONSET. Caps: the PRESS
						 * (g_arm_press_sclk, engine frames -> ring
						 * samples via tape speed — recording never
						 * reaches back before the finger) and
						 * _pre_val. Silence at arm = shipped exact.
						 * Same ring adoption as the gridded rescue
						 * below; no provisional phase, no catch-up
						 * burst. g_instant_rec clear = classic: skip
						 * the scan, shipped behavior bit-for-bit. */
						if (trigger && g_instant_rec && _pre_val) {
							uint64_t now_f = g_sample_clock + f;
							uint64_t backf = (g_arm_press_sclk &&
							                  now_f > g_arm_press_sclk)
							               ? (now_f - g_arm_press_sclk) : 0u;
							uint32_t cap = (uint32_t)
								((backf * g_cur_speed_q16) >> 16);
							if (cap > _pre_val) cap = _pre_val;
							uint32_t n = 0u;
							while (n + 64u <= cap) {
								int32_t pk = 0;
								for (uint32_t k = 1u; k <= 64u; k++) {
									int32_t sv = g_rring[(((_pre_w - n - k) >> 1) & RRING_MASK) * 2u]; /* CD-463: stored 24k, L */
									if (sv < 0) sv = -sv;
									if (sv > pk) pk = sv;
								}
								if (pk < SOUND_THRESHOLD) break;
								n += 64u;
							}
							pre_backfill = n;
						}
					}
					if (trigger) {
						/* CD-463: the pair grid is absolute — the take's flush
						 * origin (r_r = _pre_w - backfill) must be EVEN so stored
						 * pairs align with block boundaries. Shrink the backfill
						 * one frame (inaudible); if it reaches 0 the no-backfill
						 * branch resets r_w=r_r=0, which is even. */
						if (pre_backfill && ((_pre_w - pre_backfill) & 1u))
							pre_backfill--;
						if (g_loop_len == 0u) {
							/* first take: this sound is loop position 0
							 * (M20: with pre-roll, position 0 is the
							 * grid line we reached back to, so the
							 * playhead is already that far in) */
							_cpos = pre_backfill;
							g_midi_start_pending = 1; g_midi_cnt = 0;
							tempo_reset();
							rt->flush_blk = 0; rt->flush_mod = MAX_LOOP_BLOCKS;
							rt->rec_target = 0;
							rt->start_blk = 0;        /* the base take anchors the grid at 0 */
							rt->start_samps = 0;
							rt->len_samps = 0;   /* set at the stop */
							rt->len_blocks = 0;       /* set when the held length is known */
						} else {
							/* INDEPENDENT LOOPS: an overdub is an OPEN take
							 * exactly like the first — it records until the
							 * user taps the track again (or MAX), then loops
							 * at ITS OWN length on its own cycle. No
							 * quantization to the first track's grid, no
							 * silence padding while you hunt for the loop
							 * point. start_blk anchors playback to where
							 * recording began; length is set at stop.
							 * Linear flush, no wrap. */
							rt->flush_blk = 0; rt->flush_mod = MAX_LOOP_BLOCKS;
							rt->rec_target = 0;
							/* C-r3: arm the onset estimator for THIS
							 * take. It only ever armed on first takes,
							 * so an overdub's stop read a STALE
							 * first_onset from take 1 — the landmark
							 * collapsed into pure punch spacing, the
							 * convergence measured the grid against
							 * itself, railed at the cap and DIVERGED
							 * (bench: -60 then -143 ms; diag showed
							 * cnv=128/16 then 203/14 against a truth
							 * of -4). Each take now lands its own
							 * landmark; the leak fix still retires
							 * the estimator at every gridded stop. */
							tempo_reset();
							{	/* M20: an overdub anchors where
								 * recording BEGAN — the reached-back
								 * line, not the moment of the punch */
								uint32_t sp = _cpos;
								sp = (sp >= pre_backfill)
								   ? (sp - pre_backfill) : 0u;
								/* M22-A: NEAREST, not truncate — the
								 * old floor put every overdub 0-5.3 ms
								 * early, always early. Full sample
								 * anchors are Phase B. */
								rt->p16m = rt->p16m_next;   /* GS2-532: the toggled record mode */
								rt->start_blk = (sp + TSPB(rt) / 2u)
								              / TSPB(rt);
								rt->start_samps = sp;   /* M22-B: exact */
								g_dbg_anc_cp  = _cpos;
								g_dbg_anc_bkf = pre_backfill;
								g_dbg_anc_mod = g_grid_beat_frames
									      ? (sp % g_grid_beat_frames) : 0u;
								g_dbg_ganc = (uint32_t)g_grid_anchor;
								g_dbg_pat  = (uint32_t)g_grid_punch_at;
								rt->len_samps = 0;
							}
						}
						if (pre_backfill) {
							/* the pre-rolled tail IS the take's head:
							 * the ring already holds it, so simply
							 * adopt those indices (no copy). */
							rt->r_r = _pre_w - pre_backfill;
							rt->r_w = _pre_w;
							rt->rec_count = pre_backfill;
						} else {
							rt->r_w = 0; rt->r_r = 0; rt->rec_count = 0;
						}
						_pre_val = 0;   /* the ring belongs to the take now */
						{	/* r2 diag: where did this punch land on
							 * the grid? (frames past the nearest
							 * line; ~0 = exact) */
							uint64_t nowp = g_sample_clock + f;
							if (g_grid_beat_frames &&
							    nowp > g_grid_anchor) {
								uint64_t ph = (nowp - g_grid_anchor)
									% g_grid_beat_frames;
								int32_t sp2 = (ph > g_grid_beat_frames / 2u)
									? (int32_t)ph - (int32_t)g_grid_beat_frames
									: (int32_t)ph;
								g_dbg_punch_ph = pre_backfill
									? 0 - (int32_t)pre_backfill : sp2;
							}
							g_dbg_punch_sp = rt->start_samps;
							g_dbg_speed = g_cur_speed_q16;
						}
						rt->rec_silence = 0;
						if (g_grid_active && g_grid_beat_frames && g_grid_punch_at) {
							/* M8b: beat length in STORED samples at
							 * the punch-in tape speed (recording
							 * follows the tape). */
							g_gridrec_beat_samps = (uint32_t)
								(((uint64_t)g_grid_beat_frames *
								  g_cur_speed_q16) >> 16);
							g_dbg_grs0 = g_gridrec_beat_samps;   /* r6 */
							g_gridrec = 1;
							if (g_loop_len == 0u && !g_grid_fresh) {
								/* M8b-r2: your first loop IS the
								 * downbeat from here on (untapped
								 * grids only — M20 F1: a fresh
								 * TAPPED grid keeps its own phase;
								 * the punch already landed on it) */
								g_grid_anchor = g_grid_punch_at;
								{ uint64_t _bar = (uint64_t)g_grid_beat_frames * 4u;
			  g_grid_next_bar = g_grid_anchor +
				(((g_sample_clock - g_grid_anchor) / _bar) + 1u) * _bar; }
							}
						} else {
							g_gridrec = 0;
						}
						g_grid_punch_at = 0;
						/* M90: publish the hoisted playhead BEFORE any state
						 * transition -- the streamer may observe the new state
						 * and must not then read a stale g_consume_pos. */
						{ g_pphase = _pphase; g_dec_acc = _dec_acc; g_dec_accR = _dec_accR;
						  g_frames_since = _fsince; g_pre_w = _pre_w;
						  g_pre_valid = _pre_val; g_consume_pos = _cpos; }
						/* P14S: every new take is raw. Shaper restarts at
						 * the punch; shadow machinery off for this track. */
						g_p14s_e1[0] = 0; g_p14s_e1[1] = 0; g_p14s_sh = 0u;
						g_p14s_prev[rt_i][0] = 0; g_p14s_prev[rt_i][1] = 0;
						g_p14s_mask |= (uint8_t)(1u << rt_i);
						rt->p16m = rt->p16m_next;   /* GS2-532 */
						rt->state = TS_REC;
					}
				}
#if M82_PROBES
				g_pa82[0] += DWT->CYCCNT - _r82; _r82 = DWT->CYCCNT;
#endif
				if (rt_i >= 0 && rt_p->state == TS_REC) {
#if M82_PROBES
					{ uint32_t _c86 = DWT->CYCCNT;
					  rec_write_sample(lsamp, rsamp);
					  uint32_t _d86 = DWT->CYCCNT - _c86;
					  if (_d86 < g_t1min) g_t1min = _d86; }
#else
					rec_write_sample(lsamp, rsamp);
#endif
				}

#if M82_PROBES
				g_pa82[1] += DWT->CYCCNT - _r82;
#endif
				_cpos++;
				/* MIDI 24-PPQN clock: a cheap per-sample COUNTER (the divisor
				 * g_midi_div is precomputed when the tempo is detected) -- no
				 * runtime divide here. The beat-phase display moved to once-per-
				 * block (after this loop); it only drives the LED + diag. */
				if (!g_grid_active && g_midi_div && ++g_midi_cnt >= g_midi_div) {
					g_midi_cnt = 0; g_midi_clk_produced++;
				}
			}
		} else if (!g_done_pending) {
			/* M20b-r3 IDLE PRE-ROLL: the transport only runs once a
			 * loop exists, so on an EMPTY song the ring stayed cold
			 * and the very first take had nothing to reach back to.
			 * But the I2S bus is clocked by the 3.072 MHz oscillator
			 * with the nRF a frame/bit SLAVE, so input frames arrive
			 * whether or not the looper is doing anything: decimate
			 * them at the speed a take WOULD use (arming snaps
			 * g_cur_speed to g_play_speed) and keep the same short
			 * memory. No new buffer, no eMMC, and this branch cannot
			 * touch a running transport — it is the else of one. */
			if (g_pre_speed != g_play_speed_q16) {
				/* rate changed: what is stored was sampled at a
				 * different tape speed, so its LENGTH would lie */
				g_pre_speed = g_play_speed_q16;
				_pre_val = 0;
				_dec_acc = 0; _fsince = 0;
			}
			g_pre_phase += g_play_speed_q16 / DECIM;
			while (g_pre_phase >= 65536u) {
				g_pre_phase -= 65536u;
				/* MUST MATCH the decimator above, sample for sample */
				int16_t psamp, psampR;
				if (_fsince == 0u)    { psamp = (int16_t)liveL; psampR = (int16_t)liveR; }
				else if (_fsince == 1u) { psamp = (int16_t)_dec_acc; psampR = (int16_t)_dec_accR; }
				else if (_fsince < 65536u)
				{ psamp = (int16_t)((int32_t)_dec_acc /
							  (int32_t)_fsince);
				  psampR = (int16_t)((int32_t)_dec_accR /
							  (int32_t)_fsince); }
				else { psamp = (int16_t)(_dec_acc / (int64_t)_fsince);
				       psampR = (int16_t)(_dec_accR / (int64_t)_fsince); }
				_dec_acc = 0; _dec_accR = 0; _fsince = 0;
				{ /* CD-463: 24k pre-roll store (pause path, same pair grid) */
				  if ((_pre_w & 1u) == 0u) { g_cd_holdL = psamp; g_cd_holdR = psampR; }
				  else { uint32_t _fi = ((_pre_w >> 1) & RRING_MASK);
				    g_rring[_fi * 2u]      = (int16_t)(((int32_t)g_cd_holdL + (int32_t)psamp + 1) >> 1);
				    g_rring[_fi * 2u + 1u] = (int16_t)(((int32_t)g_cd_holdR + (int32_t)psampR + 1) >> 1); } }
				_pre_w++;
				if (_pre_val < PREROLL_MAX) _pre_val++;
			}
		}
	}

	M81_LAP(1);
	/* M90: publish the block's work. One store per variable per block
	 * instead of one per sample. */
	g_pphase = _pphase; g_dec_acc = _dec_acc;
	g_frames_since = _fsince; g_pre_w = _pre_w;
	g_pre_valid = _pre_val; g_consume_pos = _cpos;

	/* ==== PASS B: accumulate each playing track over the whole block ==== */
	for (int i = 0; i < NTRK; i++) {
		if (trk[i].state != TS_PLAY && !head_active(i)) continue;
		/* GAIN SMOOTHING + CLICKLESS MUTE: the fader value used to be
		 * applied as a hard step once per 5 ms block (and mute as an
		 * instant gate) — fast fader rides audibly zipper-clicked and
		 * every mute/unmute popped (community: "fast up-and-down fader
		 * movement sounds a little clicky"). The applied gain now ramps
		 * linearly across the block toward the target (mute = target 0),
		 * spreading any change over 256 samples; a muted track is skipped
		 * entirely once its ramp settles at zero. */
		/* M14: a pending blip mutes this track for ~3 blocks (~16 ms),
		 * riding the existing ramp for clickless edges. */
		const int32_t vtar = (trk[i].muted || g_head_blip[i])
				   ? 0 : (int32_t)vol_s[i];
		if (g_head_blip[i]) g_head_blip[i]--;
		const int32_t vprev = (int32_t)trk[i].vol_now;
		int32_t vd = vtar - vprev;                   /* 0 in the common case */
		/* ADC DEADBAND: the fader ADC jitters +/-1 count between reads, so
		 * without this vd was nonzero on nearly every block for every
		 * track — which silently disqualified the mixer's healthy FAST
		 * PATH (it requires vd==0) and re-cost the CPU that path had
		 * freed. Measured on hardware as renewed starvation under load
		 * (stv 59/67 in one session vs ~0 on the release). A 1-count step
		 * is 0.03 dB — far below audibility and below any zipper — so
		 * snap it instantly; only real movement (>=2 counts) ramps. */
		if (vd == 1 || vd == -1) vd = 0;
		if (vtar == 0 && vd == 0 && vprev == 0) continue;  /* silent and settled */
		trk[i].vol_now = (uint16_t)vtar;
		const int16_t *const pr = trk[i].pring;
		const int32_t vol = vtar;
		/* STOPPED fast path: the transport is frozen (no phase steps this
		 * block), so this track contributes ONE constant sample — compute
		 * it once instead of 256 times. Falls back to the exact per-frame
		 * loop whenever a starve or fade boundary is in flight so those
		 * transitions keep their per-frame behavior. */
		if (step == 0u && !trk[i].starved && trk[i].fade >= 256u && vd == 0) {
			int32_t avail = (int32_t)(trk[i].p_w - posb[0]);
			if (avail < 2) {
				trk[i].starved = 1; g_starve_cnt[i]++; STV_BUMP();
				continue;
			}
			/* M63a: one constant FRAME (L,R) instead of one sample */
			uint32_t _b0 = (posb[0] & RING_MASK) * 2u;
			int16_t aL = pr[_b0], aR = pr[_b0 + 1u];
			int16_t svL, svR;
			if (fracb[0] == 0u) {
				svL = aL; svR = aR;
			} else {
				uint32_t _b1 = ((posb[0] + 1) & RING_MASK) * 2u;
				int16_t bL = pr[_b1], bR = pr[_b1 + 1u];
				svL = (int16_t)((int32_t)aL +
					(int32_t)(((bL - aL) * (int32_t)((fracb[0]) >> 1)) >> 15));
				svR = (int16_t)((int32_t)aR +
					(int32_t)(((bR - aR) * (int32_t)((fracb[0]) >> 1)) >> 15));
			}
			if (avail < 256) {
				svL = (int16_t)(((int32_t)svL * avail) >> 8);
				svR = (int16_t)(((int32_t)svR * avail) >> 8);
			}
			int32_t addL = ((int32_t)svL * vol) >> 8;
			int32_t addR = ((int32_t)svR * vol) >> 8;
			for (uint32_t f = 0; f < BLK_FRAMES; f++) {
				mix32[f] += addL; mix32R[f] += addR;
			}
			continue;
		}
		/* HEALTHY fast path: when no starve or fade boundary can possibly
		 * occur inside this block — not starved, no fade-in running, and
		 * the frontier is far enough ahead of the block's LAST frame that
		 * even with zero refills every frame has avail >= 258 (above both
		 * the <2 starve gate and the <256 fade-out) — the per-frame
		 * volatile p_w reload and the starve/fade branches are provably
		 * dead. Skip them: output is bit-identical (refills only ever
		 * RAISE avail). This is most of the mixer's remaining cost at
		 * 3-4 healthy tracks; tracks anywhere near their edge take the
		 * exact slow path below. Read demand scales with tape speed
		 * (1.5x = 1125 blk/s for 4 tracks), and the CPU this returns to
		 * the streamer is what lifts the refill ceiling past that. */
		if (vd == 0 && !trk[i].starved && trk[i].fade >= 256u &&
		    (int32_t)(trk[i].p_w - posb[BLK_FRAMES - 1u]) >= 258) {
			for (uint32_t f = 0; f < BLK_FRAMES; f++) {
				uint32_t cpos = posb[f];
				uint32_t frac = fracb[f];
				uint32_t _b0 = (cpos & RING_MASK) * 2u;
				int16_t aL = pr[_b0], aR = pr[_b0 + 1u];
				int16_t svL, svR;
				if (frac == 0u) {
					svL = aL; svR = aR;
				} else {
					uint32_t _b1 = ((cpos + 1) & RING_MASK) * 2u;
					int16_t bL = pr[_b1], bR = pr[_b1 + 1u];
					svL = (int16_t)((int32_t)aL +
						(int32_t)(((bL - aL) * (int32_t)((frac) >> 1)) >> 15));
					svR = (int16_t)((int32_t)aR +
						(int32_t)(((bR - aR) * (int32_t)((frac) >> 1)) >> 15));
				}
				mix32[f]  += ((int32_t)svL * vol) >> 8;
				mix32R[f] += ((int32_t)svR * vol) >> 8;
			}
			continue;
		}
		for (uint32_t f = 0; f < BLK_FRAMES; f++) {
			uint32_t cpos = posb[f];
			/* underrun gate WITH HYSTERESIS (semantics unchanged): once a
			 * ring runs dry the track stays silent until half-refilled
			 * (recovering earlier re-dips and chatters — hardware-tested). */
			int32_t avail = (int32_t)(trk[i].p_w - cpos);
			if (trk[i].starved) {
				if (avail >= (int32_t)PLAY_REARM_FRAMES) {
					trk[i].starved = 0;
					trk[i].fade = 0;   /* ramp back in (~5 ms), no click */
				} else {
					continue;
				}
			} else if (avail < 2) {
				trk[i].starved = 1; g_starve_cnt[i]++; STV_BUMP();
				continue;
			}
			uint32_t frac = fracb[f];
			uint32_t _b0 = (cpos & RING_MASK) * 2u;               /* M63a frame */
			int16_t aL = pr[_b0], aR = pr[_b0 + 1u];
			int16_t sv, svR2;
			if (frac == 0u) {
				sv = aL; svR2 = aR;    /* unity speed: no interpolation */
			} else {
				uint32_t _b1 = ((cpos + 1) & RING_MASK) * 2u;
				int16_t bL = pr[_b1], bR = pr[_b1 + 1u];
				/* int64 product: (b-a)*frac can exceed INT32_MAX = signed-
				 * overflow UB; the cast keeps it defined (SMULL on M4). */
				sv = (int16_t)((int32_t)aL +
					(int32_t)(((bL - aL) * (int32_t)((frac) >> 1)) >> 15));
				svR2 = (int16_t)((int32_t)aR +
					(int32_t)(((bR - aR) * (int32_t)((frac) >> 1)) >> 15));
			}
			/* BOUNDARY FADE (unchanged): fade out over the last ~5 ms as
			 * the ring drains, fade in after recovery — dropouts duck
			 * instead of clicking. */
			{
				int32_t g = 256;
				if (avail < 256) g = avail;
				if (trk[i].fade < 256u) {
					if ((int32_t)trk[i].fade < g) g = (int32_t)trk[i].fade;
					trk[i].fade++;
				}
				if (g < 256) {
					sv   = (int16_t)(((int32_t)sv * g) >> 8);
					svR2 = (int16_t)(((int32_t)svR2 * g) >> 8);
				}
			}
			int32_t vf = vd ? (vprev + ((vd * (int32_t)(f + 1)) >> 8)) : vol;
			mix32[f]  += ((int32_t)sv * vf) >> 8;
			mix32R[f] += ((int32_t)svR2 * vf) >> 8;
		}
	}

	M81_LAP(2);
	/* ==== PASS C: master volume + soft limiter -> stereo out ==== */
	{
		/* the VOL buttons step ~3 dB at a time — ramp each step across the
		 * block instead of applying it as a hard gain jump (a click). */
		/* M10: a declick/fade ENVELOPE rides on the master gain. A chop
		 * edit dips it to 0 (the per-block interpolation below turns that
		 * into a ~5 ms ramp) and it recovers over ~27 ms — masking the
		 * window-jump discontinuity that used to click. Power-off fades
		 * it out over ~85 ms and HOLDS, so the codecs are shut down on
		 * silence. Envelope and master fold into ONE interpolated gain:
		 * the per-frame cost is unchanged. */
		static int32_t env_q8 = 256;
		if (g_off_fade) {
			env_q8 -= (env_q8 > 16) ? 16 : env_q8;
		} else if (g_dip_req) {
			g_dip_req = 0;
			env_q8 = 0;
		} else if (env_q8 < 256) {
			env_q8 += 48;
			if (env_q8 > 256) env_q8 = 256;
		}
		/* M17 DJ FILTER: mode + target coefficient from the fader once
		 * per block; the coefficient RAMPS toward its target (~40 ms
		 * across a big jump) so sweeps are zipperless. On a mode change
		 * (LP <-> bypass <-> HP) the state is reprimed against the live
		 * signal — the M11b pop lesson: never swap filter topology on
		 * stale integrator state. */
		static int32_t flt_lowL, flt_bandL, flt_lowR, flt_bandR, flt_f;  /* M63a: L/R SVFs */
		static uint8_t flt_mode;   /* 0 = bypass, 1 = LP, 2 = HP */
		{
			uint8_t fp = g_flt_pos;
			uint8_t nm; int32_t tf;
			if (fp < 112u)      { nm = 1; tf = flt_lp_tab[fp >> 3]; }
			else if (fp > 143u) { nm = 2; tf = flt_hp_tab[(fp - 144u) >> 3]; }
			else                { nm = 0; tf = 0; }
			if (nm != flt_mode) {
				flt_mode = nm;
				flt_f = tf;
				/* M25: a HIGH-pass must start TRANSPARENT — it has
				 * no accumulated low content yet — while a LOW-pass
				 * starts at the signal. Priming both to mix32[0]
				 * made hi = x - flt_low - flt_band come out at ~0,
				 * so every entry into HP ducked for a few ms. The
				 * worst case now is a low-corner HP briefly passing
				 * more bass than it should while the integrator
				 * catches up, which is what any analog high-pass
				 * does when you patch it in. */
				flt_lowL = (nm == 2u) ? 0 : mix32[0];
				flt_lowR = (nm == 2u) ? 0 : mix32R[0];
				flt_bandL = 0; flt_bandR = 0;
			} else if (tf != flt_f) {
				int32_t fd = (tf - flt_f) >> 3;
				if (fd == 0) fd = (tf > flt_f) ? 1 : -1;
				flt_f += fd;
			}
		}
		const int32_t mv = (int32_t)g_master_vol_q8;
		const int32_t ge = (mv * env_q8) >> 8;
		static int32_t ge_prev;
		const int32_t gd = ge - ge_prev;
		const int32_t g0 = ge_prev;
		ge_prev = ge;
		for (uint32_t f = 0; f < BLK_FRAMES; f++) {
			int32_t xL = mix32[f];
			int32_t xR = mix32R[f];
			if (flt_mode) {
				/* Chamberlin SVF x2 (M63a): per-channel state, shared
				 * coefficient. int64 products per the M25 overflow fix. */
				flt_lowL += (int32_t)(((int64_t)flt_f * flt_bandL) >> 14);
				int32_t hiL = xL - flt_lowL - flt_bandL;
				flt_bandL += (int32_t)(((int64_t)flt_f * hiL) >> 14);
				xL = (flt_mode == 1u) ? flt_lowL : hiL;
				flt_lowR += (int32_t)(((int64_t)flt_f * flt_bandR) >> 14);
				int32_t hiR = xR - flt_lowR - flt_bandR;
				flt_bandR += (int32_t)(((int64_t)flt_f * hiR) >> 14);
				xR = (flt_mode == 1u) ? flt_lowR : hiR;
			}
			int32_t m = gd ? (g0 + ((gd * (int32_t)(f + 1)) >> 8)) : ge;
			s[2 * f]      = soft_limit((xL * m) >> 8);
			s[2 * f + 1u] = soft_limit((xR * m) >> 8);
		}
	}
	g_sample_clock += BLK_FRAMES;
	/* TAPPED GRID: MIDI clock in wall (I2S) time, produced block-wise, even
	 * with the transport stopped — the grid is the decks' clock, not the
	 * tape's. Bounded catch-up: a block is ~5 ms, ticks are >=10 ms. */
	if (g_grid_active && g_grid_beat_frames) {
		/* M22-A: EXACT tick schedule. beat/24 truncates (937.5 -> 937 at
		 * 128 BPM), and the old += accumulated that truncation forever:
		 * always fast, ~32 ms/min at 128 — marc heard it against his gear
		 * before the code review found it. Ticks now come from an index
		 * against a fixed base, so the error is bounded at ±1 frame no
		 * matter how long the session runs. The base re-arms whenever
		 * anything resets g_grid_next_tick (tap, retune, song load): the
		 * first tick of a fresh base fires AT the base, like before. */
		if (g_grid_next_tick != g_grid_tick_base_sync) {
			/* someone else wrote next_tick (tap-commit, retune, song
			 * load, beatmatch): that value is the new base */
			g_grid_tick_base = g_grid_next_tick;
			g_grid_tick_base_sync = g_grid_next_tick;
			g_grid_tick_idx = 0;
		}
		while (g_sample_clock >= g_grid_next_tick) {
			g_grid_tick_idx++;
			g_grid_next_tick = g_grid_tick_base +
				(uint64_t)(((uint64_t)g_grid_tick_idx *
					    g_grid_beat_frames) / 24u);
			g_grid_tick_base_sync = g_grid_next_tick;
			g_midi_clk_produced++;
		}
		/* M8c: BAR-LINE service — launch-quantized mutes apply here, and a
		 * pending beatmatch resync restarts the loops on the tapped "1".
		 * Bars are ~2 s and blocks ~5 ms: one crossing per block, max.
		 * (v2.0.0: launch-quantized MUTES were removed after live testing —
		 * a bar is up to ~5 s of felt lag; mutes are instant everywhere
		 * now, like 1.x. The bar service keeps only the beatmatch resync;
		 * recording punch-ins stay bar-quantized via g_grid_punch_at.) */
		if (g_grid_next_bar && g_sample_clock >= g_grid_next_bar) {
			if (g_grid_resync_at && g_sample_clock >= g_grid_resync_at) {
				g_grid_resync_at = 0;
				g_restart_req = 1;      /* loops from the top, ON the "1" */
			}
			g_grid_next_bar += (uint64_t)g_grid_beat_frames * 4u;
		}
	}
	/* Beat-phase display computed ONCE per block now (was per loop-sample). It
	 * only feeds the LED + MIDI-grid diag, so block granularity (~5 ms) is plenty
	 * -- this lifts three runtime divides off the per-sample hot path. */
	if (g_loop_active) {
		uint32_t bs = g_beat_samples ? g_beat_samples : BEAT_SAMPLES_L;
		if (g_loop_len > 0u) {
			uint32_t lp = g_consume_pos % g_loop_len;
			g_beat_phase = lp % bs;
			g_dbg_beat = (int)(lp / bs);
		} else {
			g_beat_phase = g_consume_pos % bs;
			g_dbg_beat = (int)(g_consume_pos / bs);
		}
	} else {
		g_beat_phase = (uint32_t)((g_sample_clock % BEAT_SAMPLES_I2S) / DECIM);
	}

	/* diag WATERMARKS (once per block): how close each ring got to its cliff
	 * this window — shows near-misses even when no starve/overrun fired. */
	{
		uint32_t _cp = g_consume_pos;
		for (int i = 0; i < NTRK; i++) {
			if (trk[i].state != TS_PLAY) continue;
			int32_t _av = (int32_t)(trk[i].p_w - _cp);
			if (_av < g_play_lowat) g_play_lowat = _av;
		}
		int _rt = g_rec_track;
		if (_rt >= 0 && trk[_rt].state == TS_REC) {
			uint32_t _fill = trk[_rt].r_w - trk[_rt].r_r;
			if (_fill > g_rec_hiwat) g_rec_hiwat = _fill;
		}
	}
	M81_LAP(3);
}

/* eMMC busy-abort callback: polled ~1 kHz inside the driver's ABORTABLE R1b
 * waits (the idle cache flush), on the streamer thread. true = fire an HPI
 * and bail. Trips the moment a take is armed/recording/finalizing, shutdown
 * work is pending, or any playing ring has drained to half. */
static bool emmc_busy_abort_chk(void)
{
	if (g_stop_req || g_cache_flush_req)
		return true;
	for (int j = 0; j < NTRK; j++) {
		uint8_t sj = trk[j].state;
		if (sj == TS_ARMED || sj == TS_REC || sj == TS_DONE)
			return true;
		if ((sj == TS_PLAY || head_active(j)) &&
		    (int32_t)(trk[j].p_w - g_consume_pos) <
		    (int32_t)(RING_SAMPLES / 2u))
			return true;
	}
	return false;
}

/* ========================================================================
 *  eMMC STREAMER  —  PREEMPT-5 (below audio), the ONLY eMMC user. Each loop:
 *  PASS 1 flushes the record ring to flash (writes-first), PASS 2 reads each
 *  play track ahead into its RAM ring. A balanced ADAPTIVE FLUSH yields the
 *  bus between the two passes — playback wins unless a play ring is about to
 *  underrun, recording wins at true rec-ring overflow. Also loads/saves the
 *  slot metadata (block 0) and runs the power-off cache flush.
 * ======================================================================== */
/* ---- background eMMC streamer (the ONLY eMMC user) -------------------------
 * Preemptible priority BELOW the cooperative audio thread, so the audio thread
 * can always preempt the bit-bang busy-waits and keep the I2S DMA fed. Per
 * PLAY track: read-ahead into the play ring. Per REC/DONE track: flush the rec
 * ring to the card; on DONE, finish the tail then switch the track to PLAY. */
static K_THREAD_STACK_DEFINE(streamer_stack, 2048);  /* RD2-475: was 3072 (474), 4096 originally. 474's run RECORDED, so the write/flush chain was on this stack, and U4S STILL measured a 680 B peak -- identical to the read-only 473 figure. 3.0x margin, 1368 B free. */  /* 4096: the eMMC driver is -O2 here, so its read/send_command/crc chain inlines into a deeper frame on this thread */
static struct k_thread streamer_tcb;
static uint8_t g_streamer_started;   /* v1.2.3: streamer may start EARLY (standby) */
static void streamer_thread(void *a, void *b, void *c);
static void streamer_start(void)
{
	if (g_streamer_started) return;
	g_streamer_started = 1;
	k_thread_create(&streamer_tcb, streamer_stack, K_THREAD_STACK_SIZEOF(streamer_stack),
			streamer_thread, NULL, NULL, NULL,
			K_PRIO_PREEMPT(5), 0, K_NO_WAIT);
}
static volatile uint8_t g_usb_up;    /* usb_audio_start() completed (gates xfer polling) */

#if SP1_XFER_ENABLE
/* ISR: drain the CDC RX FIFO into the ring buffer (host -> device bytes). */
static void cdc_rx_isr(const struct device *dev, void *u)
{
	ARG_UNUSED(u);
	while (uart_irq_update(dev) && uart_irq_rx_ready(dev)) {
		uint8_t b[64];
		int n = uart_fifo_read(dev, b, sizeof b);
		if (n > 0) (void)ring_buf_put(&g_cdc_rx, b, (uint32_t)n);
	}
}

/* Blocking byte send (matches how printk drives the console). */
static void cdc_tx(const uint8_t *p, uint32_t n)
{
	for (uint32_t i = 0; i < n; i++) uart_poll_out(cdc, p[i]);
}

/* Pull exactly n bytes from the RX ring, up to timeout_ms. */
static bool cdc_rx(uint8_t *p, uint32_t n, int timeout_ms)
{
	int64_t end = k_uptime_get() + timeout_ms;
	uint32_t got = 0;
	while (got < n) {
		got += ring_buf_get(&g_cdc_rx, p + got, n - got);
		if (got < n) {
			if (k_uptime_get() > end) return false;
			k_msleep(1);
		}
	}
	return true;
}

/* A block command's sub-read stalled mid-stream, so the RX ring may hold a partial
 * payload that would misframe every later command. Drain it back to a clean command
 * boundary (consumer-side get, safe vs the producing ISR) and send the host an error
 * byte so it aborts that block; the host's next ping then resyncs cleanly. */
static void xfer_resync(uint8_t err_byte)
{
	uint8_t dump;
	while (ring_buf_get(&g_cdc_rx, &dump, 1) == 1) {
	}
	cdc_tx(&err_byte, 1);
}

/* Which track regions the host actually wrote this transfer session. At commit,
 * only these take the host's trk_content (0 = whole track — correct for an
 * upload, which writes full-length audio); every other track keeps the device's
 * value. The website rebuilds block 0 from the legacy layout and writes the
 * appended fields as zeros, and zero is NOT a safe default here: it would
 * unmask never-written flash in the silence tail of fixed-mode takes and drop
 * the saved loop-length mode. */
static uint8_t g_xfer_dirty[NUM_SLOTS][NTRK];

/* Commit host writes durably. The host writes land in the eMMC's volatile write
 * cache (and never touch the in-RAM g_meta), so without this an upload is lost on
 * the next power cut and the stale in-RAM index can overwrite it. This (1) reads
 * block 0 back into g_meta (the write cache is read-coherent), (2) repairs the
 * appended fields the host doesn't manage and writes the repaired index straight
 * back, and (3) flushes the cache — host audio and repaired index become durable
 * TOGETHER. Deferring the repair via g_meta_save_req would be wrong: the streamer
 * only services it after transfer mode ends, so for a whole keepalive-extended
 * session the host's zeroed copy would be the durable one, and a battery death
 * mid-session would persist exactly the corruption this repairs. Runs from the
 * streamer while g_xfer_mode is still set (audio is silenced), so the
 * bus-blocking flush has nothing live to starve. */
static void xfer_commit(void)
{
	static uint8_t mblk[META_BLOCKS * EMMC_BLOCK_SIZE];
	if (g_emmc_ready && emmc_read_blocks(META_BLOCK, mblk, META_BLOCKS)) {
		struct meta_blk *m = (struct meta_blk *)mblk;
		if (m->magic == META_MAGIC && m->cur_slot < NUM_SLOTS) {
			uint32_t keep[NUM_SLOTS][NTRK];
			uint8_t keep_chop[NUM_SLOTS][2];
			uint8_t keep_mode[NUM_SLOTS];
			memcpy(keep, g_meta.trk_content, sizeof(keep));
			memcpy(keep_chop, g_meta.chop, sizeof(keep_chop));
			memcpy(keep_mode, g_meta.song_mode, sizeof(keep_mode));
			memcpy(&g_meta, m, sizeof(g_meta));
			g_slot = g_meta.cur_slot;
			/* the host only manages the legacy fields (see g_xfer_dirty):
			 * restore the mode setting and every untouched track's content
			 * length, then write the repaired index back (skipped when the
			 * host's copy already matches, e.g. a read-only session). */
			g_meta.fixed_len = g_mode_pref;      /* M7c: field = preference */
			g_led_dim = (g_meta.led_full & 1u) ? 0u : 1u;   /* M8c: site owns it */
			g_instant_rec = (uint8_t)(((g_meta.led_full >> 1) & 1u) ? 0u : 1u);   /* M41-r5: bit 1 SET = classic */
			memcpy(g_meta.chop, keep_chop, sizeof(keep_chop));
			memcpy(g_meta.song_mode, keep_mode, sizeof(keep_mode));
			if (g_slot < NUM_SLOTS) {   /* reload effective for current song */
				uint32_t cd = g_meta.chop[g_slot][0];
				if (cd < 1u || cd > 64u) cd = 1u;
				uint32_t co = g_meta.chop[g_slot][1]; if (co >= cd) co = 0u;
				g_chop_div = cd; g_chop_off = co;
				g_fixed_len = (g_meta.song_mode[g_slot] & 0x0Fu)
					    ? ((g_meta.song_mode[g_slot] & 0x0Fu) == 2u ? 1u : 0u)
					    : g_mode_pref;
			}
			for (int s = 0; s < NUM_SLOTS; s++)
				for (int t = 0; t < NTRK; t++)
					if (!g_xfer_dirty[s][t])
						g_meta.trk_content[s][t] = keep[s][t];
					else   /* M7-r4: freshly uploaded audio is audible */
						g_meta.song_mode[s] &= (uint8_t)~(uint8_t)(0x10u << t);
			if (memcmp(mblk, &g_meta, sizeof(g_meta)) != 0) {
				memset(mblk, 0, sizeof(mblk));
				memcpy(mblk, &g_meta, sizeof(g_meta));
				(void)meta_write_blocks(mblk);
			}
		}
	}
	if (g_cache_on) {
		(void)emmc_cache_flush();
	}
}

/* The block-transfer protocol, serviced from the streamer (the only eMMC user).
 * OUT of transfer mode: scan the RX stream for the 8-byte enter-magic.
 * IN transfer mode: run ONE command per call ('P'ing/'R'ead/'W'rite/'F'lush/e'X'it),
 * auto-committing + auto-exiting after 15 s with no command so a dropped page can't
 * wedge it or strand an upload in volatile cache. */
static void xfer_service(void)
{
	static const uint8_t MAGIC[8] = { 'S','P','1','X','F','E','R','!' };
	static uint8_t  m;
	static int64_t  last;

	if (!g_xfer_mode) {
		uint8_t b;
		while (ring_buf_get(&g_cdc_rx, &b, 1) == 1) {
			m = (b == MAGIC[m]) ? (uint8_t)(m + 1) : (b == MAGIC[0] ? 1u : 0u);
			if (m == 8u) {
				m = 0;
				/* Don't freeze the streamer mid-take: if a recording is still
				 * being captured or flushed, finalize it first (the audio thread
				 * promotes it + the streamer drains the ring and persists the
				 * index). Enter on a later magic -- the host's handshake retries,
				 * and a take finalizes in well under that window. */
				bool busy = (g_rec_track >= 0) || g_meta_save_req;
				for (int t = 0; t < NTRK; t++)
					if (trk[t].state == TS_REC || trk[t].state == TS_DONE) busy = 1;
				if (busy) {
					g_stop_req = 1;
					break;
				}
				memset(g_xfer_dirty, 0, sizeof(g_xfer_dirty));
				g_xfer_mode = 1;
				g_playing = 0;           /* pause the transport during transfer */
				last = k_uptime_get();
				break;
			}
		}
		return;
	}

	uint8_t cmd;
	if (ring_buf_get(&g_cdc_rx, &cmd, 1) != 1) {            /* idle: commit + exit on timeout */
		if (k_uptime_get() - last > 15000) {
			xfer_commit();                         /* don't strand an upload in cache */
			g_slot_switch_req = 1;                 /* reload tracks for the active song */
			g_xfer_mode = 0;
		}
		return;
	}
	last = k_uptime_get();

	if (cmd == 'P') {                                      /* ping -> magic + layout */
		uint8_t r[4 + 6 * 4];
		memcpy(r, "SP1!", 4);
		uint32_t info[6] = { EMMC_BLOCK_SIZE, NUM_SLOTS, NTRK,
				     SLOT0_BLOCK, TRACK_BLOCKS, META_MAGIC };
		memcpy(r + 4, info, sizeof info);
		cdc_tx(r, sizeof r);
	} else if (cmd == 'R' || cmd == 'W') {                 /* read / write one block */
		uint8_t a[4];
		if (!cdc_rx(a, 4, 1000)) { xfer_resync(cmd == 'R' ? 'e' : 'E'); return; }
		uint32_t blk = (uint32_t)a[0] | ((uint32_t)a[1] << 8) |
			       ((uint32_t)a[2] << 16) | ((uint32_t)a[3] << 24);
		uint32_t total = SLOT0_BLOCK + (uint32_t)NUM_SLOTS * NTRK * TRACK_BLOCKS;
		static uint8_t sec[EMMC_BLOCK_SIZE];
		if (cmd == 'R') {
			bool ok = (blk < total) && emmc_read_blocks(blk, sec, 1);
			uint8_t h = ok ? 'r' : 'e';
			cdc_tx(&h, 1);
			if (ok) cdc_tx(sec, EMMC_BLOCK_SIZE);
		} else {
			if (!cdc_rx(sec, EMMC_BLOCK_SIZE, 4000)) { xfer_resync('E'); return; }
			bool ok = (blk < total) && emmc_write_blocks(blk, sec, 1);
			if (ok && blk >= SLOT0_BLOCK) {
				uint32_t ti = (blk - SLOT0_BLOCK) / TRACK_BLOCKS;
				if (ti < (uint32_t)NUM_SLOTS * NTRK)
					g_xfer_dirty[ti / NTRK][ti % NTRK] = 1;
			}
			uint8_t h = ok ? 'w' : 'E';
			cdc_tx(&h, 1);
		}
	} else if (cmd == 'F') {                               /* flush: commit writes to NAND */
		xfer_commit();
		uint8_t h = 'f';
		cdc_tx(&h, 1);
	} else if (cmd == 'X') {                               /* commit, then exit transfer mode */
		xfer_commit();
		g_slot_switch_req = 1;                         /* reload tracks for the active song */
		g_xfer_mode = 0;
		uint8_t h = 'x';
		cdc_tx(&h, 1);
	}
}
#endif /* SP1_XFER_ENABLE */

/* =====================================================================
 * STORAGE CODEC pack/unpack
 * Place this entire block in main.c just BEFORE streamer_thread()
 * (above `static void streamer_thread(void *a,...)` at main.c:1523).
 * SP1_CODEC, SAMP_PER_BLK, EMMC_BLOCK_SIZE are all in scope there.
 *
 *  codec_pack  : int16 ring -> packed flash bytes (ENCODE), nblk*512 bytes out
 *  codec_unpack: packed flash bytes -> int16 ring (DECODE), nblk*512 bytes in
 *
 * Args:
 *   ring       : the int16 ring base (g_rring for write, trk[].pring for read)
 *   ring_mask  : RRING_MASK (write) or RING_MASK (read) — power of two, sample-domain
 *   start      : ring sample offset of the FIRST sample (already & ring_mask'd by caller)
 *   flash      : the linear 512*nblk-byte batch buffer (batchbuf)
 *   nblk       : number of 512-byte flash blocks
 * Each block holds exactly SAMP_PER_BLK int16 samples. The caller guarantees
 * `start` is block-aligned in the ring, so each block's run wraps the ring at
 * most once (same invariant the original memcpy pairs used).
 * ===================================================================== */

#if SP1_CODEC == SP1_CODEC_PCM
/* ---- M63a PCM: STEREO ring <-> MONO blocks. The on-flash format is
 * byte-identical to v2.7.2 (256 int16 samples per block): pack stores
 * the LEFT channel of each frame; unpack writes the sample to BOTH
 * channels. Index math replaces the old memcpy pair; SAMP_PER_BLK
 * counts FRAMES (== stored samples, mono blocks). ---- */
static void codec_pack(const int16_t *ring, uint32_t ring_mask, uint32_t start,
                       uint8_t *flash, uint32_t nblk)
{
	int16_t *out = (int16_t *)flash;
	uint32_t ntot = nblk * SAMP_PER_BLK;
	for (uint32_t i = 0; i < ntot; i++)
		out[i] = ring[((start + i) & ring_mask) * 2u];
}
static void codec_unpack(int16_t *ring, uint32_t ring_mask, uint32_t start,
                         const uint8_t *flash, uint32_t nblk)
{
	const int16_t *in = (const int16_t *)flash;
	uint32_t ntot = nblk * SAMP_PER_BLK;
	for (uint32_t i = 0; i < ntot; i++) {
		uint32_t fi = ((start + i) & ring_mask) * 2u;
		ring[fi] = in[i]; ring[fi + 1u] = in[i];
	}
}
/* M22-B: adopt an arbitrary FRAME run out of a whole-block read (the
 * sample-exact loop seam). Semantics identical to v2.7.2. */
static void codec_unpack_part(int16_t *ring, uint32_t ring_mask, uint32_t start,
                              const uint8_t *flash, uint32_t skip, uint32_t nsamp)
{
	const int16_t *in = (const int16_t *)flash + skip;
	for (uint32_t i = 0; i < nsamp; i++) {
		uint32_t fi = ((start + i) & ring_mask) * 2u;
		ring[fi] = in[i]; ring[fi + 1u] = in[i];
	}
}
#elif SP1_CODEC == SP1_CODEC_A7
/* ==== M63b: SP1-ADPCM7 — the FROZEN 3.0 codec. Core verified
 * bit-exact against SP1-ADPCM7-CODEC-REFERENCE.py by M70 on hardware.
 * 7-bit, damped 2nd-order predictor, full quantiser-error noise
 * shaping clamped at 4*step. 280 STEREO FRAMES per 512-byte block:
 *   [0:2] Lp1 [2:4] Lp2 [4] Lidx [5] flags(b0=stereo)
 *   [6:8] Rp1 [8:10] Rp2 [10] Ridx [11] rsv
 *   [12:14] frames u16  [14:16] sum16(payload)  [16:506] payload
 * Headers reseed the decoder, so every block decodes independently —
 * that is what keeps loop wrap, windows, chop and reverse free. ==== */
static const int16_t a7_step[89] = {
	7,8,9,10,11,12,13,14,16,17,19,21,23,25,28,31,34,37,41,45,50,55,60,66,
	73,80,88,97,107,118,130,143,157,173,190,209,230,253,279,307,337,371,
	408,449,494,544,598,658,724,796,876,963,1060,1166,1282,1411,1552,1707,
	1878,2066,2272,2499,2749,3024,3327,3660,4026,4428,4871,5358,5894,6484,
	7132,7845,8630,9493,10442,11487,12635,13899,15289,16818,18500,20350,
	22385,24623,27086,29794,32767 };
static const int8_t a7_idx7[64] = {
	-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
	0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
	1,1,1,1,2,2,2,2,3,3,3,4,4,4,5,5,
	6,6,7,7,8,8,9,10,10,11,12,13,14,15,16,16 };
struct a7_enc { int32_t p1, p2; uint8_t idx; int32_t e; };
struct a7_dec { int32_t p1, p2; uint8_t idx; };
static inline int32_t a7_clip16(int32_t v)
{ return v > 32767 ? 32767 : (v < -32768 ? -32768 : v); }
static inline int32_t a7_pred(int32_t p1, int32_t p2)
{ return a7_clip16(p1 + ((p1 - p2) >> 1)); }
__attribute__((optimize("O2")))
static inline __attribute__((always_inline)) uint8_t a7_encode(struct a7_enc *st, int16_t s)
{
	int32_t pr = a7_pred(st->p1, st->p2);
	int32_t step = a7_step[st->idx];
	int32_t d = (int32_t)s - pr + st->e;      /* NS_NUM 8/8 => e as-is */
	uint8_t sign = 0; int32_t ad, q, ne, lim, ni; uint32_t mag;
	if (d < 0) { sign = 64u; ad = -d; } else ad = d;
	mag = (uint32_t)((ad * 32) / step);
	if (mag > 63u) mag = 63u;
	q = (int32_t)((mag * (uint32_t)step) / 32u) + step / 64;
	if (sign) q = -q;
	st->p2 = st->p1; st->p1 = a7_clip16(pr + q);
	ne = d - q; lim = 4 * step;
	st->e = ne > lim ? lim : (ne < -lim ? -lim : ne);
	ni = (int32_t)st->idx + a7_idx7[mag];
	st->idx = (uint8_t)(ni < 0 ? 0 : (ni > 88 ? 88 : ni));
	return (uint8_t)(sign | (uint8_t)mag);
}
__attribute__((optimize("O2")))
/* M74 bitstream helpers: 32-bit, LSB-first -- exactly the order the
 * format already uses (spec 4.1b: "V = c0 | c1<<7 | ... little-endian").
 * These replace uint64_t shifts, which the Cortex-M4 has no barrel
 * shifter for. */
#define A7_FILL(acc, nb, bi, p) do { \
	while ((nb) <= 24u && (bi) < 7u) { \
		(acc) |= (uint32_t)(p)[(bi)++] << (nb); (nb) += 8u; } \
	} while (0)
#define A7_TAKE(c, acc, nb) do { \
	(c) = (uint8_t)((acc) & 0x7Fu); (acc) >>= 7; (nb) -= 7u; \
	} while (0)
static inline __attribute__((always_inline)) int16_t a7_decode(struct a7_dec *st, uint8_t c)
{
	int32_t pr = a7_pred(st->p1, st->p2);
	int32_t step = a7_step[st->idx];
	uint32_t mag = c & 63u;
	int32_t q = (int32_t)((mag * (uint32_t)step) / 32u) + step / 64;
	int32_t rec = a7_clip16((c & 64u) ? (pr - q) : (pr + q));
	int32_t ni = (int32_t)st->idx + a7_idx7[mag];
	st->idx = (uint8_t)(ni < 0 ? 0 : (ni > 88 ? 88 : ni));
	st->p2 = st->p1; st->p1 = rec;
	return (int16_t)rec;
}
static int16_t a7_scrL[280], a7_scrR[280];   /* streamer-only scratch (A7 SONGS) */
/* IL-489: PCM14S decodes into ONE INTERLEAVED buffer so the
 * scratch->ring copy becomes two straight 32-bit memcpy spans
 * instead of a 16-bit-at-a-time interleave. Frame f is at
 * [f*2] = L, [f*2+1] = R. 562 not 560: see the upsample note. */
static int16_t p14s_scr[994] __attribute__((aligned(4)));   /* P16-522: 2*496+2 (P14S uses [0..561]) */
static uint8_t a7_codes[560];
static void a7_emit_block_i(const int16_t *ring, uint32_t ring_mask,
			  uint32_t start, struct a7_enc *eL,
			  struct a7_enc *eR, uint8_t *blk);
static void a7_emit_block(const int16_t *ring, uint32_t ring_mask,
			  uint32_t start, struct a7_enc *eL,
			  struct a7_enc *eR, uint8_t *blk)
{
	M73_T0();
	a7_emit_block_i(ring, ring_mask, start, eL, eR, blk);
	{ uint32_t _d88 = DWT->CYCCNT - _t73;
	  if (_d88 < g_enmin) g_enmin = _d88; }
	M73_ADD(g_t_en);
}
__attribute__((optimize("O2")))
static void a7_emit_block_i(const int16_t *ring, uint32_t ring_mask,
			  uint32_t start, struct a7_enc *eL,
			  struct a7_enc *eR, uint8_t *blk)
{
	uint32_t g, k, i2; uint16_t s16 = 0;
	blk[0] = (uint8_t)(eL->p1 & 0xFF); blk[1] = (uint8_t)((eL->p1 >> 8) & 0xFF);
	blk[2] = (uint8_t)(eL->p2 & 0xFF); blk[3] = (uint8_t)((eL->p2 >> 8) & 0xFF);
	blk[4] = eL->idx;
	blk[5] = g_cap_stereo ? 1u : 0u;  /* M78: mono takes -> mono blocks */
	blk[6] = (uint8_t)(eR->p1 & 0xFF); blk[7] = (uint8_t)((eR->p1 >> 8) & 0xFF);
	blk[8] = (uint8_t)(eR->p2 & 0xFF); blk[9] = (uint8_t)((eR->p2 >> 8) & 0xFF);
	blk[10] = eR->idx; blk[11] = 0;
	blk[12] = (uint8_t)(SAMP_PER_BLK & 0xFF); blk[13] = (uint8_t)(SAMP_PER_BLK >> 8);
	if (blk[5] & 1u) {
		for (i2 = 0; i2 < SAMP_PER_BLK; i2++) {
			/* M91: the rec ring is MONO; this encoder serves ONLY the
			 * rec ring. Stereo blocks (impossible until M63b-2) would
			 * encode L for both channels. */
			uint32_t fi = (start + i2) & ring_mask;
			a7_codes[i2 * 2u]      = a7_encode(eL, ring[fi * 2u]);
			a7_codes[i2 * 2u + 1u] = a7_encode(eR, ring[fi * 2u + 1u]);
		}
	} else {
		/* M78 MONO: one code per frame from L (capture writes the
		 * downmix to both channels, so L is the take). R seeds are
		 * zeroed; the mono decoder never reads them. */
		for (i2 = 0; i2 < SAMP_PER_BLK; i2++) {
			uint32_t fi = (start + i2) & ring_mask;   /* M91 mono ring */
			a7_codes[i2] = a7_encode(eL, ring[fi * 2u]);  /* S2CAP: L of frame */
		}
		blk[6] = 0; blk[7] = 0; blk[8] = 0; blk[9] = 0; blk[10] = 0;
	}
	{
	uint32_t _ng78 = (blk[5] & 1u) ? 70u : 35u;
	for (g = 0; g < _ng78; g++) {
		/* M74: 32-bit LSB-first pack (was a uint64_t V with a
		 * variable-distance shift per code). Identical order, so
		 * byte-for-byte identical output -- stage EQ proves it. */
		uint32_t acc74 = 0, nb74 = 0, bo74 = 0;
		for (k = 0; k < 8u; k++) {
			acc74 |= (uint32_t)(a7_codes[g * 8u + k] & 0x7Fu) << nb74;
			nb74 += 7u;
			while (nb74 >= 8u) {
				blk[16u + g * 7u + bo74++] = (uint8_t)acc74;
				acc74 >>= 8; nb74 -= 8u;
			}
		}
	}
	}
	if (!(blk[5] & 1u))
		for (g = 16u + 245u; g < 506u; g++) blk[g] = 0;
	for (g = 0; g < 490u; g++) s16 = (uint16_t)(s16 + blk[16u + g]);
	blk[14] = (uint8_t)(s16 & 0xFF); blk[15] = (uint8_t)(s16 >> 8);
	for (g = 506u; g < 512u; g++) blk[g] = 0;
}
static void a7_decode_block_i(const uint8_t *blk, int16_t *dstL, int16_t *dstR);
static void a7_decode_block(const uint8_t *blk, int16_t *dstL, int16_t *dstR)
{
	M73_T0();
	a7_decode_block_i(blk, dstL, dstR);
	M73_ADD(g_t_dc);
	g_dcc++;
}

/* M79: decode STRAIGHT INTO THE RING -- deletes the a7_scr scratch
 * store + reload + masked copy (~6-8 ops/frame). Plain fill path
 * only (100% of steady traffic, M76: dcu==dcc); the seam and reverse
 * paths keep the scratch route. The running pointer handles the wrap
 * with one compare per frame: RING_SAMPLES is NOT a multiple of
 * SAMP_PER_BLK (8192 % 280 != 0), so a block CAN wrap mid-decode.
 * Bit-exact: same sample codec, same code order, only the
 * destination changes. Carries its own M73 timing + g_dcc. */
__attribute__((optimize("O2"), noinline))
static void a7_decode_block_ring(const uint8_t *blk, int16_t *ring,
				 uint32_t ring_mask, uint32_t base)
{
	M73_T0();
	struct a7_dec dL, dR;
	uint32_t g, k, i2 = 0;
	int stereo = blk[5] & 1;
	int16_t *p = ring + (base & ring_mask) * 2u;
	int16_t * const rend = ring + (ring_mask + 1u) * 2u;
	dL.p1 = (int16_t)((uint16_t)blk[0] | ((uint16_t)blk[1] << 8));
	dL.p2 = (int16_t)((uint16_t)blk[2] | ((uint16_t)blk[3] << 8));
	dL.idx = blk[4] > 88u ? 88u : blk[4];
	if (!stereo) {
		for (g = 0; g < 35u && i2 < SAMP_PER_BLK; g++) {
			const uint8_t *p79 = blk + 16u + g * 7u;
			uint32_t acc = 0, nb = 0, bi = 0;
			A7_FILL(acc, nb, bi, p79);
			for (k = 0; k < 8u && i2 < SAMP_PER_BLK; k++, i2++) {
				uint8_t c79;
				A7_TAKE(c79, acc, nb); A7_FILL(acc, nb, bi, p79);
				int16_t s = a7_decode(&dL, c79);
				p[0] = s; p[1] = s; p += 2;
				if (p == rend) p = ring;
			}
		}
		M73_ADD(g_t_dc);
		g_dcc++;
		return;
	}
	dR.p1 = (int16_t)((uint16_t)blk[6] | ((uint16_t)blk[7] << 8));
	dR.p2 = (int16_t)((uint16_t)blk[8] | ((uint16_t)blk[9] << 8));
	dR.idx = blk[10] > 88u ? 88u : blk[10];
	for (g = 0; g < 70u && i2 < SAMP_PER_BLK; g++) {
		const uint8_t *p79 = blk + 16u + g * 7u;
		uint32_t acc = 0, nb = 0, bi = 0;
		A7_FILL(acc, nb, bi, p79);
		for (k = 0; k < 8u && i2 < SAMP_PER_BLK; k += 2u, i2++) {
			uint8_t cl79, cr79;
			A7_TAKE(cl79, acc, nb); A7_FILL(acc, nb, bi, p79);
			A7_TAKE(cr79, acc, nb); A7_FILL(acc, nb, bi, p79);
			int16_t sl = a7_decode(&dL, cl79);
			int16_t sr = a7_decode(&dR, cr79);
			p[0] = sl; p[1] = sr; p += 2;
			if (p == rend) p = ring;
		}
	}
	M73_ADD(g_t_dc);
	g_dcc++;
}
__attribute__((optimize("O2")))
static void a7_decode_block_i(const uint8_t *blk, int16_t *dstL, int16_t *dstR)
{
	struct a7_dec dL, dR;
	uint32_t g, k, i2 = 0;
	int stereo = blk[5] & 1;
	dL.p1 = (int16_t)((uint16_t)blk[0] | ((uint16_t)blk[1] << 8));
	dL.p2 = (int16_t)((uint16_t)blk[2] | ((uint16_t)blk[3] << 8));
	dL.idx = blk[4] > 88u ? 88u : blk[4];
	dR.p1 = (int16_t)((uint16_t)blk[6] | ((uint16_t)blk[7] << 8));
	dR.p2 = (int16_t)((uint16_t)blk[8] | ((uint16_t)blk[9] << 8));
	dR.idx = blk[10] > 88u ? 88u : blk[10];
	if (!stereo) {
		/* M78 MONO: 280 codes, 35 groups, one code per frame; the
		 * sample lands on BOTH ring channels. dR is never used. */
		for (g = 0; g < 35u && i2 < SAMP_PER_BLK; g++) {
			const uint8_t *p78 = blk + 16u + g * 7u;
			uint32_t acc = 0, nb = 0, bi = 0;
			A7_FILL(acc, nb, bi, p78);
			for (k = 0; k < 8u && i2 < SAMP_PER_BLK; k++, i2++) {
				uint8_t c78;
				A7_TAKE(c78, acc, nb); A7_FILL(acc, nb, bi, p78);
				int16_t s = a7_decode(&dL, c78);
				dstL[i2] = s; dstR[i2] = s;
			}
		}
		return;
	}
	for (g = 0; g < 70u && i2 < SAMP_PER_BLK; g++) {
		/* M74: 32-bit LSB-first bitstream. Was a uint64_t V with a
		 * variable-distance >> per code -- the M4 has no 64-bit
		 * barrel shifter, so each cost ~10-20 cycles. Same LSB-first
		 * order, so codes are BIT-IDENTICAL (stage EQ proves it on
		 * the host; M70 conformance proves it again on hardware).
		 * Refill keeps nb <= 24 before an OR, so every shift is
		 * in-range for a uint32_t. */
		const uint8_t *p74 = blk + 16u + g * 7u;
		uint32_t acc = 0, nb = 0, bi = 0;
		A7_FILL(acc, nb, bi, p74);
		for (k = 0; k < 8u && i2 < SAMP_PER_BLK; k += 2u, i2++) {
			uint8_t cl74, cr74;
			A7_TAKE(cl74, acc, nb); A7_FILL(acc, nb, bi, p74);
			A7_TAKE(cr74, acc, nb); A7_FILL(acc, nb, bi, p74);
			int16_t sl = a7_decode(&dL, cl74);
			int16_t sr = a7_decode(&dR, cr74);
			if (!stereo) sr = sl;
			dstL[i2] = sl; dstR[i2] = sr;
		}
	}
}
/* PACK: encoder state chains across SEQUENTIAL calls (a flush burst);
 * a non-sequential start resets it. Headers carry the pre-block state,
 * so decode never depends on that continuity. */
static void codec_pack(const int16_t *ring, uint32_t ring_mask, uint32_t start,
                       uint8_t *flash, uint32_t nblk)
{
	static struct a7_enc peL, peR;
	static uint32_t p_expect = 0xFFFFFFFFu;
	if (start != p_expect) {
		peL.p1 = 0; peL.p2 = 0; peL.idx = 0; peL.e = 0;
		peR = peL;
	}
	for (uint32_t b = 0; b < nblk; b++)
		a7_emit_block(ring, ring_mask,
			      (start + b * SAMP_PER_BLK) & ring_mask,
			      &peL, &peR, flash + b * EMMC_BLOCK_SIZE);
	p_expect = (start + nblk * SAMP_PER_BLK) & ring_mask;
}
static void codec_unpack(int16_t *ring, uint32_t ring_mask, uint32_t start,
                         const uint8_t *flash, uint32_t nblk)
{
	/* M79: straight to the ring; scratch route retired from this
	 * path (seam + reverse keep it). */
	for (uint32_t b = 0; b < nblk; b++) {
		a7_decode_block_ring(flash + b * EMMC_BLOCK_SIZE, ring,
				     ring_mask, start + b * SAMP_PER_BLK);
		g_dcu++;
	}
}
/* M22-B seam, with the M62-r2 MULTI-BLOCK walk: the caller's run can
 * span blocks (_ds = n*SAMP_PER_BLK - off). The r1 single-block version
 * of this is what caused the stutter; do not simplify it back. */
static void codec_unpack_part(int16_t *ring, uint32_t ring_mask, uint32_t start,
                              const uint8_t *flash, uint32_t skip, uint32_t nsamp)
{
	uint32_t pos = start, done = 0;
	uint32_t b = skip / SAMP_PER_BLK, off = skip % SAMP_PER_BLK;
	while (done < nsamp) {
		uint32_t take = SAMP_PER_BLK - off;
		if (take > nsamp - done) take = nsamp - done;
		a7_decode_block(flash + b * EMMC_BLOCK_SIZE, a7_scrL, a7_scrR);
		g_dcp++;
		for (uint32_t i2 = 0; i2 < take; i2++) {
			uint32_t fi = (pos & ring_mask) * 2u;
			ring[fi] = a7_scrL[off + i2];
			ring[fi + 1u] = a7_scrR[off + i2];
			pos++;
		}
		done += take; off = 0; b++;
	}
}
/* Reversed heads: coded blocks cannot be byte-flipped, so decode in
 * reverse block order and write each block's frames time-reversed.
 * Same audible result the M15-r2 batch flip had on PCM. */
static void codec_unpack_rev(int16_t *ring, uint32_t ring_mask, uint32_t start,
                             const uint8_t *flash, uint32_t nblk)
{
	uint32_t pos = start;
	for (uint32_t b = nblk; b-- > 0u; ) {
		a7_decode_block(flash + b * EMMC_BLOCK_SIZE, a7_scrL, a7_scrR);
		g_dcr++;
		for (uint32_t i2 = SAMP_PER_BLK; i2-- > 0u; ) {
			uint32_t fi = (pos & ring_mask) * 2u;
			ring[fi] = a7_scrL[i2]; ring[fi + 1u] = a7_scrR[i2];
			pos++;
		}
	}
}

#elif SP1_CODEC == SP1_CODEC_ULAW
/* ---- G.711 u-law, 8-bit, 2:1 --------------------------------------------- */
#define ULAW_BIAS 0x84
#define ULAW_CLIP 32635
static inline uint8_t ulaw_encode(int16_t pcm)
{
	int sign = (pcm >> 8) & 0x80;
	int s = pcm;
	if (sign) s = -s;
	if (s > ULAW_CLIP) s = ULAW_CLIP;
	s += ULAW_BIAS;
	int exp = 7;
	for (int em = 0x4000; (s & em) == 0 && exp > 0; exp--, em >>= 1) { }
	int mant = (s >> (exp + 3)) & 0x0F;
	return (uint8_t)(~(sign | (exp << 4) | mant));
}
static inline int16_t ulaw_decode(uint8_t u)
{
	u = ~u;
	int sign = u & 0x80;
	int exp  = (u >> 4) & 0x07;
	int mant = u & 0x0F;
	int s = ((mant << 3) + ULAW_BIAS) << exp;
	s -= ULAW_BIAS;
	return (int16_t)(sign ? -s : s);
}
/* one u-law byte per sample; SAMP_PER_BLK == 512 == EMMC_BLOCK_SIZE */
static void codec_pack(const int16_t *ring, uint32_t ring_mask, uint32_t start,
                       uint8_t *flash, uint32_t nblk)
{
	uint32_t ntot = nblk * SAMP_PER_BLK;
	uint32_t pos = start;
	for (uint32_t i = 0; i < ntot; i++) {
		flash[i] = ulaw_encode(ring[pos]);
		pos = (pos + 1u) & ring_mask;
	}
}
static void codec_unpack(int16_t *ring, uint32_t ring_mask, uint32_t start,
                         const uint8_t *flash, uint32_t nblk)
{
	uint32_t ntot = nblk * SAMP_PER_BLK;
	uint32_t pos = start;
	for (uint32_t i = 0; i < ntot; i++) {
		ring[pos] = ulaw_decode(flash[i]);
		pos = (pos + 1u) & ring_mask;
	}
}

#else /* SP1_CODEC == SP1_CODEC_ADPCM */
/* ---- IMA ADPCM, 4-bit, ~4:1, SELF-CONTAINED 512-byte blocks --------------
 * Each 512-byte flash block decodes STANDALONE (predictor + step index RESET at
 * the block start) so random-access loop seeks land on any block.
 *   byte 0..1 : int16 predictor seed (little-endian) = block's first sample
 *   byte 2    : uint8 step index seed (0..88)
 *   byte 3    : pad (0)
 *   byte 4..511 : 508 data bytes * 2 nibbles = 1016 samples (SAMP_PER_BLK).
 * Within a block, sample[k] is encoded as nibble[k] against the running
 * predictor seeded from the header (so nibble[0] re-encodes sample[0] against
 * predictor==sample[0]; round-trips to ~sample[0]). 508 bytes = exactly 1016
 * nibbles = SAMP_PER_BLK. Low nibble of each byte first, then high nibble. */
static const int8_t  ima_index_tab[16] = {
	-1, -1, -1, -1, 2, 4, 6, 8,
	-1, -1, -1, -1, 2, 4, 6, 8
};
static const int16_t ima_step_tab[89] = {
	    7,     8,     9,    10,    11,    12,    13,    14,    16,    17,
	   19,    21,    23,    25,    28,    31,    34,    37,    41,    45,
	   50,    55,    60,    66,    73,    80,    88,    97,   107,   118,
	  130,   143,   157,   173,   190,   209,   230,   253,   279,   307,
	  337,   371,   408,   449,   494,   544,   598,   658,   724,   796,
	  876,   963,  1060,  1166,  1282,  1411,  1552,  1707,  1878,  2066,
	 2272,  2499,  2749,  3024,  3327,  3660,  4026,  4428,  4871,  5358,
	 5894,  6484,  7132,  7845,  8630,  9493, 10442, 11487, 12635, 13899,
	15289, 16818, 18500, 20350, 22385, 24623, 27086, 29794, 32767
};
#define ADPCM_HDR_BYTES   4u
#define ADPCM_DATA_BYTES  (EMMC_BLOCK_SIZE - ADPCM_HDR_BYTES)   /* 508 -> 1016 samples */

static inline uint8_t ima_enc_step(int16_t sample, int32_t *pred, int *idx)
{
	int step = ima_step_tab[*idx];
	int diff = sample - *pred;
	int code = 0;
	if (diff < 0) { code = 8; diff = -diff; }
	if (diff >= step)        { code |= 4; diff -= step; }
	if (diff >= (step >> 1)) { code |= 2; diff -= step >> 1; }
	if (diff >= (step >> 2)) { code |= 1; }
	/* reconstruct EXACTLY as the decoder will, to keep predictor in lockstep */
	int diffq = step >> 3;
	if (code & 4) diffq += step;
	if (code & 2) diffq += step >> 1;
	if (code & 1) diffq += step >> 2;
	if (code & 8) *pred -= diffq; else *pred += diffq;
	if (*pred >  32767) *pred =  32767;
	if (*pred < -32768) *pred = -32768;
	*idx += ima_index_tab[code & 7];
	if (*idx < 0)  *idx = 0;
	if (*idx > 88) *idx = 88;
	return (uint8_t)(code & 0x0F);
}
static inline int16_t ima_dec_step(uint8_t code, int32_t *pred, int *idx)
{
	int step = ima_step_tab[*idx];
	int diffq = step >> 3;
	if (code & 4) diffq += step;
	if (code & 2) diffq += step >> 1;
	if (code & 1) diffq += step >> 2;
	if (code & 8) *pred -= diffq; else *pred += diffq;
	if (*pred >  32767) *pred =  32767;
	if (*pred < -32768) *pred = -32768;
	*idx += ima_index_tab[code & 7];
	if (*idx < 0)  *idx = 0;
	if (*idx > 88) *idx = 88;
	return (int16_t)*pred;
}

/* Encode exactly ONE block (SAMP_PER_BLK==1016 samples) into one 512-byte block,
 * predictor + step index RESET at block start -> block is standalone. */
static void adpcm_pack_block(const int16_t *ring, uint32_t ring_mask,
                             uint32_t start, uint8_t *blk)
{
	uint32_t pos = start;
	int32_t pred = ring[pos];          /* seed predictor = first sample */
	int idx = 0;                        /* fixed reset step index */
	blk[0] = (uint8_t)(pred & 0xFF);
	blk[1] = (uint8_t)((pred >> 8) & 0xFF);
	blk[2] = (uint8_t)idx;
	blk[3] = 0;
	uint8_t *data = blk + ADPCM_HDR_BYTES;
	for (uint32_t i = 0; i < ADPCM_DATA_BYTES; i++) {
		int16_t s0 = ring[pos];  pos = (pos + 1u) & ring_mask;
		uint8_t n0 = ima_enc_step(s0, &pred, &idx);
		int16_t s1 = ring[pos];  pos = (pos + 1u) & ring_mask;
		uint8_t n1 = ima_enc_step(s1, &pred, &idx);
		data[i] = (uint8_t)(n0 | (n1 << 4));
	}
}
/* Decode exactly ONE block back into SAMP_PER_BLK==1016 ring samples. */
static void adpcm_unpack_block(int16_t *ring, uint32_t ring_mask,
                               uint32_t start, const uint8_t *blk)
{
	uint32_t pos = start;
	int32_t pred = (int16_t)((uint16_t)blk[0] | ((uint16_t)blk[1] << 8));
	int idx = blk[2];
	if (idx > 88) idx = 88;
	const uint8_t *data = blk + ADPCM_HDR_BYTES;
	for (uint32_t i = 0; i < ADPCM_DATA_BYTES; i++) {
		uint8_t b = data[i];
		ring[pos] = ima_dec_step(b & 0x0F, &pred, &idx);
		pos = (pos + 1u) & ring_mask;
		ring[pos] = ima_dec_step((b >> 4) & 0x0F, &pred, &idx);
		pos = (pos + 1u) & ring_mask;
	}
}
/* nblk blocks, each independent (fresh predictor) — REQUIRED for random-access
 * loop seeks: a play read can start at ANY block, so every block must decode
 * without history from the previous one. */
static void codec_pack(const int16_t *ring, uint32_t ring_mask, uint32_t start,
                       uint8_t *flash, uint32_t nblk)
{
	uint32_t pos = start;
	for (uint32_t b = 0; b < nblk; b++) {
		adpcm_pack_block(ring, ring_mask, pos, flash + b * EMMC_BLOCK_SIZE);
		pos = (pos + SAMP_PER_BLK) & ring_mask;
	}
}
static void codec_unpack(int16_t *ring, uint32_t ring_mask, uint32_t start,
                         const uint8_t *flash, uint32_t nblk)
{
	uint32_t pos = start;
	for (uint32_t b = 0; b < nblk; b++) {
		adpcm_unpack_block(ring, ring_mask, pos, flash + b * EMMC_BLOCK_SIZE);
		pos = (pos + SAMP_PER_BLK) & ring_mask;
	}
}
#endif /* SP1_CODEC */

/* ==== M71: verified async reads for the streamer. The port (M50) +
 * CRC tails (M54) + PSEL re-orient (M55r6) are the six-bench-proven
 * triple. <=16-block chunks (the tail stash caps at 16), 3 attempts,
 * then the SYNC path as courier fallback — never worse than before.
 * ONLY the streamer thread may call this (single storage owner). ==== */
extern void emmc_m50_setup(void);
extern int emmc_m50_read_async(uint32_t blk, uint8_t *buf, uint32_t n);
extern int emmc_m50_wait(int ms);
extern uint8_t m54_tails[32][2];
extern void emmc_m54_crc_init(void);
extern uint16_t emmc_m54_crc16(const uint8_t *d, uint32_t n);
static volatile uint32_t g_m71_as, g_m71_rt, g_m71_fb;
static volatile uint32_t g_m71_ca, g_m71_rq, g_m71_rd, g_m71_wu;
/* ==== PCM14S: the two-tier TAKE codec (design doc + script 459) ====
 * 24 kHz stereo 14-bit shaped. 512 B = 16 B hdr + 140 stored frames
 * x 3.5 B. ONE BLOCK = 280 ENGINE frames: the decoder upsamples 2:1
 * (linear), so the transport/region/bus math is identical to A7.
 * Marker blk[11] = 0x5B -> per-block dispatch; mixed tracks decode.
 * Shaper e1 is CARRIED across blocks (encode-side; decode stateless);
 * reset at punch-in. Continuity: the sequential fill heals the odd
 * frame before each block against the previous block's last stored
 * frame (per-track state); seam/reverse paths duplicate one frame.
 * 64-bit pack shifts (4 x 14 = 56 bits) -- see 459's C-port note. */

/* PK32-484: the last PCM14S hot function still at -Os. Stage K gave
 * the A7 encoder -O2 and 479 gave the decoder -O2; this is the
 * encode side of marc's record corner. */
__attribute__((optimize("O2")))
static void p14s_pack_blocks(const int16_t *ring, uint32_t ring_mask,
			     uint32_t start, uint8_t *out, uint32_t nblk)
{
	uint32_t _tep = DWT->CYCCNT;   /* EP-484 */
	for (uint32_t b = 0; b < nblk; b++) {
		uint8_t *blk = out + b * EMMC_BLOCK_SIZE;
		uint32_t f0 = start + b * 140u;   /* CD-463: STORED (24k) frames */
		blk[0] = 0x50u; blk[1] = 0x31u; blk[2] = 0x34u; blk[3] = 0x53u;
		blk[4] = 0; blk[5] = 1u; blk[6] = 0; blk[7] = 0;
		blk[8] = 0; blk[9] = 0; blk[10] = 0; blk[11] = P14S_MARK;
		blk[12] = (uint8_t)(SAMP_PER_BLK & 0xFFu);
		blk[13] = (uint8_t)(SAMP_PER_BLK >> 8);
		/* BG-470: BLOCK FLOATING POINT. Pass 1 -- peak of the 140 stored
		 * frames (both channels). Pass 2 -- encode with the samples
		 * scaled up by `sh`, so the effective quantizer step is 4 >> sh.
		 * At a typical playing level (peak ~ -14 dBFS) sh lands on 2 and
		 * the step becomes 1: bit-exact 16-bit storage, matching v2.7.2
		 * (marc's clean reference). Headroom check leaves room for the
		 * shaper error (clamped +-16) plus one step. */
		int32_t _pk = 0;
		for (uint32_t i = 0; i < 140u; i++) {
			uint32_t fa = ((f0 + i) & ring_mask) * 2u;
			int32_t a = (int32_t)ring[fa];      if (a < 0) a = -a;
			int32_t d = (int32_t)ring[fa + 1u]; if (d < 0) d = -d;
			if (a > _pk) _pk = a;
			if (d > _pk) _pk = d;
		}
		uint32_t sh = 0u;
		while (sh < 3u && (_pk << (sh + 1u)) < 32000) sh++;
		blk[14] = (uint8_t)sh; blk[15] = 0;
		/* S8/Q RULE: the shaper error is invalid across a step-size
		 * change -- reset e1 whenever the shift moves (this exact bug
		 * bit the S8/Q build three times). */
		if (sh != g_p14s_sh) { g_p14s_e1[0] = 0; g_p14s_e1[1] = 0; g_p14s_sh = sh; }
		uint32_t o = 16u;
		for (uint32_t i = 0; i < 140u; i += 2u) {
			int32_t q4[4];
			for (uint32_t k = 0; k < 2u; k++) {
				uint32_t fa = ((f0 + i + k) & ring_mask) * 2u;
				for (uint32_t c = 0; c < 2u; c++) {
					/* CD-463: boxcar moved to capture; ring is already 24k */
					int32_t s24 = (int32_t)ring[fa + c] << sh;   /* BG-470 */
					int32_t v = s24 - g_p14s_e1[c];
					if (v > 32767) v = 32767;
					else if (v < -32768) v = -32768;
					int32_t q = (v + 2) >> 2;
					if (q > 8191) q = 8191;
					else if (q < -8192) q = -8192;
					g_p14s_e1[c] = (q << 2) - v;
					if (g_p14s_e1[c] > 16) g_p14s_e1[c] = 16;
					else if (g_p14s_e1[c] < -16) g_p14s_e1[c] = -16;
					q4[k * 2u + c] = q;
				}
			}
			{	/* PK32-484: two 32-bit words, no 64-bit arithmetic.
				 * Exact inverse of the 477 decode. */
				uint32_t _p0 = (uint32_t)q4[0] & 0x3FFFu;
				uint32_t _p1 = (uint32_t)q4[1] & 0x3FFFu;
				uint32_t _p2 = (uint32_t)q4[2] & 0x3FFFu;
				uint32_t _p3 = (uint32_t)q4[3] & 0x3FFFu;
				uint32_t _pa = (_p0 << 18) | (_p1 << 4) | (_p2 >> 10);
				uint32_t _pb = (_p2 << 14) | _p3;
				blk[o     ] = (uint8_t)(_pa >> 24);
				blk[o + 1u] = (uint8_t)(_pa >> 16);
				blk[o + 2u] = (uint8_t)(_pa >>  8);
				blk[o + 3u] = (uint8_t)(_pa);
				blk[o + 4u] = (uint8_t)(_pb >> 16);
				blk[o + 5u] = (uint8_t)(_pb >>  8);
				blk[o + 6u] = (uint8_t)(_pb);
			}
			o += 7u;
		}
	}
	if (g_rec_track >= 0) {   /* EP-484: record corner, any speed */
		g_t_ep += (uint32_t)(DWT->CYCCNT - _tep);
		g_t_epn++;
		g_ep_blk += nblk;
	}
}

/* decode ONE P14S block into a7_scrL/R (280 engine frames). The last
 * odd frame duplicates (healed by the sequential path via prev). */
/* O2P-479: the firmware is built -Os (CONFIG_SIZE_OPTIMIZATIONS=y).
 * Stage K gave the A7 codec per-function -O2; this decoder was written
 * later (two-tier, 460) and never got it -- while becoming the hottest
 * function in the build (476: 40.9%% of the corner's wall time). The 478
 * disassembly showed -Os spilling to the stack inside the inner loop. */
__attribute__((optimize("O2")))
static void p14s_dec_scr(const uint8_t *blk)
{
	M73_T0();   /* UP-476 */
	/* BG-470: block-gain shift; 0 in every pre-470 take -> identical decode */
	const uint32_t _sh = (uint32_t)(blk[14] & 3u);
	const uint8_t *o = blk + 16u;
	for (uint32_t i = 0; i < 140u; i += 2u) {
		/* X32-477: two overlapping big-endian 32-bit words replace the
		 * uint64_t. A = v64 bits 55..24, B = v64 bits 31..0. */
		uint32_t _a32, _b32;
		memcpy(&_a32, o, 4);
		memcpy(&_b32, o + 3, 4);
		_a32 = __builtin_bswap32(_a32);
		_b32 = __builtin_bswap32(_b32);
		o += 7u;
		int32_t s0 = (int32_t)((_a32 >> 18) & 0x3FFFu);
		int32_t s1 = (int32_t)((_a32 >>  4) & 0x3FFFu);
		int32_t s2 = (int32_t)((_b32 >> 14) & 0x3FFFu);
		int32_t s3 = (int32_t)( _b32        & 0x3FFFu);
		if (s0 > 8191) s0 -= 16384; if (s1 > 8191) s1 -= 16384;
		if (s2 > 8191) s2 -= 16384; if (s3 > 8191) s3 -= 16384;
		p14s_scr[i * 4u]        = (int16_t)((s0 << 2) >> _sh);  /* BG-470 */
		p14s_scr[i * 4u + 1u]   = (int16_t)((s1 << 2) >> _sh);
		p14s_scr[i * 4u + 4u]   = (int16_t)((s2 << 2) >> _sh);
		p14s_scr[i * 4u + 5u]   = (int16_t)((s3 << 2) >> _sh);
	}
	for (uint32_t j = 0; j < 277u; j += 2u) {   /* IL-489: was 279u, OOB */
		p14s_scr[j * 2u + 2u] = (int16_t)(((int32_t)p14s_scr[j * 2u]
						  + p14s_scr[j * 2u + 4u]) >> 1);
		p14s_scr[j * 2u + 3u] = (int16_t)(((int32_t)p14s_scr[j * 2u + 1u]
						  + p14s_scr[j * 2u + 5u]) >> 1);
	}
	p14s_scr[558] = p14s_scr[556]; p14s_scr[559] = p14s_scr[557];
	M73_ADD(g_t_ps);   /* UP-476 */
}

/* sequential fill dispatch: per-block marker branch; P14S blocks copy
 * scr -> stereo pring and HEAL the previous odd frame via per-track
 * continuity. A7 blocks fall through to codec_unpack one at a time. */
/* O2P-479: same reasoning -- this carries the scratch->ring copy, which
 * 476 measured at pk - ps = 15.9%% of the corner. */
__attribute__((optimize("O2")))
/* ==== P16-522: the PCM16-mono take codec (the spike's PROVEN arms) =====
 * Storage: 512-B block = 16-B header ('P16M' sig, blk[11]=P14S_MARK kept
 * so the block-level dispatch is untouched, blk[5]=0 mono, blk[12..13]=496)
 * + 248 little-endian int16 stored samples (24 kHz mono). Unit map (W136):
 * pack-internal f0 = STORED frames; decode s0 = ENGINE frames. */
static void p16m_dec_scr(const uint8_t *blk)
{
	/* r2 interp upsample, ear-proven: frame 2i = v[i] (both channels),
	 * frame 2i+1 = (v[i]+v[i+1]+1)>>1; the final odd frame holds. */
	for (uint32_t i = 0; i < 248u; i++) {
		int32_t v  = (int16_t)((uint16_t)blk[16u + i * 2u] |
		                       ((uint16_t)blk[16u + i * 2u + 1u] << 8));
		int32_t vn = (i < 247u)
		           ? (int16_t)((uint16_t)blk[18u + i * 2u] |
		                       ((uint16_t)blk[19u + i * 2u] << 8))
		           : v;
		int32_t h = (v + vn + 1) >> 1;
		p14s_scr[i * 4u]      = (int16_t)v; p14s_scr[i * 4u + 1u] = (int16_t)v;
		p14s_scr[i * 4u + 2u] = (int16_t)h; p14s_scr[i * 4u + 3u] = (int16_t)h;
	}
}

static void p16m_pack_blocks(const int16_t *ring, uint32_t ring_mask,
			     uint32_t start, uint8_t *out, uint32_t nblk)
{
	/* the spike r4 arm: 248 CONSECUTIVE stored frames per block, stride 1,
	 * downmix (L+R+1)>>1. start is in STORED (24k) frames -- W136. */
	for (uint32_t b = 0; b < nblk; b++) {
		uint8_t *blk = out + b * EMMC_BLOCK_SIZE;
		uint32_t f0 = start + b * 248u;   /* STORED (24k) frames */
		blk[0] = 0x50u; blk[1] = 0x31u; blk[2] = 0x36u; blk[3] = 0x4Du;
		blk[4] = 0; blk[5] = 0; blk[6] = 0; blk[7] = 0;
		blk[8] = 0; blk[9] = 0; blk[10] = 0; blk[11] = P14S_MARK;
		blk[12] = (uint8_t)(496u & 0xFFu);
		blk[13] = (uint8_t)(496u >> 8);
		blk[14] = 0; blk[15] = 0;
		uint32_t o = 16u;
		for (uint32_t i = 0; i < 248u; i++) {
			uint32_t fa = ((f0 + i) & ring_mask) * 2u;
			int32_t m = ((int32_t)ring[fa] + (int32_t)ring[fa + 1u] + 1) >> 1;
			blk[o]      = (uint8_t)((uint16_t)m & 0xFFu);
			blk[o + 1u] = (uint8_t)((uint16_t)m >> 8);
			o += 2u;
		}
	}
}

static void takes_pack_blocks(struct looptrk *t, const int16_t *ring,
			      uint32_t ring_mask, uint32_t start,
			      uint8_t *out, uint32_t nblk)
{
	if (t->p16m) p16m_pack_blocks(ring, ring_mask, start, out, nblk);
	else         p14s_pack_blocks(ring, ring_mask, start, out, nblk);
}

/* P16-522: the unpack family parameter is named `trk`, which SHADOWS
 * the global track array -- TSPBI(trk) would expand to trk[trk].p16m.
 * This helper lives OUTSIDE the shadowed scope. */
static uint32_t p16m_trk_spb(int ti)
{
	return TSPBI(ti);
}

static void p14s_unpack(int16_t *ring, uint32_t ring_mask, uint32_t start,
			const uint8_t *flash, uint32_t nblk, int trk)
{
	M73_T0();   /* UP-476 */
	uint32_t s0 = start;   /* P16-522: stride = the TRACK's geometry */
	for (uint32_t b = 0; b < nblk; b++) {
		const uint8_t *blk = flash + b * EMMC_BLOCK_SIZE;
		uint32_t _spb = p16m_trk_spb(trk);   /* P16-522: TRACK-driven -- the zeroed
		                               * silence pad strides correctly too */
		if (blk[11] == P14S_MARK) {
			if      (blk[2] == 0x36u) p16m_dec_scr(blk);   /* P16-522 */
			else if (blk[2] == 0x34u) p14s_dec_scr(blk);
			else    /* GS-531 (W144): mark present but FOREIGN sig -- a
			         * future codec or cross-version content. SILENCE,
			         * never garbage. */
				memset(p14s_scr, 0, (size_t)_spb * 4u);
			{	/* CPY-483: the ring wraps at most once per block, so
				 * split there and walk pointers instead of recomputing
				 * (add, AND, shift) for all 280 frames. Bit-exact by
				 * construction -- see the stage header. */
				uint32_t _cap  = ring_mask + 1u;
				uint32_t _base = s0 & ring_mask;
				uint32_t _run  = _cap - _base;
				if (_run > _spb) _run = _spb;
				/* W2X-490: ONE 32-bit word per FRAME, INLINE.
				 * 489 used memcpy() with a RUNTIME size -- GCC cannot
				 * inline that, so it emitted `bl memcpy` into libc and
				 * the copy got 3x SLOWER than the -O2 hand loop (W44).
				 * Both sides are aligned(4), so a word move is legal and
				 * halves the memory ops: 560 halfwords -> 280 words. */
				uint32_t *_d32 = (uint32_t *)(void *)
						(ring + (size_t)_base * 2u);
				const uint32_t *_s32 = (const uint32_t *)(const void *)p14s_scr;
				for (uint32_t f = 0; f < _run; f++) *_d32++ = *_s32++;
				if (_run < _spb) {
					_d32 = (uint32_t *)(void *)ring;
					for (uint32_t f = _run; f < _spb; f++)
						*_d32++ = *_s32++;
				}
			}
			{ uint32_t hp = ((s0 - 1u) & ring_mask) * 2u;
			  ring[hp]      = (int16_t)(((int32_t)g_p14s_prev[trk][0] + p14s_scr[0]) >> 1);
			  ring[hp + 1u] = (int16_t)(((int32_t)g_p14s_prev[trk][1] + p14s_scr[1]) >> 1); }
			g_p14s_prev[trk][0] = p14s_scr[_spb * 2u - 4u];   /* last EXACT frame; 556 for P14S */
			g_p14s_prev[trk][1] = p14s_scr[_spb * 2u - 3u];
		} else if (_spb == 496u) {
			/* P16-522: a non-P16M block under a P16M take = the SILENCE
			 * PAD -- write true silence at the caller's stride. */
			for (uint32_t f = 0; f < _spb; f++) {
				uint32_t fi = ((s0 + f) & ring_mask) * 2u;
				ring[fi] = 0; ring[fi + 1u] = 0;
			}
		} else {
			codec_unpack(ring, ring_mask, s0, blk, 1u);
		}
		s0 += _spb;   /* P16-522 */
	}
	if (M73_CY_NOW()) g_pk_blk += nblk;   /* UP-476 */
	M73_ADD(g_t_pk);   /* UP-476 */
}

static void p14s_unpack_part(int16_t *ring, uint32_t ring_mask, uint32_t start,
			     const uint8_t *flash, uint32_t skip, uint32_t nsamp, int trk)
{
	/* FZ-464: this is NOT seam-rate -- the plain fill and the prime path
	 * both decode through here, so it needs the SAME cross-block
	 * continuity as the full-path decoder. Without it, every block's
	 * provisional last frame stayed a DUPLICATE: a step glitch up to
	 * 171x/s = the block-edge zipper marc's ear caught twice (E render;
	 * then on hardware as "fuzzy bass", 2026-08-26). Conformance: 12,691
	 * unhealed edges vs the reference, ALL at position 279, max 13,406.
	 * A7 blocks in the span fall through to codec_unpack_part. */
	uint32_t f = skip;
	uint32_t done = 0;
	const uint32_t _spb = p16m_trk_spb(trk);   /* P16-522: TRACK-driven, so the
	                                     * zeroed silence pad stays correct */
	while (done < nsamp) {
		uint32_t blkno = f / _spb;
		uint32_t off   = f - blkno * _spb;
		uint32_t run   = _spb - off;
		if (run > nsamp - done) run = nsamp - done;
		const uint8_t *blk = flash + blkno * EMMC_BLOCK_SIZE;
		if (blk[11] == P14S_MARK) {
			if      (blk[2] == 0x36u) p16m_dec_scr(blk);   /* P16-522 */
			else if (blk[2] == 0x34u) p14s_dec_scr(blk);
			else    /* GS-531 (W144): mark present but FOREIGN sig -- a
			         * future codec or cross-version content. SILENCE,
			         * never garbage. */
				memset(p14s_scr, 0, (size_t)_spb * 4u);
			for (uint32_t k = 0; k < run; k++) {
				uint32_t fi = ((start + done + k) & ring_mask) * 2u;
				ring[fi]      = p14s_scr[(off + k) * 2u];
				ring[fi + 1u] = p14s_scr[(off + k) * 2u + 1u];
			}
			if (off == 0u) {
				/* block ENTRY: heal the previous engine frame
				 * (written by an earlier pass or the loop seam)
				 * exactly like the full path. */
				uint32_t hp = ((start + done - 1u) & ring_mask) * 2u;
				ring[hp]      = (int16_t)(((int32_t)g_p14s_prev[trk][0] + p14s_scr[0]) >> 1);
				ring[hp + 1u] = (int16_t)(((int32_t)g_p14s_prev[trk][1] + p14s_scr[1]) >> 1);
			}
			if (off + run >= _spb - 1u) {   /* P16-522: was 279u = 280-1 */
				/* this pass decoded through the block's last stored
				 * frame -> it becomes the prev for the next entry. */
				g_p14s_prev[trk][0] = p14s_scr[_spb * 2u - 4u];   /* P16-522 */
				g_p14s_prev[trk][1] = p14s_scr[_spb * 2u - 3u];
			}
		} else if (_spb == 496u) {
			/* P16-522: a non-P16M block under a P16M take = the SILENCE
			 * PAD. Write true silence; the A7 fallthrough would page a
			 * zeroed buffer at the wrong geometry. */
			for (uint32_t k = 0; k < run; k++) {
				uint32_t fi = ((start + done + k) & ring_mask) * 2u;
				ring[fi] = 0; ring[fi + 1u] = 0;
			}
		} else {
			codec_unpack_part(ring, ring_mask, start + done, flash, f, run);
		}
		f += run; done += run;
	}
}

static void p14s_unpack_rev(int16_t *ring, uint32_t ring_mask, uint32_t start,
			    const uint8_t *flash, uint32_t nblk)
{
	uint32_t _s0 = start;   /* P16-522: per-block stride, as in p14s_unpack */
	for (uint32_t b = 0; b < nblk; b++) {
		const uint8_t *blk = flash + b * EMMC_BLOCK_SIZE;
		uint32_t _spb = (blk[11] == P14S_MARK && blk[2] == 0x36u) ? 496u : SAMP_PER_BLK;
		if (blk[11] == P14S_MARK) {
			if      (blk[2] == 0x36u) p16m_dec_scr(blk);   /* P16-522 */
			else if (blk[2] == 0x34u) p14s_dec_scr(blk);
			else    /* GS-531 (W144): mark present but FOREIGN sig -- a
			         * future codec or cross-version content. SILENCE,
			         * never garbage. */
				memset(p14s_scr, 0, (size_t)_spb * 4u);
			for (uint32_t f = 0; f < _spb; f++) {
				uint32_t fi = ((_s0 + f) & ring_mask) * 2u;
				ring[fi]      = p14s_scr[(_spb - 1u - f) * 2u];
				ring[fi + 1u] = p14s_scr[(_spb - 1u - f) * 2u + 1u];
			}
		} else {
			codec_unpack_rev(ring, ring_mask, _s0, blk, 1u);
		}
		_s0 += _spb;
	}
}

static void p14s_mask_from_x3(uint32_t slot)
{
	g_p14s_mask = 0;
	if (g_x3_ok && slot < NUM_SLOTS)
		for (int xi = 0; xi < NTRK; xi++)
			if (g_x3.t[slot][xi].codec_id == X3_CODEC_P14S ||
			    g_x3.t[slot][xi].codec_id == X3_CODEC_P16M) {
				g_p14s_mask |= (uint8_t)(1u << xi);
				trk[xi].p16m = (g_x3.t[slot][xi].codec_id
				                == X3_CODEC_P16M) ? 1u : 0u;   /* P16-522 */
				{	/* PS-535, as in the restore path */
					uint8_t _rv = g_x3.t[slot][xi].rsv;
					trk[xi].p16m_next = (_rv & 0x80u)
					                  ? (uint8_t)(_rv & 1u)
					                  : trk[xi].p16m;
				}
			}
}

static bool emmc_read_blocks_fast(uint32_t blk, uint8_t *buf, uint32_t n)
{
	M73_T0();
	int64_t _t0 = k_uptime_get();
	g_m71_ca++; g_m71_rq += n;
	static uint8_t m71_init;   /* 0 = not yet, 1 = ok */
	if (!m71_init) {
		emmc_m50_setup();
		emmc_m54_crc_init();
		m71_init = 1;
	}
	uint32_t done = 0;
	while (done < n) {
		uint32_t c = n - done;
		if (c > 32u) c = 32u;   /* M71r5: whole turn in one arm */
		uint8_t *dst = buf + done * EMMC_BLOCK_SIZE;
		int good = 0;
		for (int attempt = 0; attempt < 3 && !good; attempt++) {
			int bad, r;
			if (attempt) g_m71_rt++;
			if (!emmc_m50_read_async(blk + done, dst, c)) {
				k_msleep(1);
				continue;
			}
			r = emmc_m50_wait(300);
			if (r != 1) continue;
			bad = -1;
			for (uint32_t bi = 0; bi < c; bi++) {
				uint16_t cc = emmc_m54_crc16(dst + bi * 512u, 512u);
				uint16_t tb = (uint16_t)((m54_tails[bi][0] << 8) |
							  m54_tails[bi][1]);
				if (cc != tb) { bad = (int)bi; break; }
			}
			if (bad < 0) good = 1;
		}
		if (!good) {
			/* courier: the proven sync path takes this chunk */
			g_m71_fb++;
			if (!emmc_read_blocks(blk + done, dst, c))
				return false;
		} else {
			g_m71_as += c;
		}
		done += c;
	}
	g_m71_wu += (uint32_t)(k_uptime_get() - _t0);
	M73_ADD(g_t_rd);
	return true;
}


/* ALN-525 (W143): PIN the streamer to a 2048-byte flash boundary.
 * The night of 2026-08-30 proved the max+stream corner regresses when
 * ANY upstream code growth shifts this function's address (0x25aac
 * clean everywhere, 0x25b34 regressed; the PAD probe -- dead bytes,
 * code unmoved -- ran clean). Pinning makes every future stage
 * placement-immune. If THIS build regresses, phase 0 is unlucky:
 * iterate the alignment offset, do not unpin. */
static void __attribute__((aligned(2048))) streamer_thread(void *a, void *b, void *c)
{
	ARG_UNUSED(a); ARG_UNUSED(b); ARG_UNUSED(c);
	static uint8_t blk[EMMC_BLOCK_SIZE];
	static uint8_t metabuf[META_BLOCKS * EMMC_BLOCK_SIZE];  /* 2-block song index */
	/* Flush the rec ring in MULTI-BLOCK (CMD25) bursts: the card pipelines the
	 * programming across the burst instead of fully programming each block (~30 ms
	 * single-block), so the sustained write keeps up with live recording. */
#define FLUSH_BATCH 32u   /* 16KB bursts = 2 whole 8KB pages per CMD25 (reverted from 16: the interleave+16 experiment caused catastrophic rec-ring overflow + flash write errors) */
	static uint8_t batchbuf[FLUSH_BATCH * EMMC_BLOCK_SIZE] __aligned(4); /* M71: DMA dest */

	(void)emmc_init();
	/* AFTER init: emmc_init() resets the clock to the slow safe value — the
	 * old code zeroed it BEFORE init, so every bit-bang phase (start-bit
	 * hunts, CRC tokens, busy polls) has been running ~4x slower than
	 * intended this whole time. Zero it here so it actually sticks. */
	g_emmc_clk_half_us = 0u;
	g_emmc_ready = emmc_is_ready() ? 1 : 0;
	{ /* CX: start the 1 ms census HERE, at boot, not at the first
	   * DTR tick. The old placement meant the census only ever ran
	   * while 328 was attached, so under Protocol A it started
	   * AFTER the corner was over and every number it produced
	   * described a monitored machine. */
	  g_w4c_on = 1;
	  k_timer_init(&g_w4c_tmr, w4c_tick, NULL);
	  k_timer_start(&g_w4c_tmr, K_MSEC(1), K_MSEC(1));
	}

	/* Enable the card's internal write cache if it has one. Read EXT_CSD (CMD8) to
	 * check CACHE_SIZE and the spec revision; if present, turn the cache on. It
	 * absorbs the record write-bursts so an overdub acks from the card's SRAM
	 * instead of stalling the bus -- without it the 4th simultaneous track
	 * overflows the rec ring. There is deliberately NO flush during play (that
	 * freezes the bus and starves playback); the card flushes in the background,
	 * and we force a single flush at power-off (see stop_and_flush) so loops are
	 * durable. eMMC is streamer-only, so this boot-time read is safe here. */
	/* The write cache absorbs each record burst so the write returns immediately
	 * instead of programming NAND on the bus and starving the playing tracks
	 * (which is what crackles). Both builds use it; the 24 kHz build pairs it with
	 * the in-spec 16 MHz bus (the overclock, not the cache, was its white-noise). */
	if (g_emmc_ready && emmc_read_ext_csd(blk)) {
		uint32_t cache_kb = (uint32_t)blk[249] | ((uint32_t)blk[250] << 8) |
				    ((uint32_t)blk[251] << 16) | ((uint32_t)blk[252] << 24);
		g_cache_kb = cache_kb;
		/* diag snapshot: WR_REL_SET, WR_REL_PARAM, SEC_FEATURE_SUPPORT,
		 * BKOPS_SUPPORT, HPI_FEATURES, OUT_OF_INTERRUPT_TIME, BKOPS_STATUS,
		 * EXT_CSD_REV, ERASE_GROUP_DEF — confirms on the REAL unit which
		 * FTL-management features (TRIM/BKOPS/HPI) the card supports. */
		g_extcsd_dump[0] = blk[167]; g_extcsd_dump[1] = blk[166];
		g_extcsd_dump[2] = blk[231]; g_extcsd_dump[3] = blk[502];
		g_extcsd_dump[4] = blk[503]; g_extcsd_dump[5] = blk[198];
		g_extcsd_dump[6] = blk[246]; g_extcsd_dump[7] = blk[192];
		g_extcsd_dump[8] = blk[175];
		{ /* S1: arm the shadow only if the card holds it + 64k margin */
		  uint32_t _sec = (uint32_t)blk[212] | ((uint32_t)blk[213] << 8) |
		                  ((uint32_t)blk[214] << 16) | ((uint32_t)blk[215] << 24);
		  if (_sec >= SHW_BASE + (uint32_t)NTRK * SHW_TRK_BLOCKS + 65536u)
			g_shw_armed = 1u; }
		if (cache_kb > 0u && blk[192] >= 6u)   /* CACHE_SIZE>0, EXT_CSD_REV>=6 (v4.5+) */
			g_cache_on = emmc_cache_enable() ? 1u : 0u;
		if (blk[503] & 0x01) {                 /* HPI: abort lever for the idle flush */
			g_hpi_on = emmc_hpi_enable() ? 1u : 0u;
			if (g_hpi_on)
				emmc_set_abort_cb(emmc_busy_abort_chk);
		}
	}

	/* Load the slot metadata (block 0). If absent/invalid, format fresh — this
	 * overwrites the old TE album index, deleting the original songs + reclaiming
	 * the space (they couldn't be played on this hardware anyway). */
	memset(&g_meta, 0, sizeof(g_meta));
	g_meta.magic = META_MAGIC;
	for (uint32_t s = 0; s < NUM_SLOTS; s++) g_meta.slot[s].speed_q16 = 65536u;
	if (g_emmc_ready && emmc_read_blocks(META_BLOCK, metabuf, META_BLOCKS)) {
		struct meta_blk *m = (struct meta_blk *)metabuf;
		if (m->magic == META_MAGIC && m->cur_slot < NUM_SLOTS) {
			memcpy(&g_meta, m, sizeof(g_meta));     /* resume saved songs */
		} else {
			/* Unknown/older index (incl. 'SE4A'/'SE8A': their track
			 * regions were sized for 800-beat takes and don't line up
			 * with the 400-beat layout) -> one-time format-fresh. */
			memset(metabuf, 0, sizeof(metabuf));
			memcpy(metabuf, &g_meta, sizeof(g_meta));
			(void)meta_write_blocks(metabuf);
			/* GX-509: clear EVERY side table, not just the one whose
			 * magic changed (W111). GRID_EXT_MAGIC 'GRD1' is UNCHANGED
			 * between 2.x and 3.0 -- confirmed present in both shipped
			 * binaries -- and block 2 is read INDEPENDENTLY just below,
			 * so a 2.7.2 card's per-song grid tempos would survive onto
			 * the songs we have just cleared. The user would get 16 empty
			 * songs that already carry tempos, and ungridded first-take
			 * DETECTION would silently never fire, because a grid already
			 * exists -- and by M43 a grid, once set, does not move.
			 * The v3 table is self-validating, so a 2.x card reads as "no
			 * data" today; but a 3.0 -> 2.x -> 3.0 round trip can leave a
			 * VALID stale table describing songs that were cleared.
			 * BUFFER SAFETY (W92): metabuf is META_BLOCKS*512 = 1024 B.
			 * Never hand a 1024 B buffer to a 3-block write -- one block
			 * at a time. */
			memset(metabuf, 0, sizeof(metabuf));
			(void)emmc_write_blocks(GRID_EXT_BLOCK, metabuf, 1u);
			for (uint32_t _gb = 0; _gb < X3_NBLK; _gb++)
				(void)emmc_write_blocks(X3_BLK + _gb, metabuf, 1u);
		}
	}
	/* M8a: grid extension (block 2). Bad tag/sum -> all zeros = no grids. */
	if (g_emmc_ready && emmc_read_blocks(GRID_EXT_BLOCK, metabuf, 1)) {
		struct grid_ext *ge = (struct grid_ext *)metabuf;
		uint16_t gsum = 0;
		for (uint32_t gi = 0; gi < NUM_SLOTS; gi++)
			gsum = (uint16_t)(gsum + ge->bpm_q8[gi]);
		if (ge->magic == GRID_EXT_MAGIC && gsum == ge->sum)
			for (uint32_t gi = 0; gi < NUM_SLOTS; gi++)
				g_grid_bpm_q8[gi] = ge->bpm_q8[gi];
	}
	g_slot = g_meta.cur_slot;
	g_mode_pref = g_meta.fixed_len ? 1u : 0u;   /* M7c: global mode preference */
	g_fixed_len = g_mode_pref;                  /* effective refined when the
	                                             * current song loads (main) */
	/* M72: pull the v3 extended table (blocks 3-5). Invalid/stale ->
	 * g_x3_ok stays 0 and reloads use the block-derived values. */
	if (g_emmc_ready && emmc_read_blocks(X3_BLK, batchbuf, X3_NBLK)) {
		memcpy(&g_x3, batchbuf, sizeof(g_x3));
		g_x3_ok = x3_valid(&g_x3) ? 1u : 0u;
		p14s_mask_from_x3(g_slot);   /* P14S: shadow gates follow the table */
	}
	if (!g_x3_ok) memset(&g_x3, 0, sizeof(g_x3));
	g_meta_loaded = 1;

	while (1) {
		{ /* M46d: identify the streamer for the read wrapper's boost */
		  if (!g_str_tid) { g_str_tid = k_current_get();
		    g_pb_orig = k_thread_priority_get(k_current_get()); }
		}
#if SP1_XFER_ENABLE
		/* Website loop transfer: scan for the connect-magic / run one command
		 * per pass. While a transfer is active the transport is paused and
		 * the streamer serves ONLY the transfer (audio is silent anyway).
		 * v1.2.3: gated on USB being up — the streamer can now run during
		 * charge-standby, before usb_audio_start(). */
		if (g_usb_up)
			xfer_service();
#endif
		if (g_xfer_mode) { k_msleep(1); continue; }

		/* Power-off cache flush: program the volatile write cache to NAND so the
		 * last take + slot index survive a power cut. Requested by stop_and_flush
		 * AFTER recording is finalized + while shutting down, so this bus-blocking
		 * flush has nothing live to starve. Done here because the streamer is the
		 * only eMMC user. */
		if (g_emmc_quiesce) {                   /* shutting down: bus parked */
			k_msleep(10);
			continue;
		}
		if (g_cache_flush_req) {
			(void)emmc_cache_flush();
			g_emmc_quiesce = 1;   /* no further eMMC traffic after the final flush */
			g_cache_flush_req = 0;
			continue;
		}

		bool work = false;
		uint32_t cpos = g_consume_pos;
		uint32_t slot = g_slot;
		{ /* #116 FIX: invalidate the shadow on a slot change HERE,
		   * unconditionally, before PASS 1 and PASS 2. The old check
		   * lived inside the S1 builder gate (TS_PLAY && !recording),
		   * while the S2 serve gate requires neither -- and serve runs
		   * first. Switch-then-record never reset at all. */
		  if (g_shw_slot != slot) {
			uint32_t _had = 0u;
			for (int _j = 0; _j < NTRK; _j++) {
				if (g_shw_wm[_j]) _had = 1u;
				g_shw_wm[_j] = 0u;
			}
			if (_had) g_shw_inv++;
			g_shw_slot = slot;
		  }
		}
		{ /* ==== DMP-466: ONE-SHOT TAKE-BLOCK DUMP (diagnostic; READS ONLY).
		   * Streams track-1 blocks as hex so the host reference decoder
		   * can rule on the actual card bytes. Runs only when: capture
		   * connected (armed by main's DTR tick), nothing recording or
		   * draining, playback stopped (consume frozen), and bounce idle
		   * -- bnc_acc is borrowed as the 1-block read buffer under a
		   * RUNTIME liveness gate (rule 9; same thread as bounce, so no
		   * mid-round writer is possible). */
		  if (g_dmp_arm && g_dmp_state < 2u && g_bnc_req < 0 && !g_bnc_active) {
			bool _di = true;
			for (int _dk = 0; _dk < NTRK; _dk++)
				if (trk[_dk].state == TS_REC || trk[_dk].state == TS_DONE)
					_di = false;
			static uint32_t _dcp;
			if (g_consume_pos != _dcp) { _dcp = g_consume_pos; _di = false; }
			if (_di) {
				uint8_t *_db = (uint8_t *)bnc_acc;
				if (!g_dmp_state) {
					g_dmp_n = trk[0].len_blocks ? trk[0].len_blocks : 344u;
					if (g_dmp_n > 344u) g_dmp_n = 344u;
					printk("DMP,BEGIN,slot=%u,cid=%u,len=%u,base=%u\n",
					       (unsigned)g_slot,
					       (unsigned)((g_slot < NUM_SLOTS) ? g_x3.t[g_slot][0].codec_id : 255u),
					       (unsigned)g_dmp_n, (unsigned)trk_blk(g_slot, 0u));
					g_dmp_state = 1u; g_dmp_blk = 0u;
				}
				for (uint32_t _bi = 0u; _bi < 12u && g_dmp_blk < g_dmp_n; _bi++, g_dmp_blk++) {
					if (!emmc_read_blocks_fast(trk_blk(g_slot, 0u) + g_dmp_blk, _db, 1u)) {
						printk("DMP,RDERR,%u\n", (unsigned)g_dmp_blk);
						continue;
					}
					for (uint32_t _li = 0u; _li < 8u; _li++) {
						static const char _hx[] = "0123456789abcdef";
						char _ob[132];
						for (uint32_t _bb = 0u; _bb < 64u; _bb++) {
							uint8_t _v = _db[_li * 64u + _bb];
							_ob[_bb * 2u]      = _hx[_v >> 4];
							_ob[_bb * 2u + 1u] = _hx[_v & 0xFu];
						}
						_ob[128] = 0;
						printk("DMP,%u,%u,%s\n", (unsigned)g_dmp_blk, (unsigned)_li, _ob);
					}
					k_msleep(8);
				}
				if (g_dmp_blk >= g_dmp_n) {
					printk("DMP,END,%u\n", (unsigned)g_dmp_n);
					g_dmp_state = 2u;
				}
			}
		  }
		}
		{ /* ==== S3: IDLE-TIME SEQUENTIAL SHADOW BUILD (one bite/round).
		   * Completes coverage without lap alignment (campaign #56).
		   * Gated: armed, nothing recording, every playing cushion
		   * comfortable. batchbuf layout: [0,4K) A7 in, [4K,6K) decode
		   * ring (512 fr), [8K,16K) staging. Stateless (from wm). */
		  if (g_shw_armed && g_meta_loaded && k_uptime_get_32() > 5000u) {
			static uint8_t s3_rr;
			bool _ok3 = true;
			/* M99: ovr (rec-ring lapping) is what CORRUPTS TAKES, and it is
			 * still ~2M. So shadow work during a take is allowed only while
			 * the record ring is comfortably drained -- under a quarter
			 * full. The flush always wins; the builder only uses slack. */
			if (g_rec_track >= 0) {
				uint32_t _fill99 = trk[g_rec_track].r_w - trk[g_rec_track].r_r;
				if (_fill99 >= (RRING_SAMPLES / 2u)) _ok3 = false; /* CD-463: 1/4 of 2x-engine capacity */
			}
			for (int _j = 0; _j < NTRK; _j++) {
				uint8_t _sj = trk[_j].state;
				/* M99: the record target is EXPECTED to be TS_REC now; it
				 * must not veto building the OTHER tracks' shadows. Any
				 * other non-idle state (TS_ARMED, TS_DONE) still does. */
				if (_j != g_rec_track && _sj != TS_EMPTY && _sj != TS_PLAY)
					_ok3 = false;
				if ((_sj == TS_PLAY || head_active(_j)) &&
				    (int32_t)(trk[_j].p_w - cpos) <
				    (int32_t)PLAY_CRIT_SAMPLES)  /* r2: 1x -- 2x sat above the steady cushion and starved the builder (wm 38% at 12 min, campaign #57) */
					_ok3 = false;
			}
			if (_ok3) {
				for (int _t3 = 0; _t3 < NTRK; _t3++) {
					int _i3 = (s3_rr + _t3) & 3;
					/* M99: never build the track being recorded -- its shadow is
					 * invalidated on TS_REC and the take is still growing. */
					if (_i3 == g_rec_track) continue;
					/* P14S: raw tracks need no shadow -- and building one
					 * would A7-decode raw blocks into garbage. */
					if (g_p14s_mask & (1u << _i3)) continue;
					struct looptrk *_tr = &trk[_i3];
					uint32_t _len = _tr->len_samps;
					uint32_t _wmf = g_shw_wm[_i3];
					if (!_len || _wmf + 250u > _len) continue;
					uint32_t _ab = _wmf / SAMP_PER_BLK;
					uint32_t _off = _wmf - _ab * SAMP_PER_BLK;
					uint32_t _gb3 = _tr->content_blocks;
					uint32_t _k = 8u;
					if (_ab >= _gb3) continue;
					if (_ab + _k > _gb3) _k = _gb3 - _ab;
					if (!emmc_read_blocks_fast(trk_blk(slot, (uint32_t)_i3) + _ab,
					                           batchbuf, _k)) break;
					int16_t *_dr = (int16_t *)(batchbuf + 4096u);
					uint8_t *_sb3 = (uint8_t *)(batchbuf + 8192u);
					/* S8Q gather: 250 stereo frames = 1000 B in the free
					 * [6K,8K) scratch (_dr's 511-mask ring tops out at 6K).
					 * Needed because a 15-16 frame sub-block can straddle
					 * an A7 block boundary and the exponent search needs
					 * the whole sub-block before it can quantise. */
					int16_t *_g16 = (int16_t *)(batchbuf + 6144u);
					uint32_t _have = 0, _m3 = 0, _src = _off, _bi3 = 0;
					a7_decode_block_ring(batchbuf, _dr, 511u, 0u);
					while (_m3 < 16u) {
						while (_have < 250u) {
							if (_src >= SAMP_PER_BLK) {
								_bi3++; _src = 0;
								if (_bi3 >= _k) break;
								a7_decode_block_ring(batchbuf + _bi3 * EMMC_BLOCK_SIZE,
								                     _dr, 511u, 0u);
							}
							/* S8Q: BOTH channels. The mono discard guard is
							 * DELETED -- it protected a MONO buffer from
							 * stereo data, and the buffer is stereo now. */
							_g16[_have * 2u]      = _dr[_src * 2u];
							_g16[_have * 2u + 1u] = _dr[_src * 2u + 1u];
							_have++; _src++;
						}
						if (_have < 250u) break;
						s8q_enc_sector(_g16, 0xFFFFFFFFu, 0u,
						               (uint16_t)(_wmf / 250u + _m3),
						               _sb3 + _m3 * 512u);
						_m3++; _have = 0;
					}
					if (_m3) {
						bool aw3_burst_start(uint32_t, const uint8_t *, uint32_t);
						bool aw3_burst_wait(void);
						if (aw3_burst_start(SHW_TRK((uint32_t)_i3) + _wmf / 250u,
						                    (const uint8_t *)_sb3, _m3) &&
						    aw3_burst_wait()) {
							g_shw_wm[_i3] = _wmf + _m3 * 250u;
							g_shw_blk += _m3;
						}
					}
					s3_rr = (uint8_t)(_i3 + 1);
					break;
				}
			}
		  }
		}

		if (g_meta_save_req) {                       /* persist songs + BPMs */
			g_meta_save_req = 0;
			if (g_emmc_ready) {
				memset(metabuf, 0, sizeof(metabuf));
				memcpy(metabuf, &g_meta, sizeof(g_meta));
				(void)meta_write_blocks(metabuf);
				work = true;
				/* FX3-537: the M72 refresh is GONE. It re-authored this
				 * slot's rows from live trk[], and a song jump could
				 * slip between g_slot flipping (gesture thread) and the
				 * trk[] restore (audio thread) -- this pass then stamped
				 * the DESTINATION song's rows with the OLD song's state
				 * (marc's no-recording corruption). The cross-check that
				 * once made write order irrelevant never covered
				 * codec_id (522), which has no g_meta fallback. Rows are
				 * now authored ONLY at their events: boot load, take
				 * promotion (FX2), page toggle (FX2), delete (below).
				 * This service just writes RAM to the card. */
				if (slot < NUM_SLOTS) {
					g_x3.magic = X3_MAGIC; g_x3.ver = X3_VER;
					g_x3.sum = x3_sum(&g_x3);
					memset(batchbuf, 0, X3_NBLK * EMMC_BLOCK_SIZE);
					memcpy(batchbuf, &g_x3, sizeof(g_x3));
					if (emmc_write_blocks(X3_BLK, batchbuf, X3_NBLK))
						g_x3_ok = 1u;
				}
			}
		}
		if (g_grid_save_req) {                       /* persist grids (block 2) */
			g_grid_save_req = 0;
			if (g_emmc_ready) {
				memset(metabuf, 0, 512);
				struct grid_ext *ge = (struct grid_ext *)metabuf;
				ge->magic = GRID_EXT_MAGIC;
				uint16_t gsum = 0;
				for (uint32_t gi = 0; gi < NUM_SLOTS; gi++) {
					ge->bpm_q8[gi] = g_grid_bpm_q8[gi];
					gsum = (uint16_t)(gsum + ge->bpm_q8[gi]);
				}
				ge->sum = gsum;
				(void)emmc_write_blocks(GRID_EXT_BLOCK, metabuf, 1);
				work = true;
			}
		}

		/* PASS 1 — WRITES FIRST. Flushing the rec ring always outranks play
		 * read-ahead: a rec-ring overflow corrupts the take permanently, while a
		 * play-ring underrun is only a brief, recoverable dropout. */
		for (int i = 0; i < NTRK; i++) {
			struct looptrk *t = &trk[i];
			uint8_t st = t->state;

			if (st == TS_REC) g_shw_wm[i] = 0u;   /* S1: take invalidates shadow */
			if (st == TS_REC || st == TS_DONE ||
			    (t->r_w - t->r_r) >= TSPB(t)) {
				/* M89: the wrap can flip a finished take to TS_PLAY
				 * before its tail is flushed (measured: 8,781-29,118
				 * frames stranded, frozen between takes -- every take
				 * stored missing its last stretch). Serve ANY backlog:
				 * the frames are real audio with fixed destinations;
				 * a late flush self-heals on the next loop pass. */
				while ((t->r_w - t->r_r) >= TSPB(t)) {
					uint32_t fm = t->flush_mod ? t->flush_mod : MAX_LOOP_BLOCKS;
					/* batch as many contiguous blocks as are ready, up to the
					 * buffer size and the loop-wrap boundary, into one CMD25 write */
					uint32_t navail = (t->r_w - t->r_r) / TSPB(t);
					uint32_t n = navail < FLUSH_BATCH ? navail : FLUSH_BATCH;
					uint32_t to_wrap = fm - (t->flush_blk % fm);
					if (n > to_wrap) n = to_wrap;
					uint32_t blkno = trk_blk(slot, (uint32_t)i) +
							 (t->flush_blk % fm);
					/* PAGE RULE: never let a burst straddle an 8KB (16-block)
					 * page — straddling forces the card into a slow read-
					 * modify-write; page-aligned bursts are fast. Misaligned
					 * start (overdub begun mid-loop):
					 * one short burst up to the boundary, aligned after.
					 * CRITICAL: while recording, WAIT for a full page before
					 * writing — draining the ring in dribbles makes every
					 * write a partial page = RMW = the slow path (this is
					 * what made the first 24 kHz build unable to record).
					 * Partial writes only at: overdub start, loop wrap, and
					 * the final tail after the take ends.
					 * Three cases below: (1) misaligned start -> trim to the next
					 * 8KB (16-block) page boundary; (2) >=1 whole page ready ->
					 * write whole pages only; (3) recording mid-loop with <1 page
					 * ready -> wait (the loop-wrap tail is exempt via n<to_wrap). */
					uint32_t mis = blkno % 16u;
					if (mis) {
						uint32_t to_page = 16u - mis;
						if (n > to_page) n = to_page;
					} else if (n >= 16u) {
						/* SINGLE whole pages deliberately: a 32-block
						 * double-burst experiment saved command overhead
						 * but each burst held the bus ~9 ms uninterrupted
						 * — at high tape speed the playing tracks can't
						 * ride out blackouts that long (hardware-measured:
						 * rec ring peaked 78%, a track fell 209 ms behind,
						 * MORE starves). Frequent small write bursts keep
						 * read latency bounded; total overhead matters
						 * less than its distribution here. */
						n &= ~15u;        /* whole pages only */
						if (n > 16u) n = 16u; /* CD-463: keep 460's burst size; drain ~800 blk/s vs 257 demand */
					} else if (t->state == TS_REC && n < to_wrap) {
						break;            /* let a full page accumulate */
					}
					/* ENCODE: rec ring (int16, wraps at RRING_MASK, r_r is
					 * block-aligned) -> packed flash bytes for n blocks. PCM is
					 * memcpy-equivalent; ULAW/ADPCM compress 2x/4x so this CMD25
					 * moves half/quarter the bytes the card must program. */
					if (0 /* CD-463: W3-r4 pair path FROZEN — it becomes reachable for
					       * the first time with the doubled ring; re-enable DELIBERATELY
					       * in its own build (one variable per build). */
					    && n == 16u && t->state == TS_REC &&
					    (blkno % 16u) == 0u && navail >= 32u &&
					    to_wrap >= 32u) {
						/* W3-r4 PIPELINE: pack the NEXT page while this one
						 * is in the card. Encode wall hides inside program
						 * time (the async port's overlap). Pair-granular
						 * play-crit break below; failures leave data in the
						 * ring for the single-burst path's streak logic. */
						bool aw3_burst_start(uint32_t, const uint8_t *, uint32_t);
						bool aw3_burst_wait(void);
						uint32_t _tw4 = DWT->CYCCNT;
						g_w4_pk++; g_w4_pb += 16u;
						takes_pack_blocks(t, g_rring, RRING_MASK, (t->r_r >> 1) & RRING_MASK,
						           batchbuf, 16u);
						bool _ok1 = aw3_burst_start(blkno, batchbuf, 16u);
						g_w4_pk++; g_w4_pb += 16u;
						takes_pack_blocks(t, g_rring, RRING_MASK,
						           ((t->r_r >> 1) + 16u * (t->p16m ? 248u : 140u)) & RRING_MASK,
						           batchbuf + 16u * EMMC_BLOCK_SIZE, 16u);
						if (_ok1) _ok1 = aw3_burst_wait();
						if (_ok1) {
							t->r_r += 16u * TSPB(t);
							t->flush_blk += 16u;
							bool _ok2 = aw3_burst_start(blkno + 16u,
							            batchbuf + 16u * EMMC_BLOCK_SIZE, 16u);
							if (_ok2) _ok2 = aw3_burst_wait();
							if (_ok2) {
								t->r_r += 16u * TSPB(t);
								t->flush_blk += 16u;
							}
						}
						{ uint32_t _dcx73 = (uint32_t)(DWT->CYCCNT - _tw4); g_t_wr += _dcx73; if (M73_CX_NOW()) { g_t_wr_cx += _dcx73; g_t_wr_cxn++; } if (M73_CY_NOW()) { g_t_wr_cy += _dcx73; g_t_wr_cyn++; } }
						work = true;
						if ((t->r_w - t->r_r) <
						    RRING_SAMPLES) {   /* CD-463: half of 2x-engine capacity */
							bool _pc4 = false;
							for (int j = 0; j < NTRK; j++)
								if ((trk[j].state == TS_PLAY ||
								     head_active(j)) &&
								    (int32_t)(trk[j].p_w - g_consume_pos) <
								    (int32_t)PLAY_CRIT_SAMPLES)
									_pc4 = true;
							if (_pc4)
								break;
						}
						continue;
					}
					g_w4_pk++; g_w4_pb += n;   /* W4P */
					takes_pack_blocks(t, g_rring, RRING_MASK, (t->r_r >> 1) & RRING_MASK,
					           batchbuf, n);
					static uint32_t wfail_start;   /* 0 = no failure streak */
					static uint32_t wfail_key;     /* streak identity (track|flush pos) */
					static uint8_t  wfail_ready1;  /* card seen READY once this streak */
					uint32_t _wkey = ((uint32_t)i << 28) ^ t->flush_blk;
					uint32_t _tw = DWT->CYCCNT;
					bool _wok = emmc_write_blocks(blkno, batchbuf, n);
					{ uint32_t _dcx73 = (uint32_t)(DWT->CYCCNT - _tw); g_t_wr += _dcx73; if (M73_CX_NOW()) { g_t_wr_cx += _dcx73; g_t_wr_cxn++; } if (M73_CY_NOW()) { g_t_wr_cy += _dcx73; g_t_wr_cyn++; } }
					if (!_wok) {
						/* write failed (bus CRC or busy timeout): data is
						 * still in the ring — retry next pass. Give up and
						 * advance anyway (storing a glitch) ONLY after the
						 * card has been failing >400 ms of WALL TIME and
						 * reports READY_FOR_DATA via CMD13 (recovered yet
						 * genuinely rejecting). The old 8-fast-fails counter
						 * elapsed in <50 ms mid-stall and stored a glitch
						 * that REPLAYED at the same spot every loop pass. */
						uint32_t _now = k_uptime_get_32();
						/* STREAK IDENTITY: a streak abandoned mid-take
						 * (e.g. the track was deleted while flushing)
						 * must not leak its stale timestamp into the
						 * NEXT take — that made a single routine CRC
						 * blip give up instantly and silently drop a
						 * whole burst. */
						if (!wfail_start || wfail_key != _wkey) {
							wfail_start = _now | 1u;
							wfail_key = _wkey;
							wfail_ready1 = 0;
						}
						bool _giveup = false;
						if ((_now - wfail_start) > 400u) {
							uint8_t _r1[6];
							if (emmc_cmd13(_r1) && (_r1[3] & 0x01)) {
								/* READY often means the stall just
								 * ended and THIS attempt was its tail
								 * casualty — give the card ONE clean
								 * retry before declaring the data
								 * rejected for good. */
								if (wfail_ready1)
									_giveup = true;
								else
									wfail_ready1 = 1;
							}
						}
						if (!_giveup) {
							/* BACKOFF: the card is mid-stall; an
							 * immediate CMD25 retry is a zero-yield
							 * spin that starves MIDI/main (the WDT
							 * feeder). 2 ms costs nothing here. */
							k_msleep(2);
							work = true;
							break;
						}
						g_stored_glitch_cnt++;  /* audible as a REPEATING artifact */
					}
					wfail_start = 0;
					wfail_ready1 = 0;
					t->r_r += n * TSPB(t);
					t->flush_blk += n;
					work = true;
					/* FB-529 (W137): PROACTIVE page pacing at high tape
					 * speed. The tail flush's back-to-back 16-block bursts
					 * monopolize the bus exactly when the play rings drain
					 * 1.5x faster (STV pf = 148-259 at the corner, all with
					 * g_done_pending). One page per streamer pass, then
					 * PASS 2 serves; full writes-first priority returns the
					 * moment the backlog crosses half capacity, so data
					 * safety is unchanged (the ring holds ~341 ms). */
					if (g_cur_speed_q16 >= CX_SPEED_MIN &&
					    (t->r_w - t->r_r) < RRING_SAMPLES)
						break;
					/* POST-STALL DRAIN ORDER: a big rec backlog must not
					 * starve the playing rings at their emptiest moment.
					 * After each burst, if any playing ring is inside its
					 * critical margin and the rec ring is NOT at the 7/8
					 * overflow emergency, break to PASS 2 to feed the
					 * emptiest ring one chunk, then resume flushing here.
					 * Burst-granular alternation only (one fully-terminated
					 * CMD25, then reads) — NOT the sub-page interleave that
					 * broke writes in an earlier experiment. */
					/* W3-r2: the polite play-first break now yields only
					 * below HALF a ring of backlog. The old 7/8 line left
					 * 43 ms of emergency headroom -- thinner than one
					 * write-cache stall -- and takes lapped inside it
					 * (W3-r1, campaign S43). Above half a ring the flush
					 * outranks play, as this pass's own preamble says. */
					if ((t->r_w - t->r_r) <
					    RRING_SAMPLES) {   /* CD-463: half of 2x-engine capacity */
						bool _pcrit = false;
						for (int j = 0; j < NTRK; j++)
							if ((trk[j].state == TS_PLAY ||
							     head_active(j)) &&
							    (int32_t)(trk[j].p_w - g_consume_pos) <
							    (int32_t)PLAY_CRIT_SAMPLES)
								_pcrit = true;
						if (_pcrit)
							break;  /* rec ring holds; feed play first */
					}
				}
				/* Promotion re-reads the LIVE state (not the pass-start snapshot)
				 * so an engine transition during the flush can't be overwritten.
				 * Order matters: request the meta save BEFORE publishing TS_PLAY,
				 * or stop_and_flush() (power-off/DFU) can observe "idle" between
				 * the two stores and sleep with the new recording unsaved. */
				if (t->state == TS_DONE && (t->r_w - t->r_r) < TSPB(t)) {
					g_done_pending = 0;   /* M20: ring free again */
					/* Start playback BLOCK-ALIGNED at the live playhead. p_w must be a
					 * multiple of SAMP_PER_BLK or the streamer writes each eMMC block at
					 * a misaligned ring offset and the track plays ~16 ms out of sync. */
					if (slot < NUM_SLOTS) {
						g_meta.slot[slot].present[i]   = 1;
						g_meta.slot[slot].trk_len[i]   = t->len_blocks;  /* SEGMENT: per-track length */
						g_meta.slot[slot].trk_start[i] = t->start_blk;   /* + phase anchor */
						g_meta.trk_content[slot][i]    = t->content_blocks; /* silence-pad boundary */
						{	/* FX2-536: the x3 entry, stamped IN RAM at
							 * promotion. A deferred stamp raced song
							 * switches: the new take's codec_id was
							 * never written for THIS slot, and the
							 * stale id mis-strided the track-driven
							 * reader on return (the aux-cable sound). */
							struct x3_trk *_xe = &g_x3.t[slot][i];
							_xe->start_samps    = t->start_samps;
							_xe->len_samps      = t->len_samps;
							_xe->content_blocks = t->content_blocks;
							_xe->codec_id       = t->p16m ? X3_CODEC_P16M
							                              : X3_CODEC_P14S;
							_xe->flags          = (uint8_t)(g_cap_stereo ? 1u : 0u);
							_xe->pan            = 128u;
							_xe->rsv            = (uint8_t)(0x80u |
							                      (t->p16m_next & 1u));
						}
					}
					g_meta_save_req = 1;             /* persist the new recording */
#if SP1_CODEC == SP1_CODEC_PCM
					/* TRUNCATED-STOP SEAM: the played region ends mid-audio
					 * at the WRAP — fade its last ~2.7 ms down on flash so
					 * the loop seam doesn't click. M22-B FIX (marc's crack,
					 * 3-for-3 after the first take): the wrap is now the
					 * SAMPLE length, up to 128 samples past the block
					 * boundary this fade used to target — the fade landed
					 * just BEFORE the real seam and the splice itself played
					 * unfaded, a loud crack on every lap. Fade the 128
					 * samples ending exactly at len_samps (spans up to two
					 * blocks); block-exact tracks keep the old math via the
					 * same expressions (len_samps = blocks*256). */
					if (t->len_samps && t->len_samps > 256u &&
					    (uint64_t)t->content_blocks * TSPB(t)
					        > t->len_samps) {
						uint32_t _E  = t->len_samps;
						uint32_t _s0 = _E - 128u;
						uint32_t _b0 = _s0 / TSPB(t);
						uint32_t _b1 = (_E - 1u) / TSPB(t);
						uint32_t _nb = _b1 - _b0 + 1u;   /* 1 or 2 */
						uint32_t _bl = trk_blk(slot, (uint32_t)i) + _b0;
						if (emmc_read_blocks(_bl, batchbuf, _nb)) {
							int16_t *_sm = (int16_t *)batchbuf;
							uint32_t _base = _b0 * TSPB(t);
							for (uint32_t _k = 0; _k < 128u; _k++) {
								uint32_t _ix = (_s0 - _base) + _k;
								_sm[_ix] = (int16_t)(((int32_t)_sm[_ix] *
										      (int32_t)(127u - _k)) >> 7);
							}
							if (!emmc_write_blocks(_bl, batchbuf, _nb))
								(void)emmc_write_blocks(_bl, batchbuf, _nb);
						}
					} else if (t->content_blocks > t->len_blocks &&
						   t->len_blocks) {
						uint32_t _bl = trk_blk(slot, (uint32_t)i) +
							       t->len_blocks - 1u;
						if (emmc_read_blocks(_bl, batchbuf, 1)) {
							int16_t *_sm = (int16_t *)batchbuf;
							for (int _k = 0; _k < 128; _k++) {
								int _ix = TSPB(t) - 128 + _k;
								_sm[_ix] = (int16_t)(((int32_t)_sm[_ix] *
										      (127 - _k)) >> 7);
							}
							if (!emmc_write_blocks(_bl, batchbuf, 1))
								(void)emmc_write_blocks(_bl, batchbuf, 1);
						}
					}
					/* LOOP-SEAM DECLICK (write side): ramp the take's first
					 * ~1.3 ms in, ONCE, on flash. Every lap of the loop plays
					 * last-sample -> first-sample; with a hard start that seam
					 * clicks ("loop in/out transient" in community feedback).
					 * The stop side is faded live by the recorder (rec_fade),
					 * so with both ends tapered the seam is silent-to-silent.
					 * 64 samples barely soften a real attack transient. PCM
					 * only: in-place sample math on packed flash bytes. */
					{
						uint32_t _b0 = trk_blk(slot, (uint32_t)i);
						if (emmc_read_blocks(_b0, batchbuf, 1)) {
							int16_t *_sm = (int16_t *)batchbuf;
							for (int _k = 0; _k < 64; _k++)
								_sm[_k] = (int16_t)(((int32_t)_sm[_k] * _k) >> 6);
							if (!emmc_write_blocks(_b0, batchbuf, 1))
								(void)emmc_write_blocks(_b0, batchbuf, 1);
						}
					}
#endif
					/* PRIME the play ring before publishing TS_PLAY: read ~half-ring of
					 * the loop into pring so a freshly-promoted track starts with read-
					 * ahead cushion instead of avail=0. Empty promotion made the last-
					 * recorded track starve -> silent until half-refill -> resume at the
					 * live playhead (a forward time-skip) = the 'last track clock wrong'.
					 * Runs on the streamer thread while the ring is still private (state
					 * != PLAY) so it can't race the audio read; the other rings hold
					 * ~341 ms, so this one-time ~20 ms prime burst can't starve them. */
					/* Block-align the prime start to a SAMP_PER_BLK boundary.
					 * MUST be DIVISION-based (not & ~(SAMP_PER_BLK-1)): for ADPCM
					 * SAMP_PER_BLK=1016 is NOT a power of two, so the bitmask
					 * would corrupt the address. Division is exact for every codec
					 * (256/512/1016) and identical to the mask for power-of-two. */
					uint32_t _pw_snap = t->p_w;   /* detect restart/reset mid-prime */
					uint32_t _pw   = (g_consume_pos / TSPB(t)) * TSPB(t);
					uint32_t _gb   = t->len_blocks ? t->len_blocks
					               : (TLOOPB(i) ? TLOOPB(i) : 1u);
					uint32_t _cdiv = g_chop_div, _coff = g_chop_off;
					uint32_t _cyc, _win, _wb, _wper;
					if (g_fixed_len && TLOOPB(i) && _gb >= TLOOPB(i) &&
					    (_gb % TLOOPB(i)) == 0u) {
						_wper = TLOOPB(i);
						_win = _wper / _cdiv; if (_win == 0u) _win = 1u;
						_wb = (_coff * _wper) / _cdiv;
						if (_wb + _win > _wper) _wb = _wper - _win;
						_cyc = (_gb / _wper) * _win;
					} else {
						_wper = _gb;
						_win = _gb / _cdiv; if (_win == 0u) _win = 1u;
						_wb = (_coff * _gb) / _cdiv;
						if (_wb + _win > _gb) _wb = _gb - _win;
						_cyc = _win;
					}
					if (g_win_free) {   /* M16: prime from the free window */
						uint32_t _ws = g_win_s8, _we = g_win_e8;
						if (_we < _ws) { uint32_t _t = _ws; _ws = _we; _we = _t; }
						_win = ((_we - _ws + 1u) * _wper) >> 8;
						if (_win == 0u) _win = 1u;
						_wb = (_ws * _wper) >> 8;
						if (_wb + _win > _wper) _wb = _wper - _win;
						_cyc = (_gb / _wper) * _win;
					}
					uint32_t _want = (RING_SAMPLES / 2u) + 16u * TSPB(t);
					if (_want > RING_SAMPLES) _want = RING_SAMPLES - TSPB(t);
					if (g_win_rev)
						_want = 0;   /* M16: reversed window — skip the
						              * forward prime; the starve fade-in
						              * covers the first fill (heads rule) */
#if SP1_CODEC == SP1_CODEC_PCM
					/* M22-B PLAIN PATH: no chop, no free window, not a
					 * head — the loop wraps at its SAMPLE length. The
					 * block machinery below still chooses what to read;
					 * this path only decides how much of the final
					 * block belongs to the lap. */
					bool _plain = (_cdiv == 1u && !g_win_free &&
						       !g_win_rev &&
						       !(heads_engaged() && g_head_rev[i]) &&   /* M50a: a reversed heads SOURCE must not take the express lane */
						       !head_active(i) && t->len_samps &&
						       _win == _wper && _wper == _gb);
#else
					bool _plain = false;
#endif
					for (uint32_t _got = 0; _got < _want; ) {
#if SP1_CODEC == SP1_CODEC_PCM
						if (_plain) {
							uint32_t _Ls  = t->len_samps;
							uint32_t _lp  = ((_pw % _Ls) + _Ls -
							              (t->start_samps % _Ls)) % _Ls;
							uint32_t _off = _lp % TSPB(t);
							uint32_t _lb2 = _lp / TSPB(t);
							uint32_t _n2  = 32u;
							{  /* M63b-r2: the prime loop may run MORE THAN ONCE
							    * when blocks/iteration < _want (true at 280
							    * frames/block, false at 256) — without a
							    * CUMULATIVE room clip the second pass wraps the
							    * ring and overwrites the first. Same clip PASS2
							    * has always had. */
							   int32_t _rm = (int32_t)(RING_SAMPLES - TSPB(t))
							               - (int32_t)_got;
							   uint32_t _rb = _rm > 0 ? (uint32_t)_rm / TSPB(t) : 0u;
							   if (_n2 > _rb) { _n2 = _rb; g_prime_ovf++; }
							   if (!_n2) break;
							}
							{	/* clip to the lap end (whole blocks;
								 * the decode below trims the tail) */
								uint32_t _lapb = ((_Ls - 1u) / TSPB(t)) + 1u;
								if (_lb2 + _n2 > _lapb) _n2 = _lapb - _lb2;
							}
							uint32_t _ct = t->content_blocks ? t->content_blocks
							                                 : ((_Ls - 1u) / TSPB(t)) + 1u;
							bool _ps = (_lb2 >= _ct);
							if (!_ps && _lb2 + _n2 > _ct) _n2 = _ct - _lb2;
							if (!_n2) _n2 = 1u, _ps = true;
							if (_ps) {
								memset(batchbuf, 0, (size_t)_n2 * EMMC_BLOCK_SIZE);
							} else if (!emmc_read_blocks_fast(trk_blk(slot, (uint32_t)i) + _lb2, batchbuf, _n2)) { /* M71 */
								break;
							}
							uint32_t _ds = _n2 * TSPB(t) - _off;
							if (_ds > _Ls - _lp) _ds = _Ls - _lp;
							p14s_unpack_part(t->pring, RING_MASK,
									  _pw & RING_MASK,
									  batchbuf, _off, _ds, i);
							_pw  += _ds;
							_got += _ds;
							continue;
						}
#endif
						uint32_t _pwb = _pw / TSPB(t);
						uint32_t _c   = ((_pwb % _cyc) + _cyc -
								 (t->start_blk % _cyc)) % _cyc;
						uint32_t _lb  = (_c / _win) * _wper + _wb + (_c % _win);
						uint32_t _n   = 32u;
						if (_n > (RING_SAMPLES / TSPB(t)) - 1u) _n = (RING_SAMPLES / TSPB(t)) - 1u;
						{  /* M63b-r2: cumulative room clip (see the plain path) */
						   int32_t _rm = (int32_t)(RING_SAMPLES - TSPB(t))
						               - (int32_t)_got;
						   uint32_t _rb = _rm > 0 ? (uint32_t)_rm / TSPB(t) : 0u;
						   if (_n > _rb) { _n = _rb; g_prime_ovf++; }
						   if (!_n) break;
						}
						{
							uint32_t _we = (_c / _win) * _wper + _wb + _win;
							if (_lb + _n > _we) _n = _we - _lb;
						}
						/* SILENCE PAD (see PASS 2): [content, _gb) is synthesised
						 * zeros, never read from flash. */
						uint32_t _content = t->content_blocks ? t->content_blocks : _gb;
						bool _psil = (_lb >= _content);
						if (!_psil && _lb + _n > _content) _n = _content - _lb;
						if (_psil) {
							memset(batchbuf, 0, (size_t)_n * EMMC_BLOCK_SIZE);
						} else if (!emmc_read_blocks_fast(trk_blk(slot, (uint32_t)i) + _lb, batchbuf, _n)) { /* M71 */
							break;
						}
						/* DECODE the prime burst (_n blocks) into the play ring. */
						uint32_t _ntot = _n * TSPB(t);
						p14s_unpack(t->pring, RING_MASK, _pw & RING_MASK,
						             batchbuf, _n, i);
						_pw  += _ntot;
						_got += _ntot;
					}
					if (t->p_w == _pw_snap)
						t->p_w = _pw;   /* publish: ring now has ~170 ms cushion */
					/* else a restart/song-switch reset p_w mid-prime: keep the
					 * reset value (int16 ring zeros = silence); PASS 2 refills
					 * from the new playhead. */
					t->state = TS_PLAY;    /* publish AFTER priming -> no entry starve */
					work = true;
				}
			}
		}

		/* PASS 2 — play read-ahead, only after all pending writes are flushed.
		 * Skip refills entirely while a big rec backlog exists so the recorder
		 * always wins the bus (the play rings hold ~1.2 s and can coast). */
		/* PASS 2 — ONE SWEEP PER PASS, ROTATING START, ONE CHUNK PER TRACK.
		 * Every priority heuristic tried here (emptiest-first, audible-first
		 * + starved-last, mid-round yields on rec backlog or read failure)
		 * produced the same measured pathology from a different corner: the
		 * track that sorted LAST got locked out entirely whenever the round
		 * kept terminating early, and one track would sit at ZERO delivered
		 * blocks for whole takes while its siblings stayed fat. Demand is
		 * ~750 blk/s of a ~1300 blk/s bus — there is no capacity problem,
		 * only fairness. So: serve every playing track AT MOST one chunk
		 * per sweep, starting from a rotating index so early-abort cost is
		 * shared; PASS 1 (writes) runs between sweeps EVERY pass, i.e. at
		 * least once per ~4 chunks (~15 ms) BY CONSTRUCTION, which bounds
		 * the rec backlog far below danger without any mid-sweep yield.
		 * Only the true 7/8 rec-ring emergency may abort a sweep. */
		{
			/* ROUNDS: repeat the fair sweep until every ring is topped up —
			 * one pass can deliver MANY chunks (amortizing the pass's fixed
			 * cost, which matters because the audio thread owns most of the
			 * CPU: one-chunk-per-pass measured out at only ~18 passes/s,
			 * pinning refill throughput to exactly consumption with zero
			 * surplus to rebuild margins). Fairness is per ROUND, so no
			 * track can be locked out; writes stay bounded because a round
			 * breaks out the moment a whole write page is waiting. */
			/* M71r4 SPRINT: the async benches earned 1,689-3,024 blk/s at
			 * prio 1; at PREEMPT(5) the storm load (~71% above us) parks
			 * this loop between arms (r2/r3 measured). Boost the WHOLE
			 * rounds loop while the audio thread says a ring is low; the
			 * 64-pass 0.5 ms breather below still protects main/WDT. */
			/* M63b-r4 DUTY CYCLE (M46d semantics restored): main runs at
			 * PREEMPT(1) too and there is no timeslicing, so an
			 * unbounded boost starves buttons/LEDs/the WDT feed. Sprint
			 * at most SPRINT_ON_MS, then hand the level back for
			 * SPRINT_OFF_MS. */
			static int64_t _spr_t0;
			int _m71spr = 0;
			if (g_emmc_sprint) {
				_m71spr = 1; _spr_t0 = k_uptime_get();
				k_thread_priority_set(k_current_get(), K_PRIO_PREEMPT(1));
			}
			static uint32_t rr;
			bool more = true;
			while (more && g_slot == slot) {
				more = false;
			rr = (rr + 1u) & 3u; g_m71_rd++;   /* M71r2 rounds/s */
			if (!_m71spr && g_emmc_sprint) {   /* went low mid-loop */
				_m71spr = 1; _spr_t0 = k_uptime_get();
				k_thread_priority_set(k_current_get(), K_PRIO_PREEMPT(1));
			} else if (_m71spr &&
			           k_uptime_get() - _spr_t0 >= 150) {
				/* M63b-r4: 150 ms sprinted -> give main the level back
				 * for 15 ms, then resume if still low (M46d shape). */
				k_thread_priority_set(k_current_get(), K_PRIO_PREEMPT(5));
				_m71spr = 0;
				k_msleep(15);
				if (g_emmc_sprint) {
					_m71spr = 1; _spr_t0 = k_uptime_get();
					k_thread_priority_set(k_current_get(),
					                      K_PRIO_PREEMPT(1));
				}
			}
			cpos = g_consume_pos;    /* fresh playhead for this round */
			for (int k = 0; k < NTRK; k++) {
				int i = (int)((rr + (uint32_t)k) & 3u);
				if (g_slot != slot) break;
				struct looptrk *t = &trk[i];
				if (t->state != TS_PLAY && !head_active(i)) continue;
				/* ===== M29: do not read what nobody can hear =================
				 * A muted track is still TS_PLAY, so its ring was filled at full
				 * rate from flash and the mixer discarded every sample. During a
				 * take that waste is the difference between over-budget and 84%
				 * of the bus. Scoped to takes only; heads sources never skipped. */
				if (g_rec_track >= 0 && t->muted && !head_active(i)) continue;
				int32_t avail = (int32_t)(t->p_w - cpos);
				/* DEAD-HISTORY SNAP: a frontier BEHIND the playhead is pure
				 * waste — the mixer reads exactly pring[cpos], so every
				 * sample in [p_w, cpos) can never be played, yet the old
				 * code ground through it sequentially. During an overdub
				 * the three playing tracks live just below zero (each
				 * write burst dips them), so nearly the WHOLE read budget
				 * went on never-played history, which is what actually cut
				 * the other tracks out while recording the 4th (measured
				 * live: margins oscillating 0..-350 ms for the entire
				 * take, full-rate reads, zero audible progress). Snap the
				 * frontier to the live playhead the moment it falls more
				 * than a block behind; loop_blk below is fully modular, so
				 * the loop phase is untouched — the track simply rejoins
				 * the transport where it is NOW, and every read from here
				 * on buys audible audio. */
				if (avail < -(int32_t)TSPB(t) ||
				    avail > (int32_t)RING_SAMPLES) {
					/* Test against the LIVE playhead, not the round's cpos
					 * snapshot: a restart/slot-switch during an earlier
					 * CMD18 in this round resets BOTH cpos and p_w to 0,
					 * and snapping against the stale snapshot would clobber
					 * that reset (p_w lands far AHEAD -> ring reads as
					 * pinned-full -> the mixer replays stale ring content).
					 * The upper bound is impossible in any healthy state
					 * (refill never runs more than one ring ahead), so it
					 * uniquely fingerprints such a clobber and self-heals
					 * it within one streamer pass. */
					uint32_t cnow = g_consume_pos;
					int32_t a2 = (int32_t)(t->p_w - cnow);
					if (a2 < -(int32_t)TSPB(t) ||
					    a2 > (int32_t)RING_SAMPLES) {
						uint32_t anchor = (cnow / TSPB(t)) * TSPB(t);
						t->p_w = anchor;   /* audio thread sees starved either way */
						a2 = (int32_t)(anchor - cnow);
						g_p2snap[i]++;
					}
					avail = a2;
				}
				if (avail > (int32_t)(RING_SAMPLES - 8u * TSPB(t)))
					continue;          /* ring PINNED ~full (<=8 blocks of headroom):
					                    * the cushion is real at stall onset instead of
					                    * sawtoothing between half and full. 8 blocks
					                    * (not 4) so steady-state top-ups are >=7-block
					                    * bursts, not 3-block CMD18 spam. */
				/* SEGMENT: this track loops at ITS OWN length (a whole multiple
				 * of the base), not the shared g_loop_blocks. */
				/* M13: a HEAD sources track 1's loop instead of its own —
				 * geometry (length/start/content/region) comes from track
				 * 1; ring bookkeeping stays this track's. */
				struct looptrk *hsrc = head_active(i) ? &trk[g_head_src] : t;
				uint32_t gb = hsrc->len_blocks ? hsrc->len_blocks
					    : (g_loop_blocks ? g_loop_blocks : 1u);
				/* CHOP window (M7b, mode-aware). VARIABLE: slice this
				 * track's OWN length (M5 behavior). FIXED (base known,
				 * track a whole multiple of it): slice THE BAR — every
				 * layer plays the same base/div slice OF EACH OF ITS
				 * BARS, uniform and phase-locked, multi-bar variation
				 * preserved. div=1 reduces to the original math. */
				uint32_t cdiv = g_chop_div, coff = g_chop_off;
				uint32_t cyc, win, wbase, wper;
				if (g_fixed_len && g_loop_blocks && gb >= g_loop_blocks &&
				    (gb % g_loop_blocks) == 0u) {
					wper = g_loop_blocks;
					win = wper / cdiv; if (win == 0u) win = 1u;
					wbase = (coff * wper) / cdiv;
					if (wbase + win > wper) wbase = wper - win;
					cyc = (gb / wper) * win;
				} else {
					wper = gb;
					win = gb / cdiv; if (win == 0u) win = 1u;
					wbase = (coff * gb) / cdiv;
					if (wbase + win > gb) wbase = gb - win;
					cyc = win;
				}
				if (g_win_free) {
					/* M16 FREE WINDOW overrides the stepped div/off.
					 * The pair is stored ordered, but read the two
					 * volatiles defensively: a torn read between the
					 * control thread's stores may see them crossed
					 * for one round. */
					uint32_t ws = g_win_s8, we = g_win_e8;
					if (we < ws) { uint32_t t2 = ws; ws = we; we = t2; }
					win = ((we - ws + 1u) * wper) >> 8;
					if (win == 0u) win = 1u;
					wbase = (ws * wper) >> 8;
					if (wbase + win > wper) wbase = wper - win;
					cyc = (gb / wper) * win;
				}
				/* BOUNDARY BUDGET: a chunk clipped by the loop wrap or the
				 * content/silence boundary used to consume this track's
				 * WHOLE turn in the round — so the only track with a
				 * mid-loop boundary (a fixed-mode silence tail) lost ~85 ms
				 * of refill every lap and was measurably the only one still
				 * starving (stv=[2 2 35 0] while its siblings sat at 2).
				 * The turn now keeps reading until its full 32-block quota
				 * has moved; a boundary merely splits it into 2-3 shorter
				 * bursts. Fairness is unchanged (same per-round quota). */
				bool round_abort = false;
				for (uint32_t budget = 32u; budget; ) {
					/* Snapshot the frontier: the (higher-priority) audio
					 * thread can reset p_w mid-eMMC-read on a song switch /
					 * restart. Fill from the snapshot, COMMIT only if
					 * unchanged. */
					uint32_t pw = t->p_w;
#if SP1_CODEC == SP1_CODEC_PCM
					/* M22-B PLAIN PATH (see the prime site): the loop
					 * wraps at its SAMPLE length. Mirrors the block
					 * path's room/content/race discipline exactly. */
					if (cdiv == 1u && !g_win_free && !head_active(i) &&
					    t->len_samps && win == wper && wper == gb &&
					    !g_win_rev &&
					    !(heads_engaged() && g_head_rev[i])) {   /* M50a: reversed source -> head path */
						uint32_t Ls  = t->len_samps;
						uint32_t lp  = ((pw % Ls) + Ls -
						              (t->start_samps % Ls)) % Ls;
						uint32_t off = lp % TSPB(t);
						uint32_t lb  = lp / TSPB(t);
						uint32_t n   = budget;
						if (n > (RING_SAMPLES / TSPB(t)) - 1u)
							n = (RING_SAMPLES / TSPB(t)) - 1u;
						{	/* fill to ~full, 1-block gap (as below) */
							int32_t av = (int32_t)(pw - cpos);
							int32_t room = (int32_t)(RING_SAMPLES - TSPB(t)) - av;
							uint32_t rb = room > 0 ? (uint32_t)room / TSPB(t) : 0u;
							if (n > rb) n = rb;
						}
						if (!n) break;
						{	/* clip to the lap end in whole blocks */
							uint32_t lapb = ((Ls - 1u) / TSPB(t)) + 1u;
							if (lb + n > lapb) n = lapb - lb;
						}
						uint32_t ct = t->content_blocks ? t->content_blocks
						                                : ((Ls - 1u) / TSPB(t)) + 1u;
						bool sil = (lb >= ct);
						if (!sil && lb + n > ct) n = ct - lb;
						if (!n) { n = 1u; sil = true; }
						bool rok;
						if (sil) { memset(batchbuf, 0, (size_t)n * EMMC_BLOCK_SIZE); rok = true; }
						else     { rok = emmc_read_blocks_fast(trk_blk(slot, (uint32_t)i) + lb, batchbuf, n); } /* M71 */
						if (!rok) {
							work = true;
							g_p2rfail++;
							bool rp = false;
							for (int j = 0; j < NTRK; j++) {
								uint8_t sj = trk[j].state;
								if (sj != TS_REC && sj != TS_DONE) continue;
								if ((trk[j].r_w - trk[j].r_r) >=
								    ((RRING_SAMPLES * 2u) - RRING_SAMPLES / 2u))   /* CD-463: 3/4 of 2x */
									rp = true;
							}
							if (rp) round_abort = true;
							break;
						}
						if (t->p_w != pw) { work = true; break; } /* reset raced us */
						uint32_t ds = n * TSPB(t) - off;
						if (ds > Ls - lp) ds = Ls - lp;
						p14s_unpack_part(t->pring, RING_MASK, pw & RING_MASK,
								  batchbuf, off, ds, i);
						t->p_w = pw + ds;
						g_p2blk[i] += n;
						work = true;
						more = true;
						budget -= n;
						continue;
					}
#endif
					/* phase-anchored loop position: (pw_block - start_blk)
					 * mod gb, safe when pw_block < start_blk (restart). */
					uint32_t pwb = pw / TSPB(t);
					/* phase-anchored position along the audible chop
					 * cycle, tiled onto the region (variable mode:
					 * wper=gb, cyc=win -> identical to M5). */
					uint32_t hoff = heads_engaged()
						      ? (((uint32_t)g_head_pos[i] * cyc) >> 8) : 0u;
					uint32_t c = ((pwb % cyc) + cyc -
						      (hsrc->start_blk % cyc) + hoff) % cyc;
					/* M15 REVERSE: mirror the phase — consecutive ring
					 * blocks then walk the source BACKWARD, and each
					 * block's samples are flipped after decode below:
					 * together a continuous time-reversed stream. */
					bool hrev = (bool)(heads_engaged() && g_head_rev[i]) ^
						    (bool)g_win_rev;
					if (hrev) c = (cyc - 1u) - c;
					uint32_t loop_blk = (c / win) * wper + wbase + (c % win);
					uint32_t n = budget;
					if (n > (RING_SAMPLES / TSPB(t)) - 1u) n = (RING_SAMPLES / TSPB(t)) - 1u;
					/* VARIABLE TOP-UP: fill to ~full (keep a 1-block
					 * producer/consumer gap) so rings park at ~100%. */
					{
						int32_t av = (int32_t)(pw - cpos);
						int32_t _room = (int32_t)(RING_SAMPLES - TSPB(t)) - av;
						uint32_t _rb = _room > 0 ? (uint32_t)_room / TSPB(t) : 0u;
						if (n > _rb) n = _rb;
					}
					if (!n) break;
					{	/* contiguous run ends at this tile's window edge
						 * (M15-r2: a reversed head's run walks BACKWARD,
						 * so its edge is the tile START) */
						if (!hrev) {
							uint32_t wend = (c / win) * wper + wbase + win;
							if (loop_blk + n > wend) n = wend - loop_blk;
						} else {
							uint32_t wstart = (c / win) * wper + wbase;
							if (n > loop_blk - wstart + 1u)
								n = loop_blk - wstart + 1u;
						}
					}
					/* SILENCE PAD: the loop length can exceed the recorded
					 * content (fixed mode). [content, gb) was never written
					 * to flash — read it as synthesised zeros instead of
					 * stale flash data. NOTE: memset(0) is true silence ONLY
					 * for PCM. A compressed codec (u-law/ADPCM) would need
					 * its own encoded-silence bytes here, not zeros (u-law
					 * 0x00 decodes to a loud tone). */
					uint32_t content = hsrc->content_blocks ? hsrc->content_blocks : gb;
					bool _sil = (loop_blk >= content);
					if (!hrev) {
						if (!_sil && loop_blk + n > content)
							n = content - loop_blk;
					} else if (_sil && n > loop_blk - content + 1u) {
						/* backward silence run stays silence */
						n = loop_blk - content + 1u;
					}
					uint32_t blkno = trk_blk(slot, head_active(i)
					                              ? (uint32_t)g_head_src
					                              : (uint32_t)i)
						       + (hrev ? (loop_blk - n + 1u) : loop_blk);
					/* ==== S2: SHADOW HIT? Steady forward spans fully below
					 * this track's watermark stream PCM from the shadow --
					 * no decode. Same CRC-verified read wrapper. Any miss
					 * or failure falls through to the A7 path unchanged. */
					bool _shit = false;
					if (g_shw_armed && !hrev && !_sil && !head_active(i) &&
					    (loop_blk + (n <= 27u ? n : 27u)) * SAMP_PER_BLK <= g_shw_wm[i]) {
						if (n > 27u)
							n = 27u;   /* S8Q DERIVED, not hardcoded: batchbuf is 32
							            * sectors; worst start offset 249 =>
							            * ceil((249+n*280)/250): n=27 -> 32 fits,
							            * n=28 -> 33 OVERFLOWS. */
						uint32_t _sf0 = loop_blk * SAMP_PER_BLK;
						uint32_t _sb0 = _sf0 / 250u;
						uint32_t _sbe = (_sf0 + n * SAMP_PER_BLK + 249u) / 250u;
						uint32_t _sm  = _sbe - _sb0;
						if (_sm <= 32u &&
						    emmc_read_blocks_fast(SHW_TRK((uint32_t)i) + _sb0,
						                          batchbuf, _sm)) {
							/* S8Q: decode BOTH channels -- the mono
							 * duplication is gone with the mono format. */
							s8q_dec_span((const uint8_t *)batchbuf,
							             _sf0 - _sb0 * 250u,
							             n * SAMP_PER_BLK,
							             t->pring, RING_MASK, pw);
							if (g_shw_slot != slot) g_shw_stale++;  /* #116 guard: must stay 0 */
							_shit = true;
							g_shw_hit += n;
						}
					}
					bool _rok;
					if (_shit) { _rok = true; }
					else if (_sil) { memset(batchbuf, 0, (size_t)n * EMMC_BLOCK_SIZE); _rok = true; }
					else      {
						{	/* RB-475: bucket the burst BEFORE the read.
							 * Counters only -- n is not modified. */
							uint32_t _rbn = n;
							int _rbi = (_rbn <= 2u) ? 0 : (_rbn <= 4u) ? 1 :
							           (_rbn <= 8u) ? 2 : (_rbn <= 16u) ? 3 : 4;
							if (M73_CY_NOW()) {
								g_rb_n[_rbi]++;
								g_rb_blk += _rbn;
								g_rb_cnt++;
							}
						}
						_rok = emmc_read_blocks_fast(blkno, batchbuf, n);
					} /* M71 */
					if (!_rok) {
						work = true;       /* read failed: retry in a few ms */
						g_p2rfail++;
						/* Fast command-phase failures must not abort the
						 * whole round (that lockout was the measured
						 * cut-out mechanism); only genuine rec-ring
						 * pressure may. Otherwise skip this track — the
						 * next round retries a few ms later, after the
						 * card's busy window has passed. */
						bool _rec_press = false;
						for (int j = 0; j < NTRK; j++) {
							uint8_t sj = trk[j].state;
							if (sj != TS_REC && sj != TS_DONE) continue;
							if ((trk[j].r_w - trk[j].r_r) >=
							    ((RRING_SAMPLES * 2u) - RRING_SAMPLES / 2u))   /* CD-463: 3/4 of 2x */
								_rec_press = true;
						}
						if (_rec_press) round_abort = true;
						break;
					}
					if (t->p_w != pw) { work = true; break; } /* reset raced us */
					/* DECODE: packed flash bytes (n blocks just read) -> play
					 * ring (int16, wraps at RING_MASK, pw is block-aligned).
					 * PCM is memcpy-equivalent. */
					/* M63b: coded blocks cannot be byte-flipped — decode
					 * in reverse block order instead. */
					if (_shit) {
						/* S2: ring already holds the shadow PCM */
					} else if (hrev)
						p14s_unpack_rev(t->pring, RING_MASK, pw & RING_MASK,
						                 batchbuf, n);
					else
						p14s_unpack(t->pring, RING_MASK, pw & RING_MASK,
						             batchbuf, n, i);
					t->p_w = pw + n * TSPB(t);
					g_p2blk[i] += n;
					/* ==== S1 SHADOW BUILDER. The decoded span sits in
					 * pring[pw..pw+n*280) as unconsumed PREFETCH (stable,
					 * SPSC). batchbuf is DEAD here (unpack above consumed
					 * its A7 bytes; next use overwrites) -- borrowed as
					 * staging per the M69 liveness rule. Bus is ours
					 * (sole-owner thread); writes ride the async port. */
					if (g_shw_armed && !hrev && !_sil &&
					    !head_active(i) && t->state == TS_PLAY &&
					    g_rec_track < 0 &&
					    !(g_p14s_mask & (1u << i))) {   /* P14S: no shadow */
						static uint32_t _shw_slot = 0xFFFFFFFFu;
						if (_shw_slot != slot) {   /* song switch: all stale */
							_shw_slot = slot;
							for (int _j = 0; _j < NTRK; _j++)
								g_shw_wm[_j] = 0u;
						}
						uint32_t _f0 = loop_blk * SAMP_PER_BLK;
						uint32_t _fe = _f0 + n * SAMP_PER_BLK;
						uint32_t _w  = g_shw_wm[i];
						if (_w >= _f0 && _w < _fe) {
							uint8_t *_sb = (uint8_t *)batchbuf;
							uint32_t _m = 0;
							while (_m < 32u && _w + 250u <= _fe) {
								uint32_t _rb = pw + (_w - _f0);
								/* S8Q: stereo encode straight from pring.
								 * The mono bail is deleted WITH the format. */
								s8q_enc_sector(t->pring, RING_MASK, _rb,
								               (uint16_t)(_w / 250u),
								               _sb + _m * 512u);
								_w += 250u; _m++;
							}
							if (_m) {
								bool aw3_burst_start(uint32_t, const uint8_t *, uint32_t);
								bool aw3_burst_wait(void);
								uint32_t _sblk = SHW_TRK((uint32_t)i) +
								                 g_shw_wm[i] / 250u;
								if (aw3_burst_start(_sblk, batchbuf, _m) &&
								    aw3_burst_wait()) {
									g_shw_wm[i] = _w;
									g_shw_blk += _m;
								} else {
									g_shw_skip++;
								}
							}
						}
					}
					work = true;
					more = true;             /* served: worth another round */
					budget -= n;
				}
				if (round_abort) { more = false; break; }
				/* WRITE-PAGE BREAK: the recorder fills a whole 16-block
				 * page every ~85 ms; the moment one is ready, finish the
				 * round early so PASS 1 can write it — write latency is
				 * bounded to ~one chunk (~5 ms) without any of the old
				 * mid-round yield heuristics that locked tracks out. */
				bool page_ready = false;
				for (int j = 0; j < NTRK; j++) {
					uint8_t sj = trk[j].state;
					if (sj != TS_REC && sj != TS_DONE) continue;
					if ((trk[j].r_w - trk[j].r_r) >=
					    16u * TSPBI(j)) page_ready = true;
				}
				if (page_ready) {
					g_p2yield++;
					more = false;
					break;
				}
			}
			}
			if (_m71spr)
				k_thread_priority_set(k_current_get(), K_PRIO_PREEMPT(5));
		}
		/* ==== M19b BOUNCE RENDER: one 4-block chunk per round, between
		 * the passes — the same citizenship as the PASS-1 flush. Bounded
		 * IO (<=16 single reads + one 4-block write), so the play rings
		 * keep their cushions while the heads keep sounding. ==== */
		/* M63b-1: the bounce mixer sums RAW FLASH BYTES as PCM, which is
		 * wrong for coded blocks. Refuse the request (LED shrug) rather
		 * than render noise; M63b-2 ports it to a7_decode_block. */
		if (g_bnc_req >= 0 && !g_bnc_active) {
			g_bnc_req = -1; g_bnc_abort = 0; g_led_shrug = 1;
		}
		if (0)
			g_bnc_active = 1;
		if (g_bnc_active) {
			if (g_bnc_abort) {
				g_bnc_active = 0; g_bnc_req = -1; g_bnc_abort = 0;
			} else {
				uint32_t bdst = trk_blk(g_slot, (uint32_t)bnc_dst);
				uint32_t bsrc = trk_blk(g_slot, (uint32_t)bnc_src);
				uint32_t nblk = bnc_cyc - bnc_done_blocks;
				if (nblk > 1u) nblk = 1u;   /* M63b: bnc_acc holds ONE
				                             * stereo A7 block (2,240 B of
				                             * 4 KB); b-2 ports the mixer */
				memset(bnc_acc, 0,
				       sizeof(bnc_acc[0]) * nblk * SAMP_PER_BLK);
				bool rok = true;
				for (uint32_t hk = 0; hk < NTRK && rok; hk++) {
					if (bnc_mut[hk] || bnc_vol[hk] == 0u) continue;
					for (uint32_t b = 0; b < nblk && rok; b++) {
						uint32_t c = bnc_done_blocks + b;
						uint32_t ci = (c + (((uint32_t)bnc_pos[hk] *
							bnc_cyc) >> 8)) % bnc_cyc;
						uint32_t hr = (uint32_t)bnc_rev[hk] ^
							(uint32_t)bnc_wrev;
						if (hr) ci = (bnc_cyc - 1u) - ci;
						uint32_t lb = (ci / bnc_win) * bnc_wper +
							bnc_wbase + (ci % bnc_win);
						if (lb >= bnc_content)
							continue;   /* silence adds zero */
						if (!emmc_read_blocks(bsrc + lb,
								      bnc_rdbuf, 1)) {
							rok = false; break;
						}
						const int16_t *sp2 =
							(const int16_t *)bnc_rdbuf;
						int32_t *ap = &bnc_acc[b * SAMP_PER_BLK];
						int32_t gq = (int32_t)bnc_vol[hk];
						if (!hr) {
							for (uint32_t f = 0; f < SAMP_PER_BLK; f++)
								ap[f] += ((int32_t)sp2[f] * gq) >> 8;
						} else {
							for (uint32_t f = 0; f < SAMP_PER_BLK; f++)
								ap[f] += ((int32_t)
								    sp2[SAMP_PER_BLK - 1u - f] * gq) >> 8;
						}
					}
				}
				if (rok) {
					int16_t *op = (int16_t *)batchbuf;
					for (uint32_t f = 0; f < nblk * SAMP_PER_BLK; f++)
						op[f] = soft_limit(bnc_acc[f]);
					if (emmc_write_blocks(bdst + bnc_done_blocks,
							      batchbuf, nblk)) {
						bnc_done_blocks += nblk;
						if (bnc_done_blocks >= bnc_cyc) {
							g_bnc_active = 0;
							g_bnc_req = -1;
							g_bnc_done = 1;
						}
					}
				}
				/* any failure: same chunk retries next round */
				work = true;
			}
		}
		if (!work) {
			/* IDLE WINDOW: drain the card's write cache in the background.
			 * emmc_cache_flush_try() was built for exactly this (abortable:
			 * the busy-abort hook fires an HPI the moment a take arms or a
			 * play ring drains toward half) but was NEVER WIRED IN — the
			 * cache only flushed at power-off, so it silently filled across
			 * a session and later takes paid internal-eviction busy on
			 * every write burst. That is the "gets worse and worse",
			 * worst-on-the-4th-track cut-out: the first takes write into
			 * an empty cache, the last ones fight the card's housekeeping
			 * for the bus. Keeping the cache drained between takes gives
			 * every take a fresh, absorbent cache. */
			bool quiet = (g_rec_track < 0) && !g_xfer_mode &&
				     g_hpi_on && g_emmc_ready && !g_emmc_quiesce &&
				     !g_meta_save_req && !g_cache_flush_req;
			if (quiet)
				for (int j = 0; j < NTRK; j++) {
					uint8_t sj = trk[j].state;
					if (sj == TS_ARMED || sj == TS_REC || sj == TS_DONE)
						quiet = false;
				}
			static int64_t flush_last;
			int64_t nowms = k_uptime_get();
			if (quiet && nowms - flush_last >= 50) {
				flush_last = nowms;
				(void)emmc_cache_flush_try();
			}
			k_msleep(2);
		} else {
			/* ANTI-STARVATION: the streamer at PREEMPT(5) outranks main(8),
			 * the WDT feeder. A long stretch of back-to-back work (or any
			 * future livelock in this loop) must NEVER be able to hold main
			 * off the CPU for the 4 s watchdog window — one 0.5 ms breather
			 * per 64 working passes costs <1% and guarantees it. */
			static uint32_t workpass;
			if ((++workpass & 0x3Fu) == 0u)
				k_usleep(500);
		}
	}
}

/* ========================================================================
 *  MIDI  —  timer-driven 24-PPQN clock + Start/Stop out over the SYNC jack.
 *  A free hardware timer clocks the UART bits one per ISR with interrupts
 *  left ON, so it never masks the eMMC/I2S ISRs (the fix for the >3-track
 *  crackle the old irq-locked bit-bang caused).
 * ======================================================================== */
/* ---- MIDI clock + Pocket-Operator sync out over the SYNC jack --------------
 * Pins from TimK's sync-jack schematic:
 *   MIDI  : BC807_BASE = P0.23 -> a PNP transistor that drives SYNC_RING. The
 *           PNP INVERTS: P0.23 LOW -> ring HIGH (MIDI idle/mark), P0.23 HIGH ->
 *           ring LOW (start bit/space). So we bit-bang the MIDI waveform, and
 *           midi_line() flips it for the transistor (set MIDI_INVERT 0 to undo
 *           if a receiver sees it inverted).
 *   PO sync: PO_A = P0.20 -> SYNC_TIP. A short pulse per 1/8 note (2 PPQN),
 *           the Korg/Volca/Pocket-Operator convention.
 * MIDI is 31250 baud, 8N1 = 32 us/bit. Each byte is sent with interrupts locked
 * so its 10 bits keep accurate spacing (~320 us, well within one I2S block of
 * DMA cushion). Driven from the low-priority midi_thread off the engine's
 * 24-PPQN clock counter — no UART peripheral needed.
 *
 * NOTE: untested on real gear yet — verify on a MIDI/PO device; if MIDI is
 * silent/garbled, try flipping MIDI_INVERT. */
#define MIDI_PIN      23u    /* P0.23 BC807_BASE -> SYNC_RING (MIDI)          */
#define POSYNC_PIN    20u    /* P0.20 PO_A       -> SYNC_TIP  (PO/Volca sync) */
#define POSYNC_PIN_B  17u    /* P0.17 PO_B       -> SYNC_TIP (paralleled)     */
#define MIDI_INVERT   1      /* PNP stage inverts; 1 = compensate             */
#define MIDI_BIT_US   32u    /* 31250 baud                                    */
#define PO_PULSE_MS   5      /* sync pulse width                              */
#define PO_DIV        12u    /* 24-PPQN clock / 12 = 2 PPQN (1/8-note pulses) */
/* MIDI/PO SYNC OUT — ENABLED, streaming-safe. The OLD bit-bang held irq_lock()
 * ~320us per byte (10 bits x 32us), masking the eMMC SPIM + I2S DMA ISRs ~32x/s
 * while playing -> stole the streamer's worst-case margin = the >3-track crackle
 * (v1/v2 had no MIDI thread). NOW the 10 UART bits are clocked out by a hardware
 * TIMER, one bit per tiny (~0.5us) ISR, with interrupts LEFT ON the whole time,
 * so the streamer is never starved. The PNP inverts the line, which a hardware
 * UARTE cannot compensate for -- the timer's ISR drives the bit via midi_line()
 * which applies MIDI_INVERT, so the timing is hardware-accurate AND the polarity
 * is right. Set to 0 to compile MIDI out entirely. */
/* MIDI is ON here (timer-driven) alongside the segment looper. Set to 0 to
 * compile the MIDI clock/Start-Stop output out entirely (the line stays idle). */
#define MIDI_SYNC_ENABLE 1

static K_THREAD_STACK_DEFINE(midi_stack, 512);  /* RD-474: was 768. 473 U4S measured 208 B peak -> 2.5x margin. */
static struct k_thread   midi_tcb;

static void midi_pins_init(void)
{
	NRF_P0->PIN_CNF[MIDI_PIN]   =
		(GPIO_PIN_CNF_DIR_Output << GPIO_PIN_CNF_DIR_Pos) |
		(GPIO_PIN_CNF_DRIVE_S0S1 << GPIO_PIN_CNF_DRIVE_Pos);
	NRF_P0->PIN_CNF[POSYNC_PIN] =
		(GPIO_PIN_CNF_DIR_Output << GPIO_PIN_CNF_DIR_Pos) |
		(GPIO_PIN_CNF_DRIVE_S0S1 << GPIO_PIN_CNF_DRIVE_Pos);
	NRF_P0->PIN_CNF[POSYNC_PIN_B] =
		(GPIO_PIN_CNF_DIR_Output << GPIO_PIN_CNF_DIR_Pos) |
		(GPIO_PIN_CNF_DRIVE_S0S1 << GPIO_PIN_CNF_DRIVE_Pos);
	NRF_P0->OUTCLR = (1u << POSYNC_PIN) | (1u << POSYNC_PIN_B);
	/* idle the MIDI line at MARK (ring high -> P0.23 low after inversion) */
	if (MIDI_INVERT) NRF_P0->OUTCLR = (1u << MIDI_PIN);
	else             NRF_P0->OUTSET = (1u << MIDI_PIN);
}

static inline void midi_line(int mark)   /* drive the MIDI line; mark=1 is idle/high */
{
	int p = MIDI_INVERT ? !mark : mark;
	if (p) NRF_P0->OUTSET = (1u << MIDI_PIN);
	else   NRF_P0->OUTCLR = (1u << MIDI_PIN);
}

/* Streaming-safe MIDI byte TX: a free hardware timer (TIMER2 — the board binds
 * no TIMER) clocks out the UART bits one per ISR. The start bit is driven when
 * the byte is queued; the timer then drives the 8 data bits (LSB first) + stop
 * bit at MIDI_BIT_US spacing. Interrupts stay ON throughout, so the eMMC/I2S
 * ISRs are never masked (the fix for the >3-track crackle). Only midi_thread
 * calls midi_send, sequentially, and MIDI bytes are >=31ms apart in practice,
 * so the single-byte-in-flight guard (midi_tx_done) never actually contends. */
#define MIDI_TIMER       NRF_TIMER2
#define MIDI_TIMER_IRQn  TIMER2_IRQn
static volatile uint16_t midi_tx_bits;     /* remaining frame, LSB = next bit out */
static volatile uint8_t  midi_tx_left;     /* bits still to clock (0 = done) */
static struct k_sem      midi_tx_done;     /* 1 = line free for the next byte */

static void midi_timer_isr(const void *arg)
{
	ARG_UNUSED(arg);
	MIDI_TIMER->EVENTS_COMPARE[0] = 0;
	(void)MIDI_TIMER->EVENTS_COMPARE[0];        /* flush the clear (nRF anomaly) */
	if (midi_tx_left) {
		midi_line(midi_tx_bits & 1u);       /* drive this bit (PNP-inverted) */
		midi_tx_bits >>= 1;
		midi_tx_left--;
	} else {
		MIDI_TIMER->TASKS_STOP = 1;
		midi_line(1);                       /* leave the line idle at mark */
		k_sem_give(&midi_tx_done);
	}
}

static void midi_timer_init(void)
{
	MIDI_TIMER->MODE      = TIMER_MODE_MODE_Timer;
	MIDI_TIMER->BITMODE   = TIMER_BITMODE_BITMODE_16Bit;
	MIDI_TIMER->PRESCALER = 4;                          /* 16MHz/16 = 1us tick */
	MIDI_TIMER->CC[0]     = MIDI_BIT_US;                /* fire every 32us = 1 bit */
	MIDI_TIMER->SHORTS    = TIMER_SHORTS_COMPARE0_CLEAR_Msk;
	MIDI_TIMER->INTENSET  = TIMER_INTENSET_COMPARE0_Msk;
	k_sem_init(&midi_tx_done, 1, 1);                    /* start with the line free */
	IRQ_CONNECT(MIDI_TIMER_IRQn, 2, midi_timer_isr, NULL, 0);
	irq_enable(MIDI_TIMER_IRQn);
}

static void midi_send(uint8_t b)
{
	/* wait for any in-flight byte to finish (in practice it always has) */
	if (k_sem_take(&midi_tx_done, K_MSEC(5)) != 0) return;   /* stuck -> skip byte */
	/* The ENTIRE 10-bit frame is timer-clocked -- start(0), d0..d7 (LSB first),
	 * stop(1). The START bit is the timer's FIRST event, NOT driven here, so every
	 * edge is timer-paced; a thread preemption between here and TASKS_START can no
	 * longer stretch the start bit and corrupt the framing. */
	midi_tx_bits = ((uint16_t)b << 1) | (1u << 9);   /* bit0=start(0), d0..d7 @1..8, stop @9 */
	midi_tx_left = 10;                                /* start + 8 data + stop */
	midi_line(1);                                     /* hold idle/mark until the 1st ISR */
	MIDI_TIMER->TASKS_CLEAR = 1;
	MIDI_TIMER->TASKS_START = 1;                      /* 1st ISR (+32us) emits the START bit */
}

/* BASIC MIDI ONLY: just Start/Stop + 24-PPQN clock on the MIDI line. The
 * Pocket-Operator / Volca 2-PPQN sync (the POSYNC GPIO pulses + k_uptime polling)
 * has been removed to keep this thread minimal. */
static void midi_thread(void *a, void *b, void *c)
{
	ARG_UNUSED(a); ARG_UNUSED(b); ARG_UNUSED(c);
	uint32_t consumed = 0;
	while (1) {
		if (g_midi_start_pending) { g_midi_start_pending = 0; midi_send(0xFA); }
		if (g_midi_stop_pending)  { g_midi_stop_pending  = 0; midi_send(0xFC); }
		uint32_t prod = g_midi_clk_produced;
		if (consumed != prod) {
			if ((uint32_t)(prod - consumed) > 96u) {
				/* absurd backlog (>4 beats — a stall or a counter
				 * glitch): RESYNC instead of blasting the difference,
				 * because each clock byte locks IRQs ~320 us and a huge
				 * catch-up burst starves everything below PREEMPT(6). */
				consumed = prod;
			} else {
				consumed++;
				midi_send(0xF8);               /* MIDI clock, 24 PPQN */
			}
		} else {
			k_msleep(1);
		}
	}
}

static void audio_thread(void *a, void *b, void *c)
{
	ARG_UNUSED(a); ARG_UNUSED(b); ARG_UNUSED(c);

	struct i2s_config cfg = {
		/* SLAVE on both clocks (TE native topology): the 3.072 MHz oscillator
		 * drives SCLK, the CS42L42 masters LRCK at exactly 48 kHz (64 SCLK per
		 * frame). We still send 16-bit samples — the nRF shifts the 16 MSBs of
		 * each 32-SCLK half-frame, which both codecs (set for MSB-first slots)
		 * decode correctly; the remaining LSBs are below the 16-bit noise floor. */
		.word_size      = 16,
		.channels       = 2,
		.format         = I2S_FMT_DATA_FORMAT_I2S,
		.options        = I2S_OPT_FRAME_CLK_SLAVE | I2S_OPT_BIT_CLK_SLAVE,
		.frame_clk_freq = I2S_SR,
		.mem_slab       = &tx_slab,
		.block_size     = BLK_BYTES,
		.timeout        = 2000,
	};

	if (!device_is_ready(i2s_dev)) { audio_cfg_rc = -100; return; }

	audio_cfg_rc = i2s_configure(i2s_dev, I2S_DIR_TX, &cfg);
	if (audio_cfg_rc != 0) return;

	/* Prime a few silent blocks, then START. After this the loop refills the
	 * DMA continuously with NO long gap, so the TX stream never underruns.
	 * The codec is configured separately on the main thread (it needs BCLK,
	 * which is live the moment we signal audio_started). */
	for (int i = 0; i < 4; i++) {
		void *blk;
		if (k_mem_slab_alloc(&tx_slab, &blk, K_FOREVER) != 0)
			continue;
		fill_block(blk);
		if (i2s_write(i2s_dev, blk, BLK_BYTES) != 0)
			k_mem_slab_free(&tx_slab, blk);
	}
	i2s_trigger(i2s_dev, I2S_DIR_TX, I2S_TRIGGER_START);
	audio_started = true;

	int wfail = 0;                       /* consecutive i2s_write failures */
	while (1) {
		void *blk;
		if (k_mem_slab_alloc(&tx_slab, &blk, K_FOREVER) != 0)
			continue;
		{	/* U3-471: peak tx_slab occupancy. 10 blocks are allocated
			 * (10,240 B); Zephyr I2S TX typically needs 2-4 queued.
			 * This is the evidence the RAM audit demands before any
			 * cut -- the sizes are certain, "oversized" is a hypothesis. */
			uint32_t _u3u = (uint32_t)k_mem_slab_num_used_get(&tx_slab);
			if (_u3u > g_u3_tx_hi) g_u3_tx_hi = _u3u;
		}

		/* Looper engine: drains the live USB input (prebuffer-gated inside;
		 * silence if the host isn't streaming) and mixes the 4 tracks on top.
		 * DWT-timed: worst-case exec must stay far below the 5.33 ms block
		 * budget — aus= in the diag definitively exonerates (or convicts)
		 * the CPU path for the crackle. */
		uint32_t _c0 = DWT->CYCCNT;
		looper_audio_block(blk);
		uint32_t _cus = (DWT->CYCCNT - _c0) / 64u;   /* 64 MHz -> us */
		if (_cus > g_audio_us_max) g_audio_us_max = _cus;

		int wrc = i2s_write(i2s_dev, blk, BLK_BYTES);
		if (wrc != 0) {
			g_i2s_wfail_cnt++;   /* diag: I2S path failure counter */
			k_mem_slab_free(&tx_slab, blk);
			/* FAILSAFE: if the I2S TX ever errors into the stopped state, every
			 * write fails forever and the device latches SILENT until reboot.
			 * After a burst of consecutive failures, drop + re-prime + restart
			 * the stream instead of staying mute. */
			if (++wfail >= 8) {
				wfail = 0;
				(void)i2s_trigger(i2s_dev, I2S_DIR_TX, I2S_TRIGGER_DROP);
				for (int i = 0; i < 4; i++) {
					void *pb;
					if (k_mem_slab_alloc(&tx_slab, &pb, K_NO_WAIT) != 0)
						break;
					fill_block(pb);
					if (i2s_write(i2s_dev, pb, BLK_BYTES) != 0)
						k_mem_slab_free(&tx_slab, pb);
				}
				(void)i2s_trigger(i2s_dev, I2S_DIR_TX, I2S_TRIGGER_START);
			}
			continue;
		}
		wfail = 0;
	}
}

/* Bring up the audio output path: osc on, codec configured, stream started. */
static void audio_init(void)
{
	/* The 3.072 MHz oscillator IS the bus bit-clock in TE's topology — turn it
	 * ON. (The old crackle when enabling it came from the nRF ALSO mastering
	 * SCLK = two drivers on one line; the nRF is a clock slave now.) */
	gpio_drive_high(OSC_EN_PORT, OSC_EN_PIN);
	k_msleep(5);
	k_thread_create(&audio_tcb, audio_stack, K_THREAD_STACK_SIZEOF(audio_stack),
			audio_thread, NULL, NULL, NULL,
			K_PRIO_PREEMPT(0), 0, K_NO_WAIT);
	/* PREEMPT(0), not COOP(7): still outranks every other app thread (main 8,
	 * streamer 5, MIDI 6 — none can preempt it), but the COOP USB/UDC stack
	 * threads can now interrupt the mixer for their ~100 us ISO service.
	 * MEASURED on hardware: with the mixer non-preemptible, the USB
	 * controller lost ~600 incoming audio frames/s ONLY while recording
	 * (SOF heartbeat perfect, rx pool untouched) — silence stitched into
	 * every take = THE 4-track crackle. Shared state with the USB threads is
	 * one SPSC ring buffer and one mem-slab, both preemption-safe. */

	/* eMMC streamer: preemptible + below the audio thread so audio always
	 * wins. Guarded: in the charge-standby path it was already started
	 * early so the gauge can read the saved brightness (v1.2.3). */
	streamer_start();

	/* MIDI clock + PO sync out over the SYNC jack (TimK pins). The MIDI byte TX
	 * is now clocked by a hardware timer (midi_timer_init) so it no longer masks
	 * interrupts -- the >3-track crackle fix. Thread is low priority; it just
	 * flags bytes + drives the PO-sync GPIO pulse. */
#if MIDI_SYNC_ENABLE
	midi_pins_init();
	midi_timer_init();
	k_thread_create(&midi_tcb, midi_stack, K_THREAD_STACK_SIZEOF(midi_stack),
			midi_thread, NULL, NULL, NULL,
			K_PRIO_PREEMPT(6), 0, K_NO_WAIT);
#endif

	/* Wait until the audio thread has the I2S stream running (BCLK live), then
	 * configure the codec here on the main thread. The audio thread keeps the
	 * DMA fed throughout, so its config sleeps never starve the I2S. */
	for (int i = 0; i < 100 && !audio_started; i++)
		k_msleep(2);
	tas2505_configure();
}

/* ---- UAC2 explicit feedback: software regulator (v1) ------------------------
 * The host needs to know how fast the SP-1 actually consumes samples. The SP-1
 * I2S bus runs at exactly 48000 Hz (codec-mastered); reporting the nominal rate
 * would make the host over-deliver and overflow the ring. Nordic only ships a
 * hardware feedback measurement for the nRF5340 (it needs an I2S FRAMESTART
 * event the nRF52840 lacks), so we regulate in software, reporting a USB Q10.14
 * "samples per SOF" value (1.0 sample = 1<<14 in the low 24 bits).
 *
 * CRITICAL: the reported value must be SMOOTH. The raw ring fill carries a large
 * ~187 Hz sawtooth (audio_thread drains in 256-frame blocks) plus per-packet USB
 * jitter; feeding that straight into the feedback warbles the host's asynchronous
 * resampler (audible pitch wobble) and makes the buffer hunt (crackle). So we
 *   1) low-pass the fill with an EMA, and
 *   2) apply only a GENTLE proportional gain to the smoothed fill error.
 * No separate integrator: the ring level is ITSELF the integral of the rate
 * mismatch, so a proportional law already drives the steady-state RATE error to
 * zero; the earlier extra integrator made it a double integrator that hunted.
 * feedback_update() runs once per SOF (USB thread); feedback_cb() returns the
 * atomic snapshot. Tuning knobs: FB_KP (authority) and FILL_EMA_SHIFT (smoothing). */
#define FB_FRAC        14
/* I2S_TRUE_HZ (48000) is defined up top near I2S_SR. FB_TRUE is the Q10.14
 * "samples per USB SOF" we report back to the host so it delivers at the rate
 * the I2S bus actually consumes, keeping the ring balanced. */
#define FB_TRUE        ((uint32_t)(((uint64_t)I2S_TRUE_HZ << FB_FRAC) / 1000u))
/* Clamp window centered on the true rate — safety rails only, not hit in normal
 * operation. FB_SETPOINT is defined up by the ring buffer (shared with prebuffer). */
#define FB_MIN         (FB_TRUE - (1u << FB_FRAC))  /* ~43.4 samples/SOF */
#define FB_MAX         (FB_TRUE + (1u << FB_FRAC))  /* ~45.4 samples/SOF */
#define FILL_Q         8                      /* fixed-point bits for the fill EMA */
#define FILL_EMA_SHIFT 6                      /* EMA tau ~64 SOFs (~64 ms): kills the
						* ~187 Hz block-drain sawtooth, far below
						* audio. Raise to smooth more. */
#define FB_KP          3                      /* gentle: fb-LSB per frame of smoothed err */

static atomic_t g_fb_value = ATOMIC_INIT(FB_TRUE);  /* Q10.14 snapshot for the host */
static int32_t  g_fill_avg;                         /* smoothed fill, frames << FILL_Q */
static volatile bool g_fb_running;

static void feedback_reset(void)
{
	g_fill_avg = 0;                       /* ring was just reset to empty */
	atomic_set(&g_fb_value, (atomic_val_t)FB_TRUE);
}

/* Called every USB SOF (USB thread) while the terminal is streaming. */
static void feedback_update(void)
{
	g_sof_cnt++;                        /* diag: SOF heartbeat (1000/s) */
	int frames = (int)(ring_buf_size_get(&usb_audio_ring) / USB_FRAME_BYTES);

	/* EMA low-pass of the fill (Q=FILL_Q fixed point) to strip the block-drain
	 * sawtooth before it can reach the host's resampler. */
	g_fill_avg += (((int32_t)frames << FILL_Q) - g_fill_avg) >> FILL_EMA_SHIFT;
	int err = (g_fill_avg >> FILL_Q) - FB_SETPOINT;   /* smoothed fill error (frames) */

	int32_t fb = (int32_t)FB_TRUE - err * FB_KP;      /* >0 err: ring full -> ask less */
	if (fb > (int32_t)FB_MAX) {
		fb = (int32_t)FB_MAX;
	} else if (fb < (int32_t)FB_MIN) {
		fb = (int32_t)FB_MIN;
	}

	atomic_set(&g_fb_value, (atomic_val_t)fb);
}

/* ---- UAC2 application callbacks --------------------------------------------
 * UDC-aligned pool the USB stack writes incoming audio into before handing it
 * to data_recv_cb. One SOF of FS audio is 48 frames; allow +1 for feedback
 * over-speed packets.
 * POOL DEPTH IS LOAD-BEARING: if uac2_get_recv_buf has no buffer for an
 * isochronous OUT interval, that packet is LOST FOREVER (ISO never retries) —
 * a 1 ms hole in the live input that gets RECORDED into a take. The audio
 * thread is COOP(7) and non-preemptible, so the COOP(8) USB threads can be
 * held off for several ms under recording load; 6 buffers (~6 ms) was NOT
 * enough — measured live: the input ring pinned at its floor with ~16 silence
 * frames padded into every block, 187x/s, for entire takes = THE crackle
 * (the eMMC was never the cause). 32 buffers = ~32 ms of cushion. */
#define UAC2_IN_TERMINAL_ID  UAC2_ENTITY_ID(DT_NODELABEL(in_terminal))
#define UAC2_MAX_PKT         ((48 + 1) * USB_FRAME_BYTES)
K_MEM_SLAB_DEFINE_STATIC(uac2_rx_slab, ROUND_UP(UAC2_MAX_PKT, UDC_BUF_GRANULARITY),
			 32, UDC_BUF_ALIGN);

static const struct device *const uac2_dev =
	DEVICE_DT_GET(DT_NODELABEL(uac2_speaker));

static void uac2_terminal_update_cb(const struct device *dev, uint8_t terminal,
				    bool enabled, bool microframes, void *user_data)
{
	ARG_UNUSED(dev); ARG_UNUSED(microframes); ARG_UNUSED(user_data);

	if (terminal != UAC2_IN_TERMINAL_ID) {
		return;
	}

	if (enabled) {
		/* Reset must be atomic vs the audio thread's ring_buf_get (reset is
		 * neither the producer nor the consumer role, so it is NOT safe against
		 * a concurrent get — a half-reset index pair can hand the consumer a
		 * block of garbage right at stream start). Briefly lock the scheduler. */
		k_sched_lock();
		ring_buf_reset(&usb_audio_ring);
		k_sched_unlock();
		feedback_reset();
		g_fb_running = true;
		g_usb_streaming = true;        /* audio_thread switches to the ring */
	} else {
		g_usb_streaming = false;       /* audio_thread falls back to silence/tone */
		g_fb_running = false;
	}
}

static void *uac2_get_recv_buf(const struct device *dev, uint8_t terminal,
			       uint16_t size, void *user_data)
{
	ARG_UNUSED(dev); ARG_UNUSED(user_data);
	void *buf = NULL;

	if (terminal == UAC2_IN_TERMINAL_ID && g_usb_streaming) {
		__ASSERT_NO_MSG(size <= UAC2_MAX_PKT);
		uint32_t _free = k_mem_slab_num_free_get(&uac2_rx_slab);
		if (_free < g_rx_slab_min) g_rx_slab_min = _free;
		if (_free < g_u3_rx_lo) g_u3_rx_lo = _free;   /* U3-471 cumulative */
		if (k_mem_slab_alloc(&uac2_rx_slab, &buf, K_NO_WAIT) != 0) {
			buf = NULL;            /* NO buffer for an ISO interval = the
			                        * packet is DROPPED (ISO never retries):
			                        * counted — this is the crackle source. */
			g_rx_nobuf++;
		}
	}

	return buf;
}

static void uac2_data_recv_cb(const struct device *dev, uint8_t terminal,
			      void *buf, uint16_t size, void *user_data)
{
	ARG_UNUSED(dev); ARG_UNUSED(terminal); ARG_UNUSED(user_data);
	uint32_t _t80 = DWT->CYCCNT;

	if (g_usb_streaming && size) {
		g_usb_pkts++;                /* diag: ~1000/s expected while streaming */
		g_usb_frames += size / USB_FRAME_BYTES;
		/* Push the 16-bit stereo frames into the elastic ring. If the whole
		 * packet doesn't fit, drop the WHOLE packet (one clean 1 ms gap) rather
		 * than a partial put — with a feedback-deaf host the ring pegs full and
		 * per-packet shaving would otherwise crackle continuously. */
		if (ring_buf_space_get(&usb_audio_ring) >= size) {
			(void)ring_buf_put(&usb_audio_ring, (const uint8_t *)buf, size);
		} else {
			g_ring_overflows++;  /* ring full: host out-delivering the feedback */
		}
	}

	k_mem_slab_free(&uac2_rx_slab, buf);
	/* U1: the feedback regulator, relocated off the SOF path. Same
	 * 1 ms cadence (one ISO OUT completion per frame while streaming)
	 * on a wake-cascade that is already paid for. Runs AFTER the
	 * ring_buf_put above, so it sees the fill this frame produced --
	 * a fixed one-frame phase shift versus the old SOF timing, which
	 * the FILL_EMA_SHIFT=6 (~64 ms) filter renders irrelevant. */
	if (g_fb_running) {
		feedback_update();
	}
	g_t_cb += (uint32_t)(DWT->CYCCNT - _t80);
}

static void uac2_buf_release_cb(const struct device *dev, uint8_t terminal,
				void *buf, void *user_data)
{
	/* The SP-1 never sends audio to the host, so this is never called. */
	ARG_UNUSED(dev); ARG_UNUSED(terminal); ARG_UNUSED(buf); ARG_UNUSED(user_data);
}

static uint32_t uac2_feedback_cb(const struct device *dev, uint8_t terminal,
				 void *user_data)
{
	ARG_UNUSED(dev); ARG_UNUSED(terminal); ARG_UNUSED(user_data);
	return (uint32_t)atomic_get(&g_fb_value);
}

static void uac2_sof_cb(const struct device *dev, void *user_data)
{
	ARG_UNUSED(dev); ARG_UNUSED(user_data);
	uint32_t _t80 = DWT->CYCCNT;
	/* U1: feedback_update() moved to uac2_data_recv_cb(). With
	 * CONFIG_UDC_ENABLE_SOF=n this callback no longer fires at all;
	 * it is kept so the ops struct and the g_t_sof meter stay valid
	 * (g_t_sof going to zero is itself the confirmation that SOF is
	 * off). Set SP1_U1_SOF_OFF=0 and CONFIG_UDC_ENABLE_SOF=y to
	 * restore the old path. */
	g_t_sof += (uint32_t)(DWT->CYCCNT - _t80);
}

static struct uac2_ops sp1_uac2_ops = {
	.sof_cb             = uac2_sof_cb,
	.terminal_update_cb = uac2_terminal_update_cb,
	.get_recv_buf       = uac2_get_recv_buf,
	.data_recv_cb       = uac2_data_recv_cb,
	.buf_release_cb     = uac2_buf_release_cb,
	.feedback_cb        = uac2_feedback_cb,
};

/* Bring up the composite USB device (UAC2 audio + CDC console) on device_next.
 * set_ops MUST precede usbd_enable or the UAC2 class init fails. */
static void usb_audio_start(void)
{
	struct usbd_context *usbd;

	if (!device_is_ready(uac2_dev)) {
		printk("uac2 device not ready\n");
		return;
	}

	usbd_uac2_set_ops(uac2_dev, &sp1_uac2_ops, NULL);

	usbd = sample_usbd_init_device(NULL);
	if (usbd == NULL) {
		printk("usbd init failed\n");
		return;
	}

	/* Pin bcdDevice to a new release number. Windows caches USB descriptors
	 * per VID/PID/version — without a version bump a PC that saw the old
	 * (Code-10) audio descriptor keeps judging a re-flashed SP-1 by the
	 * cached copy and can stay broken even after the fix. */
	(void)usbd_device_set_bcd_device(usbd, 0x0200);

	if (usbd_enable(usbd) != 0) {
		printk("usbd enable failed\n");
	}

#if SP1_XFER_ENABLE
	/* Register the CDC RX callback AND enable RX now. On this USB stack the
	 * CDC-ACM class only queues its FIRST receive transfer from
	 * uart_irq_rx_enable() — with it off the endpoint never accepts a single
	 * byte and the transfer site can never connect (GitHub issue #1). The ISR
	 * just moves bytes into a ring; while looping its cost is zero unless the
	 * host actually sends something. */
	uart_irq_callback_user_data_set(cdc, cdc_rx_isr, NULL);
	uart_irq_rx_enable(cdc);
#endif
}

/* Stream the raw ladder codes, but ONLY when a host has opened the port
 * (DTR asserted). That keeps us from ever stalling the watchdog loop when
 * nothing is listening. Throttled by the caller. */
/* =====================================================================
 * SEMITONE grid for the tempo rocker's DOUBLE-CLICK: 2^(k/12) in Q16 for
 * k = -12..+12 (0.5x..2.0x; the BPM clamp bounds the usable range). A
 * double-click jumps the speed to the next exact equal-tempered semitone
 * relative to 1.0x (= 80 BPM) — one musical pitch step instead of forty
 * 1-BPM clicks — and a detuned speed SNAPS ONTO the grid rather than
 * drifting off it. Integer-only; the exact Q16 speed is what the song
 * saves, so semitone speeds survive power-off bit-exact. */
static const uint32_t k_semi_q16[25] = {
	32768u,  34716u,  36781u,  38968u,  41285u,  43740u,  46341u,
	49097u,  52016u,  55109u,  58386u,  61858u,  65536u,  69433u,
	73562u,  77936u,  82570u,  87480u,  92682u,  98193u,  104032u,
	110218u, 116772u, 123715u, 131072u,
};

static uint32_t semitone_next(uint32_t sp, int dir)
{
	/* within ~0.4% of a grid point counts as ON it (absorbs BPM-integer
	 * rounding; far below the 5.9% semitone spacing) */
	if (dir > 0) {
		for (int k = 0; k < 25; k++)
			if (k_semi_q16[k] > sp + sp / 250u)
				return k_semi_q16[k];
		return k_semi_q16[24];
	}
	for (int k = 24; k >= 0; k--)
		if (k_semi_q16[k] < sp - sp / 250u)
			return k_semi_q16[k];
	return k_semi_q16[0];
}

static void controls_diag(void)
{
	{ /* BF: bug #116 + #117 evidence, one line.
	   *   inv=   stale shadow discarded on a slot change (bug window was live)
	   *   stale= serve passed on a stale slot -- MUST BE 0
	   *   cid=   codec id stamped into the v3 table (4 = SP1-ADPCM7)
	   *   flg=   v3 flags byte, bit0 = stereo content */
	  uint32_t _dbf = 0;
	  (void)uart_line_ctrl_get(cdc, UART_LINE_CTRL_DTR, &_dbf);
	  if (_dbf) {
		printk("BF,inv=%u,stale=%u,cid=%u,flg=%u\n",
		       (unsigned)g_shw_inv, (unsigned)g_shw_stale,
		       (unsigned)g_x3.t[g_slot][0].codec_id,
		       (unsigned)g_x3.t[g_slot][0].flags);
	  }
	}
	{ /* M80: USB path meters, CUMULATIVE ms (Protocol A applies).
	   * res = all-thread runtime minus our four threads = USB
	   * cluster + idle; only meaningful under load (M35: idle=0
	   * at the max corner). */
	  uint32_t _d80 = 0;
	  (void)uart_line_ctrl_get(cdc, UART_LINE_CTRL_DTR, &_d80);
	  if (_d80) {
		k_thread_runtime_stats_t _rs;
		uint64_t _all = 0, _kn = 0;
		if (!k_thread_runtime_stats_all_get(&_rs)) _all = _rs.execution_cycles;
		if (!k_thread_runtime_stats_get(&audio_tcb, &_rs))    _kn += _rs.execution_cycles;
		if (!k_thread_runtime_stats_get(&streamer_tcb, &_rs)) _kn += _rs.execution_cycles;
		if (!k_thread_runtime_stats_get(&midi_tcb, &_rs))     _kn += _rs.execution_cycles;
		if (!k_thread_runtime_stats_get(k_current_get(), &_rs)) _kn += _rs.execution_cycles;
		/* M80-r2: cb/sof are DWT (64 MHz -> /64000 = ms). res/all are
		 * RUNTIME-STATS cycles -- the 32768 Hz RTC on this config, NOT
		 * DWT. r1 divided them by 64000 and printed 0 forever (time-base
		 * artifact #6). Print them RAW; the host divides by 32.768/ms. */
		{ /* M90: live snapshot, any state (artifact #9 fix) */
		  uint32_t _bg90 = 0;
		  for (int _i90 = 0; _i90 < NTRK; _i90++) {
			uint32_t _g90 = trk[_i90].r_w - trk[_i90].r_r;
			if (_g90 >= _bg90) { _bg90 = _g90;
			  { uint32_t _g4 = 0;
		  for (int _i4 = 0; _i4 < NTRK; _i4++) {
			uint32_t _d4 = trk[_i4].r_w - trk[_i4].r_r;
			if (_d4 > _g4) _g4 = _d4;
		  }
		  if (_g4 > g_gap_max) g_gap_max = _g4; }
		g_dbg_rw = trk[_i90].r_w; g_dbg_rr = trk[_i90].r_r;
			  g_dbg_rc = trk[_i90].rec_count; }
		  }
		}
		printk("M81,d=%u,a=%u,b=%u,c=%u,dm=%u,am=%u,bm=%u,cm=%u,r=%u,t=%u,tm=%u,rw=%u,rr=%u,rc=%u,em=%u\n",
		       (unsigned)(g_ph[0] / 64000u), (unsigned)(g_ph[1] / 64000u),
		       (unsigned)(g_ph[2] / 64000u), (unsigned)(g_ph[3] / 64000u),
		       (unsigned)g_phmax[0], (unsigned)g_phmax[1],
		       (unsigned)g_phmax[2], (unsigned)g_phmax[3],
		       (unsigned)(g_pa82[0] / 64000u), (unsigned)(g_pa82[1] / 64000u),
		       (unsigned)g_t1min, (unsigned)g_dbg_rw,
		       (unsigned)g_dbg_rr, (unsigned)g_dbg_rc,
		       (unsigned)g_enmin);
		printk("M8X,d=%u,a=%u,b=%u,c=%u,blk=%u\n",
		       (unsigned)(g_cph[0] / 64u), (unsigned)(g_cph[1] / 64u),
		       (unsigned)(g_cph[2] / 64u), (unsigned)(g_cph[3] / 64u),
		       (unsigned)g_cph_blk);
		printk("M8Y,d=%u,a=%u,b=%u,c=%u,blk=%u\n",
		       (unsigned)(g_dph[0] / 64u), (unsigned)(g_dph[1] / 64u),
		       (unsigned)(g_dph[2] / 64u), (unsigned)(g_dph[3] / 64u),
		       (unsigned)g_dph_blk);
		printk("M80,up=%u,cb=%u,sof=%u,res=%u,all=%u,pk=%u,sf=%u\n",
		       (unsigned)k_uptime_get_32(),
		       (unsigned)(g_t_cb / 64000u), (unsigned)(g_t_sof / 64000u),
		       (unsigned)(_all > _kn ? _all - _kn : 0u),
		       (unsigned)_all,
		       (unsigned)g_usb_pkts, (unsigned)g_sof_cnt);
	  }
	}
	{ /* M73: CUMULATIVE ms per streamer phase since boot.
	   * CUMULATIVE, not per-second deltas, so PROTOCOL A applies:
	   * run the corner with NO monitor, connect AFTERWARDS, and this
	   * one line carries the whole run. M71-r5 proved the diag
	   * printing is itself part of the storm load, so a per-second
	   * phase readout would have measured its own weight. */
	  uint32_t _d73 = 0;
	  (void)uart_line_ctrl_get(cdc, UART_LINE_CTRL_DTR, &_d73);
	  if (_d73) {
		g_dmp_arm = 1u;   /* DMP-466: capture connected -> dump may run */
		/* DWT->CYCCNT is the 64 MHz core counter, so 64000 cycles = 1 ms
		 * exactly -- no rounding constant to get wrong. */
		printk("M73,up=%u,rd=%u,dc=%u,en=%u,wr=%u,dcc=%u,"
		       "dcu=%u,dcp=%u,dcr=%u\n",
		       (unsigned)k_uptime_get_32(),
		       (unsigned)(g_t_rd / 64000u), (unsigned)(g_t_dc / 64000u),
		       (unsigned)(g_t_en / 64000u), (unsigned)(g_t_wr / 64000u),
		       (unsigned)g_dcc, (unsigned)g_dcu,
		       (unsigned)g_dcp, (unsigned)g_dcr);
		printk("M73CX,rd=%llu/%u,dc=%llu/%u,en=%llu/%u,wr=%llu/%u\n",
		       (unsigned long long)g_t_rd_cx, g_t_rd_cxn,
		       (unsigned long long)g_t_dc_cx, g_t_dc_cxn,
		       (unsigned long long)g_t_en_cx, g_t_en_cxn,
		       (unsigned long long)g_t_wr_cx, g_t_wr_cxn);
		printk("M73CY,rd=%llu/%u,dc=%llu/%u,en=%llu/%u,wr=%llu/%u\n",
		       (unsigned long long)g_t_rd_cy, g_t_rd_cyn,
		       (unsigned long long)g_t_dc_cy, g_t_dc_cyn,
		       (unsigned long long)g_t_en_cy, g_t_en_cyn,
		       (unsigned long long)g_t_wr_cy, g_t_wr_cyn);
		printk("RB,b1_2=%u,b3_4=%u,b5_8=%u,b9_16=%u,b17_32=%u,blk=%u,cnt=%u\n",
		       (unsigned)g_rb_n[0], (unsigned)g_rb_n[1], (unsigned)g_rb_n[2],
		       (unsigned)g_rb_n[3], (unsigned)g_rb_n[4],
		       (unsigned)g_rb_blk, (unsigned)g_rb_cnt);
		printk("M73CZ,pk=%llu/%u,ps=%llu/%u,blk=%u\n",
		       (unsigned long long)g_t_pk_cy, g_t_pk_cyn,
		       (unsigned long long)g_t_ps_cy, g_t_ps_cyn,
		       (unsigned)g_pk_blk);
		printk("EP,cyc=%llu,n=%u,blk=%u\n",
		       (unsigned long long)g_t_ep,
		       (unsigned)g_t_epn, (unsigned)g_ep_blk);



		printk("P16,m=%u%u%u%u,n=%u%u%u%u\n",
		       (unsigned)trk[0].p16m, (unsigned)trk[1].p16m,
		       (unsigned)trk[2].p16m, (unsigned)trk[3].p16m,
		       (unsigned)trk[0].p16m_next, (unsigned)trk[1].p16m_next,
		       (unsigned)trk[2].p16m_next, (unsigned)trk[3].p16m_next);
		printk("STV,lo=%u,up=%u,cx=%u,pf=%u,re=%u,rhw=%u\n",
		       (unsigned)g_stv_lo, (unsigned)g_stv_up,
		       (unsigned)g_stv_re,
		       (unsigned)g_stv_cx, (unsigned)g_stv_pf, (unsigned)g_rw_hw);

		printk("BTN,lat=%u,max=%u\n",
		       (unsigned)g_stop_lat_ms, (unsigned)g_stop_lat_max);


		printk("W4P,pk=%u,pb=%u,sq=%u,tq=%u\n",
		       (unsigned)g_w4_pk, (unsigned)g_w4_pb,
		       (unsigned)g_w4_sq, (unsigned)g_w4_tq);
		{   /* CX-r2: EVERY tick. The once-per-boot guard cost the
		     * 435 run its thread map. */
			g_w4n_once = 1;
			extern struct k_thread z_main_thread;
			extern struct k_work_q k_sys_work_q;
			printk("W4N,aud=%p,str=%p,midi=%p,main=%p,sysq=%p\n",
			       (void *)&audio_tcb, (void *)&streamer_tcb,
			       (void *)&midi_tcb, (void *)&z_main_thread,
			       (void *)&k_sys_work_q.thread);
		}
		{	/* U3-471: name the census threads by PRIORITY. Zephyr coop
			 * priorities are NEGATIVE, so the USB cluster (K_PRIO_COOP(8))
			 * is unmistakable against idle (lowest) and the app threads
			 * (aud 0 / main 2 / streamer 5 or 1 sprinting / midi 6).
			 * Needs no Zephyr-internal symbols. */
			printk("U3P");
			for (int _u3i = 0; _u3i < 8; _u3i++) {
				void *_t = g_w4c_tab[_u3i].tid;
				if (!_t) { printk(",-"); continue; }
				printk(",%p:%d:%u", _t,
				       (int)k_thread_priority_get((k_tid_t)_t),
				       (unsigned)g_w4c_tab[_u3i].n);
			}
			printk("\n");
			printk("U3B,ringhi=%u,ringlo=%u,ringcap=%u,txhi=%u,txcap=%u,rxlo=%u\n",
			       (unsigned)g_u3_ring_hi,
			       (unsigned)(g_u3_ring_lo == 0xFFFFFFFFu ? 0u : g_u3_ring_lo),
			       (unsigned)USB_RING_FRAMES,
			       (unsigned)g_u3_tx_hi, 10u,
			       (unsigned)(g_u3_rx_lo == 0xFFFFu ? 9999u : g_u3_rx_lo));
		}
		{	/* SS-473: stack high-water. k_thread_stack_space_get walks the
			 * 0xAA fill (CONFIG_INIT_STACKS) and reports bytes NEVER
			 * touched since thread creation -- a true peak, not a
			 * sample, so Protocol A cannot sleep through it.
			 * rc != 0 means the config did not take; treat as no data. */
			printk("U4S");
			for (int _ssi = 0; _ssi < 8; _ssi++) {
				struct k_thread *_kt = (struct k_thread *)g_w4c_tab[_ssi].tid;
				size_t _un = 0;
				int _rc;
				if (!_kt) { printk(",-"); continue; }
				_rc = k_thread_stack_space_get((k_tid_t)_kt, &_un);
				printk(",%p:%u:%u:%d", (void *)_kt->stack_info.start,
				       (unsigned)_kt->stack_info.size,
				       (unsigned)_un, _rc);
			}
			printk("\n");
		}
		printk("W4G,gmax=%u\n", (unsigned)g_gap_max);
		printk("SHW,wm=%u,%u,%u,%u,blk=%u,sk=%u,arm=%u\n",
		       (unsigned)g_shw_wm[0], (unsigned)g_shw_wm[1],
		       (unsigned)g_shw_wm[2], (unsigned)g_shw_wm[3],
		       (unsigned)g_shw_blk, (unsigned)g_shw_skip,
		       (unsigned)g_shw_armed);
		printk("SHR,hit=%u\n", (unsigned)g_shw_hit);
		printk("W4C,%p:%u,%p:%u,%p:%u,%p:%u,%p:%u,%p:%u,%p:%u,%p:%u,m=%u,str=%p\n",
		       g_w4c_tab[0].tid, (unsigned)g_w4c_tab[0].n,
		       g_w4c_tab[1].tid, (unsigned)g_w4c_tab[1].n,
		       g_w4c_tab[2].tid, (unsigned)g_w4c_tab[2].n,
		       g_w4c_tab[3].tid, (unsigned)g_w4c_tab[3].n,
		       g_w4c_tab[4].tid, (unsigned)g_w4c_tab[4].n,
		       g_w4c_tab[5].tid, (unsigned)g_w4c_tab[5].n,
		       g_w4c_tab[6].tid, (unsigned)g_w4c_tab[6].n,
		       g_w4c_tab[7].tid, (unsigned)g_w4c_tab[7].n,
		       (unsigned)g_w4c_miss, (void *)g_str_tid);
		printk("W4X,%u,%u,%u,%u,%u,%u,%u,%u,tot=%u,hs=%u\n",
		       (unsigned)g_cx_n[0], (unsigned)g_cx_n[1],
		       (unsigned)g_cx_n[2], (unsigned)g_cx_n[3],
		       (unsigned)g_cx_n[4], (unsigned)g_cx_n[5],
		       (unsigned)g_cx_n[6], (unsigned)g_cx_n[7],
		       (unsigned)g_cx_tot, (unsigned)g_cx_hs);
		printk("W4Y,%u,%u,%u,%u,%u,%u,%u,%u,tot=%u,hs=%u\n",
		       (unsigned)g_cy_n[0], (unsigned)g_cy_n[1],
		       (unsigned)g_cy_n[2], (unsigned)g_cy_n[3],
		       (unsigned)g_cy_n[4], (unsigned)g_cy_n[5],
		       (unsigned)g_cy_n[6], (unsigned)g_cy_n[7],
		       (unsigned)g_cy_tot, (unsigned)g_cx_hs);
		printk("W4Z,%u,%u,%u,%u,%u,%u,%u,%u,tot=%u\n",
		       (unsigned)g_cz_n[0], (unsigned)g_cz_n[1],
		       (unsigned)g_cz_n[2], (unsigned)g_cz_n[3],
		       (unsigned)g_cz_n[4], (unsigned)g_cz_n[5],
		       (unsigned)g_cz_n[6], (unsigned)g_cz_n[7],
		       (unsigned)g_cz_tot);
	  }
	}
	{ /* M72: table health + track-1 exact length (a non-multiple of
	   * 256 surviving a power cycle is the PASS) */
	  uint32_t _d72 = 0;
	  (void)uart_line_ctrl_get(cdc, UART_LINE_CTRL_DTR, &_d72);
	  if (_d72)
		printk("M72,x3ok=%u,l0=%u,s0=%u\n", (unsigned)g_x3_ok,
		       (unsigned)trk[0].len_samps, (unsigned)trk[0].start_samps);
	}
	{ /* M71: async-read health, once per diag cycle (deltas) */
	  static uint32_t _p_as, _p_rt, _p_fb; uint32_t _d = 0;
	  (void)uart_line_ctrl_get(cdc, UART_LINE_CTRL_DTR, &_d);
	  if (_d) {
		static uint32_t _p_ca, _p_rq, _p_rd, _p_wu;
		printk("M71,as=%u,rt=%u,fb=%u,ca=%u,rq=%u,rd=%u,wu=%u,ovf=%u\n",
		       (unsigned)(g_m71_as - _p_as),
		       (unsigned)(g_m71_rt - _p_rt),
		       (unsigned)(g_m71_fb - _p_fb),
		       (unsigned)(g_m71_ca - _p_ca),
		       (unsigned)(g_m71_rq - _p_rq),
		       (unsigned)(g_m71_rd - _p_rd),
		       (unsigned)(g_m71_wu - _p_wu), (unsigned)g_prime_ovf);
		_p_as = g_m71_as; _p_rt = g_m71_rt; _p_fb = g_m71_fb;
		_p_ca = g_m71_ca; _p_rq = g_m71_rq; _p_rd = g_m71_rd; _p_wu = g_m71_wu;
	  }
	}
	/* Stream one status line over USB-serial, but ONLY when a host has opened
	 * the port (DTR asserted) — otherwise printk could stall the control loop.
	 * Throttled by the caller. Healthy: tracks PLAY, ovr=0 (no record-buffer
	 * overflow), rerr=0/werr=0 (clean storage bus). */
	uint32_t dtr = 0;
	(void)uart_line_ctrl_get(cdc, UART_LINE_CTRL_DTR, &dtr);
	if (!dtr)
		return;

	static const char *const tsn[] = { "---", "ARM", "REC", "DON", "PLY" };
	int batt = ladder_read(&adc_ladder[LAD_BATT]);   /* raw 12-bit, battery divider */
	uint32_t cpos = g_consume_pos;
	int mg[NTRK];
	for (int _i = 0; _i < NTRK; _i++)
		mg[_i] = (int)((int32_t)(trk[_i].p_w - cpos) / (int)(LOOP_RATE / 1000u));
	/* M25-r4 INSTRUMENTATION (diag only): each track's phase INSIDE its own
	 * loop, start_samps mod len_samps. This number is the one thing a
	 * convergence retune must NOT change — it rescales len_samps for every
	 * track but never touches start_samps, so if the hypothesis is right
	 * this jumps at the retune for any track whose anchor is non-zero.
	 * Track 1 anchors at 0 and is immune, which is why the symptom only
	 * ever showed on an overdub. */
	uint32_t phz[NTRK];
	for (int _i = 0; _i < NTRK; _i++)
		phz[_i] = trk[_i].len_samps
			? (trk[_i].start_samps % trk[_i].len_samps) : 0u;
	printk("LOOPER %dHz song=%d %s hp=%d hpin=%d usb=%d chg=%d batt=%d bpm=%d detbpm=%d vol=%d "
	       "trk[%s %s %s %s] rec=%d mut=%u%u%u%u ovr=%u rerr=%u werr=%u marg=[%d %d %d %d]ms stv=[%u %u %u %u] len=[%u %u %u %u] st=[%u %u %u %u] spim=%d cache=%d ckb=%u wbi=%u chop=%u/%u ph=[%u %u %u %u] anc[cp=%u bkf=%u mod=%u] chain[gbf0=%u grs0=%u gbf1=%u ganc=%u pat=%u] m22[tap=%u rf=%u bf=%u Ls=%u Lb=%u pph=%d sp=%u v=%u cnv=%d/%d snap=%u/%u]\n",
	       (int)LOOP_RATE, (int)g_slot, g_playing ? "PLAY" : "STOP", g_hp_on, g_hp_in,
	       usb_present() ? 1 : 0, charging() ? 1 : 0, batt,
	       g_play_bpm, g_det_bpm, g_master_vol_q8,
	       tsn[trk[0].state % 5], tsn[trk[1].state % 5],
	       tsn[trk[2].state % 5], tsn[trk[3].state % 5],
	       g_rec_track,
	       (unsigned)trk[0].muted, (unsigned)trk[1].muted,
	       (unsigned)trk[2].muted, (unsigned)trk[3].muted,
	       (unsigned)g_rec_overruns,
	       (unsigned)emmc_crc_rd_errs, (unsigned)emmc_crc_wr_errs,
	       mg[0], mg[1], mg[2], mg[3],
	       (unsigned)g_starve_cnt[0], (unsigned)g_starve_cnt[1], (unsigned)g_starve_cnt[2], (unsigned)g_starve_cnt[3],
	       (unsigned)trk[0].len_blocks, (unsigned)trk[1].len_blocks, (unsigned)trk[2].len_blocks, (unsigned)trk[3].len_blocks,
	       (unsigned)trk[0].start_blk, (unsigned)trk[1].start_blk, (unsigned)trk[2].start_blk, (unsigned)trk[3].start_blk,
	       emmc_spim_active() ? 1 : 0, g_cache_on ? 1 : 0, (unsigned)g_cache_kb, (unsigned)emmc_dbg_wr_busy_max,
	       (unsigned)g_chop_div, (unsigned)g_chop_off,
	       (unsigned)phz[0], (unsigned)phz[1], (unsigned)phz[2], (unsigned)phz[3],
	       (unsigned)g_dbg_anc_cp, (unsigned)g_dbg_anc_bkf, (unsigned)g_dbg_anc_mod,
	       (unsigned)g_dbg_gbf0, (unsigned)g_dbg_grs0, (unsigned)g_dbg_gbf1,
	       (unsigned)g_dbg_ganc, (unsigned)g_dbg_pat,
	       (unsigned)g_dbg_tap_bs, (unsigned)g_dbg_rf, (unsigned)g_dbg_bf,
	       (unsigned)g_dbg_lens, (unsigned)g_dbg_lenb,
	       (int)g_dbg_punch_ph, (unsigned)g_dbg_punch_sp, (unsigned)g_dbg_speed,
	       (int)g_dbg_cnv_beats, (int)g_dbg_cnv_corr,
	       (unsigned)g_snap_took, (unsigned)g_snap_took);
	{
		/* CPU= per-thread share of the last window, in percent: audio,
		 * streamer, midi, main, everything-else(usb/idle/isr). Answers
		 * WHERE the cycles actually go when refill can't build surplus. */
		static uint64_t l_aud, l_str, l_mid, l_mai, l_all;
		k_thread_runtime_stats_t rs;
		uint64_t aud = 0, str = 0, mid = 0, mai = 0, all = 0;
		if (!k_thread_runtime_stats_get(&audio_tcb, &rs))    aud = rs.execution_cycles;
		if (!k_thread_runtime_stats_get(&streamer_tcb, &rs)) str = rs.execution_cycles;
		if (!k_thread_runtime_stats_get(&midi_tcb, &rs))     mid = rs.execution_cycles;
		if (!k_thread_runtime_stats_get(k_current_get(), &rs)) mai = rs.execution_cycles;
		if (!k_thread_runtime_stats_all_get(&rs))            all = rs.execution_cycles;
		uint64_t d_all = all - l_all;
		if (d_all) {
			printk("CPU aud=%u%% str=%u%% midi=%u%% main=%u%%\n",
			       (unsigned)((aud - l_aud) * 100u / d_all),
			       (unsigned)((str - l_str) * 100u / d_all),
			       (unsigned)((mid - l_mid) * 100u / d_all),
			       (unsigned)((mai - l_mai) * 100u / d_all));
		}
		l_aud = aud; l_str = str; l_mid = mid; l_mai = mai; l_all = all;
	}
	extern volatile uint32_t emmc_dbg_cmd_retries;
	printk("PASS2 p2=[%u %u %u %u] sn=[%u %u %u %u] ab=%u,%u rt=%u cn=[%u %u %u %u]\n",
	       (unsigned)g_p2blk[0], (unsigned)g_p2blk[1], (unsigned)g_p2blk[2], (unsigned)g_p2blk[3],
	       (unsigned)g_p2snap[0], (unsigned)g_p2snap[1], (unsigned)g_p2snap[2], (unsigned)g_p2snap[3],
	       (unsigned)g_p2yield, (unsigned)g_p2rfail,
	       (unsigned)emmc_dbg_cmd_retries,
	       (unsigned)trk[0].content_blocks, (unsigned)trk[1].content_blocks,
	       (unsigned)trk[2].content_blocks, (unsigned)trk[3].content_blocks);
	for (int _k = 0; _k < 4; _k++) { g_p2blk[_k] = 0; g_p2snap[_k] = 0; }
	g_p2yield = 0; g_p2rfail = 0;
	{
		/* THE stall numbers, finally wall-clock: wus=write-busy window/session
		 * max (us), rus=read-access wait, sus=CMD6 busy (cache flush / future
		 * TRIM+BKOPS), bto=busy-poll expiries, low=worst play margin this
		 * window (ms), hiw=worst rec fill (ms), gl=stored glitches (REPEATING
		 * artifacts), iwf=i2s failures, aus=worst audio-block exec us,
		 * ec=EXT_CSD[167,166,231,502,503,198,246,192,175]. */
		int32_t _lwv = g_play_lowat;
		int _lw = (_lwv == 0x7FFFFFFF) ? -1
			  : (int)(_lwv / (int32_t)(LOOP_RATE / 1000u));
		/* USB live-input health: uu=drain underruns (ring dry at the mixer),
		 * uo=receive overflows (whole 1 ms packet dropped: host over-
		 * delivering), up=ISO packets this window (~2x window-ms expected...
		 * i.e. ~1000/s), ufl=ring fill low,high watermarks in frames
		 * (setpoint ~1024 of 4096), fb=feedback delta from the true rate
		 * (Q10.14 LSBs; 0 = asking exactly for 48000 Hz). */
		static uint32_t _uplast;
		uint32_t _upnow = g_usb_pkts;
		unsigned _updelta = (unsigned)(_upnow - _uplast);
		_uplast = _upnow;
		int32_t _ulw = g_usb_lowat;
		if (_ulw == 0x7FFFFFFF) _ulw = -1;
		int _fbd = (int)((int32_t)atomic_get(&g_fb_value) - (int32_t)FB_TRUE);
		printk("EMMC48 wus=%u/%u rus=%u sus=%u bto=%u low=%dms hiw=%ums gl=%u iwf=%u aus=%u rr=%x flt=%x@%x hi=%u,%u uu=%u uo=%u up=%u ufl=%d,%u fb=%d ec=%02x,%02x,%02x,%02x,%02x,%02x,%02x,%02x,%02x\n",
		       (unsigned)emmc_dbg_wr_busy_us_max, (unsigned)emmc_dbg_wr_busy_us_peak,
		       (unsigned)emmc_dbg_rd_wait_us_max, (unsigned)emmc_dbg_switch_busy_us_max,
		       (unsigned)emmc_dbg_busy_timeouts, _lw,
		       (unsigned)(g_rec_hiwat / (LOOP_RATE / 1000u)),
		       (unsigned)g_stored_glitch_cnt, (unsigned)g_i2s_wfail_cnt,
		       (unsigned)g_audio_us_max,
		       (unsigned)g_resetreas,
		       (unsigned)g_last_fault_reason, (unsigned)g_last_fault_pc,
		       (unsigned)g_hpi_on, (unsigned)emmc_dbg_hpi_fires,
		       (unsigned)g_ring_underruns, (unsigned)g_ring_overflows,
		       _updelta, _ulw, (unsigned)g_usb_hiwat, _fbd,
		       g_extcsd_dump[0], g_extcsd_dump[1], g_extcsd_dump[2],
		       g_extcsd_dump[3], g_extcsd_dump[4], g_extcsd_dump[5],
		       g_extcsd_dump[6], g_extcsd_dump[7], g_extcsd_dump[8]);
	}
	{
		/* USBIN: exact-rate splits for the input path. dt=window ms;
		 * sof/pk/fr = SOF heartbeats, ISO packets, audio frames received
		 * this window (expect dt, dt, 48*dt); nb=packets DROPPED because
		 * the rx pool was empty (MUST stay 0 after the 32-buffer fix);
		 * sl=min free rx buffers (headroom left); zp=silence frames padded
		 * into the live/record path this window (MUST stay 0). */
		static uint32_t _lms, _lsof, _lpk, _lfr, _lnb, _lzp;
		uint32_t _now2 = k_uptime_get_32();
		uint32_t _sof = g_sof_cnt, _pk = g_usb_pkts, _fr = g_usb_frames;
		uint32_t _nb = g_rx_nobuf, _zp = g_zero_pad;
		printk("USBIN dt=%u sof=%u pk=%u fr=%u nb=%u sl=%u zp=%u\n",
		       (unsigned)(_now2 - _lms), (unsigned)(_sof - _lsof),
		       (unsigned)(_pk - _lpk), (unsigned)(_fr - _lfr),
		       (unsigned)(_nb - _lnb), (unsigned)g_rx_slab_min,
		       (unsigned)(_zp - _lzp));
		_lms = _now2; _lsof = _sof; _lpk = _pk; _lfr = _fr;
		_lnb = _nb; _lzp = _zp;
		g_rx_slab_min = 0xFFFF;
	}
	emmc_dbg_wr_busy_max = 0u;   /* per-window worst, reset each print */
	emmc_dbg_wr_busy_us_max = 0u;
	emmc_dbg_rd_wait_us_max = 0u;
	g_play_lowat = 0x7FFFFFFF;
	g_rec_hiwat = 0u;
	g_usb_lowat = 0x7FFFFFFF;
	g_usb_hiwat = 0u;
}

/* ---- decode the ladders into named buttons (verified thresholds) ---- */
enum trk_btn { TRK_NONE = -1, TRK_1, TRK_2, TRK_3, TRK_4, TRK_PLAY };
enum vol_btn { VOL_NONE = -1, VOL_TEMPO_DOWN, VOL_DOWN, VOL_TEMPO_UP, VOL_UP };

static enum trk_btn decode_tracks(int v)
{
	if (v <  110) return TRK_NONE;
	if (v <  300) return TRK_1;     /* ~213  */
	if (v <  560) return TRK_2;     /* ~403  */
	if (v <  950) return TRK_3;     /* ~733  */
	if (v < 1500) return TRK_4;     /* ~1220 */
	return TRK_PLAY;                /* ~1823 */
}

static enum vol_btn decode_vol(int v)
{
	if (v <  200) return VOL_NONE;
	if (v <  560) return VOL_TEMPO_DOWN; /* ~404  */
	if (v <  950) return VOL_DOWN;       /* ~729  */
	if (v < 1500) return VOL_TEMPO_UP;   /* ~1220 */
	return VOL_UP;                       /* ~1820 */
}

/* ================= ALWAYS-DIM LEDs (soft PWM) =========================
 * Adapted unchanged from TechnicsOP's dimmed-LED build (shared on the SP-1
 * Discord 2026-07-15, MIT) — merged into this fork as ALWAYS-ON dimming.
 * The panel LEDs are plain on/off GPIO with no current control, so "dim" =
 * software PWM: every LED write (led_service, sweeps, gauges, our two-light
 * song display) goes into a shadow mask; a tiny TIMER3 ISR renders that
 * shadow at a low duty cycle. Single writer (control thread), ISR only
 * reads. ~1 kHz frame = flicker-free. LED_PWM_ON_US is the brightness. */
#define LED_PWM_PERIOD_US 1000u    /* 1 kHz frame */
#define LED_PWM_ON_US       52u    /* ~5.2% duty — v1.2.2: a hair dimmer than
                                    * the old 60 on the track row. Floor: at
                                    * 6 us, IRQ-entry jitter of +/-3 us is a
                                    * 10-80x brightness swing = flicker; at
                                    * 36 us it is +/-8% before the eye's ~10-
                                    * frame averaging — invisible. */
#define LED_STATUS_ON_US    66u    /* the SONG/status row runs a longer window
                                    * than the track row: slightly brighter
                                    * side lights relative to the tracks. CC2
                                    * mechanism, wide-window = jitter-immune. */
#define LED_GHOST_FRAME_DIV  5u    /* GHOST class: muted-but-loaded tracks lit
                                    * ONE frame in five using the SAME proven
                                    * 60 us window as normal dim -> 1/5 of dim
                                    * brightness (~1.2% of solid), refresh 200 Hz
                                    * (still far above flicker perception), ZERO
                                    * new edge timing. History: an 8 us second
                                    * CC window flickered (two independent IRQ
                                    * entry jitters on a narrow width) and a
                                    * 20 us in-ISR capture-spin failed to boot
                                    * on hardware — this design reuses only
                                    * field-proven mechanisms. */
#define LED_PWM_TIMER      NRF_TIMER3
#define LED_PWM_TIMER_IRQn TIMER3_IRQn
/* every LED pin on each port (leds[]+track_leds[]) — for the OFF phase */
#define LED_ALL_P0 ((1u<<0)|(1u<<1)|(1u<<29)|(1u<<26))
#define LED_ALL_P1 ((1u<<13)|(1u<<12)|(1u<<15)|(1u<<14))
static volatile uint32_t g_led_p0_on;   /* P0 LED pins logically lit */
static volatile uint32_t g_led_p1_on;   /* P1 LED pins logically lit */
static volatile uint32_t g_led_p0_ghost; /* P0 pins lit at GHOST duty */
static volatile uint32_t g_led_p1_ghost; /* P1 pins lit at GHOST duty */
static uint32_t g_led_sta_p0, g_led_sta_p1;   /* status-row pins (init-computed) */
static uint32_t g_led_trk_p0, g_led_trk_p1;   /* track-row pins  (init-computed) */

/* DIRECT ISR (required for IRQ_ZERO_LATENCY): pure register IO, no kernel
 * calls, returns 0 = never asks for a reschedule. */
ISR_DIRECT_DECLARE(led_pwm_isr)
{
	if (LED_PWM_TIMER->EVENTS_COMPARE[1]) {         /* period wrap: render shadow */
		LED_PWM_TIMER->EVENTS_COMPARE[1] = 0;
		(void)LED_PWM_TIMER->EVENTS_COMPARE[1];
		static uint32_t gframe;
		/* M19a-r3: in DIM mode the ghost drops to 1-in-8 frames — at
		 * 1/5 the muted glow read too close to a playing light there
		 * (marc); full-brightness mode keeps 1/5, where the contrast
		 * was already right. 125 Hz refresh, still above flicker. */
		uint32_t gdiv = g_led_dim ? 8u : LED_GHOST_FRAME_DIV;
		uint32_t gon = ((++gframe % gdiv) == 0u);
		uint32_t s0 = g_led_p0_on | (gon ? (g_led_p0_ghost & ~g_led_p0_on) : 0u);
		uint32_t s1 = g_led_p1_on | (gon ? (g_led_p1_ghost & ~g_led_p1_on) : 0u);
		NRF_P0->OUTSET = s0;
		NRF_P0->OUTCLR = LED_ALL_P0 & ~s0;
		NRF_P1->OUTSET = s1;
		NRF_P1->OUTCLR = LED_ALL_P1 & ~s1;
	}
	if (LED_PWM_TIMER->EVENTS_COMPARE[0]) {         /* track-row on-time up */
		LED_PWM_TIMER->EVENTS_COMPARE[0] = 0;
		(void)LED_PWM_TIMER->EVENTS_COMPARE[0];
		if (g_led_dim) {                        /* dim: track row goes dark;
		                                         * the status row stays lit
		                                         * until CC2. Full mode: only
		                                         * ghost pins go dark. */
			NRF_P0->OUTCLR = g_led_trk_p0;
			NRF_P1->OUTCLR = g_led_trk_p1;
		} else {
			NRF_P0->OUTCLR = g_led_p0_ghost & ~g_led_p0_on;
			NRF_P1->OUTCLR = g_led_p1_ghost & ~g_led_p1_on;
		}
	}
	if (LED_PWM_TIMER->EVENTS_COMPARE[2]) {         /* status-row on-time up */
		LED_PWM_TIMER->EVENTS_COMPARE[2] = 0;
		(void)LED_PWM_TIMER->EVENTS_COMPARE[2];
		if (g_led_dim) {
			NRF_P0->OUTCLR = g_led_sta_p0;
			NRF_P1->OUTCLR = g_led_sta_p1;
		}
	}
	return 0;
}

static void led_pwm_init(void)
{
	LED_PWM_TIMER->MODE      = TIMER_MODE_MODE_Timer;
	LED_PWM_TIMER->BITMODE   = TIMER_BITMODE_BITMODE_16Bit;
	LED_PWM_TIMER->PRESCALER = 4;                    /* 16 MHz/16 = 1 us tick */
	LED_PWM_TIMER->CC[0]     = LED_PWM_ON_US;        /* -> OFF phase */
	LED_PWM_TIMER->CC[1]     = LED_PWM_PERIOD_US;    /* -> wrap + ON phase */
	LED_PWM_TIMER->CC[2]     = LED_STATUS_ON_US;     /* -> status-row OFF */
	LED_PWM_TIMER->SHORTS    = TIMER_SHORTS_COMPARE1_CLEAR_Msk;
	LED_PWM_TIMER->INTENSET  = TIMER_INTENSET_COMPARE0_Msk |
				   TIMER_INTENSET_COMPARE1_Msk |
				   TIMER_INTENSET_COMPARE2_Msk;
	for (int li = 0; li < NUM_LEDS; li++) {
		if (leds[li].port == NRF_P0) g_led_sta_p0 |= (1u << leds[li].pin);
		else                         g_led_sta_p1 |= (1u << leds[li].pin);
	}
	for (int li = 0; li < NUM_TRACK_LEDS; li++) {
		if (track_leds[li].port == NRF_P0) g_led_trk_p0 |= (1u << track_leds[li].pin);
		else                               g_led_trk_p1 |= (1u << track_leds[li].pin);
	}
	IRQ_DIRECT_CONNECT(LED_PWM_TIMER_IRQn, 0, led_pwm_isr, IRQ_ZERO_LATENCY);
	irq_enable(LED_PWM_TIMER_IRQn);
	LED_PWM_TIMER->TASKS_CLEAR = 1;
	LED_PWM_TIMER->TASKS_START = 1;
}

/* ---------- LED helpers ---------- */
static void led_cfg_output(const struct led *l)
{
	l->port->PIN_CNF[l->pin] =
		(GPIO_PIN_CNF_DIR_Output    << GPIO_PIN_CNF_DIR_Pos)   |
		(GPIO_PIN_CNF_DRIVE_S0S1    << GPIO_PIN_CNF_DRIVE_Pos) |
		(GPIO_PIN_CNF_INPUT_Connect << GPIO_PIN_CNF_INPUT_Pos);
}
static void led_on(int i)
{
	if (leds[i].port == NRF_P0) g_led_p0_on |= (1u << leds[i].pin);
	else                        g_led_p1_on |= (1u << leds[i].pin);
}
static void led_off(int i)
{
	if (leds[i].port == NRF_P0) g_led_p0_on &= ~(1u << leds[i].pin);
	else                        g_led_p1_on &= ~(1u << leds[i].pin);
}
static void all_off(void)  { for (int i = 0; i < NUM_LEDS; i++) led_off(i); }
/* Status row = song indicator, 16 songs via TWO LIGHTS ("scheme E", chosen
 * in the LED lab): the POSITION LED (song % 4) is SOLID, and the BANK LED
 * (song / 4) BLINKS ~2 Hz (250 ms on/off). When position == bank — songs 1,
 * 6, 11 and 16 — one LED carries both roles and simply BLINKS ~2 Hz: "only
 * one light, and it blinks" reads as position-and-bank-agree.
 * Read it as: "the steady light says where in the bank, the blinking light
 * says which bank." Pure function of (g_slot, uptime): no state, no
 * blocking, ~8 ms resolution. (Same LEDs the power on/off sweep uses.) */
static void show_song_leds(void)
{
	uint32_t slot = g_slot;                 /* volatile: read once */
	uint32_t pos  = slot & 3u;              /* slot % 4 */
	uint32_t bank = slot >> 2;              /* 0..3 */
	uint32_t t    = k_uptime_get_32();
	/* Bank-blink phase: fixed ~2 Hz normally; with a TAPPED GRID the blink
	 * locks to the beat (on for the first half of each beat, off for the
	 * second — 50% duty keeps "which bank" as readable as the 2 Hz square,
	 * unlike the brief 1/8-beat track pulses). The whole face keeps time. */
	int blink = ((t / 250u) & 1u) == 0u;
	if (g_grid_active && g_grid_beat_frames) {
		uint64_t ph = g_sample_clock - g_grid_anchor;
		blink = ((uint32_t)(ph % g_grid_beat_frames) <
		         g_grid_beat_frames / 2u);
	}
	for (int i = 0; i < NUM_LEDS; i++) {
		int on;
		if ((uint32_t)i == pos && pos == bank)
			on = blink;                     /* both roles: same blink */
		else if ((uint32_t)i == pos)
			on = 1;                         /* position: solid */
		else if ((uint32_t)i == bank)
			on = blink;                     /* bank: blink */
		else
			on = 0;
		on ? led_on(i) : led_off(i);
	}
}

static void track_led_on(int i)
{
	if (track_leds[i].port == NRF_P0) { g_led_p0_on |= (1u << track_leds[i].pin);
	                                    g_led_p0_ghost &= ~(1u << track_leds[i].pin); }
	else                              { g_led_p1_on |= (1u << track_leds[i].pin);
	                                    g_led_p1_ghost &= ~(1u << track_leds[i].pin); }
}
static void track_led_off(int i)
{
	if (track_leds[i].port == NRF_P0) { g_led_p0_on &= ~(1u << track_leds[i].pin);
	                                    g_led_p0_ghost &= ~(1u << track_leds[i].pin); }
	else                              { g_led_p1_on &= ~(1u << track_leds[i].pin);
	                                    g_led_p1_ghost &= ~(1u << track_leds[i].pin); }
}
/* GHOST: barely-lit = this track HAS content but is muted (sleeping). The
 * fix for "muted and empty look identical" — community request. */
static void track_led_ghost(int i)
{
	if (track_leds[i].port == NRF_P0) { g_led_p0_ghost |= (1u << track_leds[i].pin);
	                                    g_led_p0_on &= ~(1u << track_leds[i].pin); }
	else                              { g_led_p1_ghost |= (1u << track_leds[i].pin);
	                                    g_led_p1_on &= ~(1u << track_leds[i].pin); }
}
static void track_all_off(void)  { for (int i = 0; i < NUM_TRACK_LEDS; i++) track_led_off(i); }

/* Clear BOTH LED rows. Used on power-off so nothing is left lit when SYSTEM_OFF
 * freezes the GPIO levels (the old power_off cleared only the status row, which
 * is exactly why the track/fader lights stayed on after powering down). */
static void shutdown_leds(void)
{
	all_off(); track_all_off();          /* clear the shadow */
	LED_PWM_TIMER->TASKS_STOP = 1;       /* stop the dimmer */
	NRF_P0->OUTCLR = LED_ALL_P0;         /* force every LED pin low */
	NRF_P1->OUTCLR = LED_ALL_P1;
}

/* The single owner of the LEDs in normal running. Status row = song indicator.
 * Track row = per-track looper state (rec solid / armed blink / playing pulse),
 * OR — when no host audio is streaming AND nothing is recorded — a calm "standby"
 * chase so the device clearly reads as on-and-waiting instead of four dead LEDs.
 * As soon as a host streams audio or a loop exists, it falls through to state. */
static void led_service(void)
{
	/* The standby chase means "never used yet": it shows until the FIRST time a
	 * host streams audio (or anything is recorded) and then never returns. A
	 * live host-presence gate flickered the chase mid-session whenever the
	 * player closed the stream between songs / on pause. */
	static int ever_streamed;
	if (g_usb_streaming) ever_streamed = 1;

	show_song_leds();                              /* status row = current song */

	int active = g_loop_active;
	for (int i = 0; i < NTRK; i++)
		if (trk[i].state != TS_EMPTY) active = 1;

	if (g_pg_open) {
		/* PG-533/LS-534: the MODE PAGE view -- each track LED shows
		 * its NEXT-record mode live: BLINK = stereo, SOLID = mono
		 * (marc's call: mono is the special state, it gets the
		 * steady light). */
		uint32_t _ph = (k_uptime_get_32() >> 7) & 1u;
		for (int i = 0; i < NUM_TRACK_LEDS; i++) {
			uint8_t _on = trk[i].p16m_next ? 1u : (uint8_t)_ph;
			if (_on) track_led_on(i); else track_led_off(i);
		}
	} else if (g_snap_sweep) {
		/* M23-r5 THE HOOK. A one-shot nudge deserves a one-shot picture:
		 * the row sweeps BACK AND FORTH — hunting, not yet sure — and
		 * then catches the beat and rides it BACKWARD, hand-in-hand,
		 * before letting go. It reads as "found it, locked, done", and
		 * because nothing persists afterwards there is no mode to
		 * explain. Sits above standby and the metronome: those own the
		 * whole row unconditionally and would overwrite it. */
		/* It sweeps, then it HUNTS FOR THE BEAT AND STOPS ON IT. The
		 * row bounces 1-2-3-4-3-2-1-2... off a single index, two
		 * frames per LED so the turnaround is not a stall (r8 split
		 * it in two and the shared end LED held double). From the
		 * second bounce on, every frame asks whether the walking LED
		 * is the one the grid is on RIGHT NOW, and the first time it
		 * is, the sweep ends there. led_service falls straight
		 * through to the metronome, already lit on that same LED, so
		 * there is no jump: the hunt catches the beat and the beat
		 * carries on. The walker steps ~9x faster than the beat, so a
		 * catch inside one bounce is certain; 48 is only a floor. */
		uint32_t sstep = (uint32_t)(48u - g_snap_sweep) / 2u;
		uint32_t sp_   = sstep % 6u;
		uint32_t lit   = (sp_ <= 3u) ? sp_ : (6u - sp_);
		int sgb = -1;
		if (g_grid_active && g_grid_beat_frames)
			sgb = (int)(((g_sample_clock - g_grid_anchor) /
				g_grid_beat_frames) & 3u);
		for (int i = 0; i < NUM_TRACK_LEDS; i++)
			((uint32_t)i == lit) ? track_led_on(i) : track_led_off(i);
		if (sstep >= 6u && sgb >= 0 && (uint32_t)sgb == lit) g_snap_sweep = 0;
		else g_snap_sweep--;
	} else if (g_led_shrug) {
		/* M25-r12 THE SHRUG, HOISTED. It used to be handled INSIDE the
		 * per-track LED loop, which only runs once something is
		 * recorded or audio has streamed. But the snap declines while
		 * you are still SETTING UP a grid — nothing recorded, no input
		 * — so the standby chase owned the row, the shrug was never
		 * drawn, and it never decremented either. It sat at 20 until
		 * the first track was armed and then drained all at once at
		 * the ~8 ms released cadence: a 15 Hz flicker arriving long
		 * after the gesture that caused it. This is EXACTLY the bug
		 * the snap sweep had in M23, hoisted for exactly the same
		 * reason: anything that answers a GESTURE has to outrank the
		 * ambient displays, because the gesture can happen while they
		 * own the row. (The copy still inside the per-track loop is
		 * now unreachable and harmless; the bounce's shrug comes
		 * through here too and gets the same guarantee.) */
		uint32_t son = (g_led_shrug >> 2) & 1u;
		for (int i = 0; i < NUM_TRACK_LEDS; i++)
			son ? track_led_on(i) : track_led_off(i);
		g_led_shrug--;
	} else if (!ever_streamed && !active) {
		/* STANDBY: no audio in + nothing recorded -> gentle chase = "waiting" */
		static uint32_t ch;
		uint32_t pos = (ch++ / 40u) % NUM_TRACK_LEDS;   /* advance ~every 320 ms */
		for (int i = 0; i < NUM_TRACK_LEDS; i++)
			((uint32_t)i == pos) ? track_led_on(i) : track_led_off(i);
	} else {
		int on_beat = (g_beat_phase < (BEAT_SAMPLES_L / 8u));
		int gbeat = -1;            /* tapped grid: beat 0..3 within the bar */
		if (g_grid_active && g_grid_beat_frames) {
			uint64_t ph = g_sample_clock - g_grid_anchor;
			uint32_t bf = g_grid_beat_frames;
			gbeat  = (int)((ph / bf) & 3u);
			on_beat = ((uint32_t)(ph % bf) < bf / 8u);  /* grid outranks
			                                             * the take beat */
		}
		int loaded = 0;
		for (int i = 0; i < NUM_TRACK_LEDS; i++)
			if (trk[i].state != TS_EMPTY) loaded = 1;
		if (gbeat >= 0 && !loaded) {
			/* gridded song, nothing recorded yet: 1-2-3-4 metronome
			 * chase (downbeat = LED 1) — the tapped grid made visible.
 */
			for (int i = 0; i < NUM_TRACK_LEDS; i++)
				((i == gbeat) && on_beat) ? track_led_on(i)
				                          : track_led_off(i);
		} else for (int i = 0; i < NUM_TRACK_LEDS; i++) {
			uint8_t st = trk[i].state;
			if (g_led_shrug) {   /* M19b: the "no" — all four double-blink */
				(((g_led_shrug >> 2) & 1u) ? track_led_on(i)
				                           : track_led_off(i));
				if (i == NUM_TRACK_LEDS - 1) g_led_shrug--;
				continue;
			}
			if ((g_bnc_active || g_bnc_req >= 0) && g_heads_mode &&
			    i == (int)bnc_dst) {
				/* M19b: printing — the destination fast-blinks */
				(((k_uptime_get() >> 7) & 1) ? track_led_on(i)
				                             : track_led_off(i));
				continue;
			}
			if (st == TS_REC && trk[i].rec_target && !trk[i].rec_silence &&
			    g_grid_active && g_grid_beat_frames) {
				/* grid run-on ("finishing the beat"): double-blink so
				 * continued recording reads deliberate, not stuck */
				uint64_t ph3 = g_sample_clock - g_grid_anchor;
				uint32_t hb2 = g_grid_beat_frames / 2u;
				((hb2 && (uint32_t)(ph3 % hb2) < hb2 / 4u)
					? track_led_on(i) : track_led_off(i));
			}
			else if (st == TS_REC || st == TS_DONE) track_led_on(i);
			else if (st == TS_ARMED) {
				int ab = on_beat;
				if (g_grid_punch_at && g_grid_active && g_grid_beat_frames) {
					/* waiting for the punch-in: blink at HALF-beat
					 * rate — clearly alive, clearly on purpose */
					uint64_t ph2 = g_sample_clock - g_grid_anchor;
					uint32_t hb = g_grid_beat_frames / 2u;
					if (hb) ab = ((uint32_t)(ph2 % hb) < hb / 4u);
				}
				(ab ? track_led_on(i) : track_led_off(i));
			}
			else if ((st == TS_PLAY || head_active(i)) && !trk[i].muted && !g_playing)
				track_led_on(i);   /* stopped: content reads solid, not
				                    * frozen-dark like an empty track */
			else if ((st == TS_PLAY || head_active(i)) && !trk[i].muted) {
				/* M12 (community ask): PER-TRACK WRAP PULSES when there
				 * is no grid. All four playing lights used to pulse in
				 * unison off one beat clock — four LEDs, one bit. Now
				 * each light pulses as ITS OWN loop wraps (chop-aware:
				 * the audible cycle is len/div in both modes), so
				 * different-length loops literally paint their
				 * polyrhythm on the panel. Gridded songs keep the
				 * shared grid pulse — there the point IS the one clock.
				 * Long loops get a capped ~2-beat flash at each wrap
				 * instead of a 1/8-duty minute-long glow. */
				int tp = on_beat;
				if (!g_grid_active || heads_engaged()) {
					/* M13: heads pulse against the SOURCE loop, each
					 * offset a quarter — the four lights chase in
					 * canon, matching what you hear. Heads ENGAGED
					 * overrides the gridded shared pulse too: in
					 * heads mode the canon is the clock. */
					struct looptrk *hs2 = head_active(i) ? &trk[g_head_src]
					                                     : &trk[i];
					uint32_t gb2 = hs2->len_blocks ? hs2->len_blocks
						     : (g_loop_blocks ? g_loop_blocks : 1u);
					uint32_t dv2 = g_chop_div ? g_chop_div : 1u;
					uint32_t cyc2 = g_win_free
						      ? ((gb2 * ((uint32_t)(g_win_e8 - g_win_s8) + 1u)) >> 8)
						      : gb2 / dv2;
					if (cyc2 == 0u) cyc2 = 1u;
					uint32_t ho2 = heads_engaged()
					             ? (((uint32_t)g_head_pos[i] * cyc2) >> 8) : 0u;
					uint32_t pwb2 = (uint32_t)(g_consume_pos / SAMP_PER_BLK);
					uint32_t c2 = ((pwb2 % cyc2) + cyc2 -
						       (hs2->start_blk % cyc2) + ho2) % cyc2;
					{
						int rv2 = g_win_rev ? 1 : 0;
						if (heads_engaged() && g_head_rev[i]) rv2 ^= 1;
						if (rv2)
							c2 = (cyc2 - 1u) - c2;   /* chase walks back */
					}
					uint32_t onw = cyc2 / 8u;
					if (onw < 1u) onw = 1u;
					if (onw > 280u) onw = 280u;   /* ~2 beats */
					tp = (c2 < onw);
				}
				/* M19b-r2: a HOLLOW head (nothing underneath) chases
				 * at GHOST intensity — faint = printable, so you can
				 * see the bounce targets mid-performance without
				 * remembering the song from before entry. Consistent
				 * with dark = empty outside heads mode. */
				if (head_active(i) && trk[i].state == TS_EMPTY &&
				    !(g_slot < NUM_SLOTS &&
				      g_meta.slot[g_slot].present[i]))
					(tp ? track_led_ghost(i) : track_led_off(i));
				else
					(tp ? track_led_on(i) : track_led_off(i));
			}
			else if ((st == TS_PLAY || head_active(i)) && trk[i].muted)
				track_led_ghost(i);
			else                                    track_led_off(i);
		}
	}
}

/* FN+PLAY mode toggle (v1.2.2: fires on PLAY RELEASE, 0.7-5 s of hold —
 * holding through 5 s becomes the brightness toggle instead). M7c two-layer
 * semantics + the LED confirm, verbatim from the old in-hold body. */
static void feed_wdt(void);
static void fnp_mode_toggle(void)
{
	g_fixed_len ^= 1u;
	{
		int has = 0;
		for (int k = 0; k < NTRK; k++)
			if (trk[k].state != TS_EMPTY ||
			    (g_slot < NUM_SLOTS &&
			     g_meta.slot[g_slot].present[k]))
				has = 1;
		if (has && g_slot < NUM_SLOTS) {
			g_meta.song_mode[g_slot] = (uint8_t)
				((g_meta.song_mode[g_slot] & 0xF0u) |
				 (g_fixed_len ? 2u : 1u));
		} else {
			g_mode_pref = g_fixed_len;
			g_meta.fixed_len = g_fixed_len;
		}
	}
	g_meta_save_req = 1;
	all_off(); track_all_off();
	if (g_fixed_len) {
		for (int r = 0; r < 2; r++) {
			for (int i = 0; i < NUM_LEDS; i++) led_on(i);
			feed_wdt(); k_msleep(150);
			for (int i = 0; i < NUM_LEDS; i++) led_off(i);
			feed_wdt(); k_msleep(120);
		}
	} else {
		for (int i = 0; i < NUM_LEDS; i++) {
			led_on(i); feed_wdt(); k_msleep(110); led_off(i);
		}
		for (int i = NUM_LEDS - 2; i >= 0; i--) {
			led_on(i); feed_wdt(); k_msleep(90); led_off(i);
		}
	}
	all_off();
}

/* ---------- watchdog ---------- */
static void feed_wdt(void)
{
	for (int ch = 0; ch < 8; ch++)
		NRF_WDT->RR[ch] = WDT_RR_RR_Reload;
}

/* ---------- power button ---------- */
static bool pwr_pressed(void)
{
	return (PWR_PORT->IN & (1u << PWR_PIN)) == 0u;   /* low = pressed */
}

static void pwr_btn_cfg_input(void)
{
	PWR_PORT->PIN_CNF[PWR_PIN] =
		(GPIO_PIN_CNF_DIR_Input     << GPIO_PIN_CNF_DIR_Pos)  |
		(GPIO_PIN_CNF_PULL_Pullup   << GPIO_PIN_CNF_PULL_Pos) |
		(GPIO_PIN_CNF_INPUT_Connect << GPIO_PIN_CNF_INPUT_Pos);
}

/* arm the button to wake the chip out of SYSTEM_OFF (sense the low level) */
static void pwr_btn_arm_wake(void)
{
	PWR_PORT->PIN_CNF[PWR_PIN] =
		(GPIO_PIN_CNF_DIR_Input     << GPIO_PIN_CNF_DIR_Pos)  |
		(GPIO_PIN_CNF_PULL_Pullup   << GPIO_PIN_CNF_PULL_Pos) |
		(GPIO_PIN_CNF_INPUT_Connect << GPIO_PIN_CNF_INPUT_Pos)|
		(GPIO_PIN_CNF_SENSE_Low     << GPIO_PIN_CNF_SENSE_Pos);
}

/* ========================================================================
 *  POWER / PERSISTENCE  —  battery charger control, the graceful
 *  stop_and_flush() (finalize any take, then flush the card's volatile write
 *  cache so loops + the slot index survive a power cut), power_off() ->
 *  SYSTEM_OFF (clean return to the bootloader; there is no reset pin),
 *  enter_dfu() (a track combo forces the bootloader for reflashing), and
 *  song-slot switching.
 * ======================================================================== */
/* ---------- battery charger ---------- */
/* Explicitly enable charging by driving the BQ24232 /CE pin low, and set the
 * two status pins as inputs with pull-ups (they are open-drain on the charger). */
static void charger_init(void)
{
	BQ_PORT->PIN_CNF[BQ_NCHG_PIN] =
		(GPIO_PIN_CNF_DIR_Input     << GPIO_PIN_CNF_DIR_Pos)  |
		(GPIO_PIN_CNF_PULL_Pullup   << GPIO_PIN_CNF_PULL_Pos) |
		(GPIO_PIN_CNF_INPUT_Connect << GPIO_PIN_CNF_INPUT_Pos);
	BQ_PORT->PIN_CNF[BQ_NPGOOD_PIN] =
		(GPIO_PIN_CNF_DIR_Input     << GPIO_PIN_CNF_DIR_Pos)  |
		(GPIO_PIN_CNF_PULL_Pullup   << GPIO_PIN_CNF_PULL_Pos) |
		(GPIO_PIN_CNF_INPUT_Connect << GPIO_PIN_CNF_INPUT_Pos);

	BQ_PORT->OUTCLR = (1u << BQ_NCE_PIN);          /* drive low first  */
	BQ_PORT->PIN_CNF[BQ_NCE_PIN] =
		(GPIO_PIN_CNF_DIR_Output    << GPIO_PIN_CNF_DIR_Pos)  |
		(GPIO_PIN_CNF_DRIVE_S0S1    << GPIO_PIN_CNF_DRIVE_Pos)|
		(GPIO_PIN_CNF_INPUT_Connect << GPIO_PIN_CNF_INPUT_Pos);
	BQ_PORT->OUTCLR = (1u << BQ_NCE_PIN);          /* /CE low = charge enabled */
}

/* BQ24232 status (per the SP-1-dev wiki): open-drain, LOW = active */
static bool usb_present(void)
{
	return (BQ_PORT->IN & (1u << BQ_NPGOOD_PIN)) == 0u;   /* low = USB power good */
}
static bool charging(void)
{
	return (BQ_PORT->IN & (1u << BQ_NCHG_PIN)) == 0u;     /* low = charging */
}

/* ---------- graceful stop before power-off / DFU ----------
 * If a take is mid-record, end it and give the streamer a bounded window to
 * flush the rec ring and persist the song metadata, so powering off or dropping
 * into the bootloader can't lose the loop or its saved BPM/length. WDT-fed. */
static void stop_and_flush(void)
{
	g_stop_req = 1;                       /* finalize any in-progress take */
	/* M39: stamp the live tape speed into the song index before the final
	 * flush. The only other copy happens on song SWITCH, so a tempo set
	 * and powered straight off reverted to the last saved value — while
	 * switching songs first made it stick (confirmed on hardware, both
	 * ways). Every save trigger (take end, delete, brightness) wrote a
	 * stale slot speed. The busy wait below already blocks until
	 * g_meta_save_req is serviced, so this is one index write at
	 * power-off and nothing anywhere else. */
	if (g_meta_loaded && g_slot < NUM_SLOTS &&
	    g_meta.slot[g_slot].speed_q16 != g_play_speed_q16) {
		g_meta.slot[g_slot].speed_q16 = g_play_speed_q16;
		g_meta_save_req = 1;
	}
	for (int i = 0; i < 300; i++) {      /* bounded ~3 s (WDT is 4 s, fed each pass) */
		feed_wdt();
		int busy = (g_rec_track >= 0) || g_meta_save_req;
		for (int t = 0; t < NTRK; t++)
			if (trk[t].state == TS_REC || trk[t].state == TS_DONE) busy = 1;
		if (!busy) break;
		k_msleep(10);
	}
	/* Now flush the card's volatile write cache so the just-finished take + the
	 * slot index are durable across the power cut. The recording is finalized and
	 * we're shutting down, so the bus-blocking flush has nothing live to starve.
	 * The streamer (only eMMC user) does it; we wait, feeding the WDT. */
	if (g_cache_on) {
		g_cache_flush_req = 1;
		for (int i = 0; i < 1000 && g_cache_flush_req; i++) {  /* bounded ~10 s (flush itself is allowed 8 s) */
			feed_wdt();
			k_msleep(10);
		}
	}
}

/* ---------- power off ---------- */
static void power_off(void)
{
	g_off_fade = 1;                      /* M10: fade the outputs (~85 ms) so the
	                                      * codecs power down on silence — the
	                                      * fade completes during the flush and
	                                      * LED sweep below */
	stop_and_flush();                    /* never lose an in-progress recording */

	/* shutdown sweep across BOTH rows, then force EVERY LED dark before
	 * SYSTEM_OFF latches the GPIO levels. Clearing BOTH rows is the fix for the
	 * track/fader lights staying lit after power-off (the old code cleared only
	 * the status row, so the track row froze on into sleep). */
	for (int i = NUM_LEDS - 1; i >= 0; i--) {
		led_off(i); track_led_off(i);
		feed_wdt();
		k_msleep(80);
	}
	shutdown_leds();

	/* Wait for the finger to come off the button first, otherwise the
	 * level-sense we are about to arm would instantly wake us again. */
	while (pwr_pressed()) {
		feed_wdt();
		k_msleep(20);
	}
	k_msleep(60);             /* debounce the release */

	shutdown_leds();          /* re-assert dark immediately before sleep */

	/* POWER DOWN THE EXTERNAL CHIPS. SYSTEM_OFF only stops the nRF — the
	 * speaker amp, the headphone codec and the eMMC I/O rail are separate
	 * chips, and the retained GPIO levels would otherwise keep them powered
	 * for days: the "battery drains overnight" reports. A powered amp whose
	 * clock has been removed can also murmur on its own — the "sound after
	 * shutdown" reports. Order: amp first, then codec, then the flash rail
	 * (its cache was flushed in stop_and_flush above). */
	/* M10: the mix has been silent for a while (fade above); now put both
	 * output stages in their own MUTE — registers our init already uses —
	 * so the drivers discharge quietly instead of stepping to ground
	 * (the power-off pop, user report). */
	(void)cs42_wr16(0x2001, 0x0D);   /* CS42L42 HP Control: mute all */
	tas_page(0x01);
	(void)tas_wr(0x30, 0x00);        /* TAS2505 Class-D driver: mute (P1/R48) */
	feed_wdt();
	k_msleep(30);
	tas_page(0x00);
	(void)tas_wr(0x01, 0x01);        /* TAS2505 software reset: every block
	                                  * back to its powered-down default */
	gpio_drive_low(CS42_RST_PORT, CS42_RST_PIN);   /* CS42L42 held in reset */
	emmc_power_down();               /* bus pins released, VCCQ rail off */

	gpio_drive_low(OSC_EN_PORT, OSC_EN_PIN);   /* osc off: it would otherwise
	                              keep drawing battery through SYSTEM_OFF */
	pwr_btn_arm_wake();
	feed_wdt();
	if (usb_present()) {
		/* v1.2.4: powering OFF while PLUGGED lands in the charge-standby
		 * gauge, exactly like plugging in an off device. SYSTEM_OFF with
		 * VBUS already high has no wake edge — the device just went dark
		 * until a replug (user request). A clean soft reset boots into
		 * standby instead: RESETREAS is cleared every boot, so only SREQ
		 * is set and the standby gate (!(OFF|DOG)) admits it; the external
		 * chips we just powered down stay down through standby, same as a
		 * cold plug-in. Unplugging from that standby SYSTEM_OFFs cleanly. */
		NVIC_SystemReset();
	}
	NRF_POWER->RESETREAS = 0xFFFFFFFFu;   /* best practice before SYSTEM_OFF */
	__DSB();
	NRF_POWER->SYSTEMOFF = 1u;
	__DSB();
	for (;;) { /* CPU is now off; wakes via the bootloader on button press */ }
}

/* FAILSAFE recovery: reset into the bootloader so the device can ALWAYS be
 * reflashed. Triggered by holding Track1+Track4 together (the same combo the
 * bootloader scans for at boot). We flush any recording first, then show a clean
 * cue (status row dark, all 4 track LEDs lit = "loading firmware"), write the
 * UF2 magic (harmless if the bootloader ignores it) and reset; the user keeps
 * holding 1+4 through the reset and the bootloader's own button scan enters DFU. */
static void enter_dfu(void)
{
	stop_and_flush();
	all_off();                                                 /* status row dark */
	for (int i = 0; i < NUM_TRACK_LEDS; i++) track_led_on(i);  /* 4 track LEDs = DFU */
	NRF_POWER->GPREGRET = 0x57u;
	__DSB();
	NVIC_SystemReset();
	for (;;) { }
}

/* Jump to song slot ns (M4b: FUNCTION+Track bank jump, and the tap-advance).
 * Saves the current song's BPM, loads the target's, signals the audio thread
 * to reload that slot's tracks. Refuses while a take is armed/recording/
 * flushing — the reload would trample the take and strand unflushed audio. */
static void jump_to_slot(uint32_t ns)
{
	if (!g_meta_loaded || g_slot_switch_req) return;    /* ignore until the last switch lands */
	if (g_rec_track >= 0) return;
	for (int i = 0; i < NTRK; i++) {
		uint8_t st = trk[i].state;
		if (st == TS_ARMED || st == TS_REC || st == TS_DONE) return;
	}
	if (ns >= NUM_SLOTS) return;
	if (g_slot >= NUM_SLOTS) g_slot = 0;
	if (ns == g_slot) return;
	g_meta.slot[g_slot].speed_q16 = g_play_speed_q16;   /* remember where you left it */
	g_meta.cur_slot = ns;
	g_slot = ns;
	g_play_speed_q16 = g_meta.slot[ns].speed_q16;        /* resume the new song's BPM */
	g_play_bpm = (int)(((uint64_t)g_play_speed_q16 * LOOP_BPM_BASE + 32768u) / 65536u);
	if (g_play_bpm < BPM_MIN) g_play_bpm = BPM_MIN;
	if (g_play_bpm > BPM_MAX) g_play_bpm = BPM_MAX;
	{	/* M7: restore the target song's persisted chop + effective mode */
		uint32_t cd = g_meta.chop[ns][0]; if (cd < 1u || cd > 64u) cd = 1u;
		uint32_t co = g_meta.chop[ns][1]; if (co >= cd) co = 0u;
		g_chop_div = cd; g_chop_off = co;
		g_fixed_len = (g_meta.song_mode[ns] & 0x0Fu)
			    ? ((g_meta.song_mode[ns] & 0x0Fu) == 2u ? 1u : 0u) : g_mode_pref;
		/* M8a: the song's grid tempo follows it; phase re-anchors
		 * provisionally to "now" (a fresh tap run re-anchors properly). */
		if (g_grid_bpm_q8[ns]) {
			g_grid_beat_frames = (uint32_t)((48000ULL * 60u * 256u) /
			                                g_grid_bpm_q8[ns]);
			g_grid_anchor = g_sample_clock;
			g_grid_next_tick = g_sample_clock;
			g_grid_active = 1;
			{ uint64_t _bar = (uint64_t)g_grid_beat_frames * 4u;
			  g_grid_next_bar = g_grid_anchor +
				(((g_sample_clock - g_grid_anchor) / _bar) + 1u) * _bar; }
		} else {
			g_grid_active = 0;
			g_grid_next_bar = 0;
		}
		g_grid_resync_at = 0;
	}
	if (g_bnc_active || g_bnc_req >= 0)
		g_bnc_abort = 1;   /* M19b: a song switch abandons the print */
	g_grid_fresh = 0;  /* M20 F1: a persisted grid's phase is provisional */
	g_cnv_set = 0;     /* M22c: landmarks do not survive a song switch */
	g_grid_base_beats = 0; g_grid_base_blocks = 0;   /* M20 F7 */
	g_win_free = 0;     /* M16: the free window is session performance state */
	g_win_rev = 0;
	g_heads_mode = 0;   /* M13: heads are per-song doctrine like speed/mutes/
	                     * chop — a new song always opens playing normally;
	                     * triple-tap re-enters (session-only, never stored) */
	g_slot_switch_req = 1;
	g_meta_save_req = 1;
}

/* Advance to the next song slot (FUNCTION tap). */
static void next_slot(void)
{
	if (g_slot >= NUM_SLOTS) g_slot = 0;
	jump_to_slot((g_slot + 1u) % NUM_SLOTS);
}

/* WDT PRE-WARNING (nRF52: fires ~61 us before the reset): the reported crash
 * was rr=2 = a WATCHDOG reset — something kept main (the feeder) off the CPU
 * for 4 s. Stamp WHO was running into the fault breadcrumb: 'A'udio,
 * 'S'treamer, 'M'IDI, 'm'ain (stuck in its own loop), 'I'dle (CPU idle =>
 * main is BLOCKED on something, not starved) — printed next boot as
 * flt=d09000XX@tcb. */
extern struct k_thread z_main_thread;
extern struct k_thread z_idle_threads[];
static void wdt_prewarn(const struct device *dev, int ch)
{
	ARG_UNUSED(dev); ARG_UNUSED(ch);
	k_tid_t t = k_current_get();
	uint32_t who = '?';
	if      (t == &audio_tcb)        who = 'A';
	else if (t == &streamer_tcb)     who = 'S';
	else if (t == &midi_tcb)         who = 'M';
	else if (t == &z_main_thread)    who = 'm';
	else if (t == &z_idle_threads[0]) who = 'I';
	g_fault_reason = 0xD0900000u | who;
	g_fault_pc = (uint32_t)t;
	g_fault_key = 0xFA17FA17u;
	/* RAM breadcrumbs did NOT survive a real WDT reset (the bootloader runs
	 * first and scrubs that RAM) — GPREGRET2 is a RETAINED register that
	 * survives every soft/WDT reset and the bootloader leaves it alone. */
	NRF_POWER->GPREGRET2 = (uint8_t)who;
}

int main(void)
{
	/* Why did the last boot end? (bit0 pin reset, bit1 watchdog, bit2 soft
	 * reset, bit3 CPU lockup — see nRF52840 POWER.RESETREAS.) */
	g_resetreas = NRF_POWER->RESETREAS;
	NRF_POWER->RESETREAS = 0xFFFFFFFFu;
	if (g_fault_key == 0xFA17FA17u) {
		g_last_fault_reason = g_fault_reason;   /* previous boot CRASHED */
		g_last_fault_pc = g_fault_pc;
		g_fault_key = 0u;
	} else if (NRF_POWER->GPREGRET2 != 0u) {
		/* RAM breadcrumb lost (bootloader scrub) but the retained register
		 * survived: recover the watchdog culprit letter from it. */
		g_last_fault_reason = 0xD0900000u | NRF_POWER->GPREGRET2;
		g_last_fault_pc = 0u;
	}
	NRF_POWER->GPREGRET2 = 0u;
	/* DWT cycle counter: feeds the audio-block exec-time watermark (aus=). */
	CoreDebug->DEMCR |= CoreDebug_DEMCR_TRCENA_Msk;
	DWT->CYCCNT = 0;
	DWT->CTRL |= DWT_CTRL_CYCCNTENA_Msk;
	/* Main runs at PREEMPT(1): BELOW the audio engine (0), ABOVE the streamer
	 * (5) and MIDI (6). History: main once defaulted to 0 and its blocking
	 * ladder-ADC reads preempting the streamer caused rec overflows, so a
	 * rescue round demoted it to (8) — but that turned "streamer busy" into
	 * "lights, buttons and the WATCHDOG FEED all crawl", and a 4 s busy
	 * stretch (easy with 4 independent tracks + record at 48 kHz) became a
	 * watchdog reset: the field-reported freeze/crash (rr=2, lights slow).
	 * Preempting the streamer is harmless NOW: the rings ride 341 ms and
	 * every bus wait is fail-safe/time-bounded — a few ms of ladder reads or
	 * CDC prints cannot overflow anything. Responsiveness is structural. */
	/* W3-r5: PREEMPT(2), not (1) -- the streamer's pressure sprint
	 * boosts to PREEMPT(1) and Zephyr does not preempt on ties, so
	 * at (1) main kept every cycle it held (census §48). At (2) the
	 * sprint takes the CPU during rec pressure; the 150/15 duty
	 * still hands main the level back every 165 ms (WDT, buttons). */
	k_thread_priority_set(k_current_get(), K_PRIO_PREEMPT(2));

	const struct device *wdt = DEVICE_DT_GET(WDT_NODE);

	/* Wake cause: captured ONCE at main() entry into g_resetreas (the register
	 * is write-1-to-clear and is already cleared there — a second read here
	 * returned 0 and broke this gate, parking watchdog recoveries in standby
	 * and SYSTEM_OFF-wiping the crash breadcrumb on battery). OFF = woken from
	 * SYSTEM_OFF by the power button; DOG = watchdog recovery (resume fast). */
	uint32_t wake_reas = g_resetreas;

	pwr_btn_cfg_input();
	charger_init();                 /* make sure the battery actually charges */
	for (int i = 0; i < NUM_LEDS; i++)
		led_cfg_output(&leds[i]);
	for (int i = 0; i < NUM_TRACK_LEDS; i++)
		led_cfg_output(&track_leds[i]);
	all_off();
	track_all_off();
	led_pwm_init();   /* ALWAYS-DIM: start the LED soft-PWM now, before the
	                   * charge-standby loop, so the battery gauge is dim too
	                   * (TechnicsOP's build started it later in boot). */

	if (device_is_ready(wdt)) {
		wdt_install_timeout(wdt, &(struct wdt_timeout_cfg){
			.window.max = 4000, .callback = wdt_prewarn,
		});
		wdt_setup(wdt, 0);
	}
	feed_wdt();

	/* EARLY controls_init: the battery gauge in charge-standby below needs the
	 * ladder rail + ADC channels, which used to come up only after standby.
	 * Idempotent (pure register config); the original call later is unchanged. */
	controls_init();

	/* EARLY streamer start (v1.2.3): the saved brightness lives in the song
	 * index, and only the streamer reads the eMMC — but it used to be created
	 * AFTER standby, so the charging gauge could never see the setting and
	 * always showed the dim default (user report). Started here it inits the
	 * eMMC, loads the index (g_meta_loaded -> the standby loop applies
	 * led_full), then idles; the audio_init call is guarded against a double
	 * create, and its transfer polling waits for USB (g_usb_up). */
	streamer_start();

	/* ---- CHARGE-STANDBY: the device no longer springs to life on its own ----
	 * Plugging USB in (or finishing a flash, or inserting a battery) lands here:
	 * silent, looper untouched, LED 1 blinking while charging / solid when full.
	 * HOLD the power button ~1.5 s (stock-length) to actually switch ON.
	 * M18: a button wake from SYSTEM_OFF used to SKIP this gate entirely
	 * ("the user waking the device is already holding the button") — which
	 * quietly made pocket presses a one-click power-on: breakbeats in your
	 * pants and a drained battery (luuuciano's report). EVERY power-on now
	 * walks through the same hold; releasing early on battery drops
	 * straight back to SYSTEM_OFF (an accidental blip costs milliseconds).
	 * On battery with no button held there is nothing to do -> clean
	 * SYSTEM_OFF (button wakes). Only watchdog recovery and a preserved
	 * fault breadcrumb still skip the gate: the user was mid-session, and
	 * the battery standby path would SYSTEM_OFF away the forensics. */
	if (!(wake_reas & POWER_RESETREAS_DOG_Msk) &&
	    g_last_fault_reason == 0xFFFFFFFFu) {
		/* (a valid fault breadcrumb also skips standby: the user was
		 * mid-session, and the battery standby path would SYSTEM_OFF and
		 * wipe the very forensics we just preserved) */
		int64_t hold_t = -1;
		uint32_t blink = 0;
		while (1) {
			feed_wdt();
			/* v1.2.3-r7: apply the saved brightness at the TOP of the
			 * standby loop so EVERY branch honors it — the r5 apply sat
			 * inside the gauge branch only, so the hold-to-turn-on
			 * feedback and the turn-on transition stayed dim (user
			 * report). The early streamer (r6) has the index loaded
			 * well inside the 600 ms hold. */
			if (g_meta_loaded)
				g_led_dim = (g_meta.led_full & 1u) ? 0u : 1u;
			if (pwr_pressed()) {
				int64_t hnow = k_uptime_get();
				if (hold_t < 0) hold_t = hnow;
				else if (hnow - hold_t >= 1500)
					break;                    /* -> full power-on */
				/* M18-r2: the power-off countdown, mirrored — the
				 * side row FILLS across the 1.5 s hold so the gesture
				 * teaches its own length. A pocket blip still shows
				 * just one dim LED for an instant, nothing more. */
				{
					int lit = (int)(((hnow - hold_t) * NUM_LEDS) / 1500) + 1;
					if (lit > NUM_LEDS) lit = NUM_LEDS;
					all_off();
					for (int li = 0; li < lit; li++) led_on(li);
				}
			} else {
				hold_t = -1;
				if (!usb_present())
					power_off();              /* battery, idle -> off */
				/* BATTERY GAUGE (plan §3.5): 1-4 LEDs = approximate
				 * charge level. LEDs below the level are solid; the top
				 * one blinks while charging and goes solid when the
				 * charger reports done (all four solid = full).
				 * Thresholds are RAW 12-bit readings of the AIN4
				 * battery divider (gain 1/6, 0.6 V internal ref) —
				 * PLACEHOLDERS until calibrated: note the diag line's
				 * batt= value when full and when nearly empty, then
				 * space these three between those readings. If the ADC
				 * read fails (<0), lvl stays 1 and this degrades to the
				 * original single-LED blink/solid display. */
				/* Interim calibration 2026-07-20: full anchor MEASURED
				 * at raw ~2380 (resting, plugged-not-charging = ~4.21 V);
				 * empty end is a ~3.35 V physics estimate pending a real
				 * low reading. Spread at 25/50/75% of that range. Refine
				 * batt_thr once a near-empty batt= value is logged. */
				/* v1.2.3: standby (charging) runs BEFORE the boot
				 * block that applies the saved brightness, so the
				 * gauge always showed the dim default even in full
				 * mode (user report). Apply it here as soon as the
				 * streamer has the index; idempotent per pass. */
				if (g_meta_loaded)
					g_led_dim = (g_meta.led_full & 1u) ? 0u : 1u;
				static const int batt_thr[3] = { 2020, 2140, 2260 };
				static int bavg = -1;   /* smoothed reading (EMA over ~10 passes) */
				static int blvl = 0;    /* sticky displayed level (hysteresis) */
				int braw = ladder_read(&adc_ladder[LAD_BATT]);
				if (braw >= 0)
					bavg = (bavg < 0) ? braw
					     : bavg + (braw - bavg) / 8;
				if (bavg >= 0) {
					/* v1.2.1 gauge fix (user report: LED 2 flickered
					 * while charging near-empty): a SINGLE raw sample
					 * per pass with no hysteresis let ADC noise +
					 * charger ripple flip the level ~25x/s at a
					 * threshold — the boundary LED strobed between
					 * off and blinking. Smooth first, then only move
					 * the level once the average clears a threshold
					 * by ±18 counts (a step is ~120 counts wide). */
					int nl = 1;
					for (int k = 0; k < 3; k++)
						if (bavg > batt_thr[k]) nl = k + 2;
					if (blvl == 0)      blvl = nl;   /* first read seeds */
					else if (nl > blvl && bavg > batt_thr[blvl - 1] + 18)
						blvl = nl;
					else if (nl < blvl && bavg < batt_thr[blvl - 2] - 18)
						blvl = nl;
				}
				int lvl = blvl ? blvl : 1;
				int bl = ((++blink / 12u) & 1u) == 0u;
				for (int i = 0; i < NUM_LEDS; i++) {
					int on;
					if (i < lvl - 1)       on = 1;
					else if (i == lvl - 1) on = charging() ? bl : 1;
					else                   on = 0;
					on ? led_on(i) : led_off(i);
				}
			}
			k_msleep(40);
		}
		all_off();
		/* wait for release so the hold doesn't bleed into the FUNCTION logic */
		while (pwr_pressed()) { feed_wdt(); k_msleep(20); }
	}

	controls_init();                /* power the button ladders + ADC + serial */
	codec_init();                   /* release codec resets + scan the I2C bus */
	audio_init();                   /* osc on, TAS2505 configured, I2S running  */
	hp_init();                      /* headphone codec on (always-on, TimK's driver) */
	usb_audio_start();              /* device_next: UAC2 audio-in + CDC console  */
	g_usb_up = 1;                   /* streamer may poll the transfer page now */
	feed_wdt();

	/* HEADPHONE AUTO-MUTE boot state: start muted if headphones are already in. */
#if HP_TIM_TEST
	if (g_hp_on == 1) {
		int votes = 0, reads = 0;
		for (int i = 0; i < 5; i++) {
			int c = hp_detect_connected();
			if (c >= 0) { reads++; votes += c; }
			k_msleep(8);
		}
		g_hp_in = (reads > 0 && votes * 2 > reads) ? 1 : 0;
		tas_set_speaker(!g_hp_in);
	}
#endif

	/* v1.2.3-r8: apply the saved brightness BEFORE the power-ON sweep.
	 * Button wakes skip standby entirely, so none of the standby-loop
	 * applies run on the battery power-on path — the sweep rendered three
	 * lines before the meta-wait and always used the dim default (user
	 * report, third location of the same boot-ordering gap). The early
	 * streamer has the index long before this point; the bounded wait is
	 * effectively zero. */
	for (int bw = 0; bw < 100 && !g_meta_loaded; bw++) { feed_wdt(); k_msleep(5); }
	if (g_meta_loaded)
		g_led_dim = (g_meta.led_full & 1u) ? 0u : 1u;

	/* ---- power-ON indication: sweep the LEDs on, then clear ---- */
	for (int i = 0; i < NUM_LEDS; i++) {
		led_on(i);
		feed_wdt();
		k_msleep(90);
	}
	k_msleep(160);
	all_off();

	/* wait for the streamer to load the song metadata (block 0), then select the
	 * last-used song and its saved BPM and load its tracks. */
	for (int i = 0; i < 200 && !g_meta_loaded; i++) { feed_wdt(); k_msleep(5); }
	if (g_meta_loaded) {
		g_slot = (g_meta.cur_slot < NUM_SLOTS) ? g_meta.cur_slot : 0;   /* defensive clamp */
		g_play_speed_q16 = g_meta.slot[g_slot].speed_q16;
		g_play_bpm = (int)(((uint64_t)g_play_speed_q16 * LOOP_BPM_BASE + 32768u) / 65536u);
		if (g_play_bpm < BPM_MIN) g_play_bpm = BPM_MIN;
		if (g_play_bpm > BPM_MAX) g_play_bpm = BPM_MAX;
		g_led_dim = (g_meta.led_full & 1u) ? 0u : 1u;   /* restore brightness mode */
		g_instant_rec = (uint8_t)(((g_meta.led_full >> 1) & 1u) ? 0u : 1u);   /* M41-r5: bit 1 SET = classic */
		{	/* M7: current song's persisted chop + effective mode */
			uint32_t cd = g_meta.chop[g_slot][0]; if (cd < 1u || cd > 64u) cd = 1u;
			uint32_t co = g_meta.chop[g_slot][1]; if (co >= cd) co = 0u;
			g_chop_div = cd; g_chop_off = co;
			g_fixed_len = (g_meta.song_mode[g_slot] & 0x0Fu)
				    ? ((g_meta.song_mode[g_slot] & 0x0Fu) == 2u ? 1u : 0u)
				    : g_mode_pref;
			if (g_grid_bpm_q8[g_slot]) {   /* M8a: boot grid tempo */
				g_grid_beat_frames = (uint32_t)((48000ULL * 60u * 256u) /
				                                g_grid_bpm_q8[g_slot]);
				g_grid_anchor = g_sample_clock;
				g_grid_next_tick = g_sample_clock;
				g_grid_active = 1;
				{ uint64_t _bar = (uint64_t)g_grid_beat_frames * 4u;
			  g_grid_next_bar = g_grid_anchor +
				(((g_sample_clock - g_grid_anchor) / _bar) + 1u) * _bar; }
			}
		}
		g_slot_switch_req = 1;
	}

	int64_t press_start = -1;
	int64_t tap_first = 0, tap_last = 0;  /* M8a FN-tap tempo run */
	int      tap_n = 0;
	uint64_t tap_first_s = 0;             /* sample-clock at first tap */
	uint64_t tap_last_s  = 0;             /* sample-clock at the latest tap */
	uint64_t press_start_s = 0;           /* M20 F9: sample-clock at the FN PRESS edge */
	int64_t  any_tap_t = 0;               /* M23-r6: every FN tap, run or not */
	uint8_t  fast_pair = 0;               /* M23-r6: last two taps < 280 ms apart */
	int      fnp_low = 0;                 /* PLAY-release debounce (passes) */
	int64_t combo_start = -1;   /* FUNCTION+PLAY: when the combo was first seen */
	uint8_t combo_fired = 0;    /* mode already toggled this combo press */
	uint8_t combo_seen  = 0;    /* PLAY was seen at all during this FUNCTION press */
	uint8_t suppress_play = 0;  /* swallow a trailing PLAY held past combo exit */
	enum trk_btn bj_cand = TRK_NONE; /* FUNCTION+Track bank jump: sticky candidate band */
	int bj_cnt = 0;                  /*   consecutive passes the candidate has held     */
	int bj_fired = -1;               /*   band already jumped during this FUNCTION press */
	int64_t pg_t0 = 0;               /* PG-533: when the pending FN+track press began */
	int pg_pend = -1;                /* PG-533: pressed track -- jump-on-release or page-on-dwell */
	int64_t fnp_edge = -1;           /* FUNCTION+PLAY dim toggle: last PLAY press edge */
	int fnp_chain = 0;               /* M13: consecutive PLAY taps (2 = 1.0x snap, 3 = heads) */
	int fnp_pend_snap = 0;           /* M15-r3: snap DEFERRED past the triple window */
	int fnp_presses = 0;             /* M15-r4: PLAY press edges this FUNCTION hold */
	enum vol_btn cp_cand = VOL_NONE; /* FUNCTION+rocker/Vol chop: sticky candidate */
	int cp_cnt = 0;                  /*   consecutive passes it has held */
	int cp_dcl_band = -1;            /*   last committed rocker band (double-click) */
	int64_t cp_dcl_t = 0;            /*   when it committed */
	int cp_rep_at = 0;               /*   M10 glide: cp_cnt of the next auto-repeat */
	int cp_rep_iv = 0;               /*   M10 glide: repeat interval, in ~25 ms passes */
	uint8_t ctl_flush = 0;      /* looper decode state went stale (FUNCTION page / USB transfer owned the loop) */
	int64_t last_diag = 0;      /* throttle the control read-out */

	while (1) {
		feed_wdt();

		/* USB block-transfer in progress: audio is paused and the streamer is
		 * servicing reads/writes. Ignore the controls and show a "busy" pattern
		 * (all four track LEDs blinking together) so the device clearly reads as
		 * mid-transfer rather than frozen. */
		if (g_xfer_mode) {
			static uint32_t xb;
			int on = ((xb++ / 8u) & 1u);
			for (int i = 0; i < NUM_TRACK_LEDS; i++)
				on ? track_led_on(i) : track_led_off(i);
			ctl_flush = 1;
			k_msleep(20);
			continue;
		}

		/* Print one status line ~twice a second (the 500 ms gate below) for
		 * monitoring. Only prints when a serial monitor is attached (DTR). */
		int64_t now = k_uptime_get();
		if (now - last_diag >= 500) {
			last_diag = now;
			controls_diag();
			feed_wdt();      /* the diag print path can be slow; never starve the WDT */
		}

		/* USB FEEDBACK-FORMAT AUTO-NEGOTIATION. Windows and Apple disagree
		 * about the Full-Speed feedback value format (4-byte Q16.16 vs the
		 * spec's 3-byte Q10.14) and each kills or cripples the stream when
		 * fed the other's. The wrong choice always shows up the same way:
		 * the host holds the stream OPEN but delivers (almost) nothing, so
		 * the mixer stitches silence (g_zero_pad counts it). If more than
		 * half of each 100 ms window is stitched silence for ~400 ms
		 * straight, flip the format and let the host try again — the flip
		 * repeats until data flows, so the device converges on whatever
		 * the connected host actually parses, on every OS. A closed
		 * stream never pads, so this can't fire from mere silence. */
		{
			static int64_t fb_probe_t;
			static uint32_t fb_zp_last;
			static int fb_starve_streak;
			if (fb_probe_t == 0) {
				fb_probe_t = now;
				fb_zp_last = g_zero_pad;
			} else if (now - fb_probe_t >= 100) {
				fb_probe_t = now;
				uint32_t zpn = g_zero_pad;
				uint32_t d = zpn - fb_zp_last;
				fb_zp_last = zpn;
				if (d >= (LOOP_RATE / 20u)) {   /* >50% of the window */
					if (++fb_starve_streak >= 4) {
						uac2_fs_fb_windows_fmt =
							!uac2_fs_fb_windows_fmt;
						fb_starve_streak = 0;
					}
				} else {
					fb_starve_streak = 0;
				}
			}
		}

		/* (track LEDs are driven by the looper beat clock below) */

		/* FUNCTION button: a SHORT tap changes song; a long HOLD powers off
		 * (the same button does both, like the original device). */
		if (pwr_pressed()) {
			ctl_flush = 1;
			if (press_start < 0) {
				press_start = k_uptime_get();
				/* M20 F9: stamp the PRESS, not the release. The tap
				 * cannot be CLASSIFIED until the release (a long hold
				 * means something else), but the moment it names is
				 * the press — so remember the clock here and judge
				 * later. FUNCTION is a plain GPIO with no debounce,
				 * so this read trails the finger by at most one 8 ms
				 * control pass. */
				press_start_s = g_sample_clock;
				/* M23-r6b: measure the gap from the last completed
				 * tap to THIS PRESS. The clear gesture is tap then
				 * press-and-HOLD, so the second press never becomes
				 * a tap — detecting at tap-release (r6) could not
				 * fire for the very gesture it was written for. */
				/* 280 ms is NOT an accident guard — it is the
				 * discriminator, and it pairs with the tap-run
				 * rule below that resets tap_n whenever two taps
				 * land under 200 ms apart. Both encode the same
				 * idea: this pair is FASTER THAN ANY TEMPO, so it
				 * cannot be a tap run. M25 tried widening it to
				 * 800 ms for #33 and that was wrong — 800 ms is
				 * 75 BPM, squarely musical. Worse, a tap run that
				 * FAILS to register (taps <200 ms, >1500 ms, or
				 * >20% irregular) leaves tap_n at 1, so the very
				 * next hold takes the clear branch: a fumbled snap
				 * would erase the grid. #33's discoverability is a
				 * DOCS problem, not a timing one. */
				fast_pair = (any_tap_t &&
					     (press_start - any_tap_t) < 280) ? 1u : 0u;
			}

			/* MODE TOGGLE — FUNCTION + PLAY held together ~0.7 s flips the
			 * fixed/variable loop-length mode. The normal ladder decode below
			 * is skipped while FUNCTION is held, so read PLAY here. PLAY is at
			 * the TOP of the AIN0 ladder (~1823); require >1600 so a Track-4
			 * (~1220) or the 1+4 bootloader combo (~1325) can never be mistaken
			 * for it. FUNCTION is a separate GPIO, so holding it does not shift
			 * the ladder voltage. While the combo is engaged the power-off
			 * countdown/shutdown is suppressed (this gesture must never risk a
			 * power-off), and the FUNCTION-release song-change is suppressed. */
			/* M15-r3: deferred 1.0x snap fires once the triple window is
			 * over (no 3rd tap arrived). Runs every FN-held pass. */
			if (fnp_pend_snap && fnp_edge >= 0 &&
			    k_uptime_get() - fnp_edge > 600) {
				fnp_pend_snap = 0;
				g_play_speed_q16 = 65536u;
				g_play_bpm = 80;
			}
			int fraw = ladder_read(&adc_ladder[LAD_TRACKS]);
			/* M31: 1600 -> 1773. M27 made multi-track combos reachable codes on
			 * this ladder (2+3+4 = 1683, ALL4 = 1743), and anything over the old
			 * 1600 counted as a PLAY press under FN - three phantom taps inside
			 * 600 ms toggled heads mode. 1773 sits between ALL4 and PLAY (1798+)
			 * with 25+ counts of margin against +/-9 measured noise. */
			if (fraw > 1773) {
				fnp_low = 0;
				combo_seen = 1;
				if (combo_start < 0) {           /* fresh PLAY press edge */
					int64_t fnp_now = k_uptime_get();
					fnp_presses++;
					/* FUNCTION + PLAY DOUBLE-TAP = snap to 1.0x. A
					 * second PLAY press edge fires it and blocks the
					 * hold tiers for this press so one gesture can't
					 * do two things. Window 450 -> 600 ms (M15-r4):
					 * an unhurried triple's 3rd tap kept missing it,
					 * and a lapsed chain turned the last tap into a
					 * phantom mode-toggle chord. */
					if (fnp_edge >= 0 && fnp_now - fnp_edge <= 600)
						fnp_chain++;
					else
						fnp_chain = 1;
					if (fnp_chain == 2 && !combo_fired) {
						/* M8c SNAP TO 1.0x — but DEFERRED (M15-r3)
						 * until the 450 ms triple window closes: the
						 * snap used to fire on this edge, so reaching
						 * for a triple's 3rd tap yanked beatmatched
						 * speed (marc's report). A double alone still
						 * snaps, just ~0.4 s later — "come home" is
						 * not rhythm-critical; a completed triple now
						 * never touches the tape at all. */
						fnp_pend_snap = 1;
						combo_fired = 1;
					} else if (fnp_chain == 3) {
						/* M13: TRIPLE-tap = HEADS MODE toggle. The
						 * 3rd tap CANCELS the pending snap — heads
						 * enter at the speed you were playing at.
						 * ON requires content playing on track 1.
						 * Rings 2-4 are re-anchored so the heads (or
						 * the old loops) fade in cleanly via the
						 * starve machinery + a declick dip. */
						fnp_pend_snap = 0;
						if (g_heads_mode) {
							g_heads_mode = 0;
							if (g_bnc_active || g_bnc_req >= 0)
								g_bnc_abort = 1;   /* M19b */
							for (int hm = 0; hm < NTRK; hm++)
								trk[hm].muted = (uint8_t)
								    ((g_head_mute_save >> hm) & 1u);
						} else {
							/* M19a-r2: source = the lowest playing
							 * UNMUTED track — a muted track still
							 * reads state TS_PLAY (mute is a flag,
							 * the ghost-glow design), and marc's
							 * live report was heads engaging on a
							 * muted track 1 over the audible track
							 * 2. All-muted songs fall back to any
							 * playing track. */
							int hs = -1;
							for (int hp = 0; hp < NTRK; hp++)
								if (trk[hp].state == TS_PLAY &&
								    !trk[hp].muted) {
									hs = hp; break;
								}
							if (hs < 0)
								for (int hp = 0; hp < NTRK; hp++)
									if (trk[hp].state == TS_PLAY) {
										hs = hp; break;
									}
							if (hs >= 0) {
								g_head_src = (uint8_t)hs;
								/* M19a-r4: snapshot the song's
								 * mutes and start every head
								 * AUDIBLE — heads mutes are
								 * performance state, restored
								 * on exit, never persisted
								 * (marc: a muted track must not
								 * ghost into the canon, and a
								 * silenced head must not come
								 * back as a muted track). */
								g_head_mute_save = 0;
								for (int hm = 0; hm < NTRK; hm++) {
									if (trk[hm].muted)
										g_head_mute_save |=
										    (uint8_t)(1u << hm);
									trk[hm].muted = 0;
								}
								g_heads_mode = 1;
							}
						}
						for (int hk = 0; hk < NTRK; hk++) {
							if (hk == (int)g_head_src) continue;
							trk[hk].p_w = (uint32_t)(g_consume_pos /
								TSPBI(hk)) * TSPBI(hk);
						}
						for (int hk = 0; hk < NTRK; hk++) {
							g_head_pos[hk] = (uint8_t)(hk * 64);
							g_head_rev[hk] = 0;
						}
						g_dip_req = 1;
						combo_fired = 1;
					}
					fnp_edge = fnp_now;
					combo_start = fnp_now;
				}
				if (!combo_fired &&
				    k_uptime_get() - combo_start >= 5000) {
					/* v1.2.2: HOLD THROUGH 5 s = BRIGHTNESS toggle,
					 * firing WITHOUT release — the light change is
					 * the confirm and the press is spent. The mode
					 * toggle moved to PLAY-RELEASE (0.7-5 s), so a
					 * hold that reaches 5 s never flips the mode. */
					g_led_dim ^= 1u;
					g_meta.led_full = (g_meta.led_full & ~1u) | (g_led_dim ? 0u : 1u);   /* keep bit 1 (M41-r5) */
					g_meta_save_req = 1;
					combo_fired = 1;
				}
				k_msleep(25);
				continue;                /* combo owns the button */
			}
			if (combo_start >= 0) {
				/* v1.2.2-r4: DEBOUNCED release — the shared ladder can
				 * dip below the PLAY band for a stray pass mid-hold,
				 * which used to reset the 5 s clock (user: "brightness
				 * takes ~7 s"). Only 3 consecutive low passes count as
				 * a real release — for HOLDS. M15-r4: a short press
				 * (<300 ms) is a TAP, and its release commits after 2
				 * passes: fast triples' gaps were shorter than the
				 * 75 ms debounce, so taps merged, the chain counted 2,
				 * and the snap fired instead of heads (live report).
				 * Two passes still filters the single-sample dip the
				 * debounce was built for. */
				int fnp_need =
					(k_uptime_get() - combo_start < 300) ? 2 : 3;
				if (++fnp_low < fnp_need) { k_msleep(25); continue; }
				if (!combo_fired && fnp_presses < 2) {
					/* (2+ presses this hold = a tap chain, never a
					 * mode chord — the toggle is a single-press
					 * gesture, M15-r4) */
					int64_t fnp_held = k_uptime_get() - combo_start;
					if (fnp_held >= 350 && fnp_held < 5000)
						fnp_mode_toggle();  /* mode fires on RELEASE */
				}
			}
			fnp_low = 0;
			combo_start = -1;            /* PLAY not held */

			/* BANK JUMP — FUNCTION + Track N -> first song of bank N (M4b).
			 * POWER-OFF SAFETY (the whole point): committing a track band
			 * during a FUNCTION hold sets combo_seen — the same flag the
			 * FUNCTION+PLAY combo uses — which suppresses the power-off
			 * countdown, the shutdown itself, and the release song-advance
			 * for the remainder of this press. Turning the device off now
			 * requires a CLEAN FUNCTION-only hold, exactly as before.
			 * Sticky commit: the same band must be seen on 3 consecutive
			 * passes (~75 ms) — a finger transiting the ladder can't fire.
			 * Keeping FUNCTION held and pressing another track jumps again
			 * (bank surfing). While recording, jump_to_slot() refuses, as
			 * the tap-advance always has. Note: physically pressing T1+T4
			 * with FUNCTION held reads as the Track-4 band -> bank 4; the
			 * DFU combo remains a no-FUNCTION gesture. */
			{
				/* M31-r2: only the four MEASURED single-track bands may bank-jump.
				 * The old filter (110..1500 -> decode_tracks) let combo codes through
				 * as WRONG single tracks (1+2=572 read as track 3, 2+3=989 as track 4,
				 * 1+4=1303 as track 4...), so pressing several tracks with FN held
				 * fired phantom jump_to_slot() calls - songs switched by themselves
				 * and could land on an empty slot. Combos under FN now do NOTHING.
				 * Bands from SP1-BUTTON-LADDER-MAP.md, gaps between bands excluded. */
				enum trk_btn tb = TRK_NONE;
				if      (fraw >= 110  && fraw <  308) tb = TRK_1;   /* ~213  */
				else if (fraw >= 308  && fraw <  488) tb = TRK_2;   /* ~404  */
				else if (fraw >= 650  && fraw <  795) tb = TRK_3;   /* ~728  */
				else if (fraw >= 1099 && fraw < 1256) tb = TRK_4;   /* ~1209 */
				if (tb >= TRK_1 && tb <= TRK_4) {
					if (tb == bj_cand) bj_cnt++;
					else { bj_cand = tb; bj_cnt = 1; }
					if (bj_cnt == 3) {   /* exact edge: once per press */
						combo_seen = 1;      /* never a power-off now */
						if (g_pg_open) {
							/* PG-533: in the MODE PAGE a track tap
							 * toggles that track's NEXT-record mode.
							 * No mute, no audio side effect -- the
							 * LEDs answer (solid=stereo, blink=mono). */
							trk[(int)tb].p16m_next = !trk[(int)tb].p16m_next;
							if (g_slot < NUM_SLOTS)   /* FX2-536: stamp NOW --
							 * a deferred stamp can land on the wrong
							 * slot if a jump beats the save service. */
								g_x3.t[g_slot][(int)tb].rsv = (uint8_t)(0x80u |
								    (trk[(int)tb].p16m_next & 1u));
							g_meta_save_req = 1;   /* PS-535: persist per song */
							bj_fired = (int)tb;
						} else {
							/* PG-533: the jump now resolves on RELEASE
							 * (the map's pages prerequisite); a held T4
							 * becomes the MODE PAGE instead. */
							pg_t0 = k_uptime_get();
							pg_pend = (int)tb;
						}
					}
					if (!g_pg_open && pg_pend == (int)TRK_4 &&
					    k_uptime_get() - pg_t0 >= 400) {
						g_pg_open = 1;   /* PG-533: FN + hold T4 = MODE PAGE */
						pg_pend = -1;
					}
					led_service();           /* live song display mid-hold */
					k_msleep(25);
					continue;                /* track held: combo owns the button */
				}
				if (pg_pend >= 0) {
					/* PG-533: the press ended before the dwell -- fire the
					 * M8a bank jump ON RELEASE, semantics unchanged. */
					uint32_t bank = (uint32_t)pg_pend * 4u;
					if (g_slot / 4u == (uint32_t)pg_pend)
						jump_to_slot(bank + ((g_slot % 4u) + 1u) % 4u);
					else
						jump_to_slot(bank);
					bj_fired = pg_pend;
					pg_pend = -1;
				}
				bj_cand = TRK_NONE; bj_cnt = 0;
			}

			/* LOOP CHOP (scheme A', collision-audited): while FUNCTION is
			 * held the Vol/rocker ladder — which stock never reads during
			 * FUNCTION holds — becomes the chop surface:
			 *   FWD  = window /2 (shorter)   RWD  = window x2 (longer)
			 *   Vol+ = shift window right    Vol- = shift window left
			 *   rocker DOUBLE-CLICK = reset to the full loop
			 * Sticky 3-pass commit (transit-proof); every commit sets
			 * combo_seen so the press can never become a power-off; bare
			 * rocker/Vol behavior outside FUNCTION holds is untouched. */
			{
				enum vol_btn vb = decode_vol(ladder_read(&adc_ladder[LAD_VOL]));
				if (vb != VOL_NONE) {
					if (vb == cp_cand) { if (cp_cnt < 1000) cp_cnt++; }
					else { cp_cand = vb; cp_cnt = 1; }
					if (cp_cnt == 3) {          /* committed press edge */
						int64_t cnow = k_uptime_get();
						combo_seen = 1;
						/* M23-r11 (nervouskidz): the buttons reclaim
						 * the window SHAPE from the faders — they do
						 * NOT get to overrule which DIRECTION the
						 * faders are asking for. Crossing the pair is
						 * a physical statement that stays true while
						 * the faders stay crossed, so a rocker reset
						 * must not silently un-reverse playback while
						 * the hardware still says reversed. Clearing
						 * g_win_free alone used to do exactly that,
						 * because every consumer read the direction as
						 * (g_win_free && g_win_rev) — see below, they
						 * now read g_win_rev on its own. */
						g_win_free = 0;
						uint32_t d = g_chop_div, o = g_chop_off;
						if (vb == VOL_TEMPO_UP || vb == VOL_TEMPO_DOWN) {
							if (cp_dcl_band == (int)vb &&
							    cnow - cp_dcl_t <= 400) {
								d = 1u; o = 0u;   /* double-click: RESET */
							} else if (vb == VOL_TEMPO_UP) {
								if (d < 64u) { d <<= 1; o <<= 1; }
							} else {
								if (d > 1u) { d >>= 1; o >>= 1; }
							}
							cp_dcl_band = (int)vb; cp_dcl_t = cnow;
						} else if (vb == VOL_UP) {
							o = (o + 1u) % d;
						} else {                  /* VOL_DOWN */
							o = (o + d - 1u) % d;
						}
						g_chop_off = (d > 1u) ? (o % d) : 0u;
						g_chop_div = d;
						if (g_slot < NUM_SLOTS) { /* M7a: persist per song */
							g_meta.chop[g_slot][0] = (uint8_t)d;
							g_meta.chop[g_slot][1] = (uint8_t)g_chop_off;
							g_meta_save_req = 1;
						}
						g_chop_req = 1;           /* engine: snap to it */
						g_dip_req = 1;            /* M10: declick the jump */
						cp_rep_at = cp_cnt + 18;  /* M10: first repeat ~450 ms in */
						cp_rep_iv = 10;           /*      then ~250 ms, accelerating */
					} else if (cp_cnt > 3 && cp_rep_at && cp_cnt >= cp_rep_at &&
						   (vb == VOL_UP || vb == VOL_DOWN) &&
						   g_chop_div > 1u) {
						/* M10 HOLD-TO-GLIDE: keep shifting while the chord
						 * is held — declicked whole-window steps at an
						 * accelerating rate read as a tape scrub across
						 * the loop. Only the SHIFT buttons repeat: a
						 * repeating halve/double would sweep the whole
						 * div range in a blink. Double-click detection
						 * keys on press EDGES, so repeats can't fake it. */
						uint32_t d2 = g_chop_div;
						uint32_t o2 = g_chop_off;
						o2 = (vb == VOL_UP) ? (o2 + 1u) % d2
						                    : (o2 + d2 - 1u) % d2;
						g_chop_off = o2;
						if (g_slot < NUM_SLOTS) {
							g_meta.chop[g_slot][1] = (uint8_t)o2;
							g_meta_save_req = 1;  /* writer coalesces */
						}
						g_chop_defer = 1;   /* M24: glide is continuous */
						g_defer_t = k_uptime_get();   /* r3 */
						cp_rep_at = cp_cnt + cp_rep_iv;
						if (cp_rep_iv > 5) cp_rep_iv--;   /* floor ~125 ms */
					} else if (cp_cnt > 3 && cp_rep_at && cp_cnt >= cp_rep_at &&
						   (vb == VOL_TEMPO_UP || vb == VOL_TEMPO_DOWN)) {
						/* M15 LENGTH GLIDE: holding FN+FWD/RWD now
						 * repeats the halve/double too — a STEADY
						 * ~375 ms cadence, not the accelerating shift
						 * glide: only 7 sizes exist, so bottom-to-top
						 * takes ~2.3 s under full control (the M10
						 * blink-sweep objection was about speed, and
						 * this is the slow version marc asked for).
						 * At either end the hold idles harmlessly.
						 * Double-click reset still keys on press
						 * EDGES, so repeats can never fake it. */
						uint32_t d2 = g_chop_div, o2 = g_chop_off;
						if (vb == VOL_TEMPO_UP) {
							if (d2 < 64u) { d2 <<= 1; o2 <<= 1; }
						} else {
							if (d2 > 1u)  { d2 >>= 1; o2 >>= 1; }
						}
						if (d2 != g_chop_div) {
							g_chop_off = (d2 > 1u) ? (o2 % d2) : 0u;
							g_chop_div = d2;
							if (g_slot < NUM_SLOTS) {
								g_meta.chop[g_slot][0] = (uint8_t)d2;
								g_meta.chop[g_slot][1] = (uint8_t)g_chop_off;
								g_meta_save_req = 1;
							}
							g_chop_defer = 1;   /* M24 */
							g_defer_t = k_uptime_get();   /* r3 */
						}
						cp_rep_at = cp_cnt + 15;   /* steady ~375 ms */
					}
					led_service();
					k_msleep(25);
					continue;                 /* chord owns the button */
				}
				cp_cand = VOL_NONE; cp_cnt = 0;
			}
			/* M14 HEADS v2: while FUNCTION is held with heads engaged,
			 * the faders are HEAD POSITIONS — absolute (grab = the head
			 * jumps to the fader; it's a scrub, jumping is the point),
			 * gated only by intent (move >=3 counts from the FN-down
			 * snapshot, the bank-jump brush guard). Each apply is
			 * rate-limited, re-anchors ONLY that head's ring, and asks
			 * for that track's blip. Engaging spends the press (M11a
			 * lesson: a scrubbing hold can never power off) and arms
			 * the volume re-cross latch for FUNCTION release. */
			if (heads_engaged()) {
				static int64_t hf_press = -1;
				static uint8_t hf_eng[NTRK];
				static int hf_snap[NTRK];
				static int64_t hf_at[NTRK];
				if (hf_press != press_start) {
					hf_press = press_start;
					for (int hf = 0; hf < NTRK; hf++) {
						hf_eng[hf] = 0; hf_snap[hf] = -1; hf_at[hf] = 0;
					}
				}
				int64_t hnow = k_uptime_get();
				for (int hf = 0; hf < NTRK; hf++) {
					int fv = ladder_read(&adc_ladder[LAD_FADER0 + hf]);
					if (fv < 0) continue;
					int q = (int)((uint32_t)fv * 256u / 3700u);
					if (q > 255) q = 255;
					if (hf_snap[hf] < 0) { hf_snap[hf] = q; continue; }
					if (!hf_eng[hf]) {
						int d = q - hf_snap[hf];
						if (d < 0) d = -d;
						/* M31: intent gate 3 -> 7 (~2.7% of travel). 3 was under the
						 * measured drift of a loose fader and under hand-wobble while
						 * holding FN for something else; one accidental crossing keeps
						 * the fader engaged for the WHOLE hold, which was the phantom
						 * head-scrub during unrelated FN gestures. */
						if (d < 7) continue;      /* intent gate */
						hf_eng[hf] = 1;
						combo_seen = 1;           /* press is spent */
						g_fh_latch[hf] = 1;
						g_fh_lastq[hf] = -1;
					}
					int dd = q - (int)g_head_pos[hf];
					if (dd < 0) dd = -dd;
					if (dd < 2) continue;             /* ADC deadband */
					if (hnow - hf_at[hf] < 45) continue;  /* rate limit */
					hf_at[hf] = hnow;
					g_head_blip[hf] = 3;
					g_head_pos[hf] = (uint8_t)q;
					trk[hf].p_w = (g_consume_pos / TSPBI(hf)) * TSPBI(hf);
				}
			} else {
				/* M16 WINDOW FADERS: FUNCTION held, heads NOT engaged —
				 * faders 1-3 shape the free window (see the globals
				 * comment). Same rules as the heads scrub: absolute
				 * jump-on-grab, >=3-count intent gate, engagement spends
				 * the press and arms the volume re-cross latch. Applies
				 * are rate-limited and ride g_chop_req + the declick dip
				 * (every apply is a chop edit). Fader 4 is untouched. */
				static int64_t wf_press = -1;
				static uint8_t wf_eng[4];
				static int wf_snap[4];
				static int wf_s = 0, wf_e = 255;  /* RAW ends; s>e = reversed */
				static int wf_q3 = -1;
				static int wf_pend;
				static int64_t wf_at;
				if (wf_press != press_start) {
					wf_press = press_start;
					for (int wf = 0; wf < 4; wf++) {
						wf_eng[wf] = 0; wf_snap[wf] = -1;
					}
				}
				int64_t wnow = k_uptime_get();
				for (int wf = 0; wf < 4; wf++) {
					int fv = ladder_read(&adc_ladder[LAD_FADER0 + wf]);
					if (fv < 0) continue;
					int q = (int)((uint32_t)fv * 256u / 3700u);
					if (q > 255) q = 255;
					if (wf_snap[wf] < 0) { wf_snap[wf] = q; continue; }
					if (!wf_eng[wf]) {
						int d = q - wf_snap[wf];
						if (d < 0) d = -d;
						/* M31: intent gate 3 -> 7, same reasoning as the heads loop.
						 * This is ALSO the row-49 fix: fader 4 here is the DJ filter,
						 * and its physical drift crossing the old 3-count gate while
						 * FN was held for chopping is what stripped the low end from
						 * all four loops (luuuciano's video, marc's random high-pass). */
						if (d < 7) continue;      /* intent gate */
						wf_eng[wf] = 1;
						combo_seen = 1;           /* press is spent */
						g_fh_latch[wf] = 1;
						g_fh_lastq[wf] = -1;
					}
					if (wf == 3) {
						/* M17: fader 4 = the DJ filter, applied
						 * directly (no chop_req, no dip — the
						 * coefficient ramp IS the declick) */
						g_flt_pos = (uint8_t)q;
					} else if (wf == 0) {
						int d = q - wf_s; if (d < 0) d = -d;
						if (d >= 2) { wf_s = q; wf_pend = 1; }
					} else if (wf == 1) {
						int d = q - wf_e; if (d < 0) d = -d;
						if (d >= 2) { wf_e = q; wf_pend = 1; }
					} else {
						int d = (wf_q3 < 0) ? 99 : q - wf_q3;
						if (d < 0) d = -d;
						if (d >= 2) {
							wf_q3 = q;
							/* SHIFT: absolute position, width AND
							 * order (= direction) preserved */
							int w = (wf_s <= wf_e) ? wf_e - wf_s
							                       : wf_s - wf_e;
							int base = (q * (255 - w)) >> 8;
							if (wf_s <= wf_e) { wf_s = base; wf_e = base + w; }
							else              { wf_e = base; wf_s = base + w; }
							wf_pend = 1;
						}
					}
				}
				if (wf_pend && wnow - wf_at >= 60) {
					wf_at = wnow; wf_pend = 0;
					int ws = wf_s, we = wf_e, rv = 0;
					if (ws > we) { int t2 = ws; ws = we; we = t2; rv = 1; }
					if (we - ws < 2) {          /* floor ~1/128 sliver */
						we = ws + 2;
						if (we > 255) { we = 255; ws = 253; }
					}
					g_win_s8 = (uint8_t)ws;
					g_win_e8 = (uint8_t)we;
					g_win_rev = (uint8_t)rv;
					g_win_free = 1;
					/* M24 (geraasmasjien + luuuciano): this used to
					 * snap the rings and dip the master EVERY 60 ms
					 * for the whole sweep. The dip slams gain to 0
					 * and recovers over ~28 ms, so at a 60 ms cadence
					 * it is a ~16 Hz tremolo — and the snap threw away
					 * the read-ahead on top, which is the silence they
					 * described. Neither is needed while moving: the
					 * streamer re-reads g_win_* on every fill round,
					 * so the ring converges on the new window all by
					 * itself. Defer, and settle up on release. */
					g_chop_defer = 1;
					g_defer_t = k_uptime_get();   /* r3 */
				}
			}
			if (combo_seen) {
				/* The combo has been engaged this FUNCTION press: once PLAY
				 * is lifted, do NOTHING further for the rest of the hold —
				 * no power-off countdown, no shutdown (press_start still
				 * dates from the original FUNCTION-down, so the 2.5 s
				 * power-off would otherwise fire). The FUNCTION press is
				 * spent; it ends cleanly on release below. */
				led_service();
				k_msleep(25);
				continue;
			}

			int64_t held = k_uptime_get() - press_start;

			/* M8a: a HOLD right after a tap run = CLEAR this song's grid.
			 * The run also spends the press — never a power-off. */
			if (tap_n > 0 && k_uptime_get() - tap_last < 3000) {
				/* M20 F6: window widened 1500 -> 3000 ms — the
				 * any-time grid clear (tap FN once, then hold ~1 s)
				 * was real but nearly impossible to hit
				 * (geraasmasjien's "can't get back to free mode") */
				if (held >= 1000 && !combo_seen && fast_pair) {
					/* DOUBLE-TAP then hold = clear the grid.
					 * fast_pair alone decides this: a press
					 * landing within 280 ms of a tap is faster
					 * than any tempo, so it IS a double-click.
					 * M25-r3: the old extra tap_n < 4 test broke
					 * the gesture. The first tap of the double
					 * click is indistinguishable from another
					 * TEMPO tap, so after a 4-tap run it pushed
					 * tap_n to 5 and the hold fell through to the
					 * snap branch — marc's "sometimes it rounds
					 * instead of deleting". It only misfired when
					 * the delete-tap happened to land near the
					 * beat being tapped, which is why it was
					 * intermittent. Snap still needs tap_n >= 4
					 * AND a gap wider than 280 ms, which is what
					 * tapping a tempo and then holding gives you
					 * at any sane BPM (469 ms at 128). */
					g_grid_bpm_q8[g_slot] = 0;
					g_grid_active = 0;
					g_grid_fresh = 0;
					g_cnv_set = 0;
					g_grid_save_req = 1;
					tap_n = 0;
					fast_pair = 0;
					any_tap_t = 0;
					combo_seen = 1;      /* spend the press */
				} else if (held >= 1000 && !combo_seen && tap_n >= 4) {
					/* M23: a hold after a COMMITTED run (4+ taps)
					 * toggles integer-BPM snap. The press that
					 * lands here would otherwise do nothing, and
					 * a held press never registers as a tap (the
					 * tap branch needs a release under 600 ms),
					 * so tap_n is still the run's count. 1-3 taps
					 * then hold stays the grid clear, exactly as
					 * documented. */
					/* M23-r5: a ONE-SHOT nudge, not a mode. The
					 * grid you just tapped is pulled onto the
					 * nearest whole BPM, once, right now — and
					 * then everything behaves exactly as normal.
					 * Nothing to remember, nothing to turn off,
					 * no state to read off the panel afterwards. */
					if (g_grid_active && g_grid_beat_frames) {
						uint32_t nb = bpm_snap(g_grid_beat_frames);
						g_snap_took = (nb && nb != g_grid_beat_frames);
						if (g_snap_took) {
							beat_set(nb);   /* r7: already grid-domain */
							g_det_bpm = (int)(((uint64_t)LOOP_RATE *
								60u + nb / 2u) / nb);
							for (int k3 = 0; k3 < NTRK; k3++) {
								uint32_t Lk = trk[k3].len_samps;
								if (!Lk || !g_gridrec_beat_samps)
									continue;
								uint32_t Nk = (Lk +
									g_gridrec_beat_samps / 2u) /
									g_gridrec_beat_samps;
								if (!Nk) continue;
								uint32_t Ln = Nk * nb;
								/* M25-r8: same truncating clamp as the
								 * convergence path — see there. */
								uint32_t dL3 = (Ln > Lk) ? (Ln - Lk)
										         : (Lk - Ln);
								if (Ln && (uint64_t)dL3 * 16u <=
								          (uint64_t)Lk)
									trk[k3].len_samps = Ln;
								if (trk[k3].state == TS_PLAY)
									trk[k3].p_w =
										(g_consume_pos / TSPBI(k3))
										* TSPBI(k3);
							}
							/* r7: beat_set did the rec beat too */
							g_dip_req = 1;   /* declick, as ever */
						}
					}
					if (g_snap_took) {
						g_snap_sweep = 48;   /* budget; the catch ends it */
					} else {
						/* M25-r10: declined — the tapped tempo is not
						 * near a whole number (or is out of range). Say
						 * so. Reuses the bounce's shrug: all four
						 * double-blink. Silence would be worse than
						 * either outcome, because the gesture and the
						 * grid-clear share a shape and you would not
						 * know which one you had just missed. */
						g_led_shrug = 20;
					}
					tap_n = 0;
					combo_seen = 1;      /* spend the press */
				}
				led_service();
				k_msleep(25);
				continue;
			}

			/* M28 (luuuciano): HOLD FN both rounds a tapped BPM and powers the
			 * device off, and people were switching it off mid-performance
			 * reaching for the musical gesture. Only honour the power-off hold
			 * when the tape is STOPPED — his own suggestion, and it also frees
			 * a plain HOLD FN while playing for future use. To power off, stop
			 * the tape first. */
			/* M31-r2: also allow power-off when NO LOOP EXISTS. A song switch
			 * onto an empty slot leaves g_playing latched with nothing loaded,
			 * and the M28 gate then refused power-off on a silent device. */
			if (held >= HOLD_MS_TO_OFF && (!g_playing || !g_loop_active))
				power_off();             /* never returns */

			/* show the power-off countdown only once it's clearly a hold, so a
			 * quick tap (song change) doesn't flash it. Clear BOTH rows so the
			 * countdown fills cleanly against a dark track row. */
			if (held > 400 && !g_snap_sweep && (!g_playing || !g_loop_active)) {
				/* M23: a pending snap sweep owns the display. The
				 * countdown clears BOTH rows every 25 ms and skips
				 * led_service, so without this the confirmation was
				 * invisible for as long as the finger stayed down —
				 * which is the whole duration of the gesture. */
				int lit = (int)((held * NUM_LEDS) / HOLD_MS_TO_OFF) + 1;
				if (lit > NUM_LEDS) lit = NUM_LEDS;
				all_off();
				track_all_off();
				for (int i = 0; i < lit; i++) led_on(i);
			} else if (held > 400 && g_snap_sweep) {
				all_off();          /* side row dark; sweep is the message */
				led_service();
			}
			k_msleep(25);
			continue;
		}

		if (press_start >= 0) {                  /* just released */
			/* v1.2.2-r4: releasing FUNCTION first (or both together —
			 * the natural way to end the chord) must ALSO fire the
			 * release-toggle; before, only a PLAY-first release did,
			 * so the gesture silently aborted most of the time (user:
			 * "mode takes ~4 s" = retries until a lucky stagger). */
			if (combo_start >= 0 && !combo_fired && fnp_presses < 2) {
				int64_t fnp_held2 = k_uptime_get() - combo_start;
				if (fnp_held2 >= 350 && fnp_held2 < 5000)
					fnp_mode_toggle();
			}
			if (!combo_seen &&
			    (k_uptime_get() - press_start) < 600) {
				/* M8a: FN-tap = TAP TEMPO (navigation moved into the
				 * FN hold). 1-3 taps: nothing. 4+ taps in steady
				 * rhythm: commit the grid — tempo from mean spacing,
				 * downbeat = the first tap. Every further tap refines. */
				/* M20 F9: the tap happened when the button went
				 * DOWN. Timing it at the release planted the whole
				 * grid late by however long the finger stayed on the
				 * button — tens of ms, different every tap — and F8
				 * could never see it, because refinement corrects
				 * SPACING and leaves PHASE alone. */
				int64_t tnow = press_start;
				uint64_t snow = press_start_s;
				/* M23-r6: a DOUBLE-TAP is faster than any tempo.
				 * The grid runs 50-200 BPM, i.e. 300-1200 ms
				 * between taps, so anything under 280 ms cannot
				 * be someone tapping time — it can only be a
				 * deliberate double. That is now what separates
				 * "clear the grid" from "round the BPM", instead
				 * of the tap COUNT, which the two gestures kept
				 * confusing each other over. */
				any_tap_t = tnow;
				if (tap_n > 0 && (tnow - tap_last > 1500 ||
				                  tnow - tap_last < 200)) tap_n = 0;
				if (tap_n > 1) {
					int64_t mean = (tap_last - tap_first) / (tap_n - 1);
					int64_t dvi = (tnow - tap_last) - mean;
					if (dvi < 0) dvi = -dvi;
					if (dvi * 5 > mean) tap_n = 0;  /* >20% off: new run */
				}
				if (tap_n == 0) { tap_first = tnow; tap_first_s = snow; }
				tap_last = tnow; tap_last_s = snow; tap_n++;
				if (tap_n >= 4) {
					/* M20 F9: the grid spacing comes from the SAMPLE
					 * clock — the same clock the audio is written
					 * with — instead of the millisecond uptime it used
					 * to be rounded through. One division, no trip
					 * through BPM and back, and 48000 ticks per second
					 * of resolution instead of 1000. */
					uint32_t nf = (uint32_t)((tap_last_s - tap_first_s) /
								 (uint64_t)(tap_n - 1));
					if (nf >= (48000u * 60u) / 200u &&
					    nf <= (48000u * 60u) / 50u) {   /* 50..200 BPM */
						uint32_t bpmq8 = (uint32_t)
							((48000ULL * 60u * 256u) / nf);
						/* M8c BEATMATCH: if this song already has
						 * loops, the tap run means "match THIS" —
						 * capture their native tempo first. */
						uint32_t native_q8 = 0;
						if (g_loop_len > 0u) {
							if (g_grid_bpm_q8[g_slot])
								native_q8 = g_grid_bpm_q8[g_slot];
							else if (g_beat_samples)
								native_q8 = (uint32_t)
									((48000ULL * 60u * 256u) /
									 g_beat_samples);
						}
						g_grid_bpm_q8[g_slot] = (uint16_t)bpmq8;
						g_grid_beat_frames = nf;   /* F9: exact */
						g_dbg_tap_bs = nf;         /* r2 diag */
						g_dbg_gbf0   = g_grid_beat_frames;   /* r6 */
						g_grid_fresh = 1;   /* M20 F1: taps = truth */
						g_grid_anchor = tap_first_s;
						g_grid_next_tick = g_sample_clock;
						g_grid_active = 1;
						g_grid_save_req = 1;
						{ uint64_t _bar = (uint64_t)g_grid_beat_frames * 4u;
			  g_grid_next_bar = g_grid_anchor +
				(((g_sample_clock - g_grid_anchor) / _bar) + 1u) * _bar; }
						if (native_q8) {
							/* retune the tape so the loops play at
							 * the tapped tempo (vinyl rules: pitch
							 * moves too), clamped to the physical
							 * 0.5-1.5x range, and restart the loops
							 * on the tapped downbeat at the next
							 * bar line — tempo AND phase matched. */
							uint64_t sp = ((uint64_t)bpmq8 << 16) /
								      native_q8;
							if (sp < 32768u) sp = 32768u;
							else if (sp > 98304u) sp = 98304u;
							g_play_speed_q16 = (uint32_t)sp;
							g_play_bpm = (int)((sp * 80u + 32768u) >> 16);
							if (g_play_bpm < BPM_MIN) g_play_bpm = BPM_MIN;
							if (g_play_bpm > BPM_MAX) g_play_bpm = BPM_MAX;
							g_grid_resync_at = g_grid_next_bar;
						}
					}
				}
			}
			all_off();
			/* If the combo was ended by lifting FUNCTION FIRST while PLAY is
			 * still down, swallow that trailing PLAY until it is released, so
			 * it can't leak into the normal decode as a restart / play-stop. */
			if (combo_seen &&
			    ladder_read(&adc_ladder[LAD_TRACKS]) >= 110) suppress_play = 1;
		}
		press_start = -1;
		combo_start = -1;
		combo_fired = 0;
		combo_seen  = 0;
		if (g_chop_defer) {
			/* M24: the gesture is over — pay once. The rings have been
			 * tracking the window all along, so this is a latency snap
			 * rather than a correction; the single dip covers whatever
			 * splice the last edit left in flight. Discrete presses do
			 * NOT come through here — they still take effect instantly,
			 * because chop is a rhythmic gesture and immediacy is the
			 * whole point of it. */
			g_chop_defer = 0;
			if (k_uptime_get() - g_defer_t < 150) {
				/* released mid-motion: the last edit's splice may still be
				 * in flight — settle as before (snap + one covering dip). */
				g_chop_req = 1;
				g_dip_req = 1;
			}
			/* r3: released after settling — the rings converged on the final
			 * window rounds ago (see the M24 comment above); snapping and
			 * dipping here was the audible FN-release silence. Skip both. */
		}
		if (fnp_pend_snap) {   /* M15-r3: released mid-window — still a double */
			fnp_pend_snap = 0;
			g_play_speed_q16 = 65536u;
			g_play_bpm = 80;
		}
		bj_cand = TRK_NONE; bj_cnt = 0; bj_fired = -1; fnp_edge = -1; fnp_chain = 0;
		g_pg_open = 0; pg_pend = -1;   /* PG-533: releasing FUNCTION closes the page */
		fnp_presses = 0;
		cp_cand = VOL_NONE; cp_cnt = 0; cp_dcl_band = -1;

		/* ---- looper controls + LEDs ---- */
		{
			/* FAILSAFE: Track1+Track4 combo (AIN0 ~1325, between T4 1220 and PLAY
			 * 1823) held ~1.2 s -> reset into the bootloader for reflashing. Checked
			 * BEFORE the normal decode so the combo isn't mistaken for a Track-4 press. */
			int trk_raw = ladder_read(&adc_ladder[LAD_TRACKS]);
			static int64_t combo14_t = -1;     /* when the 1+4 band was first seen */
			enum trk_btn raw;
			/* This DFU check runs BEFORE ctl_flush is consumed below, so clear
			 * the stale 1+4 timestamp here: after a FUNCTION+PLAY mode toggle
			 * (which freezes this block for the whole combo) a PLAY release
			 * sweeping through the 1280-1390 band must not find a >1.2 s-old
			 * combo14_t and reboot to the bootloader mid-performance. */
			static uint8_t combo_held;         /* M27: tracks seen during this gesture */
			static int combo_cand, combo_cnt;  /* M27-r3: two-pass confirm */
			if (ctl_flush) { combo14_t = -1; combo_held = 0; combo_cand = 0; combo_cnt = 0; }
			/* ===== M27-r3 COMBO DECODE =====================================
			 * Any set of track buttons pressed together makes its OWN code on this
			 * ladder. All sixteen states measured on hardware, all separable
			 * (SP1-BUTTON-LADDER-MAP.md):
			 *
			 *   idle    2 | T1   213 | T2    404 | 1+2   572 | T3    728
			 *   1+3   862 | 2+3  989 | 1+2+3 1100 | T4   1209 | 1+4  1303
			 *   2+4  1391 | 1+2+4 1470 | 3+4  1548 | 1+3+4 1618
			 *   2+3+4 1683 | ALL4 1743 | PLAY 1804
			 *
			 * Tightest gap 60 counts against +/-9 of noise. Bands are midpoints;
			 * anything unlisted falls through to decode_tracks(), which still owns
			 * idle / T1 / T2 / T3 / T4 / PLAY.
			 *
			 * THE HARD PART IS NOT THE BANDS, IT IS THE EDGES. Fingers neither
			 * land nor lift together, so pressing 2+3+4 walks
			 *   idle -> T2 -> 2+3 -> 2+3+4 -> 2+3 -> T2 -> idle
			 * Hence three rules, each of which fixed a real hardware symptom:
			 *  1. ACCUMULATE the mask (|=). r2 assigned it, so the 2+3 on the way
			 *     OUT overwrote 2+3+4 and track 4 was never toggled — 'muting 3
			 *     leaves one behind'.
			 *  2. Toggle only at TRUE IDLE, not merely when no combo is present:
			 *     the release sweep sits in single-button bands for several passes.
			 *  3. Require a combo to hold for TWO passes before accepting it. A
			 *     fast single press can transit a combo band for one sample on the
			 *     way up, which would otherwise mute tracks nobody pressed.
			 *
			 * Bit order: 1<<0 = track 1 ... 1<<3 = track 4. */
			int combo_now = 0;
			if      (trk_raw >=  488 && trk_raw <  650) combo_now = 0x3; /* 1+2   ~572  */
			else if (trk_raw >=  795 && trk_raw <  925) combo_now = 0x5; /* 1+3   ~862  */
			else if (trk_raw >=  925 && trk_raw < 1044) combo_now = 0x6; /* 2+3   ~989  */
			else if (trk_raw >= 1044 && trk_raw < 1154) combo_now = 0x7; /* 1+2+3 ~1100 */
			else if (trk_raw >= 1256 && trk_raw < 1347) combo_now = 0x9; /* 1+4   ~1303 */
			else if (trk_raw >= 1347 && trk_raw < 1430) combo_now = 0xA; /* 2+4   ~1391 */
			else if (trk_raw >= 1430 && trk_raw < 1509) combo_now = 0xB; /* 1+2+4 ~1470 */
			else if (trk_raw >= 1509 && trk_raw < 1583) combo_now = 0xC; /* 3+4   ~1548 */
			else if (trk_raw >= 1583 && trk_raw < 1650) combo_now = 0xD; /* 1+3+4 ~1618 */
			else if (trk_raw >= 1650 && trk_raw < 1713) combo_now = 0xE; /* 2+3+4 ~1683 */
			else if (trk_raw >= 1713 && trk_raw < 1773) combo_now = 0xF; /* ALL4  ~1743 */
			if (combo_now) {
				raw = TRK_NONE;          /* a combo must never reach the single decode */
				if (combo_now == combo_cand) { if (combo_cnt < 3) combo_cnt++; }
				else { combo_cand = combo_now; combo_cnt = 1; }
				if (combo_cnt >= 2) combo_held |= (uint8_t)combo_now;   /* rule 1 + 3 */
				if (combo_now == 0x9) {  /* ONLY exactly 1+4 arms the bootloader */
					/* time-based (not a +8/iter counter) so the diag-print path
					 * can't skew the threshold. */
					if (combo14_t < 0) combo14_t = k_uptime_get();
					else if (k_uptime_get() - combo14_t >= DFU_HOLD_MS) enter_dfu();
				} else {
					combo14_t = -1;
				}
			} else if (combo_held) {
				/* Mid-release: still sweeping down through single-button bands.
				 * Swallow everything and wait for TRUE idle (rule 2). */
				raw = TRK_NONE;
				combo14_t = -1;
				combo_cand = 0; combo_cnt = 0;
				if (trk_raw >= 0 && trk_raw < 110) {
					for (int _p = 0; _p < NTRK; _p++) {
						if (!(combo_held & (1u << _p))) continue;
						if (trk[_p].state == TS_EMPTY) continue;  /* nothing to mute */
						trk[_p].muted ^= 1u;
						if (g_slot < NUM_SLOTS) {
							if (trk[_p].muted)
								g_meta.song_mode[g_slot] |= (uint8_t)(0x10u << _p);
							else
								g_meta.song_mode[g_slot] &= (uint8_t)~(uint8_t)(0x10u << _p);
						}
					}
					if (g_slot < NUM_SLOTS) g_meta_save_req = 1;  /* mutes persist */
					combo_held = 0;
					suppress_play = 1;
				}
			} else {
				combo14_t = -1;
				combo_cand = 0; combo_cnt = 0;
				raw = decode_tracks(trk_raw);
			}
			/* trailing-PLAY guard (see the FUNCTION+PLAY combo exit): ignore
			 * the ladder until the RAW reading goes fully idle once, so a PLAY
			 * still held after the mode toggle — and its whole release sweep
			 * down through the track bands — never reaches the decode. Idle
			 * means the reading itself: 1280-1390 decodes as NONE but is NOT
			 * idle, and clearing there would expose the rest of the sweep. */
			if (suppress_play) {
				if (trk_raw >= 0 && trk_raw < 110) suppress_play = 0;
				else raw = TRK_NONE;
			}

			/* STICKY DEBOUNCE -> `committed` (the stable, settled button). Recording
			 * stops on RELEASE, so a single noisy ADC sample (audio/USB activity
			 * couples into the button ladder while a loop streams) must NOT look like
			 * a release: the committed button only changes after a DIFFERENT value is
			 * seen on 3 consecutive reads (~24 ms); a lone glitch back to the held
			 * value resets the counter, so a steady hold can never false-trigger. */
			static enum trk_btn committed = TRK_NONE, cand = TRK_NONE;
			static int cand_cnt;
			static int64_t cand_t0;              /* M96: first sighting of `cand` */
			static int64_t press_t[NTRK];        /* when committed first named this track */
			static int64_t tap_deadline[NTRK];   /* >0: a single tap awaiting a possible 2nd */
			static uint8_t armed_press[NTRK];    /* this press already armed a take */
			/* M44-r2 instant-arm bookkeeping: when the current arm fired,
			 * whether it was an instant EMPTY arm (migration only ever
			 * cancels those), and whether a press edge arrived from a
			 * HIGHER band (= that button's release down-sweep). */
			static int64_t arm_t;
			static uint8_t arm_was_instant;
			static uint8_t press_from_above[NTRK];
			static int stop_tap_trk = -1;        /* R1: stop already fired at press;
			                                      * swallow that press's release */
			static int64_t ep_time[TRK_PLAY + 1];/* committed ms per button, this episode */
			static int64_t ep_since;             /* when `committed` last changed */
			static uint8_t ep_open;              /* a press episode is in progress */
			static uint8_t ep_play_held;         /* this episode's PLAY press became a hold */
			static int64_t play_t = -1;          /* when PLAY was committed (hold timing) */
			static int     play_held;            /* this PLAY press already fired the restart */
			/* FUNCTION (or a USB transfer) owned the loop since the last pass
			 * here, so every static above is stale: a PLAY committed just
			 * before the combo froze this block would otherwise look like a
			 * long hold (phantom restart) and its open episode would fire a
			 * phantom play/stop on release. Reset everything and swallow the
			 * ladder until it reads idle. */
			if (ctl_flush) {
				ctl_flush = 0;
				committed = TRK_NONE; cand = TRK_NONE; cand_cnt = 0; cand_t0 = 0;
				for (int k = TRK_1; k <= TRK_PLAY; k++) ep_time[k] = 0;
				ep_open = 0; ep_play_held = 0;
				play_t = -1; play_held = 0;
				for (int k = 0; k < NTRK; k++) { tap_deadline[k] = 0; armed_press[k] = 0; }
				stop_tap_trk = -1;
				if (!(trk_raw >= 0 && trk_raw < 110)) suppress_play = 1;
				raw = TRK_NONE;
			}
			enum trk_btn before = committed;
			/* M96: TIME-BASED commit. Was `++cand_cnt >= 3`, i.e. three
			 * control passes -- which reads as 24 ms only while the pass
			 * runs every 8 ms. k_msleep(8) is a FLOOR; under corner load
			 * the pass stretches and the gesture stretched with it.
			 * Healthy behaviour is IDENTICAL: at an 8 ms pass the 2nd
			 * confirming read is at 16 ms (< 24), so commit still lands
			 * on the 3rd at ~24 ms. Glitch rejection unchanged -- a lone
			 * bad read still falls to the else and restarts the window. */
			if (raw == committed) {
				cand_cnt = 0;
			} else if (raw == cand) {
				int64_t _el96 = k_uptime_get() - cand_t0;
				if (++cand_cnt >= 2 && _el96 >= BTN_DEBOUNCE_MS) {
					committed = raw; cand_cnt = 0;
					g_stop_lat_ms = (uint32_t)_el96;
					if ((uint32_t)_el96 > g_stop_lat_max)
						g_stop_lat_max = (uint32_t)_el96;
				}
			} else {
				cand = raw; cand_cnt = 1; cand_t0 = k_uptime_get();
			}

			/* TRACK buttons:
			 *   HOLD (button physically down >= HOLD_RECORD_MS) -> RECORD (auto-start
			 *      then captures from the first sound). A quick tap never lasts this long.
			 *   TAP (released before that) -> MUTE / unmute.
			 *   DOUBLE-TAP (a 2nd tap within DTAP_GAP_MS of the 1st tap's release) -> DELETE.
			 * Tap-vs-hold is decided by the PHYSICAL down-time and double-tap by the
			 * rhythm of two quick taps, so taps/double-taps stay reliable regardless of
			 * how fast recording arms (a quick ~HOLD_RECORD_MS hold instead of 300ms).
			 *
			 * PRESS EPISODE tracker: one episode = the ladder leaving idle
			 * until it settles back at idle. A finger pressing or releasing a
			 * HIGHER ladder button sweeps the voltage THROUGH the lower
			 * buttons' bands, and the debounce can commit one of them for a
			 * beat (~24-32 ms) on the way — the old code treated every
			 * committed change as a real release edge and fired PHANTOM taps
			 * ("recording track 4 muted track 1"). Now committed-time is
			 * accumulated per button and the release action fires ONCE, at
			 * episode end, for the DOMINANT (longest-committed) button.
			 * Three rules keep the phantom window closed:
			 *   - a press edge wipes the accumulated time of every band BELOW
			 *     it (provably the up-sweep in transit, not a press);
			 *   - the episode only ends when the RAW reading is idle, so a
			 *     slow release dwelling in the 1280-1390 no-man's band (which
			 *     decodes as NONE) can't split one gesture into two;
			 *   - a dominant under 40 ms fires nothing (a real tap commits
			 *     ~40 ms+, a transit blip caps at ~32 ms per traversal).
			 * Hold actions (arm, restart) are duration-based and transit-immune. */
			if (committed != before) {
				int64_t tnow = k_uptime_get();
				if (before != TRK_NONE)
					ep_time[(int)before] += tnow - ep_since;
				ep_since = tnow;
				if (committed != TRK_NONE) {
					ep_open = 1;
					for (int k = TRK_1; k < (int)committed; k++)
						ep_time[k] = 0;  /* below = up-sweep transit */
					/* M44-r2 ARM MIGRATION: with instant empty arms, an
					 * up-sweep transit can arm a LOWER empty track for
					 * the ~24-32 ms the finger needs to land on the
					 * button it actually wants. The theft signature is
					 * this exact transition: a DIFFERENT button commits
					 * while a young (<=40 ms), still-silent instant arm
					 * waits. Cancel it — stop-on-ARMED is already the
					 * cancel and nothing was recorded; the real button
					 * then arms on its own press within a pass. Also
					 * catches PLAY presses sweeping the track bands. A
					 * fast roll between two empty tracks resolves to
					 * the LAST one — the finger's final word. */
					if (g_rec_track >= 0 &&
					    (int)committed != g_rec_track &&
					    arm_was_instant &&
					    trk[g_rec_track].state == TS_ARMED &&
					    tnow - arm_t <= 40) {
						g_stop_req = 1;
						armed_press[g_rec_track] = 0;
						arm_was_instant = 0;
					}
				}
				if (committed >= TRK_1 && committed <= TRK_4) { /* PRESS edge */
					int ti = (int)committed;
					press_t[ti] = tnow;
					armed_press[ti] = 0;
					/* M44-r2: from a HIGHER band = that button's release
					 * down-sweep; it must not instant-arm (the 48 ms
					 * floor below outlasts any transit). */
					press_from_above[ti] =
						(before > committed && before <= TRK_PLAY) ? 1u : 0u;
				}
			}
			if (ep_open && committed == TRK_NONE &&
			    trk_raw >= 0 && trk_raw < 110) {
				/* EPISODE END (ladder settled at idle): attribute the
				 * release to the button that was committed the longest. */
				ep_open = 0;
				int64_t tnow = k_uptime_get();
				int b = -1; int64_t bt = 0;
				for (int k = TRK_1; k <= TRK_PLAY; k++) {
					if (ep_time[k] > bt) { bt = ep_time[k]; b = k; }
				}
				/* Order matters: first decide the episode is REAL (its
				 * dominant out-lasts any possible transit blip), THEN decide
				 * which button owns it. */
				if (bt < 40) {
					b = -1;          /* pure transit blip: fire nothing */
				} else {
					/* ROLL-OFF ATTRIBUTION: a release sweep only ever dwells
					 * on bands BELOW the button that was really pressed (the
					 * ladder cannot overshoot above it, and up-sweep transit
					 * is wiped at the press edge). So when a lower band
					 * out-dwelt the HIGHEST committed button, prefer the
					 * highest — provided it was committed >=24 ms (a real
					 * contact, longer than debounce noise) and at least half
					 * the dominant's time. This keeps a quick stop-tap on the
					 * recording track from becoming a phantom mute with the
					 * take left running, and equally protects the taps right
					 * AFTER a take finalizes and lazy PLAY releases — the old
					 * rule only guarded the recording track, so the "did it
					 * stop?" and delete taps had no protection at all. */
					int H = -1;
					for (int k = TRK_PLAY; k >= TRK_1; k--)
						if (ep_time[k] >= 24) { H = k; break; }
					if (H > b && ep_time[H] * 2 >= bt) {
						b = H; bt = ep_time[H];
					}
				}
				for (int k = TRK_1; k <= TRK_PLAY; k++) ep_time[k] = 0;
				/* PHANTOM-ARM SWEEP GUARD: the empty-track 40 ms instant
				 * arm can be tripped by a slow roll toward a HIGHER button
				 * dwelling on an empty track in transit. The episode's
				 * dominant button tells the truth at release: any track
				 * that armed during this episode but is NOT the dominant
				 * was a transit artifact — cancel it (an ARMED take
				 * cancels losslessly; one that already caught sound
				 * finalizes tiny and double-tap deletes). */
				for (int x = 0; x < NTRK; x++) {
					if (!armed_press[x] || x == b) continue;
					armed_press[x] = 0;
					if (g_rec_track == x) {
						g_stop_req = 1;
						tap_deadline[x] = 0;
					}
				}
				if (b >= TRK_1 && b <= TRK_4) {
					int ti = b;
					if (ti == stop_tap_trk) {
						stop_tap_trk = -1;   /* R1: stop fired at press;
						                      * this release is spent */
					} else if (armed_press[ti]) {
						armed_press[ti] = 0;
						/* LATCHED RECORDING: releasing the arming hold
						 * does NOT stop the take — it records hands-free
						 * until the same track is tapped again or the
						 * region fills. (See the HOLD-ARM comment for why
						 * the momentary variant was rolled back.) */
					} else if ((g_rec_track == ti &&
						    (trk[ti].state == TS_ARMED ||
						     trk[ti].state == TS_REC)) ||
						   trk[ti].state == TS_DONE) {
						/* tap on the recording track = STOP
						 * (on ARMED-but-silent = cancel; on a
						 * just-auto-finalized TS_DONE take the
						 * tap is swallowed — never a mute or
						 * delete window on a fresh take). */
						g_stop_req = 1;
						tap_deadline[ti] = 0;
					} else if (tap_deadline[ti] > 0 && tnow <= tap_deadline[ti] &&
						   !g_heads_mode) {
						/* (heads mode: taps only mute — never
						 * delete or arm; the mode is playback) */
						/* PG-533: the base-layer toggle is REMOVED -- marc's
						 * rule: no gesture passes THROUGH mute. The toggle
						 * lives on the FN+hold-T4 MODE PAGE. A quick 2nd
						 * tap is just another mute; the DELETE dwell (kept,
						 * marc-approved) still owns the held 2nd tap. */
						tap_deadline[ti] = 0;
						trk[ti].muted = !trk[ti].muted;
					} else if (tap_deadline[ti] > 0 && tnow <= tap_deadline[ti]) {
						/* M15: heads mode double-tap = REVERSE that
						 * head. The first tap toggled the mute — undo
						 * it (and its persisted bit), flip direction,
						 * re-anchor this ring behind a blip. */
						tap_deadline[ti] = 0;
						trk[ti].muted = !trk[ti].muted;
						/* (no persistence — heads-only path, and
						 * M19a-r4 makes all head mutes session) */
						g_head_rev[ti] = !g_head_rev[ti];
						g_head_blip[ti] = 3;
						trk[ti].p_w = (g_consume_pos / TSPBI(ti)) * TSPBI(ti);
					} else {
						/* tap -> mute, INSTANT on gridded and
						 * ungridded songs alike (v2.0.0: the M8c
						 * bar-wait was removed after live testing —
						 * see the bar-service note). */
						trk[ti].muted = !trk[ti].muted;
						if (!g_heads_mode && g_slot < NUM_SLOTS) {
							/* M7-r4: remember per song — but NOT
							 * in heads mode (M19a-r4): head mutes
							 * are session performance state */
							uint8_t mb = (uint8_t)(0x10u << ti);
							if (trk[ti].muted) g_meta.song_mode[g_slot] |= mb;
							else               g_meta.song_mode[g_slot] &= (uint8_t)~mb;
							g_meta_save_req = 1;
						}
						tap_deadline[ti] = tnow + DTAP_GAP_MS;
					}
				} else if (b == TRK_PLAY) {
					/* PLAY tap -> toggle play/stop. ep_play_held was set
					 * the instant the hold-restart fired (a hold is not a
					 * tap). Ignored while a take is in progress: stopping
					 * would freeze the recording mid-take. */
					if (!ep_play_held && g_rec_track < 0) {
						g_playing = !g_playing;
						if (g_playing) g_midi_start_pending = 1;
						else           g_midi_stop_pending  = 1;
					}
				}
				ep_play_held = 0;
			}
			/* R1 STOP-ON-PRESS (perfect-loop): on the RECORDING track a
			 * press can only mean STOP — no mute/delete/arm ambiguity —
			 * so fire it once the commit has SUSTAINED ~48 ms (transit
			 * grazes commit for at most ~32 ms per the episode notes)
			 * instead of waiting for the release: the tap's physical
			 * duration (50-150 ms, different every time) no longer
			 * stretches the loop. CRITICAL: armed_press excludes the
			 * press that ARMED this take — releasing the arming hold
			 * stays latched (it must never read as a stop; without this
			 * the arm cancelled itself ~50 ms after arming). The
			 * episode-end handler above swallows this press's release;
			 * R2 backdates the remaining constant. */
			if (committed >= TRK_1 && committed <= TRK_4) {
				int ti = (int)committed;
				if (ti != stop_tap_trk && !armed_press[ti] &&
				    ((g_rec_track == ti &&
				      (trk[ti].state == TS_ARMED ||
				       trk[ti].state == TS_REC)) ||
				     trk[ti].state == TS_DONE) &&
				    k_uptime_get() - press_t[ti] >= 48) {
					g_stop_req = 1;
					tap_deadline[ti] = 0;
					stop_tap_trk = ti;
				}
			}
			/* HOLD-ARM, always LATCHED on release. EMPTY tracks arm after
			 * just 100 ms: a tap has no meaning there (nothing to mute or
			 * delete), so there is nothing to disambiguate — and 100 ms is
			 * above the realistic transit-graze range (blips commit
			 * 24-32 ms; only a deliberately lazy roll dwells ~100 ms+, and
			 * the episode-end sweep guard cancels those losslessly).
			 * Unlike the rolled-back 40 ms instant-arm there is NO
			 * provisional RAM-only phase here — flushing starts
			 * immediately, so the write pattern is identical to the
			 * release (the provisional's clumped catch-up burst was what
			 * starved playback at high tape speed). Content tracks keep
			 * the full HOLD_RECORD_MS so tap-mute stays instant. The
			 * hold-duration MOMENTARY variant stays rolled back: with a
			 * slow arm its latch window collapsed to a sliver and broke
			 * hands-free recording. */
			if (committed >= TRK_1 && committed <= TRK_4) {
				int ti = (int)committed;
				int empt = (trk[ti].state == TS_EMPTY &&
					    !(g_slot < NUM_SLOTS && g_meta.slot[g_slot].present[ti]));
				if (g_heads_mode && !armed_press[ti] &&
				    ti != stop_tap_trk && heads_engaged() &&
				    trk[ti].state == TS_PLAY && ti != (int)g_head_src &&
				    k_uptime_get() - press_t[ti] >= 400) {
					/* M19a: in heads mode, HOLD a LOADED track =
					 * make IT the tape ("hold the loop you want
					 * to head"). All other rings re-anchor behind
					 * per-track blips; positions and directions
					 * are KEPT — they are the performance. The
					 * press is spent via armed_press (its release
					 * is swallowed by the latched-arm branch), so
					 * it can never read as a mute. Empty-track
					 * holds are reserved for the M19b bounce. */
					g_head_src = (uint8_t)ti;
					for (int hk = 0; hk < NTRK; hk++) {
						if (hk == ti) continue;
						g_head_blip[hk] = 3;
						trk[hk].p_w = (g_consume_pos /
							TSPBI(hk)) * TSPBI(hk);
					}
					armed_press[ti] = 1;   /* spend the press */
					tap_deadline[ti] = 0;
				}
				if (g_heads_mode && !armed_press[ti] &&
				    ti != stop_tap_trk && heads_engaged() &&
				    trk[ti].state == TS_EMPTY &&
				    !(g_slot < NUM_SLOTS && g_meta.slot[g_slot].present[ti]) &&
				    g_bnc_req < 0 && !g_bnc_active && !g_bnc_done &&
				    k_uptime_get() - press_t[ti] >= 400) {
					/* M19b: in heads mode, HOLD an EMPTY track =
					 * PRINT the tape into it ("record this into
					 * here" — because it is). Everything audible is
					 * snapshotted NOW; the streamer renders while
					 * the heads keep playing; the dst fast-blinks.
					 * All heads silent = the shrug (locked: a
					 * silent bounce is never what anyone meant). */
					int aud = 0;
					for (int hk2 = 0; hk2 < NTRK; hk2++)
						if (!trk[hk2].muted && trk[hk2].vol_q8 > 0)
							aud = 1;
					if (!aud) {
						g_led_shrug = 20;
					} else {
						struct looptrk *bs = &trk[g_head_src];
						uint32_t gb = bs->len_blocks ? bs->len_blocks
							    : (g_loop_blocks ? g_loop_blocks : 1u);
						uint32_t cdiv = g_chop_div ? g_chop_div : 1u;
						uint32_t coff = g_chop_off;
						uint32_t cyc, win, wbase, wper;
						if (g_fixed_len && g_loop_blocks &&
						    gb >= g_loop_blocks &&
						    (gb % g_loop_blocks) == 0u) {
							wper = g_loop_blocks;
							win = wper / cdiv; if (!win) win = 1u;
							wbase = (coff * wper) / cdiv;
							if (wbase + win > wper) wbase = wper - win;
							cyc = (gb / wper) * win;
						} else {
							wper = gb;
							win = gb / cdiv; if (!win) win = 1u;
							wbase = (coff * gb) / cdiv;
							if (wbase + win > gb) wbase = gb - win;
							cyc = win;
						}
						if (g_win_free) {
							uint32_t ws = g_win_s8, we = g_win_e8;
							if (we < ws) { uint32_t t2 = ws; ws = we; we = t2; }
							win = ((we - ws + 1u) * wper) >> 8;
							if (!win) win = 1u;
							wbase = (ws * wper) >> 8;
							if (wbase + win > wper) wbase = wper - win;
							cyc = (gb / wper) * win;
						}
						bnc_src = g_head_src;
						bnc_dst = (uint8_t)ti;
						for (int hk2 = 0; hk2 < NTRK; hk2++) {
							bnc_pos[hk2] = g_head_pos[hk2];
							bnc_rev[hk2] = g_head_rev[hk2];
							bnc_mut[hk2] = trk[hk2].muted;
							bnc_vol[hk2] = trk[hk2].vol_q8;
						}
						bnc_wfree = g_win_free; bnc_wrev = g_win_rev;
						bnc_cyc = cyc; bnc_win = win;
						bnc_wbase = wbase; bnc_wper = wper;
						bnc_start = bs->start_blk;
						bnc_content = bs->content_blocks
							    ? bs->content_blocks : gb;
						bnc_done_blocks = 0;
						{	/* GS-531: the bounce accumulator is 280-frame
							 * geometry; a P16M source would overflow it
							 * (496*3 > 1024). Refuse with the shrug until
							 * the accumulator learns mixed geometry. */
							uint8_t _p16s = 0;
							for (int _j = 0; _j < NTRK; _j++)
								if (trk[_j].p16m && trk[_j].state == TS_PLAY)
									_p16s = 1;
							if (_p16s) {
								g_led_shrug = 1;   /* the M19b 'no' */
								armed_press[ti] = 1;
								tap_deadline[ti] = 0;
							} else {
								__DSB();   /* snapshot lands before the request */
								g_bnc_req = (int8_t)ti;
							}
						}
					}
					armed_press[ti] = 1;   /* spend the press */
					tap_deadline[ti] = 0;
				}
				/* GS-531 (map v2 row 99): DOUBLE-TAP-AND-HOLD = DELETE. The press
			 * began inside the window (stable test: the deadline is only
			 * consumed by the quick-toggle or by this delete, so it cannot
			 * lapse mid-hold) and has dwelt DTAP_DEL_HOLD_MS. */
			if (!armed_press[ti] && ti != stop_tap_trk && !g_heads_mode &&
			    tap_deadline[ti] > 0 && press_t[ti] <= tap_deadline[ti] &&
			    k_uptime_get() - press_t[ti] >= DTAP_DEL_HOLD_MS) {
				tap_deadline[ti] = 0;
				g_del_req[ti] = 1;
				trk[ti].muted = 0;
				armed_press[ti] = 1;   /* spend the press: its release
				                        * must not read as a mute */
			}
			if (!armed_press[ti] && ti != stop_tap_trk &&
				    g_rec_track < 0 && !g_heads_mode &&
				    !(tap_deadline[ti] > 0 &&
				      press_t[ti] <= tap_deadline[ti]) &&   /* GS-531: inside the
				      * double-tap window a hold means DELETE (below), never ARM */
				    trk[ti].state != TS_DONE &&
				    k_uptime_get() - press_t[ti] >=
				        (empt ? (((g_grid_active && g_grid_fresh) ||
				                  !press_from_above[ti])
				                 ? 0 : EMPTY_ARM_MS)   /* M44-r2: instant
				                  * from idle/lower; 48 ms only for the
				                  * release down-sweep case */
				              : HOLD_RECORD_MS)) {
					/* A-r2: on a FRESH-TAPPED grid an empty track
					 * arms at the press COMMIT (~25-30 ms) — the
					 * 100 ms filter made pressing ON the beat the
					 * worst possible phase (the line passed during
					 * the filter and the punch waited a whole
					 * beat; marc's "small delay"). Press ~40 ms
					 * before the line and the punch catches it
					 * sample-exact; a committed graze merely arms
					 * a visible fast-blink, cancellable with a
					 * tap. */
					/* v2.0.0: the gridded re-record hold is HOLD_RECORD_MS
					 * again. M8b-r5 trimmed it to 120 ms ("the punch waits
					 * for the bar anyway") but real taps measure 50-150 ms
					 * (the R1 notes), so the top of the tap band was ARMING
					 * RE-RECORDS on gridded songs — eating the 2nd tap of
					 * double-tap delete and zeroing its window (user found
					 * it as "delete works worse on gridded songs"). The
					 * 60 ms the trim saved was invisible anyway: an overdub
					 * punch waits for the bar regardless. Empty tracks keep
					 * the 100 ms instant arm (a tap means nothing there). */
					/* g_rec_track < 0: one take at a time — while a latched
					 * take runs, holding ANY track does nothing (no phantom
					 * arm, no forced g_playing). state != TS_DONE: a hold on
					 * a just-auto-finalized take (user trying to stop it)
					 * must not silently arm a latched re-record that would
					 * overwrite the take it is still flushing.
					 * ti != stop_tap_trk (M8b-r4): the press that STOPPED a
					 * take is SPENT — R1 stops fire at press-down, so the
					 * finger is still on the button while the take flushes;
					 * once it lands back in TS_PLAY the TS_DONE guard no
					 * longer covers it, and a deliberate 200-400 ms stop
					 * press re-armed a re-record that overwrote the loop
					 * just made (user report; the grid punch then started
					 * it recording all by itself). Arming requires a FRESH
					 * press — the latch clears at episode end. */
					armed_press[ti] = 1;
					arm_t = k_uptime_get();          /* M44-r2 */
					arm_was_instant = empt ? 1u : 0u;
					tap_deadline[ti] = 0;            /* a hold cancels a pending single-tap */
					{	/* A-r2: remember when the FINGER landed,
						 * in engine samples (approximate the
						 * elapsed ms back from now). M44: plus the
						 * constant pipeline latency press_t itself
						 * cannot see (debounce + pass), so the
						 * stamp lands on the touchdown. */
						int64_t _ago = k_uptime_get() - press_t[ti]
						             + PRESS_COMP_MS;
						if (_ago < 0) _ago = 0;
						uint64_t _sc = g_sample_clock;
						uint64_t _back = (uint64_t)_ago * 48u;
						g_arm_press_sclk =
							(_sc > _back) ? (_sc - _back) : _sc;
					}
					g_arm_req[ti] = 1;
					g_playing = 1;                   /* recording implies play */
				}
			}
			g_dbg_btn = (int)committed;                      /* diag: settled button */

			/* PLAY/STOP button: a short TAP toggles play/stop in place (tape ramp);
			 * a HOLD (>=400 ms) jumps to the START of the song and plays — a reliable
			 * "play the whole thing from the top" that never depends on current state. */
			if (committed == TRK_PLAY) {
				if (play_t < 0) { play_t = k_uptime_get(); play_held = 0; }
				else if (!play_held && (k_uptime_get() - play_t) >= 400) {
					g_restart_req = 1; play_held = 1;        /* hold -> play from start */
					/* mark the episode a hold NOW — a clean PLAY->idle
					 * release dispatches the episode end before this block
					 * runs again; marking it at release was too late (the
					 * "tap" toggle fired right after the restart and the
					 * stale flag then swallowed the next genuine tap). */
					ep_play_held = 1;
				}
			} else {
				play_t = -1;
			}

			if (g_bnc_done) {
				/* M19b COMPLETION: every audio block is on flash —
				 * NOW the index (torn-write doctrine), then the
				 * locked auto-exit: mutes restored, the print plays
				 * unmuted, in phase with the loop it came from. */
				g_bnc_done = 0;
				int bd = (int)bnc_dst;
				trk[bd].len_blocks = bnc_cyc;
				trk[bd].content_blocks = bnc_cyc;
				trk[bd].start_blk = bnc_start;
				trk[bd].len_samps = bnc_cyc * TSPBI(bd);   /* prints stay block loops */
				trk[bd].start_samps = bnc_start * TSPBI(bd);
				trk[bd].muted = 0;
				trk[bd].p_w = (g_consume_pos / TSPBI(bd)) * TSPBI(bd);
				trk[bd].state = TS_PLAY;
				if (g_slot < NUM_SLOTS) {
					g_meta.slot[g_slot].present[bd] = 1;
					g_meta.slot[g_slot].trk_len[bd] = bnc_cyc;
					g_meta.slot[g_slot].trk_start[bd] = bnc_start;
					g_meta.trk_content[g_slot][bd] = bnc_cyc;
					g_meta.song_mode[g_slot] &=
						(uint8_t)~(uint8_t)(0x10u << bd);
					g_meta_save_req = 1;
				}
				g_heads_mode = 0;
				for (int hm = 0; hm < NTRK; hm++) {
					if (hm == bd) continue;
					trk[hm].muted = (uint8_t)
						((g_head_mute_save >> hm) & 1u);
					trk[hm].p_w = (g_consume_pos /
						TSPBI(hm)) * TSPBI(hm);
				}
				g_dip_req = 1;
			}
#if HP_TIM_TEST
			/* HEADPHONE AUTO-MUTE: poll the codec jack-detect ~5x/s and mute the
			 * speaker while headphones are in. Debounced (3 consecutive equal
			 * reads) so a single noisy read can't flip it; failed reads hold. */
			if (g_hp_on == 1) {
				static int hp_poll, hp_cand = -1, hp_cnt;
				if (++hp_poll >= 5) {            /* ~40 ms */
					hp_poll = 0;
					int c = hp_detect_connected();
					if (c >= 0) {
						if (c == hp_cand) {
							if (++hp_cnt >= 3 && c != g_hp_in) {
								g_hp_in = c;
								tas_set_speaker(!c);
							}
						} else { hp_cand = c; hp_cnt = 1; }
					}
				}
			}
#endif

			/* faders -> per-track volume (Q8); ~0..3700 maps to 0..256 (unity).
			 * ROUND-ROBIN one fader per pass (each still updates every ~32 ms —
			 * imperceptible for a volume slider) to keep the main loop's blocking
			 * ADC time low; see the ladder_read comment for why that matters. */
			{
				static int fi;
				int fv = ladder_read(&adc_ladder[LAD_FADER0 + fi]);
				if (fv >= 0) {        /* ADC error -> hold the last volume */
					uint32_t q = (uint32_t)fv * 256u / 3700u;
					if (q > 256u) q = 256u;
					/* M14: a fader that was scrubbing a head keeps its
					 * OLD volume until it rejoins it (±6%) or crosses
					 * it — no volume jump on FUNCTION release. */
					if (g_fh_latch[fi]) {
						int d = (int)q - (int)trk[fi].vol_q8;
						int p = g_fh_lastq[fi];
						g_fh_lastq[fi] = (int)q;
						if ((d >= -15 && d <= 15) ||
						    (p >= 0 &&
						     ((p - (int)trk[fi].vol_q8 > 0) != (d > 0))))
							g_fh_latch[fi] = 0;
					}
					if (!g_fh_latch[fi])
						trk[fi].vol_q8 = (uint16_t)q;
				}
				fi = (fi + 1) & 3;
			}

			/* VOL ladder (master vol buttons + FWD/RWD varispeed rocker), DEBOUNCED
			 * the same sticky way as the tracks — it sits on the same noisy rail and
			 * single raw reads were causing spurious volume/tempo jumps. */
			static enum vol_btn vcommit = VOL_NONE, vcand = VOL_NONE;
			static int vcnt;
			enum vol_btn vraw = decode_vol(ladder_read(&adc_ladder[LAD_VOL]));
			enum vol_btn vbefore = vcommit;
			if (vraw == vcommit)       { vcnt = 0; }
			else if (vraw == vcand)    { if (++vcnt >= 3) { vcommit = vraw; vcnt = 0; } }
			else                       { vcand = vraw; vcnt = 1; }

			/* master volume: one perceptual (~3 dB) step per fresh press, along
			 * g_vol_table[] — gradual from full (256) down to fully muted (0).
			 * Hold to repeat for a quick sweep. */
			{
				static int64_t vrep_t = -1, vrep_last;
				int vdir = (vcommit == VOL_UP) ? 1 : (vcommit == VOL_DOWN) ? -1 : 0;
				int vstep = 0;
				if (vdir != 0) {
					int64_t tnow = k_uptime_get();
					if (vcommit != vbefore) { vstep = 1; vrep_t = tnow; vrep_last = tnow; }
					else if (tnow - vrep_t >= 500 && tnow - vrep_last >= 110) {
						vstep = 1; vrep_last = tnow;
					}
				} else { vrep_t = -1; }
				if (vstep) {
					g_vol_idx += vdir;
					if (g_vol_idx < 0) g_vol_idx = 0;
					if (g_vol_idx > VOL_STEPS) g_vol_idx = VOL_STEPS;
					g_master_vol_q8 = g_vol_table[g_vol_idx];
				}
			}
			/* FWD/RWD rocker -> tempo, 1 BPM PER CLICK for fine control (the old
			 * version ramped ~37 BPM/s — way too coarse). Holding repeats slowly
			 * (~12 BPM/s) after 600 ms so big jumps don't need 40 clicks. Speed is
			 * derived exactly from the integer BPM, so 80 = exactly 1.0x.
			 * DOUBLE-CLICK (a 2nd click within 350 ms, same direction) = jump a
			 * SEMITONE: snap to the next 2^(k/12) grid point (see k_semi_q16),
			 * computed from the speed BEFORE the first click so the +/-1 BPM
			 * that click already applied is absorbed, not compounded. Further
			 * quick clicks chain more semitones. Single click and hold are
			 * exactly as before. */
			{
				static int64_t tempo_t = -1, tempo_last;
				static int64_t dclick_t;        /* last fresh click (0 = none) */
				static int     dclick_dir;      /* its direction */
				static uint32_t dclick_base;    /* the speed BEFORE that click */
				/* tempo LOCKED while a take is in flight: a mid-take speed
				 * glide records the warp into the loop (tape-bend artifact) */
				int dir = (g_rec_track >= 0) ? 0 :
					  (vcommit == VOL_TEMPO_UP) ? 1 :
					  (vcommit == VOL_TEMPO_DOWN) ? -1 : 0;
				int step = 0;
				if (dir != 0) {
					int64_t tnow = k_uptime_get();
					if (vcommit != vbefore) {            /* fresh click */
						if (dclick_t != 0 && dir == dclick_dir &&
						    tnow - dclick_t <= 350) {
							/* DOUBLE-CLICK -> next semitone */
							uint32_t ns = semitone_next(dclick_base, dir);
							int b = (int)(((uint64_t)ns * LOOP_BPM_BASE
								       + 32768u) / 65536u);
							if (b < BPM_MIN) {
								b = BPM_MIN;
								ns = (uint32_t)b * 65536u / LOOP_BPM_BASE;
							} else if (b > BPM_MAX) {
								b = BPM_MAX;
								ns = (uint32_t)b * 65536u / LOOP_BPM_BASE;
							}
							g_play_bpm = b;
							g_play_speed_q16 = ns;
							dclick_base = ns;   /* chain steps the grid */
							dclick_t = tnow;
							tempo_t = -1;       /* a double never hold-repeats */
						} else {
							dclick_base = g_play_speed_q16;
							dclick_dir  = dir;
							dclick_t    = tnow;
							step = 1; tempo_t = tnow; tempo_last = tnow;
						}
					} else if (tempo_t >= 0 && tnow - tempo_t >= 600 &&
						   tnow - tempo_last >= 80) {  /* slow hold-repeat */
						step = 1; tempo_last = tnow;
						dclick_t = 0;   /* a hold is not a click */
					}
				} else {
					tempo_t = -1;
				}
				if (step) {
					int b = g_play_bpm + dir;
					if (b < BPM_MIN) b = BPM_MIN;
					if (b > BPM_MAX) b = BPM_MAX;
					g_play_bpm = b;
					g_play_speed_q16 = (uint32_t)b * 65536u / LOOP_BPM_BASE;
				}
			}

			led_service();         /* one owner: song row + track row + standby */
			feed_wdt();
			k_msleep(8);
		}
	}

	return 0;
}
