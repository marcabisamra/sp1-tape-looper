/*
 * ============================================================================
 *  SP-1 eMMC flash driver  (1-bit MMC protocol over the nRF52840)
 * ============================================================================
 *  The SP-1's 4 GB flash is wired to the nRF with just three lines (CLK, CMD,
 *  DAT0) — "1-bit" MMC mode. This driver speaks that protocol in two layers:
 *
 *    * COMMAND / control phases (init, CMD17/18/24/25 headers, the write-status
 *      token, busy polling) are bit-banged on GPIO. They are short and timing-
 *      insensitive, so simple software toggling is fine.
 *
 *    * The 512-byte DATA payloads — the throughput-critical part — ride the
 *      nRF's SPIM3 SPI engine with DMA at 16 MHz (eMMC default-speed mode
 *      allows up to 26 MHz). This is ~40x faster than bit-banging the data and
 *      frees the CPU during each transfer. SPIM3 is the only SPI instance that
 *      runs above 8 MHz, and is otherwise unused in this firmware.
 *
 *  INTEGRITY: every block read is verified against the card's CRC16, and every
 *  block write checks the card's CRC-status token. On a mismatch the call
 *  returns false and the caller retries — so the fast bus is self-correcting
 *  (emmc_crc_rd_errs / emmc_crc_wr_errs count any catches).
 *
 *  Protocol logic is ported from Tim Knapen's SP-1-dev emmc.c; the SPIM3 data
 *  path and CRC enforcement are additions for the looper's bandwidth needs.
 * ============================================================================
 */
#include "sp1_emmc.h"
#include <zephyr/kernel.h>
#include <soc.h>            /* NRF_P0 register block for the fast data loops */
#include <hal/nrf_gpio.h>
#include <string.h>

/* Pins (from Tim Knapen's stemplayer_pins.h) */
#define PIN_EMMC_CLK   NRF_GPIO_PIN_MAP(0, 6)
#define PIN_EMMC_DAT0  NRF_GPIO_PIN_MAP(0, 7)
#define PIN_EMMC_CMD   NRF_GPIO_PIN_MAP(0, 8)
#define PIN_EMMC_RST   NRF_GPIO_PIN_MAP(1, 8)
#define PIN_EMMC_VCCQ  NRF_GPIO_PIN_MAP(0, 14)

#define CMD_SAFE_HALF_US 1u   /* slow clock for the IDENTIFICATION phase only */

/* Command-phase half-period: starts safe (eMMC identification requires a slow
 * clock), switched to 0 (full-speed bit-bang, ~1-2 MHz) once init completes —
 * the data path already proved the bus at 8 MHz, and each CMD18/CMD25/CMD12
 * handshake at the slow clock cost ~400-600 us of pure overhead per chunk. */
static uint32_t s_cmd_half_us = CMD_SAFE_HALF_US;

volatile uint32_t g_emmc_clk_half_us = CMD_SAFE_HALF_US;

static bool s_ready;
static uint32_t s_rca;

/* diagnostics (see header) */
bool    emmc_dbg_cmd0_sent;
int     emmc_dbg_cmd1_retries = -1;
bool    emmc_dbg_cmd2_resp;
bool    emmc_dbg_cmd3_resp;
bool    emmc_dbg_cmd7_resp;
bool    emmc_dbg_cmd16_resp;
uint8_t emmc_dbg_ocr[6];
uint8_t emmc_dbg_r1[6];
bool    emmc_dbg_last_cmd_resp;
int     emmc_dbg_resp_clocks = -1;   /* clocks until last response start bit */
int     emmc_dbg_cmd2_clocks = -1;   /* same, captured specifically for CMD2 */
int     emmc_dbg_cmd2_tries  = 0;    /* how many CMD2 attempts before a response */
int     emmc_dbg_wr_status   = -1;   /* CRC status token from last block write */
uint16_t emmc_dbg_rd_crc     = 0;    /* CRC16 the card appended to last read block */

#define CLK_HIGH()   nrf_gpio_pin_set(PIN_EMMC_CLK)
#define CLK_LOW()    nrf_gpio_pin_clear(PIN_EMMC_CLK)
#define CMD_HIGH()   nrf_gpio_pin_set(PIN_EMMC_CMD)
#define CMD_LOW()    nrf_gpio_pin_clear(PIN_EMMC_CMD)
#define DAT0_HIGH()  nrf_gpio_pin_set(PIN_EMMC_DAT0)
#define DAT0_LOW()   nrf_gpio_pin_clear(PIN_EMMC_DAT0)
#define DAT0_IN()    nrf_gpio_cfg_input(PIN_EMMC_DAT0, NRF_GPIO_PIN_PULLUP)
/* DAT0 as a HIGH-DRIVE output (H0H1) so writes have fast, clean edges. */
#define DAT0_OUT()   nrf_gpio_cfg(PIN_EMMC_DAT0, NRF_GPIO_PIN_DIR_OUTPUT, \
				  NRF_GPIO_PIN_INPUT_DISCONNECT, NRF_GPIO_PIN_NOPULL, \
				  NRF_GPIO_PIN_H0H1, NRF_GPIO_PIN_NOSENSE)
#define CMD_IN()     nrf_gpio_cfg_input(PIN_EMMC_CMD, NRF_GPIO_PIN_PULLUP)
#define CMD_OUT()    nrf_gpio_cfg_output(PIN_EMMC_CMD)
#define READ_CMD()   nrf_gpio_pin_read(PIN_EMMC_CMD)
#define READ_DAT0()  nrf_gpio_pin_read(PIN_EMMC_DAT0)

/* Direct port-0 register access for the throughput-critical DATA loops.
 * CLK = P0.06 (bit 6), DAT0 = P0.07 (bit 7) — both on GPIO port 0. These are
 * ~3 cycles each vs ~130 for the nrf_gpio HAL calls, which is what pinned the
 * bit-bang at ~58 KB/s. The command/init path keeps the HAL macros above. */
#define P0_CLK_BIT   (1u << 6)
#define P0_DAT_BIT   (1u << 7)
#define RCLK_HIGH()  (NRF_P0->OUTSET = P0_CLK_BIT)
#define RCLK_LOW()   (NRF_P0->OUTCLR = P0_CLK_BIT)
#define RDAT_HIGH()  (NRF_P0->OUTSET = P0_DAT_BIT)
#define RDAT_LOW()   (NRF_P0->OUTCLR = P0_DAT_BIT)
#define RDAT_GET()   ((NRF_P0->IN >> 7) & 1u)
/* A few NOPs of settle after a clock edge for the delay-free (hd==0) path:
 * covers the card's data-output valid time without throttling to a busy-wait. */
#define EDGE_SETTLE() __asm__ volatile("nop\nnop\nnop")
#define HALF(hd)      do { if (hd) { k_busy_wait(hd); } } while (0)

/* ===== SPIM2 hardware-accelerated DATA path ===================================
 * The bit-bang moves data at ~1.3 Mbit/s with the CPU pinned for every bit;
 * SPIM3 + EasyDMA clocks the identical wire format at 16 MHz with the CPU free.
 * eMMC DAT0 at default speed is SPI-mode-0 compatible: the host launches data
 * while CLK is low, the card samples (and launches) on the rising edge, MSB
 * first. Only the raw 512-byte payloads ride SPIM; commands, start-bit hunts,
 * the CRC-status token and busy polling stay bit-banged (slow, protocol-
 * fiddly, timing-insensitive phases). SPIM3 (0x4002F000) is the only SPIM that
 * supports >8MHz and is otherwise unused (I2C=TWIM0, UARTE1 deleted). */
/* 16 MHz on SPIM3 (the only instance with >8MHz). eMMC default-speed mode
 * allows <=26 MHz, so this is in spec; the CRC verify+retry layer catches any
 * signal-integrity errors at the higher rate (watch rerr=/werr= in the diag).
 * SPIM3 anomaly 198 (TX corruption on concurrent RAM access) is covered by the
 * same integrity layer: a corrupted write is rejected by the card and retried. */
#define SPIM_FREQ_M16 0x0A000000u
static bool   s_spim_ok;
static uint8_t s_dma_tx[517];        /* FF gap | FE start | 512 | CRC16 | FF */
static uint8_t s_dma_rx[514];        /* 512 data | CRC16 (byte-aligned)      */

static void spim_data_init(void)
{
	NRF_SPIM3->ENABLE    = 0;
	NRF_SPIM3->PSEL.SCK  = PIN_EMMC_CLK;
	NRF_SPIM3->PSEL.MOSI = 0xFFFFFFFFu;  /* attached per-transfer */
	NRF_SPIM3->PSEL.MISO = 0xFFFFFFFFu;
	NRF_SPIM3->PSEL.CSN  = 0xFFFFFFFFu;
	NRF_SPIM3->FREQUENCY = SPIM_FREQ_M16;
	NRF_SPIM3->CONFIG    = 0;            /* MSB first, CPOL0/CPHA0 (mode 0) */
	NRF_SPIM3->ORC       = 0xFF;         /* idle-high filler */
	s_spim_ok = true;
}

/* One blocking DMA transfer with the wires temporarily owned by SPIM. While
 * ENABLED the peripheral drives SCK (+MOSI for TX) / samples MISO; on disable
 * the pins fall back to their GPIO latches (CLK low, DAT0 as configured), so
 * the surrounding bit-bang phases continue seamlessly. ~65 us per 64 bytes. */
static void spim_xfer(const uint8_t *tx, uint32_t txlen, uint8_t *rx, uint32_t rxlen)
{
	NRF_SPIM3->PSEL.MOSI = tx ? PIN_EMMC_DAT0 : 0xFFFFFFFFu;
	NRF_SPIM3->PSEL.MISO = rx ? PIN_EMMC_DAT0 : 0xFFFFFFFFu;
	NRF_SPIM3->ENABLE    = 7;
	NRF_SPIM3->TXD.PTR    = (uint32_t)tx;
	NRF_SPIM3->TXD.MAXCNT = tx ? txlen : 0;
	NRF_SPIM3->RXD.PTR    = (uint32_t)rx;
	NRF_SPIM3->RXD.MAXCNT = rx ? rxlen : 0;
	NRF_SPIM3->EVENTS_END = 0;
	NRF_SPIM3->TASKS_START = 1;
	while (!NRF_SPIM3->EVENTS_END) {
		/* ~260 us for a full block at 16 MHz */
	}
	NRF_SPIM3->ENABLE = 0;
}

static inline void half_delay(uint32_t us)
{
	if (us) {
		k_busy_wait(us);
	}
}

/* Safe clock pulse for command/CRC phases. */
static inline void clk_pulse(void)
{
	CLK_HIGH();
	half_delay(s_cmd_half_us);
	CLK_LOW();
	half_delay(s_cmd_half_us);
}

static void cmd_send_bit(uint8_t bit)
{
	CMD_OUT();
	if (bit) {
		CMD_HIGH();
	} else {
		CMD_LOW();
	}
	clk_pulse();
}

static uint8_t cmd_recv_bit(void)
{
	CMD_IN();
	CLK_HIGH();
	half_delay(s_cmd_half_us);
	uint8_t b = (uint8_t)READ_CMD();
	CLK_LOW();
	half_delay(s_cmd_half_us);
	return b;
}

static uint8_t crc7(const uint8_t *data, uint8_t len)
{
	uint8_t crc = 0;
	for (uint8_t i = 0; i < len; i++) {
		uint8_t byte = data[i];
		for (int b = 7; b >= 0; b--) {
			crc <<= 1;
			if (((byte >> b) & 1) ^ ((crc >> 7) & 1)) {
				crc ^= 0x09;
			}
			crc &= 0x7F;
		}
	}
	return (crc << 1) | 1;
}

/* CRC error counters: at 8 MHz SPIM speeds, occasional bit errors are a fact of
 * life on this bus — every read is now verified and every write's CRC-status
 * token is enforced, with the caller retrying. These count the catches. */
volatile uint32_t emmc_crc_rd_errs;
volatile uint32_t emmc_crc_wr_errs;

/* Table-driven CRC16-CCITT: the bitwise version costs ~14% CPU at the 48 kHz
 * read rate; the table costs ~1%. Built once at init. */
static uint16_t s_crc16_tab[256];
static void crc16_tab_init(void)
{
	for (uint32_t i = 0; i < 256; i++) {
		uint16_t crc = (uint16_t)(i << 8);
		for (int b = 0; b < 8; b++)
			crc = (crc & 0x8000) ? (uint16_t)((crc << 1) ^ 0x1021)
					     : (uint16_t)(crc << 1);
		s_crc16_tab[i] = crc;
	}
}
static uint16_t crc16(const uint8_t *data, uint32_t len)
{
	uint16_t crc = 0;
	for (uint32_t i = 0; i < len; i++)
		crc = (uint16_t)((crc << 8) ^ s_crc16_tab[(crc >> 8) ^ data[i]]);
	return crc;
}

static bool send_command(uint8_t cmd_index, uint32_t arg, uint8_t *r1_out)
{
	uint8_t frame[6];
	frame[0] = 0x40 | (cmd_index & 0x3F);
	frame[1] = (uint8_t)(arg >> 24);
	frame[2] = (uint8_t)(arg >> 16);
	frame[3] = (uint8_t)(arg >> 8);
	frame[4] = (uint8_t)(arg);
	frame[5] = crc7(frame, 5);

	CMD_OUT();
	cmd_send_bit(0);
	cmd_send_bit(1);
	for (int b = 5; b >= 0; b--) {
		cmd_send_bit((frame[0] >> b) & 1);
	}
	for (int i = 1; i <= 4; i++) {
		for (int b = 7; b >= 0; b--) {
			cmd_send_bit((frame[i] >> b) & 1);
		}
	}
	for (int b = 7; b >= 1; b--) {
		cmd_send_bit((frame[5] >> b) & 1);
	}
	cmd_send_bit(1);

	CMD_IN();
	emmc_dbg_resp_clocks = -1;
	for (int t = 0; t < 200; t++) {
		clk_pulse();
		if (!READ_CMD()) {
			emmc_dbg_resp_clocks = t;
			break;
		}
	}
	if (emmc_dbg_resp_clocks < 0) {
		return false;
	}

	if (!r1_out) {
		return true;
	}

	uint8_t resp[6] = {0};
	for (int i = 0; i < 38; i++) {
		uint8_t bit = cmd_recv_bit();
		resp[i / 8] |= (bit << (7 - (i % 8)));
	}
	memcpy(r1_out, resp, 6);

	CMD_OUT();
	CMD_HIGH();
	for (int i = 0; i < 8; i++) {
		clk_pulse();
	}
	return true;
}

/* Bit-banged MMC commands intermittently miss the response on the first try
 * (settling after the previous command); retry until the card answers. */
static bool send_command_retry(uint8_t cmd, uint32_t arg, uint8_t *r1_out, int tries)
{
	for (int t = 0; t < tries; t++) {
		if (send_command(cmd, arg, r1_out)) {
			return true;
		}
		k_msleep(2);
	}
	return false;
}

/* DATA read: per-bit CLK toggle uses the configurable (possibly 0) half-period. */
static bool read_data_block(uint8_t *buf)
{
	const uint32_t hd = g_emmc_clk_half_us;

	DAT0_IN();
	for (int timeout = 10000; timeout > 0; timeout--) {
		RCLK_HIGH();
		HALF(hd); EDGE_SETTLE();
		if (!RDAT_GET()) {
			break;
		}
		RCLK_LOW();
		HALF(hd);
		if (timeout == 1) {
			return false;
		}
	}
	RCLK_LOW();
	HALF(hd);

	if (s_spim_ok) {
		/* FAST PATH: the start bit was just consumed by the bit-bang hunt
		 * above, so the remaining 512 data bytes + CRC16 are exactly byte-
		 * aligned — one 8 MHz SPIM RX DMA (~515 us vs ~1.7 ms bit-banged). */
		spim_xfer(NULL, 0, s_dma_rx, sizeof(s_dma_rx));
		memcpy(buf, s_dma_rx, EMMC_BLOCK_SIZE);
		emmc_dbg_rd_crc = (uint16_t)(((uint16_t)s_dma_rx[EMMC_BLOCK_SIZE] << 8) |
					     s_dma_rx[EMMC_BLOCK_SIZE + 1]);
		RCLK_HIGH(); HALF(hd); RCLK_LOW(); HALF(hd);  /* end bit */
		if (crc16(buf, EMMC_BLOCK_SIZE) != emmc_dbg_rd_crc) {
			emmc_crc_rd_errs++;          /* corrupt read: caller retries */
			DAT0_OUT();
			DAT0_HIGH();
			return false;
		}
	} else {
		for (uint32_t i = 0; i < EMMC_BLOCK_SIZE; i++) {
			uint8_t byte = 0;
			for (int b = 7; b >= 0; b--) {
				RCLK_HIGH();
				HALF(hd); EDGE_SETTLE();
				byte |= (uint8_t)(RDAT_GET() << b);
				RCLK_LOW();
				HALF(hd);
			}
			buf[i] = byte;
		}

		uint16_t rdcrc = 0;     /* capture the card's CRC16 to validate ours */
		for (int i = 0; i < 16; i++) {
			RCLK_HIGH(); HALF(hd); EDGE_SETTLE();
			rdcrc = (uint16_t)((rdcrc << 1) | RDAT_GET());
			RCLK_LOW(); HALF(hd);
		}
		emmc_dbg_rd_crc = rdcrc;
		RCLK_HIGH(); HALF(hd); RCLK_LOW(); HALF(hd);  /* end bit */
	}

	DAT0_OUT();
	DAT0_HIGH();
	return true;
}

uint16_t emmc_calc_crc16(const uint8_t *data, uint32_t len)
{
	return crc16(data, len);
}

bool emmc_cmd13(uint8_t *r1_out)
{
	return send_command_retry(13, s_rca, r1_out, 8);
}

static bool write_data_block(const uint8_t *buf)
{
	const uint32_t hd = g_emmc_clk_half_us;

	/* Write convention: change DAT0 while CLK is LOW, then a full half-period of
	 * setup before the rising edge where the card latches it.
	 * First hold DAT0 idle-HIGH for several clocks (the Nwr gap) so the card does
	 * NOT mistake a stray low for an early start bit and mis-frame the token. */
	DAT0_OUT();
	RDAT_HIGH();
	if (s_spim_ok) {
		/* FAST PATH: the whole framed block — Nwr gap, start bit, 512 data
		 * bytes, CRC16, end bit — as one 8 MHz SPIM DMA burst (~520 us vs
		 * ~3.3 ms bit-banged, with the CPU free for the audio engine). */
		uint16_t crc = crc16(buf, EMMC_BLOCK_SIZE);
		s_dma_tx[0] = 0xFF;                       /* Nwr idle gap          */
		s_dma_tx[1] = 0xFE;                       /* 7 idle bits + START 0 */
		memcpy(&s_dma_tx[2], buf, EMMC_BLOCK_SIZE);
		s_dma_tx[2 + EMMC_BLOCK_SIZE]     = (uint8_t)(crc >> 8);
		s_dma_tx[2 + EMMC_BLOCK_SIZE + 1] = (uint8_t)crc;
		RCLK_LOW();
		/* TX ends EXACTLY at the CRC's last bit — no trailing idle byte!
		 * The card emits its CRC-status token 2 clocks after the END bit;
		 * a byte of idle clocks inside the DMA let the token fly by before
		 * the bit-bang hunt below ever looked (status read as garbage —
		 * which froze recording solid once the status became enforced).
		 * The END bit is clocked by hand right after, on time. */
		spim_xfer(s_dma_tx, 2 + EMMC_BLOCK_SIZE + 2, NULL, 0);
		/* END bit: DAT0 is back at its GPIO latch (output HIGH) — clock it */
		HALF(hd); EDGE_SETTLE();
		RCLK_HIGH(); HALF(hd); RCLK_LOW();
	} else {
		for (int i = 0; i < 8; i++) { HALF(hd); RCLK_HIGH(); HALF(hd); RCLK_LOW(); }
		RDAT_LOW();
		HALF(hd); EDGE_SETTLE();
		RCLK_HIGH(); HALF(hd); RCLK_LOW();            /* start bit */

		for (uint32_t i = 0; i < EMMC_BLOCK_SIZE; i++) {
			uint8_t byte = buf[i];
			for (int b = 7; b >= 0; b--) {
				if ((byte >> b) & 1) {
					RDAT_HIGH();
				} else {
					RDAT_LOW();
				}
				HALF(hd); EDGE_SETTLE();
				RCLK_HIGH(); HALF(hd); RCLK_LOW();
			}
		}

		uint16_t crc = crc16(buf, EMMC_BLOCK_SIZE);
		for (int b = 15; b >= 0; b--) {
			if ((crc >> b) & 1) {
				RDAT_HIGH();
			} else {
				RDAT_LOW();
			}
			HALF(hd); EDGE_SETTLE();
			RCLK_HIGH(); HALF(hd); RCLK_LOW();
		}

		RDAT_HIGH();
		HALF(hd); EDGE_SETTLE();
		RCLK_HIGH(); HALF(hd); RCLK_LOW();            /* end bit */
	}

	/* Read the CRC status token: the card drives DAT0 low (start bit), then 3
	 * status bits (010=accepted, 101=CRC err, 110=write err), then high. */
	DAT0_IN();
	emmc_dbg_wr_status = -1;
	for (int i = 0; i < 16; i++) {
		RCLK_HIGH(); HALF(hd); EDGE_SETTLE();
		int start = (int)RDAT_GET();
		RCLK_LOW(); HALF(hd);
		if (!start) {
			int st = 0;
			for (int k = 0; k < 3; k++) {
				RCLK_HIGH(); HALF(hd); EDGE_SETTLE();
				st = (st << 1) | (int)RDAT_GET();
				RCLK_LOW(); HALF(hd);
			}
			emmc_dbg_wr_status = st;
			break;
		}
	}
	/* wait for programming to finish (card holds DAT0 low while busy) */
	for (int timeout = 200000; timeout > 0; timeout--) {
		clk_pulse();
		if (READ_DAT0()) {
			break;
		}
	}

	DAT0_OUT();
	DAT0_HIGH();
	/* ENFORCE the CRC-status token: 0b010 = accepted. Anything else means the
	 * card rejected the block (bus bit error) — returning false makes the
	 * caller retry instead of silently storing a glitch into the loop. */
	if (emmc_dbg_wr_status != 0x2) {
		emmc_crc_wr_errs++;
		return false;
	}
	return true;
}

bool emmc_init(void)
{
	s_ready = false;
	g_emmc_clk_half_us = CMD_SAFE_HALF_US;

	nrf_gpio_cfg(PIN_EMMC_CLK, NRF_GPIO_PIN_DIR_OUTPUT, NRF_GPIO_PIN_INPUT_DISCONNECT,
		     NRF_GPIO_PIN_NOPULL, NRF_GPIO_PIN_H0H1, NRF_GPIO_PIN_NOSENSE);  /* high-drive CLK */
	nrf_gpio_cfg_output(PIN_EMMC_CMD);
	DAT0_OUT();                          /* high-drive DAT0 */
	nrf_gpio_cfg_output(PIN_EMMC_RST);
	nrf_gpio_cfg_output(PIN_EMMC_VCCQ);

	spim_data_init();                    /* hardware-clocked data path */
	crc16_tab_init();

	CLK_LOW();
	CMD_HIGH();
	DAT0_HIGH();

	nrf_gpio_pin_set(PIN_EMMC_VCCQ);
	k_msleep(10);

	nrf_gpio_pin_clear(PIN_EMMC_RST);
	k_msleep(1);
	nrf_gpio_pin_set(PIN_EMMC_RST);
	k_msleep(2);

	CMD_HIGH();
	for (int i = 0; i < 80; i++) {
		clk_pulse();
	}

	send_command(0, 0x00000000, NULL);   /* CMD0 GO_IDLE (no response expected) */
	emmc_dbg_cmd0_sent = true;
	k_msleep(1);

	uint8_t r3[6] = {0};
	emmc_dbg_cmd1_retries = -1;
	for (int retry = 0; retry < 1000; retry++) {
		bool ok = send_command(1, 0x40FF8000, r3); /* CMD1 SEND_OP_COND, HCS=1 */
		k_msleep(1);
		if (ok && (r3[1] & 0x80)) {       /* response seen AND busy bit set = ready */
			emmc_dbg_cmd1_retries = retry;
			break;
		}
	}
	memcpy(emmc_dbg_ocr, r3, 6);
	if (emmc_dbg_cmd1_retries < 0) {      /* card never responded ready -> stop */
		return false;
	}

	/* CMD2 ALL_SEND_CID returns a 136-bit R2. send_command only waits for the
	 * start bit (r1_out=NULL); on success we must clock out the remaining 135
	 * bits so the bus is clean for CMD3. Retry a few times + capture timing. */
	for (int t = 0; t < 8; t++) {
		emmc_dbg_cmd2_tries = t + 1;
		emmc_dbg_cmd2_resp = send_command(2, 0, NULL);
		emmc_dbg_cmd2_clocks = emmc_dbg_resp_clocks;
		if (emmc_dbg_cmd2_resp) {
			for (int i = 0; i < 135; i++) { clk_pulse(); }  /* drain R2 (CID) */
			break;
		}
		k_msleep(2);
	}
	k_msleep(1);

	uint8_t r6[6] = {0};
	s_rca = 0x0001u << 16;
	emmc_dbg_cmd3_resp = send_command_retry(3, s_rca, r6, 8);   /* CMD3 SET_RELATIVE_ADDR */
	k_msleep(1);

	uint8_t r1[6] = {0};
	emmc_dbg_cmd7_resp = send_command_retry(7, s_rca, r1, 8);   /* CMD7 SELECT_CARD */
	memcpy(emmc_dbg_r1, r1, 6);
	k_msleep(1);
	emmc_dbg_cmd16_resp = send_command_retry(16, EMMC_BLOCK_SIZE, r1, 8); /* CMD16 SET_BLOCKLEN */
	k_msleep(1);

	/* strict: ready only if the card actually selected AND accepted block length */
	s_ready = emmc_dbg_cmd7_resp && emmc_dbg_cmd16_resp;
	if (s_ready) {
		s_cmd_half_us = 0u;   /* identification done: full-speed commands */
	}
	return s_ready;
}

bool emmc_is_ready(void)
{
	return s_ready;
}

bool emmc_read_blocks(uint32_t block_addr, uint8_t *buf, uint32_t count)
{
	if (!s_ready) {
		return false;
	}
	uint8_t r1[6];
	if (count == 1) {
		emmc_dbg_last_cmd_resp = send_command_retry(17, block_addr, r1, 8);
		if (!emmc_dbg_last_cmd_resp) {
			return false;
		}
		return read_data_block(buf);
	}
	if (!send_command(18, block_addr, r1)) {
		return false;
	}
	for (uint32_t i = 0; i < count; i++) {
		if (!read_data_block(buf + i * EMMC_BLOCK_SIZE)) {
			send_command(12, 0, r1);
			return false;
		}
	}
	send_command(12, 0, r1);
	return true;
}

bool emmc_write_blocks(uint32_t block_addr, const uint8_t *buf, uint32_t count)
{
	if (!s_ready) {
		return false;
	}
	uint8_t r1[6];
	if (count == 1) {
		emmc_dbg_last_cmd_resp = send_command_retry(24, block_addr, r1, 8);
		if (!emmc_dbg_last_cmd_resp) {
			return false;
		}
		return write_data_block(buf);
	}
	if (!send_command(25, block_addr, r1)) {
		return false;
	}
	for (uint32_t i = 0; i < count; i++) {
		if (!write_data_block(buf + i * EMMC_BLOCK_SIZE)) {
			send_command(12, 0, r1);
			return false;
		}
	}
	send_command(12, 0, r1);
	return true;
}
