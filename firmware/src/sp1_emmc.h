/*
 * SP-1 eMMC 1-bit bit-bang driver (Zephyr port of Tim Knapen's SP-1-dev emmc.c).
 * Toshiba THGBMNG5D1LBAIL, 4 GB, connected CLK/CMD/DAT0/RST_n + VCCQ only.
 * Ported to use the nrfx GPIO HAL + k_busy_wait so it builds in the Zephyr app.
 * The DATA-phase clock half-period is runtime-configurable (g_emmc_clk_half_us)
 * so the benchmark can measure the safe (delayed) vs fast (delay-free) ceiling.
 */
#ifndef SP1_EMMC_H
#define SP1_EMMC_H

#include <stdint.h>
#include <stdbool.h>

#define EMMC_BLOCK_SIZE 512u

/* DATA-transfer clk half-period in microseconds. 0 = fastest (no busy-wait, just
 * GPIO register toggles). Commands/init always use a fixed safe clock internally.
 * Set this AFTER emmc_init() to tune the read/write data rate. */
extern volatile uint32_t g_emmc_clk_half_us;
extern volatile uint32_t emmc_crc_rd_errs;   /* verified-read CRC catches  */
extern volatile uint32_t emmc_crc_wr_errs;   /* write status-token catches */

/* ---- diagnostics, filled by emmc_init() to pinpoint where bring-up fails ---- */
extern bool    emmc_dbg_cmd0_sent;
extern int     emmc_dbg_cmd1_retries;   /* retries until ready; -1 = never ready */
extern bool    emmc_dbg_cmd2_resp;
extern bool    emmc_dbg_cmd3_resp;
extern bool    emmc_dbg_cmd7_resp;
extern bool    emmc_dbg_cmd16_resp;
extern uint8_t emmc_dbg_ocr[6];          /* CMD1 R3 response bytes */
extern uint8_t emmc_dbg_r1[6];           /* CMD7 R1 response bytes */
/* Last single-block read/write command response flags (for read/write tests). */
extern bool    emmc_dbg_last_cmd_resp;
extern int     emmc_dbg_resp_clocks;   /* clocks until last response start bit (-1=none) */
extern int     emmc_dbg_cmd2_clocks;   /* clocks-to-response captured for CMD2 (-1=none) */
extern int     emmc_dbg_cmd2_tries;    /* CMD2 attempts before a response */
extern int     emmc_dbg_wr_status;     /* CRC status token from last block write:
					* 0b010=2 accepted, 0b101=5 CRC err, 0b110=6 write err, -1=none */
extern uint16_t emmc_dbg_rd_crc;       /* CRC16 the card appended to the last read block */

/* Expose the data CRC16 so the diag can compare our value to the card's read CRC. */
uint16_t emmc_calc_crc16(const uint8_t *data, uint32_t len);

bool emmc_init(void);
bool emmc_is_ready(void);
bool emmc_cmd13(uint8_t *r1_out);      /* SEND_STATUS — card status register R1 */
bool emmc_read_blocks(uint32_t block_addr, uint8_t *buf, uint32_t count);
bool emmc_write_blocks(uint32_t block_addr, const uint8_t *buf, uint32_t count);

#endif /* SP1_EMMC_H */
