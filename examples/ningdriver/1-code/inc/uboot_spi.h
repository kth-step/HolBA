#ifndef _UBOOT_SPI_H_
#define _UBOOT_SPI_H_

#include <stdint.h>


/*SPI registers offset*/
#define  MCSPI_SYSCONFIG            0x00000010
#define  MCSPI_SYSSTATUS            0x00000014
#define  MCSPI_IRQCONFIG            0x00000018
#define  MCSPI_IRQENABLE            0x0000001C
#define  MCSPI_SYST                 0x00000024
#define  MCSPI_MODULCTRL            0x00000028
#define  MCSPI_CH0CONF              0x0000002C
#define  MCSPI_CH0STAT              0x00000030
#define  MCSPI_CH0CTRL              0x00000034
#define  MCSPI_TX0                  0x00000038
#define  MCSPI_RX0                  0x0000003C
#define  MCSPI_CH1CONF              0x00000040
#define  MCSPI_CH1STAT              0x00000044
#define  MCSPI_CH1CTRL              0x00000048
#define  MCSPI_TX1                  0x0000004C
#define  MCSPI_RX1                  0x00000050
#define  MCSPI_CH2CONF              0x00000054
#define  MCSPI_CH2STAT              0x00000058
#define  MCSPI_CH2CTRL              0x0000005C
#define  MCSPI_TX2                  0x00000060
#define  MCSPI_RX2                  0x00000064
#define  MCSPI_CH3CONF              0x00000068
#define  MCSPI_CH3STAT              0x0000006C
#define  MCSPI_CH3CTRL              0x00000070
#define  MCSPI_TX3                  0x00000074
#define  MCSPI_RX3                  0x00000078
#define  MCSPI_XFERLEVEL            0x0000007C
#define  MCSPI_DAFTX                0x00000080
#define  MCSPI_DAFRX                0x000000A0

/* SYSCONFIG bitmasks */
#define SYSCONFIG_SMARTIDLE (2 << 3)
#define SYSCONFIG_SOFTRESET (1 << 1)
#define SYSCONFIG_AUTOIDLE	(1 << 0)

/* SYSSTATUS bitmasks */
#define SYSSTATUS_RESETDONE (1 << 0)

/* MODULCTRL bitmasks */
#define MODULCTRL_SINGLE	(1 << 0)
#define MODULCTRL_MS	    (1 << 2)
#define MODULCTRL_SYSTEM_TEST	    (1 << 3)

/* CHXCONF bitmasks, x = 0, 1, 2, 3 */
#define CHXCONF_PHA		             (1 << 0)
#define CHXCONF_POL           		 (1 << 1)
#define CHXCONF_CLKD_MASK	         (0xF << 2)
#define CHXCONF_EPOL		         (1 << 6)
#define CHXCONF_WL_MASK	             (0x1F << 7)
#define CHXCONF_TRM_RX_ONLY	         (1 << 12)
#define CHXCONF_TRM_TX_ONLY	         (1 << 13)
#define CHXCONF_TRM_MASK	         (0x3 << 12)
#define CHXCONF_DMAW		         (1 << 14)
#define CHXCONF_DMAR		         (1 << 15)
#define CHXCONF_DPE0     	   	     (1 << 16)
#define CHXCONF_DPE1		         (1 << 17)
#define CHXCONF_IS		             (1 << 18)
#define CHXCONF_TURBO	             (1 << 19)
#define CHXCONF_FORCE	             (1 << 20)

/* CHXSTAT bitmasks, x = 0, 1, 2, 3 */
#define CHXSTAT_RXS		             (1 << 0)
#define CHXSTAT_TXS		             (1 << 1)
#define CHXSTAT_EOT		             (1 << 2)

/* CHXCTRL bitmasks, x = 0, 1, 2, 3 */
#define CHXCTRL_EN		(1 << 0)
#define CHXCTRL_DIS		(0 << 0)

/* SPI D0 and D1 setup */
#define MCSPI_PINDIR_D0_IN_D1_OUT	0
#define MCSPI_PINDIR_D0_OUT_D1_IN	1

/* SPI mode flags */
#define SPI_CPHA	(1 << 0)			/* clock phase */
#define SPI_CPOL	(1 << 1)			/* clock polarity */

#define  MCSPI_MAX_FREQ		    48000000
#define  SPI_WAIT_TIMEOUT		2000

#define SPI_XFER_BEGIN              (1 << 0)
#define SPI_XFER_END                (1 << 1)



void enable_spi0_pin_mux (void);
void spi_write_ch0conf (int val);
void spi_set_ch0ctrl_enable(int enable);
int spi_write(unsigned int len, const void *txp, uint32_t flags);
int spi_read(unsigned int len, void *rxp, uint32_t flags);
int spi_txrx(unsigned int len, const void *txp, void *rxp, uint32_t flags);
int spi_xfer(unsigned int bitlen, const void *dout, void *din, uint32_t flags);
void spi_set_speed(uint32_t speed_hz);
void spi_set_mode(int mode);
void spi_set_wordlen(int wordlen);
void spi_reset(void);
void spi_claim_bus(void);
void spi_init (void);
void spi_self_test (void);
void spi_camera_test (void);


#endif /* _UBOOT_SPI_H_ */
