#include "uboot_spi.h"
#include <stdint.h>		//For uint32_t.

#define MCSPI0_BASE 0x48030100

#define OFFSET(x) ((x) + 0xB2000000)

#define spi_phys_to_virt(phys) (OFFSET(phys))

#define spi_value_at_register(offset) (*((volatile  uint32_t *) spi_phys_to_virt(MCSPI0_BASE + (offset))))



void spi_write_ch0conf(int val)
{
	spi_value_at_register(MCSPI_CH0CONF) = val;
	/* Flash post writes to make immediate effect */
	spi_value_at_register(MCSPI_CH0CONF);
}

void spi_set_ch0ctrl_enable(int enable)
{
	spi_value_at_register(MCSPI_CH0CTRL) = enable;
	/* Flash post writes to make immediate effect */
	spi_value_at_register(MCSPI_CH0CTRL);
}

/* McSPI Transmit Receive Mode */
int spi_txrx(unsigned int len, const void *txp, void *rxp, uint32_t flags)
{
	int timeout = SPI_WAIT_TIMEOUT;
	int chconf, i = 0;

	chconf = spi_value_at_register(MCSPI_CH0CONF);

	/*set TRANSMIT-RECEIVE Mode*/
    chconf &= ~(CHXCONF_TRM_MASK | CHXCONF_WL_MASK);
	chconf |= (8 - 1) << 7;
	chconf |= CHXCONF_FORCE;
    spi_write_ch0conf(chconf);

      /*Enable SPI channel*/
    spi_set_ch0ctrl_enable(CHXCTRL_EN);

	/*Shift in and out 1 byte at one time*/
	for (i = 0; i < len; i++){
		/* Write: wait for TX empty (TXS == 1)*/
        while (!(spi_value_at_register(MCSPI_CH0STAT) & CHXSTAT_TXS) && timeout--)
        {
			if (timeout <= 0) {
				return -1;
			}
		}
        
		/* Write the data */
		spi_value_at_register(MCSPI_TX0) = ((uint8_t *) txp)[i];
		

		/*Read: wait for RX containing data (RXS == 1)*/
		timeout = SPI_WAIT_TIMEOUT;
        while (!(spi_value_at_register(MCSPI_CH0STAT) & CHXSTAT_RXS) && timeout--)
        {
			if (timeout <= 0) {
				return -1;
			}
		}

		/* Read the data */
	    ((uint8_t *)rxp)[i] = (uint8_t) spi_value_at_register(MCSPI_RX0);
	}
	/* Disable the channel */
        spi_set_ch0ctrl_enable(CHXCTRL_DIS);

	/*if transfer must be terminated disable the channel*/
	if (flags & SPI_XFER_END) {

        chconf &= ~CHXCONF_FORCE;
		spi_write_ch0conf(chconf);
	}

	return 0;
}

