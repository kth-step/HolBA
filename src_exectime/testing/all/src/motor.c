/*
 * motor.c
 *
 *  Created on: 12 apr. 2019
 *      Author: Andreas Lindner
 */

//#include "LPC11xx.h"
//#include "dev/hw.h"

#include <stdint.h>
//#include <robot_params.h>

////////////////// configuration ////////////////////

#define TMR_PCLK		(12 * 1000 * 1000)
#define TMR_PRESCALE	(1)
#define TMR_FREQ		(2000)

////////////////// pinouts for motor circuits ////////////////////
/*
==========================================================================================================
*/

/*
Motor (DRV8833)
--------------
nFAULT
- R/PIO1_0/AD1/CT32B1_CAP0
IN1-2
- PIO0_8/MISO0/CT16B0_MAT0
- PIO0_9/MOSI0/CT16B0_MAT1
IN3-4
- R/PIO1_1/AD2/CT32B1_MAT0
- R/PIO1_2/AD3/CT32B1_MAT1
*/

/*
==========================================================================================================
*/

/*
Motor (L298) 2kHz max
------------
PWML = PIO0_8/CT16B0_MAT0
INL1 = PIO0_9
INL2 = PIO0_2

PWMR = PIO1_1/CT32B1_MAT0
INR1 = PIO1_2
INR2 = PIO 3_2

 */
/*
==========================================================================================================
*/

////////////////// common timer-related helper functions ////////////////////
#define MOTOR_MAX_VAL (TMR_PCLK/TMR_PRESCALE/TMR_FREQ)
#if MOTOR_MAX_VAL >= (32768-1)
#error "something might not fit in the timer registers, check this"
#endif
//#define MOTOR_START_VAL (MOTOR_MAX_VAL * 5 / 60)

void motor_dummy_fun() {
  __asm__("nop\n\t");
  __asm__("nop\n\t");
  __asm__("nop\n\t");
}

int motor_prep_input(int r);
int motor_prep_input(int r) {
	char sign = r < 0;
	if (sign)
		r = -r;

	r = r > MOTOR_MAX_VAL ? MOTOR_MAX_VAL : r;

#ifdef MOTOR_START_VAL
	r = r < MOTOR_START_VAL ? (r < MOTOR_START_VAL / 2 ? 0 : MOTOR_START_VAL) : r;
#endif

	r = MOTOR_MAX_VAL - r;

	return r;
}


volatile uint32_t motor_sram_mem1;
volatile uint32_t motor_sram_mem2;
volatile uint32_t motor_sram_mema_0;
volatile uint32_t motor_sram_mema_1;
volatile uint32_t motor_sram_mema_2;
volatile uint32_t motor_sram_memb_0;
volatile uint32_t motor_sram_memb_1;
volatile uint32_t motor_sram_memb_2;
void motor_set_l(int l) {
	char sign = l < 0;
	l = motor_prep_input(l);
	motor_sram_mem1 = 1;

	if (l == MOTOR_MAX_VAL) {
		motor_sram_mema_0 = motor_sram_mema_2 + 1;
		motor_sram_mema_1 = motor_sram_mema_2 + 1;
	} else if (sign) {
		motor_sram_mema_0 = motor_sram_mema_2 + 1;
		motor_sram_mema_1 = l;
	} else {
		motor_sram_mema_0 = l;
		motor_sram_mema_1 = motor_sram_mema_2 + 1;
	}
}
void motor_set_r(int r) {
	char sign = r < 0;
	r = motor_prep_input(r);
	motor_sram_mem2 = 1;

	if (r == MOTOR_MAX_VAL) {
		motor_sram_memb_0 = motor_sram_memb_2 + 1;
		motor_sram_memb_1 = motor_sram_memb_2 + 1;
	} else if (sign) {
		motor_sram_memb_0 = r;
		motor_sram_memb_1 = motor_sram_memb_2 + 1;
	} else {
		motor_sram_memb_0 = motor_sram_memb_2 + 1;
		motor_sram_memb_1 = r;
	}
}

void motor_set(int l, int r) {
	motor_set_l(l);
	motor_set_r(r);
}

void motor_set_multi(int l, int r) {
/*
  asm volatile (
    "bl motor_set\n"
    "bl motor_set\n"
  );
*/
/*
  asm volatile (
    "bl motor_set\n"
    "bl motor_set\n"
    :
    :
    : "lr" //x30
  );
*/
/*
  asm volatile (
    "mov r9,lr\n"
    "bl motor_set\n"
    "bl motor_set\n"
    "mov lr,r9\n"
    :
    :
    : //"lr" //x30
  );
*/
  asm volatile (
    "mov r7,lr\n"
    "mov r8,r0\n"
    "mov r9,r1\n"
    "bl motor_set\n"
    "mov r0,r8\n"
    "mov r1,r9\n"
    "bl motor_set\n"
    "mov lr,r7\n"
    :
    :
    : //"lr" //x30
  );
/*
  asm volatile (
    "mov r7,lr\n"
    "mov r8,r0\n"
    "mov r9,r1\n"
    "bl motor_set\n"
    "mov r0,r8\n"
    "mov r1,r9\n"
    "bl motor_set\n"
    "mov r0,r8\n"
    "mov r1,r9\n"
    "bl motor_set\n"
    "mov r0,r8\n"
    "mov r1,r9\n"
    "bl motor_set\n"
    "mov r0,r8\n"
    "mov r1,r9\n"
    "bl motor_set\n"
    "mov r0,r8\n"
    "mov r1,r9\n"
    "bl motor_set\n"
    "mov r0,r8\n"
    "mov r1,r9\n"
    "bl motor_set\n"
    "mov r0,r8\n"
    "mov r1,r9\n"
    "bl motor_set\n"
    "mov lr,r7\n"
    :
    :
    : //"lr" //x30
  );
*/
  //__asm__("bl motor_set\n\t"); //motor_set(l, r);
  //__asm__("bl motor_set\n\t"); //motor_set(l, r);
}

void motor_set_f(float l, float r) {
/*
	if (l < 0.1f) {
		l = 0.1f;
	} else if (l < 0.2f) {
		l = 0.1f + (l - 0.1f) * 2;
	} else if (l < 0.4f) {
		l = 0.3f + (l - 0.3f) * 1.5f;
	}
*/

	motor_set(l*MOTOR_MAX_VAL, r*MOTOR_MAX_VAL);
}


