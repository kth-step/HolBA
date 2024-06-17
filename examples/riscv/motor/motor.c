/*
 * motor.c
 *
 *  Created on: 12 apr. 2019
 *      Author: Andreas Lindner
 *
 *  Modified to act as standalone example for symbolic execution
 */
 
 int main() {}


#define MOTOR_MAX_VAL (32768-2)
#if MOTOR_MAX_VAL >= (32768-1)
#error "something might not fit in the timer registers, check this"
#endif
#define MOTOR_START_VAL (MOTOR_MAX_VAL * 5 / 60)

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

#define GEN_ADDR(x) (0xFFFFFFFF00000000 + (0x10 * x))

#define TMR0_MAX  ((*( (int*) GEN_ADDR(0) )) + 1)
#define TMR0_SET0 (*( (int*) GEN_ADDR(1) ))
#define TMR0_SET1 (*( (int*) GEN_ADDR(2) ))

#define TMR1_MAX  ((*( (int*) GEN_ADDR(3) )) + 1)
#define TMR1_SET0 (*( (int*) GEN_ADDR(4) ))
#define TMR1_SET1 (*( (int*) GEN_ADDR(5) ))

void motor_set_l(int l) {
	char sign = l < 0;
	l = motor_prep_input(l);

	if (l == MOTOR_MAX_VAL) {
		TMR0_SET0 = TMR0_MAX;
		TMR0_SET1 = TMR0_MAX;
	} else if (sign) {
		TMR0_SET0 = TMR0_MAX;
		TMR0_SET1 = l;
	} else {
		TMR0_SET0 = l;
		TMR0_SET1 = TMR0_MAX;
	}
}
void motor_set_r(int r) {
	char sign = r < 0;
	r = motor_prep_input(r);

	if (r == MOTOR_MAX_VAL) {
		TMR1_SET0 = TMR1_MAX;
		TMR1_SET1 = TMR1_MAX;
	} else if (sign) {
		TMR1_SET0 = r;
		TMR1_SET1 = TMR1_MAX;
	} else {
		TMR1_SET0 = TMR1_MAX;
		TMR1_SET1 = r;
	}
}

// target analysis function
void motor_set(int l, int r) {
	motor_set_l(l);
	motor_set_r(r);
}

// target analysis function, if want to try floating-point operations
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


