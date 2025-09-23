/*
 * pid.c
 *
 *  Created on: 8 aug. 2019
 *      Author: andreas
 */


//#include <robot_params.h>

#include <stdint.h>
#include <math.h>


//#define BOT_LEGO
#define BOT_MINI
//#define BOT_BALPEN
//#define BOT_EMPTY

#ifdef BOT_LEGO
#define ACC_X_OFF				-1251
#define ACC_Z_OFF				910
#define GYRO_Y_OFF				-18
#define GYR_SCALE 390
#define ANGLETARGET -14.2
#define INIT_KP 0.398
#define INIT_KI 0.002
#define INIT_KD 0.0084
#endif

#ifdef BOT_MINI
#define ACC_X_OFF				-2214
#define ACC_Z_OFF				1096
#define GYRO_Y_OFF				18
#define GYR_SCALE 250
//#define ANGLETARGET 6.2
//#define ANGLETARGET 5.88
#define ANGLETARGET 8.44
/*
// somewhat working
#define INIT_KP 0.1
#define INIT_KI 0.2
#define INIT_KD 0.0001
*/
/*
// way better
#define INIT_KP 0.15
#define INIT_KI 0.9
#define INIT_KD 0.002
*/
//quite stable
/*
#define INIT_KP 0.15
#define INIT_KI 0.9
#define INIT_KD 0.003
*/
//seems even better
#define INIT_KP 0.15
#define INIT_KI 0.9
#define INIT_KD 0.00375
#endif

#ifdef BOT_BALPEN
#define ACC_X_OFF				-1399
#define ACC_Z_OFF				790
#define GYRO_Y_OFF				78
#define GYR_SCALE 250
#define ANGLETARGET -3.0
#define INIT_KP 0.086
#define INIT_KI 0.192
#define INIT_KD 0.0038
#endif

#ifdef BOT_EMPTY
#define ACC_X_OFF				0x00
#define ACC_Z_OFF				0x00
#define GYRO_Y_OFF				0x00
#define GYR_SCALE 0x00
#define ANGLETARGET 0x00
#define INIT_KP 0x00
#define INIT_KI 0x00
#define INIT_KD 0x00
#endif

#define ERROR_SUM_LIMIT 200

#define DONTKNOWMATH

volatile int16_t imu_values[7];


// -------------------------------------------------------------------------------------
// pid controller in the imu_handler
// -------------------------------------------------------------------------------------

#define RAD_TO_DEG		(57.29578f)
#define SAMPLE_TIME		(0.005f)
#define ALPHA			(0.9934f)


// inputs
volatile uint8_t motor_on = 0;
volatile float angleTarget = ANGLETARGET;
volatile float kp = INIT_KP;
volatile float ki = INIT_KI;
volatile float kd = INIT_KD;

// output
//#define DEBUG_ANGLESCALE
#ifdef DEBUG_ANGLESCALE
volatile float accAngle_ = 0;
volatile float gyrAngle_ = 0;
#endif
volatile float motorPower = 0;

// controller state
float angleLast = 0;
float errorLast = 0;
float errorSum = 0;
uint32_t pid_counter = 0;

#ifdef DONTKNOWMATH

static float abs_own(float f) {
	if (f < 0)
		return -1 * f;
	else
		return f;
}

#define ATAN2F_FUN atan2f_own
static float atan2f_own(float y, float x) {
	float coeff_1 = M_PI / 4.0f;
	float coeff_2 = 3.0f * coeff_1;
	float abs_y = abs_own(y);
	float angle;
	if (x < 0.0f) {
		float r = (x + abs_y) / (abs_y - x);
		angle = coeff_2 - coeff_1 * r;
	} else {
		float r = (x - abs_y) / (x + abs_y);
		angle = coeff_1 - coeff_1 * r;
	}
	return y < 0.0f ? -angle : angle;
}
#else
#define ATAN2F_FUN atan2f
#endif

void imu_handler_pid_entry_empty(uint8_t noyield, uint32_t pid_sampletime);
void imu_handler_pid_entry(uint8_t noyield, uint32_t pid_sampletime);

volatile float angle;
volatile float error;
volatile float errorDiff;
volatile float errorSumNew;

void imu_handler_pid_entry_empty(uint8_t noyield, uint32_t pid_sampletime) {
	motorPower = 0;
	angle = 0;
	error = 0;
	errorDiff = 0;
	errorSum = 0;
}

void imu_handler_pid_set_state_PID(float __kp, float __ki, float __kd, float __angleLast, float __errorLast, float __errorSum) {
  kp = __kp;
  ki = __ki;
  kd = __kd;

  angleLast = __angleLast;
  errorLast = __errorLast;
  errorSum  = __errorSum;
}
void imu_handler_pid_set_state_INPUT(uint8_t __msg_flag, uint8_t __motor_on, float __angleTarget, uint32_t __pid_counter) {
  //msg_flag = __msg_flag;
  motor_on = __motor_on;

  angleTarget = __angleTarget;
  pid_counter = __pid_counter;
}
void imu_handler_pid_set_state_IMU(int16_t __accX, int16_t __accZ, int16_t __gyrY) {
  imu_values[0] = __accX;
  imu_values[2] = __accZ;

  imu_values[5] = __gyrY;
}

void imu_handler_pid_entry(uint8_t noyield, uint32_t pid_sampletime) {

	// pick out the relevant imu values
    int16_t accX = imu_values[0];
    int16_t accZ = imu_values[2];
    int16_t gyrY = imu_values[5];

	float angle_offset = 0.0f;
#ifdef ENCODERS_ENABLED
	float loc_error = -encoder_values[0] - 0.0f;
	angle_offset = loc_error / 20;
	angle_offset = angle_offset > 1.0f ? 1.0f : (angle_offset < -1.0f ? -1.0f : angle_offset);
#endif

	// calc angle using complementary filter
	float accAngle =  (accZ == 0) ? 0 : (ATAN2F_FUN(accX,accZ) * RAD_TO_DEG);
	float gyrAngleDiff = (-((((int32_t)gyrY)  * GYR_SCALE) / 32768.0f)) * SAMPLE_TIME;

#ifdef DEBUG_ANGLESCALE
	accAngle_  = accAngle;
	gyrAngle_ += gyrAngleDiff;
#endif

	/*float*/ angle = (ALPHA * (angleLast + gyrAngleDiff)) + ((1-ALPHA) * accAngle);
	angleLast = angle;

	// compute error and its derivative and integral
	/*float*/ error = angle - (angleTarget + angle_offset);
	/*float*/ errorDiff = error - errorLast;
	errorLast = error;
	/*float*/ errorSumNew = errorSum + (error);
	errorSum = (!(errorSumNew < ERROR_SUM_LIMIT)) ? ERROR_SUM_LIMIT : (errorSumNew < -ERROR_SUM_LIMIT ? -ERROR_SUM_LIMIT : errorSumNew);

	// compute output signal
//#define BUG
//#define ALITTLELOOSE
#ifdef BUG
  #define KD_FACTOR 10
#else
  #ifdef ALITTLELOOSE
    #define KD_FACTOR 0.3f
  #else
    #define KD_FACTOR 1
  #endif
#endif
	motorPower = (kp * error) + (ki * errorSum * SAMPLE_TIME) + (kd * KD_FACTOR * errorDiff / SAMPLE_TIME);
}


