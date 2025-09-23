
#ifdef __BENCHMARK_MODE

#include <stdint.h>

//#include "LPC11xx.h"

#include <io.h>

void disable_all_interrupts() {
/*
  for (uint8_t i = WAKEUP0_IRQn; i <= EINT0_IRQn; i++) {
    //out_info_inthex("\r\nIRQn", i);
    NVIC_DisableIRQ(i);
  }
  __DSB();
  __ISB();
*/
}

// input setter
void imu_handler_pid_set_state_PID(float __kp, float __ki, float __kd, float __angleLast, float __errorLast, float __errorSum);
void imu_handler_pid_set_state_INPUT(uint8_t __msg_flag, uint8_t __motor_on, float __angleTarget, uint32_t __pid_counter);
void imu_handler_pid_set_state_IMU(int16_t __accX, int16_t __accZ, int16_t __gyrY);

// target function
void imu_handler_pid_entry(uint8_t noyield, uint32_t pid_sampletime);
float __aeabi_fadd(float a, float b);
float __aeabi_fdiv(float a, float b);

void motor_set(int32_t l, int32_t r);
int32_t motor_prep_input(int32_t r);
void motor_set_l(int32_t l);
void motor_set_r(int32_t r);
void motor_set_multi(int32_t l, int32_t r);

typedef uint8_t byte;
typedef uint32_t word32;
#define MY_AES_ROUNDS_NUM 10
extern word32 my_aes_rk[((128/8)/4) * (MY_AES_ROUNDS_NUM + 1)];
//128 bit blocks
extern byte my_aes_inBlock[128/8];
void my_aes();

uint32_t _my_modexp_asm(uint32_t e, uint32_t b, uint32_t m);
uint32_t _my_uidivmod_mod_asm(uint32_t a, uint32_t b);
int32_t _motor_prep_input(int32_t r);
int32_t _motor_prep_input_mod(int32_t r);

// from asm code
void _benchmark_timer_reset();
uint32_t _benchmark_timer_measure();
void _benchmark_helper_wait_1ms();
void _imu_handler_pid_entry_dummy(uint8_t noyield, uint32_t pid_sampletime);

// composite measurement primitive
uint32_t benchmark_measure(void (*fun_ptr)(uint8_t, uint32_t), uint8_t __noyield, uint32_t __pid_sampletime) {
  // TODO: WHHHYYYYYYYYYYYYYYYYYYY?
  fun_ptr = (void (*)(uint8_t, uint32_t))(((uint32_t)fun_ptr) | 0x1);

  _benchmark_timer_reset();
  fun_ptr(__noyield, __pid_sampletime);

  uint32_t cycles = _benchmark_timer_measure();

  if (cycles > 0xFFFF) {
    out_error("unexpected cycle measurement");
    while(1); // out_error already blocks, but here we want to be sure
  }

  return cycles;
}
// quick and dirty adaption of "composite measurement primitive"
uint32_t benchmark_measure2(float (*fun_ptr)(float, float), float a, float b) {
  // TODO: WHHHYYYYYYYYYYYYYYYYYYY?
  fun_ptr = (float (*)(float, float))(((uint32_t)fun_ptr) | 0x1);

  _benchmark_timer_reset();
  fun_ptr(a, b);

  uint32_t cycles = _benchmark_timer_measure();

  if (cycles > 0xFFFF) {
    out_error("unexpected cycle measurement");
    while(1); // out_error already blocks, but here we want to be sure
  }

  return cycles;
}
// quick and dirty adaption of "composite measurement primitive"
uint32_t benchmark_measure3(void (*fun_ptr)(int32_t, int32_t), int32_t a, int32_t b) {
  // TODO: WHHHYYYYYYYYYYYYYYYYYYY?
  fun_ptr = (void (*)(int32_t, int32_t))(((uint32_t)fun_ptr) | 0x1);

  _benchmark_timer_reset();
  fun_ptr(a, b);

  uint32_t cycles = _benchmark_timer_measure();

  if (cycles > 0xFFFF) {
    out_error("unexpected cycle measurement");
    while(1); // out_error already blocks, but here we want to be sure
  }

  return cycles;
}
// quick and dirty adaption of "composite measurement primitive"
uint32_t benchmark_measure4(void (*fun_ptr)(int32_t), int32_t a) {
  // TODO: WHHHYYYYYYYYYYYYYYYYYYY?
  fun_ptr = (void (*)(int32_t))(((uint32_t)fun_ptr) | 0x1);

  _benchmark_timer_reset();
  fun_ptr(a);

  uint32_t cycles = _benchmark_timer_measure();

  if (cycles > 0xFFFF) {
    out_error("unexpected cycle measurement");
    while(1); // out_error already blocks, but here we want to be sure
  }

  return cycles;
}
// quick and dirty adaption of "composite measurement primitive"
uint32_t benchmark_measure5(int32_t (*fun_ptr)(int32_t), int32_t a) {
  // TODO: WHHHYYYYYYYYYYYYYYYYYYY?
  fun_ptr = (int32_t (*)(int32_t))(((uint32_t)fun_ptr) | 0x1);

  _benchmark_timer_reset();
  fun_ptr(a);

  uint32_t cycles = _benchmark_timer_measure();

  if (cycles > 0xFFFF) {
    out_error("unexpected cycle measurement");
    while(1); // out_error already blocks, but here we want to be sure
  }

  return cycles;
}
// quick and dirty adaption of "composite measurement primitive"
uint32_t benchmark_measure6(uint32_t (*fun_ptr)(uint32_t, uint32_t, uint32_t), uint32_t a, uint32_t b, uint32_t c) {
  // TODO: WHHHYYYYYYYYYYYYYYYYYYY?
  fun_ptr = (uint32_t (*)(uint32_t, uint32_t, uint32_t))(((uint32_t)fun_ptr) | 0x1);

  _benchmark_timer_reset();
  fun_ptr(a, b, c);

  uint32_t cycles = _benchmark_timer_measure();

  if (cycles > 0xFFFFF) {
    out_error("unexpected cycle measurement");
    while(1); // out_error already blocks, but here we want to be sure
  }

  return cycles;
}
// quick and dirty adaption of "composite measurement primitive"
uint32_t benchmark_measure7(void (*fun_ptr)()) {
  // TODO: WHHHYYYYYYYYYYYYYYYYYYY?
  fun_ptr = (void (*)())(((uint32_t)fun_ptr) | 0x1);

  _benchmark_timer_reset();
  fun_ptr();

  uint32_t cycles = _benchmark_timer_measure();

  if (cycles > 0xFFFF) {
    out_error("unexpected cycle measurement");
    while(1); // out_error already blocks, but here we want to be sure
  }

  return cycles;
}

void _reffunc_test4_9nopsubadd();
void _reffunc_ld();
void _reffunc_st();
void _reffunc_ld2_ldnop();
void _alignmenttestfun_b16(uint32_t, uint32_t);
void _reffunc_cjmp(uint32_t, uint32_t);
void _reffunc_ld5_ldldbr8();
void _reffunc_b16_00();
void _reffunc_b16_10();
uint32_t _mymodexp(uint32_t, uint32_t, uint32_t);
/*
void _reffunc_test4_9nopsubadd() {}
void _reffunc_ld() {}
void _reffunc_st() {}
void _reffunc_ld2_ldnop() {}
void _alignmenttestfun_b16(uint32_t a, uint32_t b) {}
void _reffunc_ld5_ldldbr8() {}
void _reffunc_b16_00() {}
void _reffunc_b16_10() {}
uint32_t _mymodexp(uint32_t a, uint32_t b, uint32_t c) {
  return 0;
}
*/
uint32_t __aeabi_uidivmod(uint32_t, uint32_t);


//#define USE_FIXED_BENCHMARK_INPUTS
// retrieve inputs from uart and set them
void set_inputs() {
#ifdef USE_FIXED_BENCHMARK_INPUTS
  //out_info("preparing");
  imu_handler_pid_set_state_PID(0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f);
  imu_handler_pid_set_state_INPUT(1, 0, 12.0f, 128);
  imu_handler_pid_set_state_IMU(1024, -1500, -2048);
#else
  out_info("wait4inputs");
  while (1) {
    int in_ch;
    uint32_t buf_ptr;

    uint32_t cycles_bl, cycles;
    float a, b, res;
    int32_t c, d;
    uint32_t e, f, g;

    // handle io
    while ((in_ch = in_handle()) == -3);

    if (in_ch == 100) {
      out_info("ok100");
      break;
    }

    switch (in_ch) {
      case -1:
        // nothing available
        break;
      case -2:
        // start sync error
        break;
      case 101:
        if (in_data_len != (4*(6) + 1*(2) + 1*(2) + 4*(2) + 2*(3) + 1*(2))) {
          out_info("nok101");
          break;
        }

        buf_ptr = (uint32_t)in_buffer + 4;
        float __kp = *((float*)(buf_ptr));
        buf_ptr += sizeof(float);
        float __ki = *((float*)(buf_ptr));
        buf_ptr += sizeof(float);
        float __kd = *((float*)(buf_ptr));
        buf_ptr += sizeof(float);
        float __angleLast = *((float*)(buf_ptr));
        buf_ptr += sizeof(float);
        float __errorLast = *((float*)(buf_ptr));
        buf_ptr += sizeof(float);
        float __errorSum  = *((float*)(buf_ptr));
        buf_ptr += sizeof(float);
        imu_handler_pid_set_state_PID(__kp, __ki, __kd, __angleLast, __errorLast, __errorSum);

        uint8_t __msg_flag = *((uint8_t*)(buf_ptr));
        buf_ptr += sizeof(uint8_t);
        uint8_t __motor_on = *((uint8_t*)(buf_ptr));
        buf_ptr += sizeof(uint8_t);
	// 2 byted padding
        buf_ptr += 2;
        float __angleTarget    = *((float*)(buf_ptr));
        buf_ptr += sizeof(float);
        uint32_t __pid_counter = *((uint32_t*)(buf_ptr));
        buf_ptr += sizeof(uint32_t);
        imu_handler_pid_set_state_INPUT(__msg_flag, __motor_on, __angleTarget, __pid_counter);

        int16_t __accX = *((int16_t*)(buf_ptr));
        buf_ptr += sizeof(int16_t);
        int16_t __accZ = *((int16_t*)(buf_ptr));
        buf_ptr += sizeof(int16_t);
        int16_t __gyrY = *((int16_t*)(buf_ptr));
        buf_ptr += sizeof(int16_t);
        imu_handler_pid_set_state_IMU(__accX, __accZ, __gyrY);

        out_info("ok101");
        break;
      case 102:
        if (in_data_len != (4*(2))) {
          out_info("nok102");
          break;
        }

        buf_ptr = (uint32_t)in_buffer + 4;
        a = *((float*)(buf_ptr));
        buf_ptr += sizeof(float);
        b = *((float*)(buf_ptr));
        buf_ptr += sizeof(float);

        cycles_bl = benchmark_measure2((float (*)(float,float))_imu_handler_pid_entry_dummy, 0, 0);
        cycles = benchmark_measure2(__aeabi_fadd, a, b);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        res = __aeabi_fadd(a, b);
        out_info_inthex("res", *((uint32_t*)&res));
        out_info("ok102");
        break;
      case 103:
        if (in_data_len != (4*(2))) {
          out_info("nok103");
          break;
        }

        buf_ptr = (uint32_t)in_buffer + 4;
        a = *((float*)(buf_ptr));
        buf_ptr += sizeof(float);
        b = *((float*)(buf_ptr));
        buf_ptr += sizeof(float);

        cycles_bl = benchmark_measure2((float (*)(float,float))_imu_handler_pid_entry_dummy, 0, 0);
        cycles = benchmark_measure2(__aeabi_fdiv, a, b);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        res = __aeabi_fdiv(a, b);
        out_info_inthex("res", *((uint32_t*)&res));
        out_info("ok103");
        break;

      case 105:
        if (in_data_len != (4*(2))) {
          out_info("nok105");
          break;
        }

        buf_ptr = (uint32_t)in_buffer + 4;
        c = *((int32_t*)(buf_ptr));
        buf_ptr += sizeof(int32_t);
        d = *((int32_t*)(buf_ptr));
        buf_ptr += sizeof(int32_t);

        cycles_bl = benchmark_measure3((void (*)(int32_t,int32_t))_imu_handler_pid_entry_dummy, 0, 0);
        cycles = benchmark_measure3(motor_set, c, d);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        out_info("ok105");
        break;

      case 106:
        if (in_data_len != (4*(1))) {
          out_info("nok106");
          break;
        }

        buf_ptr = (uint32_t)in_buffer + 4;
        c = *((int32_t*)(buf_ptr));
        buf_ptr += sizeof(int32_t);

        cycles_bl = benchmark_measure4((void (*)(int32_t))_imu_handler_pid_entry_dummy, 0);
        cycles = benchmark_measure4(motor_set_l, c);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        out_info("ok106");
        break;

      case 107:
        if (in_data_len != (4*(1))) {
          out_info("nok107");
          break;
        }

        buf_ptr = (uint32_t)in_buffer + 4;
        c = *((int32_t*)(buf_ptr));
        buf_ptr += sizeof(int32_t);

        cycles_bl = benchmark_measure5((int32_t (*)(int32_t))_imu_handler_pid_entry_dummy, 0);
        cycles = benchmark_measure5(motor_prep_input, c);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        out_info("ok107");
        break;

      case 108: // otherbenchs: _alignmenttestfun_b16(uint32, uint32)
        if (in_data_len != (4*(2))) {
          out_info("nok108");
          break;
        }

        buf_ptr = (uint32_t)in_buffer + 4;
        e = *((uint32_t*)(buf_ptr));
        buf_ptr += sizeof(uint32_t);
        f = *((uint32_t*)(buf_ptr));
        buf_ptr += sizeof(uint32_t);

        cycles_bl = benchmark_measure6((uint32_t (*)(uint32_t, uint32_t, uint32_t))_imu_handler_pid_entry_dummy, 0, 0, 0);
        //_alignmenttestfun_b16
        //_reffunc_cjmp
        cycles = benchmark_measure6((uint32_t (*)(uint32_t, uint32_t, uint32_t))_alignmenttestfun_b16, e, f, 0);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        out_info("ok108");
        break;

      case 109: // otherbenchs: _reffunc_test4()
        if (in_data_len != (4*(0))) {
          out_info("nok109");
          break;
        }

        c = 0;

        cycles_bl = benchmark_measure5((int32_t (*)(int32_t))_imu_handler_pid_entry_dummy, 0);
        // _reffunc_test4
        // _reffunc_b16_10
        // _reffunc_ld5_ldldbr8
        cycles = benchmark_measure5((int32_t (*)(int32_t))_reffunc_ld5_ldldbr8, c);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        out_info("ok109");
        break;

      case 110: // otherbenchs: _mymodexp(uint32, uint32, uint32)
        if (in_data_len != (4*(3))) {
          out_info("nok110");
          break;
        }

        buf_ptr = (uint32_t)in_buffer + 4;
        e = *((uint32_t*)(buf_ptr));
        buf_ptr += sizeof(uint32_t);
        f = *((uint32_t*)(buf_ptr));
        buf_ptr += sizeof(uint32_t);
        g = *((uint32_t*)(buf_ptr));
        buf_ptr += sizeof(uint32_t);

        cycles_bl = benchmark_measure6((uint32_t (*)(uint32_t, uint32_t, uint32_t))_imu_handler_pid_entry_dummy, 0, 0, 0);
        cycles = benchmark_measure6(_mymodexp, e, f, g);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        out_info("ok110");
        break;

      case 111: // otherbenchs: __aeabi_uidivmod(uint32, uint32)
        if (in_data_len != (4*(2))) {
          out_info("nok111");
          break;
        }

        buf_ptr = (uint32_t)in_buffer + 4;
        e = *((uint32_t*)(buf_ptr));
        buf_ptr += sizeof(uint32_t);
        f = *((uint32_t*)(buf_ptr));
        buf_ptr += sizeof(uint32_t);

        cycles_bl = benchmark_measure6((uint32_t (*)(uint32_t, uint32_t, uint32_t))_imu_handler_pid_entry_dummy, 0, 0, 0);
        cycles = benchmark_measure6((uint32_t (*)(uint32_t, uint32_t, uint32_t))__aeabi_uidivmod, e, f, 0);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        out_info("ok111");
        break;

      case 112: // morebenchs: my_aes()
        if (in_data_len != (4*(0))) {
          out_info("nok112");
          break;
        }

        cycles_bl = benchmark_measure6((uint32_t (*)(uint32_t, uint32_t, uint32_t))_imu_handler_pid_entry_dummy, 0, 0, 0);
        cycles = benchmark_measure6((uint32_t (*)(uint32_t, uint32_t, uint32_t))my_aes, 0, 0, 0);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        out_info("ok112");
        break;

      case 113: // morebenchs: _my_modexp_asm(uint32, uint32, uint32)
        if (in_data_len != (4*(3))) {
          out_info("nok113");
          break;
        }

        buf_ptr = (uint32_t)in_buffer + 4;
        e = *((uint32_t*)(buf_ptr));
        buf_ptr += sizeof(uint32_t);
        f = *((uint32_t*)(buf_ptr));
        buf_ptr += sizeof(uint32_t);
        g = *((uint32_t*)(buf_ptr));
        buf_ptr += sizeof(uint32_t);

        cycles_bl = benchmark_measure6((uint32_t (*)(uint32_t, uint32_t, uint32_t))_imu_handler_pid_entry_dummy, 0, 0, 0);
        cycles = benchmark_measure6((uint32_t (*)(uint32_t, uint32_t, uint32_t))_my_modexp_asm, e, f, g);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        out_info("ok113");
        break;

      case 114:
        if (in_data_len != (4*(1))) {
          out_info("nok114");
          break;
        }

        buf_ptr = (uint32_t)in_buffer + 4;
        c = *((int32_t*)(buf_ptr));
        buf_ptr += sizeof(int32_t);

        cycles_bl = benchmark_measure5((int32_t (*)(int32_t))_imu_handler_pid_entry_dummy, 0);
        cycles = benchmark_measure5(_motor_prep_input, c);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        out_info("ok114");
        break;

      case 115:
        if (in_data_len != (4*(1))) {
          out_info("nok115");
          break;
        }

        buf_ptr = (uint32_t)in_buffer + 4;
        c = *((int32_t*)(buf_ptr));
        buf_ptr += sizeof(int32_t);

        cycles_bl = benchmark_measure5((int32_t (*)(int32_t))_imu_handler_pid_entry_dummy, 0);
        cycles = benchmark_measure5(_motor_prep_input_mod, c);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        out_info("ok115");
        break;

        case 116: // morebenchs: _my_uidivmod_mod_asm(uint32, uint32)
          if (in_data_len != (4*(2))) {
            out_info("nok116");
            break;
          }
  
          buf_ptr = (uint32_t)in_buffer + 4;
          e = *((uint32_t*)(buf_ptr));
          buf_ptr += sizeof(uint32_t);
          f = *((uint32_t*)(buf_ptr));
          buf_ptr += sizeof(uint32_t);
  
          cycles_bl = benchmark_measure6((uint32_t (*)(uint32_t, uint32_t, uint32_t))_imu_handler_pid_entry_dummy, 0, 0, 0);
          cycles = benchmark_measure6((uint32_t (*)(uint32_t, uint32_t, uint32_t))_my_uidivmod_mod_asm, e, f, 0);
          out_info_inthex("cyclesres", cycles - cycles_bl + 3);
          out_info("ok116");
          break;

        case 117: // pid_entry
          if (in_data_len != (4*(0))) {
            out_info("nok117");
            break;
          }
  
          cycles_bl = benchmark_measure(_imu_handler_pid_entry_dummy, 0, 0);
          cycles = benchmark_measure(imu_handler_pid_entry, 0, 0);
          out_info_inthex("cyclesres", cycles - cycles_bl + 3);
          out_info("ok117");
          break;

      case 118:
        if (in_data_len != (sizeof(my_aes_rk) + sizeof(my_aes_inBlock))) { //(16*(11) + 16*(1))
          out_info("nok118");
          break;
        }

        uint8_t* ptr;
        buf_ptr = (uint32_t)in_buffer + 4;

        // byte order might be wrong, but it doesn't matter because we use random inputs
        ptr = (uint8_t*)&my_aes_rk;
        for (int i = 0; i < sizeof(my_aes_rk); i++) {
          *(ptr++) = *((uint8_t*)(buf_ptr++));
        }

        ptr = (uint8_t*)&my_aes_inBlock;
        for (int i = 0; i < sizeof(my_aes_inBlock); i++) {
          *(ptr++) = *((uint8_t*)(buf_ptr++));
        }

        out_info("ok118");
        break;

      case 119:
        if (in_data_len != (4*(2))) {
          out_info("nok119");
          break;
        }

        buf_ptr = (uint32_t)in_buffer + 4;
        c = *((int32_t*)(buf_ptr));
        buf_ptr += sizeof(int32_t);
        d = *((int32_t*)(buf_ptr));
        buf_ptr += sizeof(int32_t);

        cycles_bl = benchmark_measure3((void (*)(int32_t,int32_t))_imu_handler_pid_entry_dummy, 0, 0);
        cycles = benchmark_measure3(motor_set_multi, c, d);
        out_info_inthex("cyclesres", cycles - cycles_bl + 3);
        out_info("ok119");
        break;

      default:
        if (in_ch >= 0) {
          // unknown channel
          out_info_inthex("in_ch", in_ch);
          out_info("unknown channel");
          //out_error("unknown channel");
        } else {
          // some error
          out_info_inthex("in_ch", in_ch);
          out_info("unknown error");
          //out_error("unknown error");
        }
        break;
    }
  }
#endif
}


// one benchmark round (input-run-output)
void benchmark_run() {
  //out_info("\r\na benchmark");

  //out_info("disabling all interrupts (although they should be off at this point)");
  disable_all_interrupts();

  //out_info("baseline");
  //uint32_t cycles_bl = benchmark_measure(_imu_handler_pid_entry_dummy, 0, 0);
  //out_info_inthex("cyclesbl", cycles_bl);

  // set the inputs (fixed or after retrieving them from the uart)
  //out_info_inthex("szfl", sizeof(float));
  set_inputs();

  //out_info("running");
  //uint32_t cycles = benchmark_measure(imu_handler_pid_entry, 0, 0);
  //out_info_inthex("cyclesres", cycles - cycles_bl + 3);

  while(1);
/*
  for (uint32_t i = 0; i < 1000 * 2; i++) {
    _benchmark_helper_wait_1ms();
  }
*/
}

#endif

