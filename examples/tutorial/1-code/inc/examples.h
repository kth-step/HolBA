#ifndef _EXAMPLES_H
#define _EXAMPLES_H

#include <stdint.h>

// first examples
int8_t add_ (int8_t x, int8_t y);
uint64_t gcd(uint64_t x, uint64_t y);
int64_t sqrt_(int64_t x);
uint64_t modular_pow(uint64_t base, uint64_t exponent, uint64_t modulus);
uint64_t binary_search_buggy(uint64_t * buffer, uint64_t length, uint64_t value);
uint8_t binary_search_buggy2(uint64_t * buffer, uint8_t length, uint64_t value);
uint64_t binary_search_ok(uint64_t * buffer, uint64_t length, uint64_t value);
uint8_t binary_search_ok2(uint64_t * buffer, uint8_t length, uint64_t value);

// main tutorial example
int64_t add_reg (int64_t x, int64_t y);

// new examples
// - mutual recursion
uint64_t is_even(uint64_t n);
// - function sharing
int64_t add_times_two(int64_t x, int64_t y);
int64_t add_rec_times_two(int64_t x, int64_t y);
int64_t add_reg_fast_times_two(int64_t x, int64_t y);

#endif // _EXAMPLES_H
