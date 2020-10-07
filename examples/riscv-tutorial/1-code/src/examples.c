#include <stdint.h>
#include "examples_main.h"


int8_t add_ (int8_t x, int8_t y) {
  int8_t lx = x;
  int8_t volatile ly = y;
  while (lx > 0) {
    ly += 1;
    lx -= 1;
  }
  return ly;
}


uint64_t gcd(uint64_t x, uint64_t y) {
  while ((x>0) && (y>0) && (x != y)) {
    if (x > y)
      x = x-y;
    else
      y = y-x;
  }
  return x;
}


int64_t sqrt_(int64_t x) {
  int64_t y = 0;
  while ((y+1)*(y+1) <= x) {
    y += 1;
  }
  return y;
}


uint64_t modular_pow(uint64_t base, uint64_t exponent, uint64_t modulus) {
  if (modulus == 1) return 0;
  uint64_t result = 1;
  base = base % modulus;
  while (exponent > 0) {
    if ((exponent % 2) == 1) {
      result = (result * base) % modulus;
    }
    exponent = exponent >> 1;
    base = (base * base) % modulus;
  }
  return result;
}


uint64_t binary_search_buggy(uint64_t * buffer, uint64_t length, uint64_t value) {
  uint64_t left = 0;
  uint64_t right = length-1;
  while (left < right) {
    uint64_t middle = (right+left)/2;
    if (buffer[middle] == value)
      return middle;
    if (buffer[middle] < value)
      left = middle;
    else
      right = middle;
  }
  return length;
}

uint8_t binary_search_buggy2(uint64_t * buffer, uint8_t length, uint64_t value) {
  uint8_t left = 0;
  uint8_t right = length-1;
  PRINTF(("Size %d\n", sizeof(uint8_t)));
  while (left <= right) {
    uint8_t sum = right+left;
    uint8_t middle = (sum)/2;
    PRINTF(("left right left+right %ld, %ld, %ld\n", left, right, sum));
    PRINTF(("middle = %ld\n", middle));
    if (buffer[middle] == value)
      return middle;
    if (buffer[middle] < value)
      left = middle + 1;
    else
      right = middle - 1;
  }
  return length;
}

uint64_t binary_search_ok(uint64_t * buffer, uint64_t length, uint64_t value) {
  uint64_t left = 0;
  uint64_t right = length-1;
  uint64_t middle;
  while (left < right) {
    middle = left + (right-left)/2;
    if (buffer[middle] < value)
      left = middle + 1;
    else
      right = middle - 1;
  }
  if (buffer[middle] == value)
    return middle;
  return length;
}

uint8_t binary_search_ok2(uint64_t * buffer, uint8_t length, uint64_t value) {
  uint8_t left = 0;
  uint8_t right = length-1;
  uint8_t middle;
  while (left <= right) {
    middle = left + (right-left)/2;
    PRINTF(("left, middle, right = %ld, %ld, %ld\n", left, middle, right));
    if (buffer[middle] < value)
      left = middle + 1;
    else
      right = middle - 1;
  }
  if (buffer[middle] == value)
    return middle;
  return length;
}


