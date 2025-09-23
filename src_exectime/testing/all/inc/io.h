/*
 * io.h
 *
 *  Created on: 8 aug. 2019
 *      Author: andreas
 */

#ifndef IO_H_
#define IO_H_

#include <stdint.h>

void io_init();


// returns negative number if there is no data available, otherwise channel id
int in_handle();
// data that has been produced last
extern int32_t in_data;
extern uint32_t in_data_len;
extern uint8_t in_buffer[2+1+1+255+2];


void out_data(uint8_t ch, uint8_t* data, uint8_t len);
void out_data_int(uint8_t ch, int32_t data);

void out_info(char *fmt, ...);
void out_debug(char *fmt, ...);
void out_error(char *fmt, ...);


// helpers
void out_info_inthex(char* s, uint32_t v);


#endif /* IO_H_ */
