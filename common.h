/*
 * common.h
 *
 *  Created on: Jun 5, 2017
 *      Author: root
 */

#ifndef COMMON_H_
#define COMMON_H_

//----- Type defines ----------------------------------------------------------
typedef unsigned char      BYTE;    // Byte is a char
typedef unsigned short	   word16;  // 16-bit word is a short int
typedef unsigned int       word32;  // 32-bit word is an int

unsigned int crc32(unsigned int crc, const void *buf, int size);
unsigned short checksum(unsigned char *addr, unsigned int count);
unsigned int xor128(void);

#endif /* COMMON_H_ */
