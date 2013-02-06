/*
 * Copyright (c) 2002, Adam Dunkels.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials provided
 *    with the distribution.
 * 3. The name of the author may not be used to endorse or promote
 *    products derived from this software without specific prior
 *    written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
 * GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * This file is part of the Contiki desktop environment for the C64.
 *
 * $Id: petsciiconv.c,v 1.2 2010/01/31 23:46:19 oliverschmidt Exp $
 *
 */

/*
static unsigned char petscii2ascii[128] = {
  0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
  0x14,0x09,0x0d,0x11,0x93,0x0a,0x0e,0x0f,
  0x10,0x0b,0x12,0x13,0x08,0x15,0x16,0x17,
  0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,
  0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,
  0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
  0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,
  0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f,
  0x40,0x61,0x62,0x63,0x64,0x65,0x66,0x67,
  0x68,0x69,0x6a,0x6b,0x6c,0x6d,0x6e,0x6f,
  0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,
  0x78,0x79,0x7a,0x5b,0x5c,0x5d,0x7e,0x5f,
  0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7,
  0xc8,0xc9,0xca,0xcb,0xcc,0xcd,0xce,0xcf,
  0xd0,0xd1,0xd2,0xd3,0xd4,0xd5,0xd6,0xd7,
  0xd8,0xd9,0xda,0xdb,0xdc,0xdd,0x7e,0xdf
};
*/

static unsigned char ascii2petscii[128] = {
  0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
  0x14,0x09,0x0d,0x11,0x93,0x0a,0x0e,0x0f,
  0x10,0x0b,0x12,0x13,0x08,0x15,0x16,0x17,
  0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,
  0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,
  0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
  0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,
  0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f,
  0x40,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7,
  0xc8,0xc9,0xca,0xcb,0xcc,0xcd,0xce,0xcf,
  0xd0,0xd1,0xd2,0xd3,0xd4,0xd5,0xd6,0xd7,
  0xd8,0xd9,0xda,0x5b,0x5c,0x5d,0x5e,0x5f,
  0xc0,0x41,0x42,0x43,0x44,0x45,0x46,0x47,
  0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f,
  0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,
  0x58,0x59,0x5a,0xdb,0xdd,0xdd,0x5e,0xdf,
};

static unsigned int i;
static unsigned char *ptr;

/*-----------------------------------------------------------------------------------*/
void
petsciiconv_toascii(char *buf, unsigned int len)
{
  static char c;

  ptr = buf;
  for(i = len; i > 0; --i) {
    c = *ptr;
    if(c == 0x0a) {
      c = 0x0d;
    } else if(c == 0x0d) {
      c = 0x0a;
    }
    if(c != 0x40) {
      switch (c & 0xe0) {
      case 0x40:
      case 0x60:
        c ^= 0x20;
        break;
      case 0xc0:
        c ^= 0x80;
        break;
      }
    }
    *ptr = c & 0x7f;
    ++ptr;
  }
}
/*-----------------------------------------------------------------------------------*/
void
petsciiconv_topetscii(char *buf, unsigned int len)
{
  ptr = buf;
  for(i = len; i > 0; --i) {
    *ptr = ascii2petscii[*ptr & 0x7f];
    ++ptr;
  }
}
/*-----------------------------------------------------------------------------------*/
