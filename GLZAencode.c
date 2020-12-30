/***********************************************************************

Copyright 2014-2017 Kennon Conrad

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

***********************************************************************/

// GLZAencode.c
//   Encodes files created by GLZAcompress


#include <inttypes.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include "GLZA.h"
#include "GLZAmodel.h"

const uint8_t MAX_BITS_IN_CODE = 25;
const uint32_t UNIQUE_CHAR = 0xFFFFFFFF;
const uint32_t READ_SIZE = 0x80000;

uint8_t UTF8_compliant, cap_encoded, prior_is_cap, end_char, prior_end, use_mtf, use_mtfg;
uint8_t max_code_length, max_regular_code_length, found_first_symbol, cap_symbol_defined, cap_lock_symbol_defined;
uint8_t mtfg_queue_8_offset, mtfg_queue_16_offset, mtfg_queue_32_offset;
uint8_t mtfg_queue_64_offset, mtfg_queue_128_offset, mtfg_queue_192_offset;
uint8_t symbol_lengths[0x100], bin_code_length[0x100], sym_list_bits[0x100][26], mtf_queue_miss_code_length[16];
uint8_t mtf_queue_size[16];
uint16_t nbob[0x100][26], sum_nbob[0x100], fbob[0x100][26];
uint32_t num_grammar_rules, num_codes, start_my_symbols, num_base_symbols;
uint32_t mtfg_queue_symbol_7, mtfg_queue_symbol_15, mtfg_queue_symbol_31;
uint32_t mtfg_queue_symbol_63, mtfg_queue_symbol_127, mtfg_queue_symbol_191;
uint32_t mtf_queue[16][64], mtf_queue_started[16], mtf_queue_done[16], mtf_queue_peak[16], mtf_queue_hits[16];
uint32_t mtfg_queue_0[8], mtfg_queue_8[8], mtfg_queue_16[0x10], mtfg_queue_32[0x20];
uint32_t mtfg_queue_64[0x40], mtfg_queue_128[0x40], mtfg_queue_192[0x40];
uint32_t nsob[0x100][26], *sym_list_ptrs[0x100][26], *symbol_array;
int32_t prior_symbol;


// type:  bit 0: string ends 'C' or 'B' (cap symbol/cap lock symbol), bit1: string starts a-z, bit 2: non-ergodic, bit 3: in queue
// bit 4: "word"ness determined, bit 5: "word", bit 6: >15 instance word, bit 7: >15 instance word likely to be followed by ' '

struct symbol_data {
  uint8_t starts, ends, code_length, type;
  uint32_t count, inst_found, array_index, mtfg_hits, hit_score, define_symbol_start_index;
  int32_t space_score;
} *sd;


void print_string(uint32_t symbol_number) {
  uint32_t *symbol_ptr, *next_symbol_ptr;
  if (symbol_number < start_my_symbols) {
    if (UTF8_compliant != 0) {
      if (symbol_number < START_UTF8_2BYTE_SYMBOLS)
        printf("%c",(unsigned char)symbol_number);
      else if (symbol_number < START_UTF8_3BYTE_SYMBOLS) {
        printf("%c",(unsigned char)(symbol_number >> 6) + 0xC0);
        printf("%c",(unsigned char)(symbol_number & 0x3F) + 0x80);
      }
      else if (symbol_number < START_UTF8_4BYTE_SYMBOLS) {
        printf("%c",(unsigned char)(symbol_number >> 12) + 0xE0);
        printf("%c",(unsigned char)((symbol_number >> 6) & 0x3F) + 0x80);
        printf("%c",(unsigned char)(symbol_number & 0x3F) + 0x80);
      }
      else {
        printf("%c",(unsigned char)(symbol_number >> 18) + 0xF0);
        printf("%c",(unsigned char)((symbol_number >> 12) & 0x3F) + 0x80);
        printf("%c",(unsigned char)((symbol_number >> 6) & 0x3F) + 0x80);
        printf("%c",(unsigned char)(symbol_number & 0x3F) + 0x80);
      }
    }
    else
      printf("%c",(unsigned char)symbol_number);
  }
  else {
    symbol_ptr = symbol_array + sd[symbol_number].define_symbol_start_index;
    next_symbol_ptr = symbol_array + sd[symbol_number+1].define_symbol_start_index - 1;
    while (symbol_ptr != next_symbol_ptr)
      print_string(*symbol_ptr++);
  }
  return;
}


void print_string2(uint32_t symbol_number) {
  uint32_t *symbol_ptr, *next_symbol_ptr;
  if (symbol_number < start_my_symbols) {
    if (UTF8_compliant != 0) {
      if (symbol_number < START_UTF8_2BYTE_SYMBOLS)
        fprintf(stderr,"%c",(unsigned char)symbol_number);
      else if (symbol_number < START_UTF8_3BYTE_SYMBOLS) {
        fprintf(stderr,"%c",(unsigned char)(symbol_number >> 6) + 0xC0);
        fprintf(stderr,"%c",(unsigned char)(symbol_number & 0x3F) + 0x80);
      }
      else if (symbol_number < START_UTF8_4BYTE_SYMBOLS) {
        fprintf(stderr,"%c",(unsigned char)(symbol_number >> 12) + 0xE0);
        fprintf(stderr,"%c",(unsigned char)((symbol_number >> 6) & 0x3F) + 0x80);
        fprintf(stderr,"%c",(unsigned char)(symbol_number & 0x3F) + 0x80);
      }
      else {
        fprintf(stderr,"%c",(unsigned char)(symbol_number >> 18) + 0xF0);
        fprintf(stderr,"%c",(unsigned char)((symbol_number >> 12) & 0x3F) + 0x80);
        fprintf(stderr,"%c",(unsigned char)((symbol_number >> 6) & 0x3F) + 0x80);
        fprintf(stderr,"%c",(unsigned char)(symbol_number & 0x3F) + 0x80);
      }
    }
    else
      fprintf(stderr,"%c",(unsigned char)symbol_number);
  }
  else {
    symbol_ptr = symbol_array + sd[symbol_number].define_symbol_start_index;
    next_symbol_ptr = symbol_array + sd[symbol_number+1].define_symbol_start_index - 1;
    while (symbol_ptr != next_symbol_ptr)
      print_string2(*symbol_ptr++);
  }
  return;
}


void get_symbol_category(uint32_t symbol_number, uint8_t *sym_type_ptr) {
  if (symbol_number >= start_my_symbols) {
    if (sd[symbol_number].type & 0x20) {
      *sym_type_ptr |= 0x30;
      return;
    }
    uint32_t * string_ptr = symbol_array + sd[symbol_number+1].define_symbol_start_index - 2;
    get_symbol_category(*string_ptr, sym_type_ptr);
    while (((*sym_type_ptr & 0x10) == 0) && (string_ptr != symbol_array + sd[symbol_number].define_symbol_start_index))
      get_symbol_category(*--string_ptr, sym_type_ptr);
    if ((sd[symbol_number].type & 0x10) == 0)
      sd[symbol_number].type |= *sym_type_ptr & 0x30;
  }
  else if (symbol_number == (uint32_t)' ')
    *sym_type_ptr |= 0x30;
  return;
}


uint8_t find_first(uint32_t symbol_number) {
  uint8_t first_char;
  uint32_t first_symbol = symbol_array[sd[symbol_number].define_symbol_start_index];
  if (first_symbol >= start_my_symbols) {
    if ((first_char = sd[first_symbol].starts) == 0) {
      first_char = find_first(first_symbol);
      sd[first_symbol].starts = first_char;
    }
    return(first_char);
  }
  return((uint8_t)first_symbol);
}


uint8_t find_first_UTF8(uint32_t symbol_number) {
  uint8_t first_char;
  uint32_t first_symbol = symbol_array[sd[symbol_number].define_symbol_start_index];
  if (first_symbol >= start_my_symbols) {
    if ((first_char = sd[first_symbol].starts) == 0) {
      first_char = find_first_UTF8(first_symbol);
      sd[first_symbol].starts = first_char;
    }
    return(first_char);
  }
  if (first_symbol < START_UTF8_2BYTE_SYMBOLS)
    return((uint8_t)first_symbol);
  else if (first_symbol < 0x250)
    return(0x80);
  else if (first_symbol < 0x370)
    return(0x81);
  else if (first_symbol < 0x400)
    return(0x82);
  else if (first_symbol < 0x530)
    return(0x83);
  else if (first_symbol < 0x590)
    return(0x84);
  else if (first_symbol < 0x600)
    return(0x85);
  else if (first_symbol < 0x700)
    return(0x86);
  else if (first_symbol < START_UTF8_3BYTE_SYMBOLS)
    return(0x87);
  else if (first_symbol < 0x1000)
    return(0x88);
  else if (first_symbol < 0x2000)
    return(0x89);
  else if (first_symbol < 0x3000)
    return(0x8A);
  else if (first_symbol < 0x3040)
    return(0x8B);
  else if (first_symbol < 0x30A0)
    return(0x8C);
  else if (first_symbol < 0x3100)
    return(0x8D);
  else if (first_symbol < 0x3200)
    return(0x8E);
  else if (first_symbol < 0xA000)
    return(0x8F);
  else if (first_symbol < START_UTF8_4BYTE_SYMBOLS)
    return(0x8E);
  else
    return(0x90);
}


uint8_t find_last(uint32_t symbol_number) {
  uint8_t last_char;
  uint32_t last_symbol = symbol_array[sd[symbol_number+1].define_symbol_start_index - 2];
  if (last_symbol >= start_my_symbols) {
    if ((last_char = sd[last_symbol].ends) == 0) {
      last_char = find_last(last_symbol);
      sd[last_symbol].ends = last_char;
    }
    return(last_char);
  }
  if ((cap_encoded != 0) && (last_symbol == 'B'))
    return('C');
  return((uint8_t)last_symbol);
}


uint8_t find_last_UTF8(uint32_t symbol_number) {
  uint8_t last_char;
  uint32_t last_symbol = symbol_array[sd[symbol_number+1].define_symbol_start_index - 2];
  if (last_symbol >= start_my_symbols) {
    if ((last_char = sd[last_symbol].ends) == 0) {
      last_char = find_last_UTF8(last_symbol);
      sd[last_symbol].ends = last_char;
    }
    return(last_char);
  }
  if ((cap_encoded != 0) && (last_symbol == 'B'))
    return('C');
  if (last_symbol < START_UTF8_2BYTE_SYMBOLS)
    return((uint8_t)last_symbol);
  else if (last_symbol < 0x250)
    return(0x80);
  else if (last_symbol < 0x370)
    return(0x81);
  else if (last_symbol < 0x400)
    return(0x82);
  else if (last_symbol < 0x530)
    return(0x83);
  else if (last_symbol < 0x590)
    return(0x84);
  else if (last_symbol < 0x600)
    return(0x85);
  else if (last_symbol < 0x700)
    return(0x86);
  else if (last_symbol < START_UTF8_3BYTE_SYMBOLS)
    return(0x87);
  else if (last_symbol < 0x1000)
    return(0x88);
  else if (last_symbol < 0x2000)
    return(0x89);
  else if (last_symbol < 0x3000)
    return(0x8A);
  else if (last_symbol < 0x3040)
    return(0x8B);
  else if (last_symbol < 0x30A0)
    return(0x8C);
  else if (last_symbol < 0x3100)
    return(0x8D);
  else if (last_symbol < 0x3200)
    return(0x8E);
  else if (last_symbol < 0xA000)
    return(0x8F);
  else if (last_symbol < START_UTF8_4BYTE_SYMBOLS)
    return(0x8E);
  else
    return(0x90);
}


uint8_t add_dictionary_symbol(uint32_t symbol, uint8_t bits) {
  uint8_t first_char = sd[symbol].starts;
  if (nsob[first_char][bits] == ((uint32_t)1 << sym_list_bits[first_char][bits])) {
    sym_list_bits[first_char][bits]++;
    if (0 == (sym_list_ptrs[first_char][bits]
        = (uint32_t *)realloc(sym_list_ptrs[first_char][bits], sizeof(uint32_t) * (1 << sym_list_bits[first_char][bits])))) {
      fprintf(stderr,"FATAL ERROR - symbol list realloc failure\n");
      return(0);
    }
  }
  sd[symbol].array_index = nsob[first_char][bits];
  sym_list_ptrs[first_char][bits][nsob[first_char][bits]] = symbol;
  if ((nsob[first_char][bits]++ << (32 - bits)) == ((uint32_t)nbob[first_char][bits] << (32 - bin_code_length[first_char]))) {
    if (bits >= bin_code_length[first_char]) { /* add a bin */
      nbob[first_char][bits]++;
      if (sum_nbob[first_char] < 0x1000) {
        sum_nbob[first_char]++;
        while (bits++ != max_code_length)
          fbob[first_char][bits]++;
      }
      else {
        bin_code_length[first_char]--;
        sum_nbob[first_char] = 0;
        for (bits = 1 ; bits <= max_code_length ; bits++) {
          fbob[first_char][bits] = sum_nbob[first_char];
          sum_nbob[first_char] += (nbob[first_char][bits] = (nbob[first_char][bits] + 1) >> 1);
        }
      }
    }
    else { /* add multiple bins */
      uint32_t new_bins = 1 << (bin_code_length[first_char] - bits);
      if (sum_nbob[first_char] + new_bins <= 0x1000) {
        sum_nbob[first_char] += new_bins;
        nbob[first_char][bits] += new_bins;
        while (bits++ != max_code_length)
          fbob[first_char][bits] += new_bins;
      }
      else {
        if (new_bins <= 0x1000) {
          nbob[first_char][bits] += new_bins;
          do {
            bin_code_length[first_char]--;
            sum_nbob[first_char] = 0;
            for (bits = 1 ; bits <= max_code_length ; bits++)
              sum_nbob[first_char] += (nbob[first_char][bits] = (nbob[first_char][bits] + 1) >> 1);
          } while (sum_nbob[first_char] > 0x1000);
        }
        else {
          uint8_t bin_shift = bin_code_length[first_char] - 12 - bits;
          if (sum_nbob[first_char] != 0)
            bin_shift++;
          bin_code_length[first_char] -= bin_shift;
          sum_nbob[first_char] = 0;
          uint8_t code_length;
          for (code_length = 1 ; code_length <= max_code_length ; code_length++)
            sum_nbob[first_char] += (nbob[first_char][code_length]
                = ((nbob[first_char][code_length] - 1) >> bin_shift) + 1);
          nbob[first_char][bits] += new_bins >> bin_shift;
          sum_nbob[first_char] += new_bins >> bin_shift;
        }
        uint16_t bin = nbob[first_char][1];
        for (bits = 2 ; bits <= max_code_length ; bits++) {
          fbob[first_char][bits] = bin;
          bin += nbob[first_char][bits];
        }
      }
    }
  }
  return(1);
}


void remove_dictionary_symbol(uint32_t symbol, uint8_t bits) {
  uint8_t first_char = sd[symbol].starts;
  uint32_t * sym_list_ptr = &sym_list_ptrs[first_char][bits][--nsob[first_char][bits]];
  sym_list_ptrs[first_char][bits][sd[symbol].array_index] = *sym_list_ptr;
  sd[*sym_list_ptr].array_index = sd[symbol].array_index;
  return;
}


void remove_mtfg_queue_symbol_16(uint8_t mtfg_queue_position) {
  while (mtfg_queue_position != 31) {
    *(mtfg_queue_16 + ((mtfg_queue_16_offset + mtfg_queue_position) & 0xF))
        = *(mtfg_queue_16 + ((mtfg_queue_16_offset + mtfg_queue_position + 1) & 0xF));
    mtfg_queue_position++;
  }
  *(mtfg_queue_16 + ((mtfg_queue_16_offset - 1) & 0xF)) = *(mtfg_queue_32 + mtfg_queue_32_offset);
  *(mtfg_queue_32 + mtfg_queue_32_offset) = *(mtfg_queue_64 + mtfg_queue_64_offset);
  mtfg_queue_32_offset = (mtfg_queue_32_offset + 1) & 0x1F;
  *(mtfg_queue_64 + mtfg_queue_64_offset) = *(mtfg_queue_128 + mtfg_queue_128_offset);
  mtfg_queue_64_offset = (mtfg_queue_64_offset + 1) & 0x3F;
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset);
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F;
  *(mtfg_queue_192 + mtfg_queue_192_offset) = num_codes;
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F;
  return;
}


void remove_mtfg_queue_symbol_32(uint8_t mtfg_queue_position) {
  while (mtfg_queue_position != 63) {
    *(mtfg_queue_32 + ((mtfg_queue_32_offset + mtfg_queue_position) & 0x1F))
        = *(mtfg_queue_32 + ((mtfg_queue_32_offset + mtfg_queue_position + 1) & 0x1F));
    mtfg_queue_position++;
  }
  *(mtfg_queue_32 + ((mtfg_queue_32_offset - 1) & 0x1F)) = *(mtfg_queue_64 + mtfg_queue_64_offset);
  *(mtfg_queue_64 + mtfg_queue_64_offset) = *(mtfg_queue_128 + mtfg_queue_128_offset);
  mtfg_queue_64_offset = (mtfg_queue_64_offset + 1) & 0x3F;
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset);
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F;
  *(mtfg_queue_192 + mtfg_queue_192_offset) = num_codes;
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F;
  return;
}


void remove_mtfg_queue_symbol_64(uint8_t mtfg_queue_position) {
  while (mtfg_queue_position != 127) {
    *(mtfg_queue_64 + ((mtfg_queue_64_offset + mtfg_queue_position) & 0x3F))
        = *(mtfg_queue_64 + ((mtfg_queue_64_offset + mtfg_queue_position + 1) & 0x3F));
    mtfg_queue_position++;
  }
  *(mtfg_queue_64 + ((mtfg_queue_64_offset - 1) & 0x3F)) = *(mtfg_queue_128 + mtfg_queue_128_offset);
  *(mtfg_queue_128 + mtfg_queue_128_offset) = *(mtfg_queue_192 + mtfg_queue_192_offset);
  mtfg_queue_128_offset = (mtfg_queue_128_offset + 1) & 0x3F;
  *(mtfg_queue_192 + mtfg_queue_192_offset) = num_codes;
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F;
  return;
}


void remove_mtfg_queue_symbol_128(uint8_t mtfg_queue_position) {
  while (mtfg_queue_position != 191) {
    *(mtfg_queue_128 + ((mtfg_queue_128_offset + mtfg_queue_position) & 0x3F))
        = *(mtfg_queue_128 + ((mtfg_queue_128_offset + mtfg_queue_position + 1) & 0x3F));
    mtfg_queue_position++;
  }
  *(mtfg_queue_128 + ((mtfg_queue_128_offset - 1) & 0x3F)) = *(mtfg_queue_192 + mtfg_queue_192_offset);
  *(mtfg_queue_192 + mtfg_queue_192_offset) = num_codes;
  mtfg_queue_192_offset = (mtfg_queue_192_offset + 1) & 0x3F;
  return;
}


void remove_mtfg_queue_symbol_192(uint8_t mtfg_queue_position) {
  while (mtfg_queue_position != 255) {
    *(mtfg_queue_192 + ((mtfg_queue_192_offset + mtfg_queue_position) & 0x3F))
        = *(mtfg_queue_192 + ((mtfg_queue_192_offset + mtfg_queue_position + 1) & 0x3F));
    mtfg_queue_position++;
  }
  *(mtfg_queue_192 + ((mtfg_queue_192_offset - 1) & 0x3F)) = num_codes;
  return;
}


void increment_mtfg_queue_0(uint32_t symbol_number) {
  mtfg_queue_symbol_7 = mtfg_queue_0[7];
  mtfg_queue_0[7] = mtfg_queue_0[6];
  mtfg_queue_0[6] = mtfg_queue_0[5];
  mtfg_queue_0[5] = mtfg_queue_0[4];
  mtfg_queue_0[4] = mtfg_queue_0[3];
  mtfg_queue_0[3] = mtfg_queue_0[2];
  mtfg_queue_0[2] = mtfg_queue_0[1];
  mtfg_queue_0[1] = mtfg_queue_0[0];
  mtfg_queue_0[0] = symbol_number;
  return;
}


void increment_mtfg_queue_8() {
  mtfg_queue_8_offset = (mtfg_queue_8_offset - 1) & 7;
  mtfg_queue_symbol_15 = *(mtfg_queue_8 + mtfg_queue_8_offset);
  *(mtfg_queue_8 + mtfg_queue_8_offset) = mtfg_queue_symbol_7;
  return;
}


void increment_mtfg_queue_16() {
  mtfg_queue_16_offset = (mtfg_queue_16_offset - 1) & 0xF;
  mtfg_queue_symbol_31 = *(mtfg_queue_16 + mtfg_queue_16_offset);
  *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15;
  return;
}


void increment_mtfg_queue_32() {
  mtfg_queue_32_offset = (mtfg_queue_32_offset - 1) & 0x1F;
  mtfg_queue_symbol_63 = *(mtfg_queue_32 + mtfg_queue_32_offset);
  *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31;
  return;
}


void increment_mtfg_queue_64() {
  mtfg_queue_64_offset = (mtfg_queue_64_offset - 1) & 0x3F;
  mtfg_queue_symbol_127 = *(mtfg_queue_64 + mtfg_queue_64_offset);
  *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63;
  return;
}


void increment_mtfg_queue_128() {
  mtfg_queue_128_offset = (mtfg_queue_128_offset - 1) & 0x3F;
  mtfg_queue_symbol_191 = *(mtfg_queue_128 + mtfg_queue_128_offset);
  *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127;
  return;
}


void increment_mtfg_queue_192_1() {
  mtfg_queue_192_offset = (mtfg_queue_192_offset - 1) & 0x3F;
  sd[*(mtfg_queue_192 + mtfg_queue_192_offset)].type &= 0xF7;
  *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191;
  return;
}


void increment_mtfg_queue_192() {
  mtfg_queue_192_offset = (mtfg_queue_192_offset - 1) & 0x3F;
if (*(mtfg_queue_192 + mtfg_queue_192_offset) != num_codes) {
 sd[*(mtfg_queue_192 + mtfg_queue_192_offset)].type &= 0xF7;
 add_dictionary_symbol(*(mtfg_queue_192 + mtfg_queue_192_offset),sd[*(mtfg_queue_192 + mtfg_queue_192_offset)].code_length);
}
  *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191;
  return;
}


void add_symbol_to_mtfg_queue1(uint32_t symbol_number) {
  sd[symbol_number].type |= 8;
  increment_mtfg_queue_0(symbol_number);
  increment_mtfg_queue_8();
  if (sd[mtfg_queue_symbol_15].code_length > 12) {
    increment_mtfg_queue_16();
    if (sd[mtfg_queue_symbol_31].code_length != 13) {
      increment_mtfg_queue_32();
      if (sd[mtfg_queue_symbol_63].code_length != 14) {
        increment_mtfg_queue_64();
        if (sd[mtfg_queue_symbol_127].code_length != 15) {
          increment_mtfg_queue_128();
          if (sd[mtfg_queue_symbol_191].code_length != 16)
            increment_mtfg_queue_192_1();
          else if (mtfg_queue_symbol_191 != num_codes)
            sd[mtfg_queue_symbol_191].type &= 0xF7;
        }
        else if (mtfg_queue_symbol_127 != num_codes)
          sd[mtfg_queue_symbol_127].type &= 0xF7;
      }
      else if (mtfg_queue_symbol_63 != num_codes)
        sd[mtfg_queue_symbol_63].type &= 0xF7;
    }
    else if (mtfg_queue_symbol_31 != num_codes)
      sd[mtfg_queue_symbol_31].type &= 0xF7;
  } 
  else if (mtfg_queue_symbol_15 != num_codes)
    sd[mtfg_queue_symbol_15].type &= 0xF7;
  return;
}


void add_symbol_to_mtfg_queue(uint32_t symbol_number) {
  sd[symbol_number].type |= 8;
  increment_mtfg_queue_0(symbol_number);
  increment_mtfg_queue_8();
  if (sd[mtfg_queue_symbol_15].code_length > 12) {
    increment_mtfg_queue_16();
    if (sd[mtfg_queue_symbol_31].code_length != 13) {
      increment_mtfg_queue_32();
      if (sd[mtfg_queue_symbol_63].code_length != 14) {
        increment_mtfg_queue_64();
        if (sd[mtfg_queue_symbol_127].code_length != 15) {
          increment_mtfg_queue_128();
          if (sd[mtfg_queue_symbol_191].code_length != 16)
            increment_mtfg_queue_192();
          else if (mtfg_queue_symbol_191 != num_codes) {
            sd[mtfg_queue_symbol_191].type &= 0xF7;
            add_dictionary_symbol(mtfg_queue_symbol_191,sd[mtfg_queue_symbol_191].code_length);
          }
        }
        else if (mtfg_queue_symbol_127 != num_codes) {
          sd[mtfg_queue_symbol_127].type &= 0xF7;
          add_dictionary_symbol(mtfg_queue_symbol_127,sd[mtfg_queue_symbol_127].code_length);
        }
      }
      else if (mtfg_queue_symbol_63 != num_codes) {
        sd[mtfg_queue_symbol_63].type &= 0xF7;
        add_dictionary_symbol(mtfg_queue_symbol_63,sd[mtfg_queue_symbol_63].code_length);
      }
    }
    else if (mtfg_queue_symbol_31 != num_codes) {
      sd[mtfg_queue_symbol_31].type &= 0xF7;
      add_dictionary_symbol(mtfg_queue_symbol_31,sd[mtfg_queue_symbol_31].code_length);
    }
  } 
  else if (mtfg_queue_symbol_15 != num_codes) {
    sd[mtfg_queue_symbol_15].type &= 0xF7;
    add_dictionary_symbol(mtfg_queue_symbol_15,sd[mtfg_queue_symbol_15].code_length);
  }
  return;
}


void manage_mtfg_queue1(uint32_t symbol_number) {
  uint8_t mtfg_queue_position;
  uint32_t subqueue_position;
  mtfg_queue_position = 0;
  do {
    if (symbol_number == mtfg_queue_0[mtfg_queue_position]) {
      sd[symbol_number].hit_score += 61 - 3 * mtfg_queue_position;
      while (mtfg_queue_position) {
        mtfg_queue_0[mtfg_queue_position] = mtfg_queue_0[mtfg_queue_position-1];
        mtfg_queue_position--;
      }
      mtfg_queue_0[0] = symbol_number;
      break;
    }
  } while (++mtfg_queue_position != 5);
  if (mtfg_queue_position == 5) {
    do {
      if (symbol_number == mtfg_queue_0[mtfg_queue_position]) {
        sd[symbol_number].hit_score += 56 - 2 * mtfg_queue_position;
        while (mtfg_queue_position != 5) {
          mtfg_queue_0[mtfg_queue_position] = mtfg_queue_0[mtfg_queue_position-1];
          mtfg_queue_position--;
        }
        mtfg_queue_0[5] = mtfg_queue_0[4];
        mtfg_queue_0[4] = mtfg_queue_0[3];
        mtfg_queue_0[3] = mtfg_queue_0[2];
        mtfg_queue_0[2] = mtfg_queue_0[1];
        mtfg_queue_0[1] = mtfg_queue_0[0];
        mtfg_queue_0[0] = symbol_number;
        break;
      }
    } while (++mtfg_queue_position != 8);
    if (mtfg_queue_position == 8) {
      increment_mtfg_queue_0(symbol_number);
      do {
        if (symbol_number == *(mtfg_queue_8 + ((mtfg_queue_position + mtfg_queue_8_offset) & 7))) {
          sd[symbol_number].hit_score += 48 - mtfg_queue_position;
          subqueue_position = mtfg_queue_position - 8;
          while (subqueue_position) {
            *(mtfg_queue_8 + ((mtfg_queue_8_offset + subqueue_position) & 7))
                = *(mtfg_queue_8 + ((mtfg_queue_8_offset + subqueue_position - 1) & 7));
            subqueue_position--;
          }
          *(mtfg_queue_8 + mtfg_queue_8_offset) = mtfg_queue_symbol_7;
          break;
        }
      } while (++mtfg_queue_position != 16);
      if (mtfg_queue_position == 16) {
        increment_mtfg_queue_8();
        do {
          if (symbol_number == *(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF))) {
            sd[symbol_number].hit_score += 40 - (mtfg_queue_position >> 1);
            if (sd[mtfg_queue_symbol_15].code_length <= 12) {
              sd[mtfg_queue_symbol_15].type &= 0xF7;
              remove_mtfg_queue_symbol_16(mtfg_queue_position);
            }
            else {
              subqueue_position = mtfg_queue_position - 16;
              while (subqueue_position) {
                *(mtfg_queue_16 + ((mtfg_queue_16_offset + subqueue_position) & 0xF))
                    = *(mtfg_queue_16 + ((mtfg_queue_16_offset + subqueue_position - 1) & 0xF));
                subqueue_position--;
              }
              *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15;
            }
            break;
          }
        } while (++mtfg_queue_position != 32);
        if (mtfg_queue_position == 32) {
          do {
            if (symbol_number == *(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F))) {
              sd[symbol_number].hit_score += 28 - (mtfg_queue_position >> 3);
              if (sd[mtfg_queue_symbol_15].code_length <= 12) {
                sd[mtfg_queue_symbol_15].type &= 0xF7;
                remove_mtfg_queue_symbol_32(mtfg_queue_position);
              }
              else {
                increment_mtfg_queue_16();
                if (sd[mtfg_queue_symbol_31].code_length == 13) {
                  sd[mtfg_queue_symbol_31].type &= 0xF7;
                  remove_mtfg_queue_symbol_32(mtfg_queue_position);
                }
                else {
                  subqueue_position = mtfg_queue_position - 32;
                  while (subqueue_position) {
                    *(mtfg_queue_32 + ((mtfg_queue_32_offset + subqueue_position) & 0x1F))
                        = *(mtfg_queue_32 + ((mtfg_queue_32_offset + subqueue_position - 1) & 0x1F));
                    subqueue_position--;
                  }
                  *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31;
                }
              }
              break;
            }
          } while (++mtfg_queue_position != 64);
          if (mtfg_queue_position == 64) {
            do {
              if (symbol_number == *(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F))) {
                sd[symbol_number].hit_score += 22 - (mtfg_queue_position >> 5);
                if (sd[mtfg_queue_symbol_15].code_length <= 12) {
                  sd[mtfg_queue_symbol_15].type &= 0xF7;
                  remove_mtfg_queue_symbol_64(mtfg_queue_position);
                }
                else {
                  increment_mtfg_queue_16();
                  if (sd[mtfg_queue_symbol_31].code_length == 13) {
                    sd[mtfg_queue_symbol_31].type &= 0xF7;
                    remove_mtfg_queue_symbol_64(mtfg_queue_position);
                  }
                  else {
                    increment_mtfg_queue_32();
                    if (sd[mtfg_queue_symbol_63].code_length == 14) {
                      sd[mtfg_queue_symbol_63].type &= 0xF7;
                      remove_mtfg_queue_symbol_64(mtfg_queue_position);
                    }
                    else {
                      subqueue_position = mtfg_queue_position - 64;
                      while (subqueue_position) {
                        *(mtfg_queue_64 + ((mtfg_queue_64_offset + subqueue_position) & 0x3F))
                            = *(mtfg_queue_64 + ((mtfg_queue_64_offset + subqueue_position - 1) & 0x3F));
                        subqueue_position--;
                      }
                      *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63;
                    }
                  }
                }
                break;
              }
            } while (++mtfg_queue_position != 128);
            if (mtfg_queue_position == 128) {
              do {
                if (symbol_number == *(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F))) {
                  sd[symbol_number].hit_score += 20 - (mtfg_queue_position >> 6);
                  if (sd[mtfg_queue_symbol_15].code_length <= 12) {
                    sd[mtfg_queue_symbol_15].type &= 0xF7;
                    remove_mtfg_queue_symbol_128(mtfg_queue_position);
                  }
                  else {
                    increment_mtfg_queue_16();
                    if (sd[mtfg_queue_symbol_31].code_length == 13) {
                      sd[mtfg_queue_symbol_31].type &= 0xF7;
                      remove_mtfg_queue_symbol_128(mtfg_queue_position);
                    }
                    else {
                      increment_mtfg_queue_32();
                      if (sd[mtfg_queue_symbol_63].code_length == 14) {
                        sd[mtfg_queue_symbol_63].type &= 0xF7;
                        remove_mtfg_queue_symbol_128(mtfg_queue_position);
                      }
                      else {
                        increment_mtfg_queue_64();
                        if (sd[mtfg_queue_symbol_127].code_length == 15) {
                          sd[mtfg_queue_symbol_127].type &= 0xF7;
                          remove_mtfg_queue_symbol_128(mtfg_queue_position);
                        }
                        else {
                          subqueue_position = mtfg_queue_position - 128;
                          while (subqueue_position) {
                            *(mtfg_queue_128 + ((mtfg_queue_128_offset + subqueue_position) & 0x3F))
                                = *(mtfg_queue_128 + ((mtfg_queue_128_offset + subqueue_position - 1) & 0x3F));
                            subqueue_position--;
                          }
                          *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127;
                        }
                      }
                    }
                  }
                  break;
                }
              } while (++mtfg_queue_position != 192);
              if (mtfg_queue_position == 192) {
                while (symbol_number != *(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F)))
                  mtfg_queue_position++;
                sd[symbol_number].hit_score += 20 - (mtfg_queue_position >> 6);
                if (sd[mtfg_queue_symbol_15].code_length <= 12) {
                  sd[mtfg_queue_symbol_15].type &= 0xF7;
                  remove_mtfg_queue_symbol_192(mtfg_queue_position);
                }
                else {
                  increment_mtfg_queue_16();
                  if (sd[mtfg_queue_symbol_31].code_length == 13) {
                    sd[mtfg_queue_symbol_31].type &= 0xF7;
                    remove_mtfg_queue_symbol_192(mtfg_queue_position);
                  }
                  else {
                    increment_mtfg_queue_32();
                    if (sd[mtfg_queue_symbol_63].code_length == 14) {
                      sd[mtfg_queue_symbol_63].type &= 0xF7;
                      remove_mtfg_queue_symbol_192(mtfg_queue_position);
                    }
                    else {
                      increment_mtfg_queue_64();
                      if (sd[mtfg_queue_symbol_127].code_length == 15) {
                        sd[mtfg_queue_symbol_127].type &= 0xF7;
                        remove_mtfg_queue_symbol_192(mtfg_queue_position);
                      }
                      else {
                        increment_mtfg_queue_128();
                        if (sd[mtfg_queue_symbol_191].code_length == 16) {
                          sd[mtfg_queue_symbol_191].type &= 0xF7;
                          remove_mtfg_queue_symbol_192(mtfg_queue_position);
                        }
                        else {
                          subqueue_position = mtfg_queue_position - 192;
                          while (subqueue_position) {
                            *(mtfg_queue_192 + ((mtfg_queue_192_offset + subqueue_position) & 0x3F))
                                = *(mtfg_queue_192 + ((mtfg_queue_192_offset + subqueue_position - 1) & 0x3F));
                            subqueue_position--;
                          }
                          *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  return;
}


void manage_mtfg_queue(uint32_t symbol_number, uint8_t in_definition) {
  uint8_t mtfg_queue_position = 0;
  uint8_t cap_queue_position = 0;
  uint8_t subqueue_position;
  do {
    if (symbol_number == mtfg_queue_0[mtfg_queue_position]) {
      if (in_definition == 0)
        EncodeMtfgType(LEVEL0);
      else
        EncodeMtfgType(LEVEL1);
      EncodeMtfgQueuePos(NOT_CAP, mtfg_queue_position);
      while (mtfg_queue_position) {
        mtfg_queue_0[mtfg_queue_position] = mtfg_queue_0[mtfg_queue_position-1];
        mtfg_queue_position--;
      }
      mtfg_queue_0[0] = symbol_number;
      break;
    }
  } while (++mtfg_queue_position != 8);
  if (mtfg_queue_position == 8) {
    increment_mtfg_queue_0(symbol_number);
    do {
      if (symbol_number == *(mtfg_queue_8 + ((mtfg_queue_position + mtfg_queue_8_offset) & 7))) {
        if (in_definition == 0)
          EncodeMtfgType(LEVEL0);
        else
          EncodeMtfgType(LEVEL1);
        EncodeMtfgQueuePos(NOT_CAP, mtfg_queue_position);
        subqueue_position = mtfg_queue_position - 8;
        while (subqueue_position) {
          *(mtfg_queue_8 + ((mtfg_queue_8_offset + subqueue_position) & 7))
              = *(mtfg_queue_8 + ((mtfg_queue_8_offset + subqueue_position - 1) & 7));
          subqueue_position--;
        }
        *(mtfg_queue_8 + mtfg_queue_8_offset) = mtfg_queue_symbol_7;
        break;
      }
    } while (++mtfg_queue_position != 16);
    if (mtfg_queue_position == 16) {
      increment_mtfg_queue_8();
      do {
        if (symbol_number == *(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF))) {
          if (in_definition == 0)
            EncodeMtfgType(LEVEL0);
          else
            EncodeMtfgType(LEVEL1);
          EncodeMtfgQueuePos(NOT_CAP, mtfg_queue_position);
          if (sd[mtfg_queue_symbol_15].code_length <= 12) {
            remove_mtfg_queue_symbol_16(mtfg_queue_position);
            if (mtfg_queue_symbol_15 != num_codes) {
              sd[mtfg_queue_symbol_15].type &= 0xF7;
              add_dictionary_symbol(mtfg_queue_symbol_15,sd[mtfg_queue_symbol_15].code_length);
            }
          }
          else {
            subqueue_position = mtfg_queue_position - 16;
            while (subqueue_position) {
              *(mtfg_queue_16 + ((mtfg_queue_16_offset + subqueue_position) & 0xF))
                  = *(mtfg_queue_16 + ((mtfg_queue_16_offset + subqueue_position - 1) & 0xF));
              subqueue_position--;
            }
            *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15;
          }
          break;
        }
      } while (++mtfg_queue_position != 32);
      if (mtfg_queue_position == 32) {
        do {
          if (symbol_number == *(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F))) {
            if (in_definition == 0)
              EncodeMtfgType(LEVEL0);
            else
              EncodeMtfgType(LEVEL1);
            EncodeMtfgQueuePos(NOT_CAP, mtfg_queue_position);
            if (sd[mtfg_queue_symbol_15].code_length <= 12) {
              remove_mtfg_queue_symbol_32(mtfg_queue_position);
              if (mtfg_queue_symbol_15 != num_codes) {
                sd[mtfg_queue_symbol_15].type &= 0xF7;
                add_dictionary_symbol(mtfg_queue_symbol_15,sd[mtfg_queue_symbol_15].code_length);
              }
            }
            else {
              increment_mtfg_queue_16();
              if (sd[mtfg_queue_symbol_31].code_length == 13) {
                remove_mtfg_queue_symbol_32(mtfg_queue_position);
                if (mtfg_queue_symbol_31 != num_codes) {
                  sd[mtfg_queue_symbol_31].type &= 0xF7;
                  add_dictionary_symbol(mtfg_queue_symbol_31,sd[mtfg_queue_symbol_31].code_length);
                }
              }
              else {
                subqueue_position = mtfg_queue_position - 32;
                while (subqueue_position) {
                  *(mtfg_queue_32 + ((mtfg_queue_32_offset + subqueue_position) & 0x1F))
                      = *(mtfg_queue_32 + ((mtfg_queue_32_offset + subqueue_position - 1) & 0x1F));
                  subqueue_position--;
                }
                *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31;
              }
            }
            break;
          }
        } while (++mtfg_queue_position != 64);
        if (mtfg_queue_position == 64) {
          do {
            if (symbol_number == *(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F))) {
              if (in_definition == 0)
                EncodeMtfgType(LEVEL0);
              else
                EncodeMtfgType(LEVEL1);
              EncodeMtfgQueuePos(NOT_CAP, mtfg_queue_position);
              if (sd[mtfg_queue_symbol_15].code_length <= 12) {
                remove_mtfg_queue_symbol_64(mtfg_queue_position);
                if (mtfg_queue_symbol_15 != num_codes) {
                  sd[mtfg_queue_symbol_15].type &= 0xF7;
                  add_dictionary_symbol(mtfg_queue_symbol_15,sd[mtfg_queue_symbol_15].code_length);
                }
              }
              else {
                increment_mtfg_queue_16();
                if (sd[mtfg_queue_symbol_31].code_length == 13) {
                  remove_mtfg_queue_symbol_64(mtfg_queue_position);
                  if (mtfg_queue_symbol_31 != num_codes) {
                    sd[mtfg_queue_symbol_31].type &= 0xF7;
                    add_dictionary_symbol(mtfg_queue_symbol_31,sd[mtfg_queue_symbol_31].code_length);
                  }
                }
                else {
                  increment_mtfg_queue_32();
                  if (sd[mtfg_queue_symbol_63].code_length == 14) {
                    remove_mtfg_queue_symbol_64(mtfg_queue_position);
                    if (mtfg_queue_symbol_63 != num_codes) {
                      sd[mtfg_queue_symbol_63].type &= 0xF7;
                      add_dictionary_symbol(mtfg_queue_symbol_63,sd[mtfg_queue_symbol_63].code_length);
                    }
                  }
                  else {
                    subqueue_position = mtfg_queue_position - 64;
                    while (subqueue_position) {
                      *(mtfg_queue_64 + ((mtfg_queue_64_offset + subqueue_position) & 0x3F))
                          = *(mtfg_queue_64 + ((mtfg_queue_64_offset + subqueue_position - 1) & 0x3F));
                      subqueue_position--;
                    }
                    *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63;
                  }
                }
              }
              break;
            }
          } while (++mtfg_queue_position != 128);
          if (mtfg_queue_position == 128) {
            do {
              if (symbol_number == *(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F))) {
                if (in_definition == 0)
                  EncodeMtfgType(LEVEL0);
                else
                  EncodeMtfgType(LEVEL1);
                EncodeMtfgQueuePos(NOT_CAP, mtfg_queue_position);
                if (sd[mtfg_queue_symbol_15].code_length <= 12) {
                  remove_mtfg_queue_symbol_128(mtfg_queue_position);
                  if (mtfg_queue_symbol_15 != num_codes) {
                    sd[mtfg_queue_symbol_15].type &= 0xF7;
                    add_dictionary_symbol(mtfg_queue_symbol_15,sd[mtfg_queue_symbol_15].code_length);
                  }
                }
                else {
                  increment_mtfg_queue_16();
                  if (sd[mtfg_queue_symbol_31].code_length == 13) {
                    remove_mtfg_queue_symbol_128(mtfg_queue_position);
                    if (mtfg_queue_symbol_31 != num_codes) {
                      sd[mtfg_queue_symbol_31].type &= 0xF7;
                      add_dictionary_symbol(mtfg_queue_symbol_31,sd[mtfg_queue_symbol_31].code_length);
                    }
                  }
                  else {
                    increment_mtfg_queue_32();
                    if (sd[mtfg_queue_symbol_63].code_length == 14) {
                      remove_mtfg_queue_symbol_128(mtfg_queue_position);
                      if (mtfg_queue_symbol_63 != num_codes) {
                        sd[mtfg_queue_symbol_63].type &= 0xF7;
                        add_dictionary_symbol(mtfg_queue_symbol_63,sd[mtfg_queue_symbol_63].code_length);
                      }
                    }
                    else {
                      increment_mtfg_queue_64();
                      if (sd[mtfg_queue_symbol_127].code_length == 15) {
                        remove_mtfg_queue_symbol_128(mtfg_queue_position);
                        if (mtfg_queue_symbol_127 != num_codes) {
                          sd[mtfg_queue_symbol_127].type &= 0xF7;
                          add_dictionary_symbol(mtfg_queue_symbol_127,sd[mtfg_queue_symbol_127].code_length);
                        }
                      }
                      else {
                        subqueue_position = mtfg_queue_position - 128;
                        while (subqueue_position) {
                          *(mtfg_queue_128 + ((mtfg_queue_128_offset + subqueue_position) & 0x3F))
                              = *(mtfg_queue_128 + ((mtfg_queue_128_offset + subqueue_position - 1) & 0x3F));
                          subqueue_position--;
                        }
                        *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127;
                      }
                    }
                  }
                }
                break;
              }
            } while (++mtfg_queue_position != 192);
            if (mtfg_queue_position == 192) {
              while (symbol_number != *(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F))) {
                if (sd[*(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F))].type & 2)
                  cap_queue_position++;
                mtfg_queue_position++;
              }
              if (in_definition == 0)
                EncodeMtfgType(LEVEL0);
              else
                EncodeMtfgType(LEVEL1);
              EncodeMtfgQueuePos(NOT_CAP, mtfg_queue_position);
              if (sd[mtfg_queue_symbol_15].code_length <= 12) {
                remove_mtfg_queue_symbol_192(mtfg_queue_position);
                if (mtfg_queue_symbol_15 != num_codes) {
                  sd[mtfg_queue_symbol_15].type &= 0xF7;
                  add_dictionary_symbol(mtfg_queue_symbol_15,sd[mtfg_queue_symbol_15].code_length);
                }
              }
              else {
                increment_mtfg_queue_16();
                if (sd[mtfg_queue_symbol_31].code_length == 13) {
                  remove_mtfg_queue_symbol_192(mtfg_queue_position);
                  if (mtfg_queue_symbol_31 != num_codes) {
                    sd[mtfg_queue_symbol_31].type &= 0xF7;
                    add_dictionary_symbol(mtfg_queue_symbol_31,sd[mtfg_queue_symbol_31].code_length);
                  }
                }
                else {
                  increment_mtfg_queue_32();
                  if (sd[mtfg_queue_symbol_63].code_length == 14) {
                    remove_mtfg_queue_symbol_192(mtfg_queue_position);
                    if (mtfg_queue_symbol_63 != num_codes) {
                      sd[mtfg_queue_symbol_63].type &= 0xF7;
                      add_dictionary_symbol(mtfg_queue_symbol_63,sd[mtfg_queue_symbol_63].code_length);
                    }
                  }
                  else {
                    increment_mtfg_queue_64();
                    if (sd[mtfg_queue_symbol_127].code_length == 15) {
                      remove_mtfg_queue_symbol_192(mtfg_queue_position);
                      if (mtfg_queue_symbol_127 != num_codes) {
                        sd[mtfg_queue_symbol_127].type &= 0xF7;
                        add_dictionary_symbol(mtfg_queue_symbol_127,sd[mtfg_queue_symbol_127].code_length);
                      }
                    }
                    else {
                      increment_mtfg_queue_128();
                      if (sd[mtfg_queue_symbol_191].code_length == 16) {
                        remove_mtfg_queue_symbol_192(mtfg_queue_position);
                        if (mtfg_queue_symbol_191 != num_codes) {
                          sd[mtfg_queue_symbol_191].type &= 0xF7;
                          add_dictionary_symbol(mtfg_queue_symbol_191,sd[mtfg_queue_symbol_191].code_length);
                        }
                      }
                      else {
                        subqueue_position = mtfg_queue_position - 192;
                        while (subqueue_position) {
                          *(mtfg_queue_192 + ((mtfg_queue_192_offset + subqueue_position) & 0x3F))
                              = *(mtfg_queue_192 + ((mtfg_queue_192_offset + subqueue_position - 1) & 0x3F));
                          subqueue_position--;
                        }
                        *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  return;
}


void manage_mtfg_queue_prior_cap(uint32_t symbol_number, uint8_t in_definition) {
  uint8_t mtfg_queue_position = 0;
  uint8_t cap_queue_position = 0;
  uint8_t subqueue_position;
  do {
    if (symbol_number == mtfg_queue_0[mtfg_queue_position]) {
      if (in_definition == 0)
        EncodeMtfgType(LEVEL0_CAP);
      else
        EncodeMtfgType(LEVEL1_CAP);
      uint8_t saved_qp = mtfg_queue_position;
      mtfg_queue_position = cap_queue_position;
      EncodeMtfgQueuePos(CAP, mtfg_queue_position);
      mtfg_queue_position = saved_qp;
      while (mtfg_queue_position) {
        mtfg_queue_0[mtfg_queue_position] = mtfg_queue_0[mtfg_queue_position-1];
        mtfg_queue_position--;
      }
      mtfg_queue_0[0] = symbol_number;
      break;
    }
    else if (sd[mtfg_queue_0[mtfg_queue_position]].type & 2)
      cap_queue_position++;
  } while (++mtfg_queue_position != 8);
  if (mtfg_queue_position == 8) {
    increment_mtfg_queue_0(symbol_number);
    do {
      if (symbol_number == *(mtfg_queue_8 + ((mtfg_queue_position + mtfg_queue_8_offset) & 7))) {
        if (in_definition == 0)
          EncodeMtfgType(LEVEL0_CAP);
        else
          EncodeMtfgType(LEVEL1_CAP);
        uint8_t saved_qp = mtfg_queue_position;
        mtfg_queue_position = cap_queue_position;
        EncodeMtfgQueuePos(CAP, mtfg_queue_position);
        mtfg_queue_position = saved_qp;
        subqueue_position = mtfg_queue_position - 8;
        while (subqueue_position) {
          *(mtfg_queue_8 + ((mtfg_queue_8_offset + subqueue_position) & 7))
              = *(mtfg_queue_8 + ((mtfg_queue_8_offset + subqueue_position - 1) & 7));
          subqueue_position--;
        }
        *(mtfg_queue_8 + mtfg_queue_8_offset) = mtfg_queue_symbol_7;
        break;
      }
      else if (sd[*(mtfg_queue_8 + ((mtfg_queue_position + mtfg_queue_8_offset) & 7))].type & 2)
        cap_queue_position++;
    } while (++mtfg_queue_position != 16);
    if (mtfg_queue_position == 16) {
      increment_mtfg_queue_8();
      do {
        if (symbol_number == *(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF))) {
          if (in_definition == 0)
            EncodeMtfgType(LEVEL0_CAP);
          else
            EncodeMtfgType(LEVEL1_CAP);
          uint8_t saved_qp = mtfg_queue_position;
          mtfg_queue_position = cap_queue_position;
          EncodeMtfgQueuePos(CAP, mtfg_queue_position);
          mtfg_queue_position = saved_qp;
          if (sd[mtfg_queue_symbol_15].code_length <= 12) {
            remove_mtfg_queue_symbol_16(mtfg_queue_position);
            if (mtfg_queue_symbol_15 != num_codes) {
              sd[mtfg_queue_symbol_15].type &= 0xF7;
              add_dictionary_symbol(mtfg_queue_symbol_15,sd[mtfg_queue_symbol_15].code_length);
            }
          }
          else {
            subqueue_position = mtfg_queue_position - 16;
            while (subqueue_position) {
              *(mtfg_queue_16 + ((mtfg_queue_16_offset + subqueue_position) & 0xF))
                  = *(mtfg_queue_16 + ((mtfg_queue_16_offset + subqueue_position - 1) & 0xF));
              subqueue_position--;
            }
            *(mtfg_queue_16 + mtfg_queue_16_offset) = mtfg_queue_symbol_15;
          }
          break;
        }
        else if (sd[*(mtfg_queue_16 + ((mtfg_queue_position + mtfg_queue_16_offset) & 0xF))].type & 2)
          cap_queue_position++;
      } while (++mtfg_queue_position != 32);
      if (mtfg_queue_position == 32) {
        do {
          if (symbol_number == *(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F))) {
            if (in_definition == 0)
              EncodeMtfgType(LEVEL0_CAP);
            else
              EncodeMtfgType(LEVEL1_CAP);
            uint8_t saved_qp = mtfg_queue_position;
            mtfg_queue_position = cap_queue_position;
            EncodeMtfgQueuePos(CAP, mtfg_queue_position);
            mtfg_queue_position = saved_qp;
            if (sd[mtfg_queue_symbol_15].code_length <= 12) {
              remove_mtfg_queue_symbol_32(mtfg_queue_position);
              if (mtfg_queue_symbol_15 != num_codes) {
                sd[mtfg_queue_symbol_15].type &= 0xF7;
                add_dictionary_symbol(mtfg_queue_symbol_15,sd[mtfg_queue_symbol_15].code_length);
              }
            }
            else {
              increment_mtfg_queue_16();
              if (sd[mtfg_queue_symbol_31].code_length == 13) {
                remove_mtfg_queue_symbol_32(mtfg_queue_position);
                if (mtfg_queue_symbol_31 != num_codes) {
                  sd[mtfg_queue_symbol_31].type &= 0xF7;
                  add_dictionary_symbol(mtfg_queue_symbol_31,sd[mtfg_queue_symbol_31].code_length);
                }
              }
              else {
                subqueue_position = mtfg_queue_position - 32;
                while (subqueue_position) {
                  *(mtfg_queue_32 + ((mtfg_queue_32_offset + subqueue_position) & 0x1F))
                      = *(mtfg_queue_32 + ((mtfg_queue_32_offset + subqueue_position - 1) & 0x1F));
                  subqueue_position--;
                }
                *(mtfg_queue_32 + mtfg_queue_32_offset) = mtfg_queue_symbol_31;
              }
            }
            break;
          }
          else if (sd[*(mtfg_queue_32 + ((mtfg_queue_position + mtfg_queue_32_offset) & 0x1F))].type & 2)
            cap_queue_position++;
        } while (++mtfg_queue_position != 64);
        if (mtfg_queue_position == 64) {
          do {
            if (symbol_number == *(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F))) {
              if (in_definition == 0)
                EncodeMtfgType(LEVEL0_CAP);
              else
                EncodeMtfgType(LEVEL1_CAP);
              uint8_t saved_qp = mtfg_queue_position;
              mtfg_queue_position = cap_queue_position;
              EncodeMtfgQueuePos(CAP, mtfg_queue_position);
              mtfg_queue_position = saved_qp;
              if (sd[mtfg_queue_symbol_15].code_length <= 12) {
                remove_mtfg_queue_symbol_64(mtfg_queue_position);
                if (mtfg_queue_symbol_15 != num_codes) {
                  sd[mtfg_queue_symbol_15].type &= 0xF7;
                  add_dictionary_symbol(mtfg_queue_symbol_15,sd[mtfg_queue_symbol_15].code_length);
                }
              }
              else {
                increment_mtfg_queue_16();
                if (sd[mtfg_queue_symbol_31].code_length == 13) {
                  remove_mtfg_queue_symbol_64(mtfg_queue_position);
                  if (mtfg_queue_symbol_31 != num_codes) {
                    sd[mtfg_queue_symbol_31].type &= 0xF7;
                    add_dictionary_symbol(mtfg_queue_symbol_31,sd[mtfg_queue_symbol_31].code_length);
                  }
                }
                else {
                  increment_mtfg_queue_32();
                  if (sd[mtfg_queue_symbol_63].code_length == 14) {
                    remove_mtfg_queue_symbol_64(mtfg_queue_position);
                    if (mtfg_queue_symbol_63 != num_codes) {
                      sd[mtfg_queue_symbol_63].type &= 0xF7;
                      add_dictionary_symbol(mtfg_queue_symbol_63,sd[mtfg_queue_symbol_63].code_length);
                    }
                  }
                  else {
                    subqueue_position = mtfg_queue_position - 64;
                    while (subqueue_position) {
                      *(mtfg_queue_64 + ((mtfg_queue_64_offset + subqueue_position) & 0x3F))
                          = *(mtfg_queue_64 + ((mtfg_queue_64_offset + subqueue_position - 1) & 0x3F));
                      subqueue_position--;
                    }
                    *(mtfg_queue_64 + mtfg_queue_64_offset) = mtfg_queue_symbol_63;
                  }
                }
              }
              break;
            }
            else if (sd[*(mtfg_queue_64 + ((mtfg_queue_position + mtfg_queue_64_offset) & 0x3F))].type & 2)
              cap_queue_position++;
          } while (++mtfg_queue_position != 128);
          if (mtfg_queue_position == 128) {
            do {
              if (symbol_number == *(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F))) {
                if (in_definition == 0)
                  EncodeMtfgType(LEVEL0_CAP);
                else
                  EncodeMtfgType(LEVEL1_CAP);
                uint8_t saved_qp = mtfg_queue_position;
                mtfg_queue_position = cap_queue_position;
                EncodeMtfgQueuePos(CAP, mtfg_queue_position);
                mtfg_queue_position = saved_qp;
                if (sd[mtfg_queue_symbol_15].code_length <= 12) {
                  remove_mtfg_queue_symbol_128(mtfg_queue_position);
                  if (mtfg_queue_symbol_15 != num_codes) {
                    sd[mtfg_queue_symbol_15].type &= 0xF7;
                    add_dictionary_symbol(mtfg_queue_symbol_15,sd[mtfg_queue_symbol_15].code_length);
                  }
                }
                else {
                  increment_mtfg_queue_16();
                  if (sd[mtfg_queue_symbol_31].code_length == 13) {
                    remove_mtfg_queue_symbol_128(mtfg_queue_position);
                    if (mtfg_queue_symbol_31 != num_codes) {
                      sd[mtfg_queue_symbol_31].type &= 0xF7;
                      add_dictionary_symbol(mtfg_queue_symbol_31,sd[mtfg_queue_symbol_31].code_length);
                    }
                  }
                  else {
                    increment_mtfg_queue_32();
                    if (sd[mtfg_queue_symbol_63].code_length == 14) {
                      remove_mtfg_queue_symbol_128(mtfg_queue_position);
                      if (mtfg_queue_symbol_63 != num_codes) {
                        sd[mtfg_queue_symbol_63].type &= 0xF7;
                        add_dictionary_symbol(mtfg_queue_symbol_63,sd[mtfg_queue_symbol_63].code_length);
                      }
                    }
                    else {
                      increment_mtfg_queue_64();
                      if (sd[mtfg_queue_symbol_127].code_length == 15) {
                        remove_mtfg_queue_symbol_128(mtfg_queue_position);
                        if (mtfg_queue_symbol_127 != num_codes) {
                          sd[mtfg_queue_symbol_127].type &= 0xF7;
                          add_dictionary_symbol(mtfg_queue_symbol_127,sd[mtfg_queue_symbol_127].code_length);
                        }
                      }
                      else {
                        subqueue_position = mtfg_queue_position - 128;
                        while (subqueue_position) {
                          *(mtfg_queue_128 + ((mtfg_queue_128_offset + subqueue_position) & 0x3F))
                              = *(mtfg_queue_128 + ((mtfg_queue_128_offset + subqueue_position - 1) & 0x3F));
                          subqueue_position--;
                        }
                        *(mtfg_queue_128 + mtfg_queue_128_offset) = mtfg_queue_symbol_127;
                      }
                    }
                  }
                }
                break;
              }
              else if (sd[*(mtfg_queue_128 + ((mtfg_queue_position + mtfg_queue_128_offset) & 0x3F))].type & 2)
                cap_queue_position++;
            } while (++mtfg_queue_position != 192);
            if (mtfg_queue_position == 192) {
              while (symbol_number != *(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F))) {
                if (sd[*(mtfg_queue_192 + ((mtfg_queue_position + mtfg_queue_192_offset) & 0x3F))].type & 2)
                  cap_queue_position++;
                mtfg_queue_position++;
              }
              if (in_definition == 0)
                EncodeMtfgType(LEVEL0_CAP);
              else
                EncodeMtfgType(LEVEL1_CAP);
              uint8_t saved_qp = mtfg_queue_position;
              mtfg_queue_position = cap_queue_position;
              EncodeMtfgQueuePos(CAP, mtfg_queue_position);
              mtfg_queue_position = saved_qp;
              if (sd[mtfg_queue_symbol_15].code_length <= 12) {
                remove_mtfg_queue_symbol_192(mtfg_queue_position);
                if (mtfg_queue_symbol_15 != num_codes) {
                  sd[mtfg_queue_symbol_15].type &= 0xF7;
                  add_dictionary_symbol(mtfg_queue_symbol_15,sd[mtfg_queue_symbol_15].code_length);
                }
              }
              else {
                increment_mtfg_queue_16();
                if (sd[mtfg_queue_symbol_31].code_length == 13) {
                  remove_mtfg_queue_symbol_192(mtfg_queue_position);
                  if (mtfg_queue_symbol_31 != num_codes) {
                    sd[mtfg_queue_symbol_31].type &= 0xF7;
                    add_dictionary_symbol(mtfg_queue_symbol_31,sd[mtfg_queue_symbol_31].code_length);
                  }
                }
                else {
                  increment_mtfg_queue_32();
                  if (sd[mtfg_queue_symbol_63].code_length == 14) {
                    remove_mtfg_queue_symbol_192(mtfg_queue_position);
                    if (mtfg_queue_symbol_63 != num_codes) {
                      sd[mtfg_queue_symbol_63].type &= 0xF7;
                      add_dictionary_symbol(mtfg_queue_symbol_63,sd[mtfg_queue_symbol_63].code_length);
                    }
                  }
                  else {
                    increment_mtfg_queue_64();
                    if (sd[mtfg_queue_symbol_127].code_length == 15) {
                      remove_mtfg_queue_symbol_192(mtfg_queue_position);
                      if (mtfg_queue_symbol_127 != num_codes) {
                        sd[mtfg_queue_symbol_127].type &= 0xF7;
                        add_dictionary_symbol(mtfg_queue_symbol_127,sd[mtfg_queue_symbol_127].code_length);
                      }
                    }
                    else {
                      increment_mtfg_queue_128();
                      if (sd[mtfg_queue_symbol_191].code_length == 16) {
                        remove_mtfg_queue_symbol_192(mtfg_queue_position);
                        if (mtfg_queue_symbol_191 != num_codes) {
                          sd[mtfg_queue_symbol_191].type &= 0xF7;
                          add_dictionary_symbol(mtfg_queue_symbol_191,sd[mtfg_queue_symbol_191].code_length);
                        }
                      }
                      else {
                        subqueue_position = mtfg_queue_position - 192;
                        while (subqueue_position) {
                          *(mtfg_queue_192 + ((mtfg_queue_192_offset + subqueue_position) & 0x3F))
                              = *(mtfg_queue_192 + ((mtfg_queue_192_offset + subqueue_position - 1) & 0x3F));
                          subqueue_position--;
                        }
                        *(mtfg_queue_192 + mtfg_queue_192_offset) = mtfg_queue_symbol_191;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  return;
}


void encode_dictionary_symbol(uint32_t symbol) {
  uint32_t bin_code;
  uint16_t bin_num;
  uint8_t bin_shift;

  uint8_t first_char = sd[symbol].starts;
  uint32_t symbol_index = sd[symbol].array_index;
  if (cap_encoded != 0) {
    if (prior_end != 0xA) {
      if (sd[prior_symbol].type & 0x20) {
        if (sd[prior_symbol].type & 0x80)
          EncodeFirstChar(first_char, 2, prior_end);
        else if (sd[prior_symbol].type & 0x40)
          EncodeFirstChar(first_char, 3, prior_end);
        else
          EncodeFirstChar(first_char, 1, prior_end);
      }
      else
        EncodeFirstChar(first_char, 0, prior_end);
    }
  }
  else if (UTF8_compliant != 0)
    EncodeFirstChar(first_char, 0, prior_end);
  else 
    EncodeFirstCharBinary(first_char, prior_end);

  uint8_t code_length = sd[symbol].code_length;
  if (code_length > bin_code_length[first_char]) {
    uint32_t max_codes_in_bins, mcib;
    uint8_t reduce_bits = 0;
    bin_shift = code_length - bin_code_length[first_char];
    max_codes_in_bins = (uint32_t)nbob[first_char][code_length] << bin_shift;
    mcib = max_codes_in_bins >> 1;
    while (mcib >= nsob[first_char][code_length]) {
      reduce_bits++;
      mcib = mcib >> 1;
    }
    if (code_length - reduce_bits > bin_code_length[first_char]) {
      bin_num = fbob[first_char][code_length];
      uint32_t min_extra_reduce_index = 2 * nsob[first_char][code_length] - (max_codes_in_bins >> reduce_bits);
      if (symbol_index >= min_extra_reduce_index) {
        uint16_t symbol_bins = 2;
        bin_code = 2 * symbol_index - min_extra_reduce_index;
        uint16_t code_bin = (uint16_t)(bin_code >> (bin_shift - reduce_bits));
        bin_num += code_bin;
        bin_code -= (uint32_t)code_bin << (bin_shift - reduce_bits);
        code_length -= reduce_bits + bin_code_length[first_char];
        EncodeLongDictionarySymbol(bin_code, bin_num, sum_nbob[first_char], code_length, symbol_bins);
      }
      else {
        bin_code = symbol_index;
        uint16_t symbol_bins = 1;
        code_length -= reduce_bits + bin_code_length[first_char];
        uint16_t code_bin = (uint16_t)(symbol_index >> code_length);
        bin_num += code_bin;
        bin_code -= (uint32_t)code_bin << code_length;
        EncodeLongDictionarySymbol(bin_code, bin_num, sum_nbob[first_char], code_length, symbol_bins);
      }
      return;
    }
  }
  uint16_t bins_per_symbol = nbob[first_char][code_length] / nsob[first_char][code_length];
  uint16_t extra_bins = nbob[first_char][code_length] - nsob[first_char][code_length] * bins_per_symbol;
  bin_num = fbob[first_char][code_length] + symbol_index * bins_per_symbol;
  if (symbol_index >= extra_bins)
    bin_num += extra_bins;
  else {
    bin_num += symbol_index;
    bins_per_symbol++;
  }
  EncodeShortDictionarySymbol(bin_num, sum_nbob[first_char], bins_per_symbol);
  return;
}


void update_mtf_queue(uint32_t symbol, uint32_t symbol_inst, uint32_t symbol_count) {
  uint8_t i;
  if (symbol_inst != symbol_count - 1) { // not the last instance
    if ((sd[symbol].type & 8) != 0) { // symbol in queue
      i = mtf_queue_size[symbol_count] - 1;
      while (mtf_queue[symbol_count][i] != symbol)
        i--;
      mtf_queue_hits[symbol_count]++;
      while (i < mtf_queue_size[symbol_count] - 1) {
        mtf_queue[symbol_count][i] = mtf_queue[symbol_count][i+1];
        i++;
      }
      mtf_queue[symbol_count][i] = symbol;
    }
    else { // symbol not in mtf queue, move it back into the queue
      sd[symbol].type |= 8;
      if (mtf_queue_size[symbol_count] < MTF_QUEUE_SIZE)
        mtf_queue[symbol_count][mtf_queue_size[symbol_count]++] = symbol;
      else { // move the queue elements down
        sd[mtf_queue[symbol_count][0]].type &= 0xF7;
        i = 0;
        while (i < mtf_queue_size[symbol_count] - 1) {
          mtf_queue[symbol_count][i] = mtf_queue[symbol_count][i+1];
          i++;
        }
        mtf_queue[symbol_count][i] = symbol;
      }
    }
  }
  else { // last instance
    mtf_queue_done[symbol_count]++;
    if ((sd[symbol].type & 8) != 0) {
      i = --mtf_queue_size[symbol_count];
      while (mtf_queue[symbol_count][i] != symbol)
        i--;
      mtf_queue_hits[symbol_count]++;
      while (i < mtf_queue_size[symbol_count]) {
        mtf_queue[symbol_count][i] = mtf_queue[symbol_count][i+1];
        i++;
      }
    }
  }
  return;
}


uint8_t manage_mtf_queue(uint32_t symbol, uint32_t symbol_inst, uint32_t symbol_count, uint8_t in_definition) {
  uint8_t i, mtf_queue_position;
  uint8_t mtf_queue_number = (uint8_t)symbol_count - 2;

  if ((sd[symbol].type & 8) != 0) { // symbol already in queue
    i = mtf_queue_size[symbol_count];
    while (mtf_queue[symbol_count][--i] != symbol); // do nothing
    mtf_queue_position = mtf_queue_size[symbol_count] - i - 1;
    if (symbol_inst != symbol_count - 1) { // not the last instance
      if (prior_is_cap == 0) {
        if (in_definition == 0)
          EncodeMtfType(LEVEL0);
        else
          EncodeMtfType(LEVEL1);
        EncodeMtfQueueNum(NOT_CAP, mtf_queue_number);
        EncodeMtfQueuePos(NOT_CAP, mtf_queue_number, mtf_queue_size, mtf_queue_position);
      }
      else {
        if (in_definition == 0)
          EncodeMtfType(LEVEL0_CAP);
        else
          EncodeMtfType(LEVEL1_CAP);
        EncodeMtfQueueNum(CAP, mtf_queue_number);
        if (mtf_queue_position != 0) {
          uint32_t * end_mtf_queue_ptr = &mtf_queue[symbol_count][mtf_queue_size[symbol_count] - 1];
          uint32_t * mtf_queue_ptr = end_mtf_queue_ptr - mtf_queue_position + 1;
          do {
            if ((sd[*mtf_queue_ptr].type & 2) == 0)
              mtf_queue_position--; // don't count symbols that don't start a-z
          } while (mtf_queue_ptr++ != end_mtf_queue_ptr);
        }
        EncodeMtfQueuePos(CAP, mtf_queue_number, mtf_queue_size, mtf_queue_position);
      }
      while (i < mtf_queue_size[symbol_count] - 1) {
        mtf_queue[symbol_count][i] = mtf_queue[symbol_count][i+1];
        i++;
      }
      mtf_queue[symbol_count][i] = symbol;
    }
    else {
      if (prior_is_cap == 0) {
        if (in_definition == 0)
          EncodeMtfType(LEVEL0);
        else
          EncodeMtfType(LEVEL1);
        EncodeMtfQueueNumLastSymbol(NOT_CAP, mtf_queue_number);
        EncodeMtfQueuePos(NOT_CAP, mtf_queue_number, mtf_queue_size, mtf_queue_position);
      }
      else {
        if (in_definition == 0)
          EncodeMtfType(LEVEL0_CAP);
        else
          EncodeMtfType(LEVEL1_CAP);
        EncodeMtfQueueNumLastSymbol(CAP, mtf_queue_number);
        if (mtf_queue_position != 0) {
          uint32_t * end_mtf_queue_ptr = &mtf_queue[symbol_count][mtf_queue_size[symbol_count] - 1];
          uint32_t * mtf_queue_ptr = end_mtf_queue_ptr - mtf_queue_position + 1;
          do {
            if ((sd[*mtf_queue_ptr].type & 2) == 0)
              mtf_queue_position--;
          } while (mtf_queue_ptr++ != end_mtf_queue_ptr);
        }
        EncodeMtfQueuePos(CAP, mtf_queue_number, mtf_queue_size, mtf_queue_position);
      }
      mtf_queue_size[symbol_count]--;
      uint32_t * end_mtf_queue_ptr = &mtf_queue[symbol_count][mtf_queue_size[symbol_count]];
      uint32_t * mtf_queue_ptr = &mtf_queue[symbol_count][i];
      while (mtf_queue_ptr != end_mtf_queue_ptr) {
        *mtf_queue_ptr = *(mtf_queue_ptr+1);
        mtf_queue_ptr++;
      }
    }
  }
  else { // symbol not in mtf queue
    if (symbol_inst != symbol_count - 1) { // not the last instance
      sd[symbol].type |= 8;
      UpFreqMtfQueueNum(prior_is_cap, mtf_queue_number);
      if (prior_is_cap == 0) {
        if (in_definition == 0)
          EncodeDictType(LEVEL0);
        else
          EncodeDictType(LEVEL1);
      }
      else {
        if (in_definition == 0)
          EncodeDictType(LEVEL0_CAP);
        else
          EncodeDictType(LEVEL1_CAP);
      }
      encode_dictionary_symbol(symbol);
      // move the symbol back into the mtf queue
      remove_dictionary_symbol(symbol, mtf_queue_miss_code_length[symbol_count]);
      if (mtf_queue_size[symbol_count] < MTF_QUEUE_SIZE)
        mtf_queue[symbol_count][mtf_queue_size[symbol_count]++] = symbol;
      else {
        sd[mtf_queue[symbol_count][0]].type &= 0xF7;
        uint32_t symbol_to_move = mtf_queue[symbol_count][0];
        if (add_dictionary_symbol(symbol_to_move, mtf_queue_miss_code_length[symbol_count]) == 0)
          return(0);
        // move the queue elements down
        i = 0;
        while (i < MTF_QUEUE_SIZE - 1) {
          mtf_queue[symbol_count][i] = mtf_queue[symbol_count][i+1];
          i++;
        }
        mtf_queue[symbol_count][i] = symbol;
      }
    }
    else { // last instance
      if (prior_is_cap == 0) {
        if (in_definition == 0)
          EncodeDictType(LEVEL0);
        else
          EncodeDictType(LEVEL1);
      }
      else {
        if (in_definition == 0)
          EncodeDictType(LEVEL0_CAP);
        else
          EncodeDictType(LEVEL1_CAP);
      }
      encode_dictionary_symbol(symbol);
      remove_dictionary_symbol(symbol, mtf_queue_miss_code_length[symbol_count]);
    }
  }
  prior_is_cap = sd[symbol].type & 1;
  return(1);
}


void manage_mtf_symbol(uint32_t symbol, uint32_t symbol_inst, uint32_t symbol_count, uint8_t in_definition) {
  if (prior_is_cap == 0) {
    if (in_definition == 0)
      EncodeDictType(LEVEL0);
    else
      EncodeDictType(LEVEL1);
  }
  else {
    if (in_definition == 0)
      EncodeDictType(LEVEL0_CAP);
    else
      EncodeDictType(LEVEL1_CAP);
  }
  encode_dictionary_symbol(symbol);
  if (symbol_inst == symbol_count - 1)  // last instance
    remove_dictionary_symbol(symbol, mtf_queue_miss_code_length[symbol_count]);
  prior_is_cap = sd[symbol].type & 1;
  return;
}


uint32_t count_symbols(uint32_t symbol) {
  uint32_t string_symbols, *symbol_string_ptr, *end_symbol_string_ptr;
  if (symbol < start_my_symbols)
    return(1);
  symbol_string_ptr = symbol_array + sd[symbol].define_symbol_start_index;
  end_symbol_string_ptr = symbol_array + sd[symbol+1].define_symbol_start_index - 1;

  string_symbols = 0;
  while (symbol_string_ptr != end_symbol_string_ptr) {
    if ((sd[*symbol_string_ptr].count == 1) && (*symbol_string_ptr >= start_my_symbols))
      string_symbols += count_symbols(*symbol_string_ptr);
    else
      string_symbols++;
    symbol_string_ptr++;
  }
  return(string_symbols);
}


void count_embedded_definition_symbols(uint32_t define_symbol) {
  uint32_t *define_string_ptr, *define_string_end_ptr;
  uint32_t symbol, symbol_inst, symbol_count;

  if ((sd[define_symbol].count == 1) && (define_symbol >= start_my_symbols)) {
    // count the symbols in the string instead of creating a single instance symbol (artifacts of TreeCompress)
    define_string_ptr = symbol_array + sd[define_symbol].define_symbol_start_index;
    define_string_end_ptr = symbol_array + sd[define_symbol+1].define_symbol_start_index - 1;
    do {
      symbol = *define_string_ptr++;
      symbol_inst = sd[symbol].inst_found++;
      if (symbol_inst == 0)
        count_embedded_definition_symbols(symbol);
      else {
        if (sd[prior_symbol].type & 0x20) {
          if (sd[symbol].starts == 0x20)
            sd[prior_symbol].space_score += 1;
          else
            sd[prior_symbol].space_score -= 4;
        }
        if (sd[symbol].count <= MAX_INSTANCES_FOR_MTF_QUEUE)
          update_mtf_queue(symbol, symbol_inst, sd[symbol].count);
        else {
          if (sd[symbol].code_length >= 11) {
            if ((sd[symbol].type & 8) != 0) {
              manage_mtfg_queue1(symbol);
              sd[symbol].mtfg_hits++;
            }
            else
              add_symbol_to_mtfg_queue1(symbol);
          }
        }
        prior_symbol = symbol;
      }
    } while (define_string_ptr != define_string_end_ptr);
    define_string_ptr--;
    sd[define_symbol].type |= sd[symbol].type & 0x30;
    while (((sd[define_symbol].type & 0x10) == 0)
        && (define_string_ptr-- != symbol_array + sd[define_symbol].define_symbol_start_index))
      get_symbol_category(*define_string_ptr, &sd[define_symbol].type);
    return;
  }

  // count the symbols in the definition
  if (define_symbol >= start_my_symbols) {
    define_string_ptr = symbol_array + sd[define_symbol].define_symbol_start_index;
    define_string_end_ptr = symbol_array + sd[define_symbol+1].define_symbol_start_index - 1;
    do {
      symbol = *define_string_ptr++;
      symbol_inst = sd[symbol].inst_found++;
      if (symbol_inst == 0)
        count_embedded_definition_symbols(symbol);
      else {
        if (sd[prior_symbol].type & 0x20) {
          if (sd[symbol].starts == 0x20)
            sd[prior_symbol].space_score += 1;
          else
            sd[prior_symbol].space_score -= 4;
        }
        if (sd[symbol].count <= MAX_INSTANCES_FOR_MTF_QUEUE)
          update_mtf_queue(symbol, symbol_inst, sd[symbol].count);
        else {
          if (sd[symbol].code_length >= 11) {
            if ((sd[symbol].type & 8) != 0) {
              manage_mtfg_queue1(symbol);
              sd[symbol].mtfg_hits++;
            }
            else
              add_symbol_to_mtfg_queue1(symbol);
          }
        }
        prior_symbol = symbol;
      }
    } while (define_string_ptr != define_string_end_ptr);
    define_string_ptr--;
    sd[define_symbol].type |= sd[symbol].type & 0x30;
    while (((sd[define_symbol].type & 0x10) == 0)
        && (define_string_ptr-- != symbol_array + sd[define_symbol].define_symbol_start_index))
      get_symbol_category(*define_string_ptr, &sd[define_symbol].type);
  }
  else if ((define_symbol == (uint32_t)' ') || (define_symbol == (uint32_t)'C') || (define_symbol == (uint32_t)'B'))
    sd[define_symbol].type |= 0x10;
  prior_symbol = define_symbol;

  symbol_count = sd[define_symbol].count;
  if (symbol_count != 1) { // assign symbol code
    if (symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE) { // Handle initial mtf instance
      sd[define_symbol].type |= 8;
      mtf_queue_started[symbol_count]++;
      if (mtf_queue_started[symbol_count] - mtf_queue_done[symbol_count] > mtf_queue_peak[symbol_count])
        mtf_queue_peak[symbol_count]++;
      if (mtf_queue_size[symbol_count] < MTF_QUEUE_SIZE)
        mtf_queue[symbol_count][mtf_queue_size[symbol_count]++] = define_symbol;
      else {
        sd[mtf_queue[symbol_count][0]].type &= 0xF7;
        uint8_t i;
        for (i = 0 ; i < 63 ; i++)
          mtf_queue[symbol_count][i] = mtf_queue[symbol_count][i+1];
        mtf_queue[symbol_count][63] = define_symbol;
      }
    }
    else {
      sd[define_symbol].mtfg_hits = 0;
      sd[define_symbol].hit_score = 0;
      if (sd[define_symbol].code_length >= 11)
        add_symbol_to_mtfg_queue1(define_symbol);
    }
  }
  return;
}


uint8_t embed_define_binary(uint32_t define_symbol, uint8_t in_definition) {
  uint32_t *define_string_ptr, *define_symbol_start_ptr, *define_string_end_ptr;
  uint32_t define_symbol_instances, symbols_in_definition, symbol, symbol_inst, symbol_count;
  uint8_t new_symbol_code_length, SID_symbol;

  if ((sd[define_symbol].count == 1) && (define_symbol >= start_my_symbols)) {
    // write the symbol string instead of creating a single instance symbol (artifacts of TreeCompress)
    define_string_ptr = symbol_array + sd[define_symbol].define_symbol_start_index;
    define_string_end_ptr = symbol_array + sd[define_symbol+1].define_symbol_start_index - 1;
    while (define_string_ptr != define_string_end_ptr) {
      symbol = *define_string_ptr++;
      symbol_inst = sd[symbol].inst_found++;
      define_symbol_instances = sd[symbol].count;
      if (symbol_inst == 0) {
        if (embed_define_binary(symbol, in_definition) == 0)
          return(0);
      }
      else if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf != 0) {
          if (manage_mtf_queue(symbol, symbol_inst, define_symbol_instances, in_definition) == 0)
            return(0);
        }
        else
          manage_mtf_symbol(symbol, symbol_inst, define_symbol_instances, in_definition);
      }
      else {
        if ((sd[symbol].type & 8) != 0) {
          if (prior_is_cap == 0)
            manage_mtfg_queue(symbol, in_definition);
          else
            manage_mtfg_queue_prior_cap(symbol, in_definition);
        }
        else {
          if (in_definition == 0)
            EncodeDictType(LEVEL0);
          else
            EncodeDictType(LEVEL1);
          encode_dictionary_symbol(symbol);
          if (sd[symbol].type & 4) {
            remove_dictionary_symbol(symbol, sd[symbol].code_length);
            add_symbol_to_mtfg_queue(symbol);
          }
        }
      }
      prior_end = sd[symbol].ends;
    }
    return(1);
  }

  // write the define code
  if (in_definition == 0)
    EncodeNewType(LEVEL0);
  else
    EncodeNewType(LEVEL1);

  define_symbol_instances = sd[define_symbol].count;
  if (define_symbol_instances != 1)
    new_symbol_code_length = sd[define_symbol].code_length;
  else
    new_symbol_code_length = 0x20;

  // send symbol length, instances and ergodicity bit
  if (define_symbol < start_my_symbols) {
    symbol_lengths[define_symbol] = new_symbol_code_length;
    SID_symbol = 0;
    EncodeSID(NOT_CAP, SID_symbol);
    if (define_symbol_instances == 1)
      EncodeINST(NOT_CAP, SID_symbol, MAX_INSTANCES_FOR_MTF_QUEUE - 1);
    else if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE)
      EncodeINST(NOT_CAP, SID_symbol, define_symbol_instances - 2);
    else
      EncodeINST(NOT_CAP, SID_symbol, MAX_INSTANCES_FOR_MTF_QUEUE + max_regular_code_length - new_symbol_code_length);
    EncodeBaseSymbol(define_symbol, 0x100, 0x100);
    if ((define_symbol & 1) != 0) {
      if (symbol_lengths[define_symbol - 1] != 0) {
        DoubleRangeDown();
      }
    }
    else if (symbol_lengths[define_symbol + 1] != 0)
      DoubleRange();

    prior_end = (uint8_t)define_symbol;
    uint8_t j1 = 0xFF;
    do {
      InitFirstCharBinBinary(j1, prior_end, new_symbol_code_length);
    } while (j1-- != 0);
    InitTrailingCharBinary(prior_end, symbol_lengths);

    if (found_first_symbol == 0) {
      found_first_symbol = 1;
      end_char = prior_end;
      sym_list_ptrs[end_char][max_code_length][0] = num_codes;
      nsob[end_char][max_code_length] = 1;
      nbob[end_char][max_code_length] = 1;
      sum_nbob[end_char] = 1;
    }
  }
  else {
    num_grammar_rules++;
    define_symbol_start_ptr = symbol_array + sd[define_symbol].define_symbol_start_index;
    define_string_ptr = define_symbol_start_ptr;
    define_string_end_ptr = symbol_array + sd[define_symbol+1].define_symbol_start_index - 1;

    // count the symbols in the definition
    symbols_in_definition = 0;
    while (define_string_ptr != define_string_end_ptr) {
      if ((sd[*define_string_ptr].count != 1) || (*define_string_ptr < start_my_symbols))
        symbols_in_definition++;
      else
        symbols_in_definition += count_symbols(*define_string_ptr);
      define_string_ptr++;
    }
    if (symbols_in_definition < 16) {
      SID_symbol = symbols_in_definition - 1;
      EncodeSID(NOT_CAP, SID_symbol);
    }
    else {
      SID_symbol = 15;
      EncodeSID(NOT_CAP, SID_symbol);
      int32_t extra_symbols = symbols_in_definition - 16;
      int32_t temp2 = extra_symbols;
      uint8_t data_bits = 1;
      while (temp2 >= (1 << data_bits))
        temp2 -= (1 << data_bits++);
      temp2 = (int32_t)data_bits;
      while (temp2 > 2) {
        temp2 -= 2;
        EncodeExtraLength(3);
      }
      extra_symbols += 2 - (1 << data_bits);
      if (temp2 == 2)
        EncodeExtraLength(2);
      else
        data_bits++;
      while (data_bits) {
        data_bits -= 2;
        EncodeExtraLength((extra_symbols >> data_bits) & 3);
      }
    }

    if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE)
      EncodeINST(NOT_CAP, SID_symbol, define_symbol_instances - 2);
    else
      EncodeINST(NOT_CAP, SID_symbol, MAX_INSTANCES_FOR_MTF_QUEUE + max_regular_code_length - new_symbol_code_length);

    // write the symbol string
    define_string_ptr = define_symbol_start_ptr;
    while (define_string_ptr != define_string_end_ptr) {
      symbol = *define_string_ptr++;
      symbol_inst = sd[symbol].inst_found++;
      symbol_count = sd[symbol].count;
      if (symbol_inst == 0) {
        if (embed_define_binary(symbol, 1) == 0)
          return(0);
      }
      else if (symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf != 0) {
          if (manage_mtf_queue(symbol, symbol_inst, symbol_count, 1) == 0)
            return(0);
        }
        else
          manage_mtf_symbol(symbol, symbol_inst, symbol_count, 1);
      }
      else {
        if ((sd[symbol].type & 8) != 0) {
          if (prior_is_cap == 0)
            manage_mtfg_queue(symbol, 1);
          else
            manage_mtfg_queue_prior_cap(symbol, 1);
        }
        else {
          EncodeDictType(LEVEL1);
          encode_dictionary_symbol(symbol);
          if (sd[symbol].type & 4) {
            remove_dictionary_symbol(symbol, sd[symbol].code_length);
            add_symbol_to_mtfg_queue(symbol);
          }
        }
      }
      prior_end = sd[symbol].ends;
    }
  }

  if (define_symbol_instances != 1) { // assign symbol code
    if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
      if (use_mtf != 0) {
        UpFreqMtfQueueNum(NOT_CAP, define_symbol_instances - 2);
        // Handle initial mtf symbol instance
        sd[define_symbol].type |= 8;
        if (mtf_queue_size[define_symbol_instances] < MTF_QUEUE_SIZE)
          mtf_queue[define_symbol_instances][mtf_queue_size[define_symbol_instances]++] = define_symbol;
        else {
          uint32_t symbol_to_move = mtf_queue[define_symbol_instances][0];
          sd[symbol_to_move].type &= 0xF7;
          if (add_dictionary_symbol(symbol_to_move, new_symbol_code_length) == 0)
            return(0);
          uint8_t i;
          for (i = 0 ; i < 63 ; i++)
            mtf_queue[define_symbol_instances][i] = mtf_queue[define_symbol_instances][i+1];
          mtf_queue[define_symbol_instances][63] = define_symbol;
        }
      }
      else if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
        return(0);
    }
    else if (use_mtfg && (new_symbol_code_length >= 11)) {
      if (sd[define_symbol].type & 4) {
        EncodeERG(0, 1);
        add_symbol_to_mtfg_queue(define_symbol);
      }
      else {
        EncodeERG(0, 0);
        if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
          return(0);
      }
    }
    else if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
      return(0);
  }
  return (1);
}


uint8_t embed_define(uint32_t define_symbol, uint8_t in_definition) {
  uint32_t *define_string_ptr, *define_symbol_start_ptr, *define_string_end_ptr;
  uint32_t define_symbol_instances, symbols_in_definition, symbol, symbol_inst, symbol_count;
  uint8_t new_symbol_code_length, SID_symbol, char_before_define_is_cap;

  if ((sd[define_symbol].count == 1) && (define_symbol >= start_my_symbols)) {
    // write the symbol string instead of creating a single instance symbol (artifacts of TreeCompress)
    define_string_ptr = symbol_array + sd[define_symbol].define_symbol_start_index;
    define_string_end_ptr = symbol_array + sd[define_symbol+1].define_symbol_start_index - 1;
    while (define_string_ptr != define_string_end_ptr) {
      symbol = *define_string_ptr++;
      symbol_inst = sd[symbol].inst_found++;
      define_symbol_instances = sd[symbol].count;
      if (symbol_inst == 0) {
        if (embed_define(symbol, in_definition) == 0)
          return(0);
      }
      else if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf != 0) {
          if (manage_mtf_queue(symbol, symbol_inst, define_symbol_instances, in_definition) == 0)
            return(0);
        }
        else
          manage_mtf_symbol(symbol, symbol_inst, define_symbol_instances, in_definition);
        prior_symbol = symbol;
      }
      else {
        if ((sd[symbol].type & 8) != 0) {
          if (prior_is_cap == 0)
            manage_mtfg_queue(symbol, in_definition);
          else
            manage_mtfg_queue_prior_cap(symbol, in_definition);
        }
        else {
          if (prior_is_cap == 0) {
            if (in_definition == 0)
              EncodeDictType(LEVEL0);
            else
              EncodeDictType(LEVEL1);
          }
          else {
            if (in_definition == 0)
              EncodeDictType(LEVEL0_CAP);
            else
              EncodeDictType(LEVEL1_CAP);
          }
          encode_dictionary_symbol(symbol);
          if (sd[symbol].type & 4) {
            remove_dictionary_symbol(symbol, sd[symbol].code_length);
            add_symbol_to_mtfg_queue(symbol);
          }
        }
        prior_is_cap = sd[symbol].type & 1;
        prior_symbol = symbol;
      }
      prior_end = sd[symbol].ends;
    }
    if ((sd[define_symbol].type & 0x40) == 0)
      sd[define_symbol].type |= sd[symbol_array[sd[define_symbol+1].define_symbol_start_index - 2]].type & 0xC0;
    return(1);
  }

  // write the define code
  if (prior_is_cap == 0) {
    if (in_definition == 0)
      EncodeNewType(LEVEL0);
    else
      EncodeNewType(LEVEL1);
  }
  else {
    if (in_definition == 0)
      EncodeNewType(LEVEL0_CAP);
    else
      EncodeNewType(LEVEL1_CAP);
  }

  define_symbol_instances = sd[define_symbol].count;
  if (define_symbol_instances != 1)
    new_symbol_code_length = sd[define_symbol].code_length;
  else
    new_symbol_code_length = 0x20;

  // send symbol length, instances and ergodicity bit
  if (define_symbol < start_my_symbols) {
    SID_symbol = 0;
    EncodeSID(prior_is_cap, 0);
    if (define_symbol_instances == 1)
      EncodeINST(prior_is_cap, 0, MAX_INSTANCES_FOR_MTF_QUEUE - 1);
    else if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE)
      EncodeINST(prior_is_cap, 0, define_symbol_instances - 2);
    else
      EncodeINST(prior_is_cap, 0, MAX_INSTANCES_FOR_MTF_QUEUE + max_regular_code_length - new_symbol_code_length);
    uint32_t new_symbol = define_symbol;
    if (cap_encoded != 0) {
      if (new_symbol > 'Z')
        new_symbol -= 24;
      else if (new_symbol > 'A')
        new_symbol -= 1;
      EncodeBaseSymbol(new_symbol, num_base_symbols - 24, num_base_symbols);
    }
    else
      EncodeBaseSymbol(new_symbol, num_base_symbols, num_base_symbols);
    if ((UTF8_compliant == 0) || (define_symbol < START_UTF8_2BYTE_SYMBOLS)) {
      if ((define_symbol & 1) != 0) {
        if (symbol_lengths[define_symbol - 1] != 0)
          DoubleRangeDown();
      }
      else if (symbol_lengths[define_symbol + 1] != 0)
        DoubleRange();
    }

    if (cap_encoded != 0) {
      if (UTF8_compliant != 0) {
        if (define_symbol < START_UTF8_2BYTE_SYMBOLS) {
          prior_end = (uint8_t)define_symbol;
          symbol_lengths[prior_end] = new_symbol_code_length;
          InitBaseSymbolCap(prior_end, 0x90, new_symbol_code_length, &cap_symbol_defined, &cap_lock_symbol_defined,
              symbol_lengths);
          if (prior_end == 'B')
            prior_end = 'C';
        }
        else {
          if (define_symbol < 0x250)
            prior_end = 0x80;
          else if (define_symbol < 0x370)
            prior_end = 0x81;
          else if (define_symbol < 0x400)
            prior_end = 0x82;
          else if (define_symbol < 0x530)
            prior_end = 0x83;
          else if (define_symbol < 0x590)
            prior_end = 0x84;
          else if (define_symbol < 0x600)
            prior_end = 0x85;
          else if (define_symbol < 0x700)
            prior_end = 0x86;
          else if (define_symbol < START_UTF8_3BYTE_SYMBOLS)
            prior_end = 0x87;
          else if (define_symbol < 0x1000)
            prior_end = 0x88;
          else if (define_symbol < 0x2000)
            prior_end = 0x89;
          else if (define_symbol < 0x3000)
            prior_end = 0x8A;
          else if (define_symbol < 0x3040)
            prior_end = 0x8B;
          else if (define_symbol < 0x30A0)
            prior_end = 0x8C;
          else if (define_symbol < 0x3100)
            prior_end = 0x8D;
          else if (define_symbol < 0x3200)
            prior_end = 0x8E;
          else if (define_symbol < 0xA000)
            prior_end = 0x8F;
          else if (define_symbol < START_UTF8_4BYTE_SYMBOLS)
            prior_end = 0x8E;
          else
            prior_end = 0x90;
          if (symbol_lengths[prior_end] == 0) {
            symbol_lengths[prior_end] = new_symbol_code_length;
            uint8_t j1 = 0x90;
            do {
              InitFirstCharBin(j1, prior_end, new_symbol_code_length, cap_symbol_defined, cap_lock_symbol_defined);
            } while (--j1 != 'Z');
            j1 = 'A' - 1;
            do {
              InitFirstCharBin(j1, prior_end, new_symbol_code_length, cap_symbol_defined, cap_lock_symbol_defined);
            } while (j1-- != 0);
            j1 = 0x90;
            do {
              InitSymbolFirstChar(prior_end, j1);
              if (symbol_lengths[j1])
                InitTrailingCharBin(prior_end, j1, symbol_lengths[j1]);
              else if ((j1 == 'C') && cap_symbol_defined)
                InitTrailingCharBin(prior_end, 'C', symbol_lengths[j1]);
              else if ((j1 == 'B') && cap_lock_symbol_defined)
                InitTrailingCharBin(prior_end, 'B', symbol_lengths[j1]);
            } while (j1-- != 0);
          }
        }
      }
      else {
        prior_end = (uint8_t)define_symbol;
        symbol_lengths[prior_end] = new_symbol_code_length;
        InitBaseSymbolCap(prior_end, 0xFF, new_symbol_code_length, &cap_symbol_defined, &cap_lock_symbol_defined,
            symbol_lengths);
      }
    }
    else {
      if (UTF8_compliant != 0) {
        if (define_symbol < START_UTF8_2BYTE_SYMBOLS) {
          prior_end = (uint8_t)define_symbol;
          symbol_lengths[prior_end] = new_symbol_code_length;
          uint8_t j1 = 0x90;
          do {
            InitFirstCharBin(j1, prior_end, new_symbol_code_length, cap_symbol_defined, cap_lock_symbol_defined);
          } while (j1-- != 0);
          j1 = 0x90;
          do {
            InitSymbolFirstChar(prior_end, j1);
            if (symbol_lengths[j1])
              InitTrailingCharBin(prior_end, j1, symbol_lengths[j1]);
          } while (j1-- != 0);
        }
        else {
          if (define_symbol < 0x250)
            prior_end = 0x80;
          else if (define_symbol < 0x370)
            prior_end = 0x81;
          else if (define_symbol < 0x400)
            prior_end = 0x82;
          else if (define_symbol < 0x530)
            prior_end = 0x83;
          else if (define_symbol < 0x590)
            prior_end = 0x84;
          else if (define_symbol < 0x600)
            prior_end = 0x85;
          else if (define_symbol < 0x700)
            prior_end = 0x86;
          else if (define_symbol < START_UTF8_3BYTE_SYMBOLS)
            prior_end = 0x87;
          else if (define_symbol < 0x1000)
            prior_end = 0x88;
          else if (define_symbol < 0x2000)
            prior_end = 0x89;
          else if (define_symbol < 0x3000)
            prior_end = 0x8A;
          else if (define_symbol < 0x3040)
            prior_end = 0x8B;
          else if (define_symbol < 0x30A0)
            prior_end = 0x8C;
          else if (define_symbol < 0x3100)
            prior_end = 0x8D;
          else if (define_symbol < 0x3200)
            prior_end = 0x8E;
          else if (define_symbol < 0xA000)
            prior_end = 0x8F;
          else if (define_symbol < START_UTF8_4BYTE_SYMBOLS)
            prior_end = 0x8E;
          else
            prior_end = 0x90;
          if (symbol_lengths[prior_end] == 0) {
            symbol_lengths[prior_end] = new_symbol_code_length;
            uint8_t j1 = 0x90;
            do {
              InitFirstCharBin(j1, prior_end, new_symbol_code_length, cap_symbol_defined, cap_lock_symbol_defined);
            } while (j1-- != 0);
            j1 = 0x90;
            do {
              InitSymbolFirstChar(prior_end, j1);
              if (symbol_lengths[j1])
                InitTrailingCharBin(prior_end, j1, symbol_lengths[j1]);
            } while (j1-- != 0);
            InitFreqFirstChar(prior_end, prior_end);
          }
        }
      }
      else {
        prior_end = (uint8_t)define_symbol;
        symbol_lengths[prior_end] = new_symbol_code_length;
        uint8_t j1 = 0xFF;
        do {
          InitFirstCharBin(j1, prior_end, new_symbol_code_length, cap_symbol_defined, cap_lock_symbol_defined);
        } while (j1-- != 0);
        j1 = 0xFF;
        do {
          InitSymbolFirstChar(prior_end, j1);
          if (symbol_lengths[j1])
            InitTrailingCharBin(prior_end, j1, symbol_lengths[j1]);
        } while (j1-- != 0);
      }
    }
    prior_symbol = define_symbol;

    char_before_define_is_cap = prior_is_cap;
    prior_is_cap = sd[define_symbol].type & 1;
    if (found_first_symbol == 0) {
      found_first_symbol = 1;
      if (prior_end != 0x43)
        end_char = prior_end;
      else
        end_char = (uint8_t)define_symbol;
      sym_list_ptrs[end_char][max_code_length][0] = num_codes;
      nsob[end_char][max_code_length] = 1;
      nbob[end_char][max_code_length] = 1;
      sum_nbob[end_char] = 1;
    }
  }
  else {
    num_grammar_rules++;
    define_symbol_start_ptr = symbol_array + sd[define_symbol].define_symbol_start_index;
    define_string_ptr = define_symbol_start_ptr;
    define_string_end_ptr = symbol_array + sd[define_symbol+1].define_symbol_start_index - 1;

    // count the symbols in the definition
    symbols_in_definition = 0;
    while (define_string_ptr != define_string_end_ptr) {
      if ((sd[*define_string_ptr].count != 1) || (*define_string_ptr < start_my_symbols))
        symbols_in_definition++;
      else
        symbols_in_definition += count_symbols(*define_string_ptr);
      define_string_ptr++;
    }
    if (symbols_in_definition < 16) {
      SID_symbol = symbols_in_definition - 1;
      EncodeSID(prior_is_cap, SID_symbol);
    }
    else {
      SID_symbol = 15;
      EncodeSID(prior_is_cap, SID_symbol);
      int32_t extra_symbols = symbols_in_definition - 16;
      int32_t temp2 = extra_symbols;
      uint8_t data_bits = 1;
      while (temp2 >= (1 << data_bits))
        temp2 -= (1 << data_bits++);
      temp2 = (int32_t)data_bits;
      while (temp2 > 2) {
        temp2 -= 2;
        EncodeExtraLength(3);
      }
      extra_symbols += 2 - (1 << data_bits);
      if (temp2 == 2) {
        EncodeExtraLength(2);
      }
      else
        data_bits++;
      while (data_bits) {
        data_bits -= 2;
        EncodeExtraLength((extra_symbols >> data_bits) & 3);
      }
    }

    if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE)
      EncodeINST(prior_is_cap, SID_symbol, define_symbol_instances - 2);
    else
      EncodeINST(prior_is_cap, SID_symbol, MAX_INSTANCES_FOR_MTF_QUEUE + max_regular_code_length - new_symbol_code_length);

    char_before_define_is_cap = prior_is_cap;

    // write the symbol string
    define_string_ptr = define_symbol_start_ptr;
    while (define_string_ptr != define_string_end_ptr) {
      symbol = *define_string_ptr++;
      symbol_inst = sd[symbol].inst_found++;
      symbol_count = sd[symbol].count;
      if (symbol_inst == 0) {
        if (embed_define(symbol, 1) == 0)
          return(0);
      }
      else if (symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf != 0) {
          if (manage_mtf_queue(symbol, symbol_inst, symbol_count, 1) == 0)
            return(0);
        }
        else
          manage_mtf_symbol(symbol, symbol_inst, symbol_count, 1);
        prior_symbol = symbol;
      }
      else {
        if ((sd[symbol].type & 8) != 0) {
          if (prior_is_cap == 0)
            manage_mtfg_queue(symbol, 1);
          else
            manage_mtfg_queue_prior_cap(symbol, 1);
        }
        else {
          if (prior_is_cap == 0)
            EncodeDictType(LEVEL1);
          else
            EncodeDictType(LEVEL1_CAP);
          encode_dictionary_symbol(symbol);
          if (sd[symbol].type & 4) {
            remove_dictionary_symbol(symbol, sd[symbol].code_length);
            add_symbol_to_mtfg_queue(symbol);
          }
        }
        prior_is_cap = sd[symbol].type & 1;
        prior_symbol = symbol;
      }
      prior_end = sd[symbol].ends;
    }
    prior_symbol = define_symbol;
  }

  if (define_symbol_instances != 1) { // assign symbol code
    uint8_t tag_type = 0;
    if (cap_encoded != 0) {
      if (sd[define_symbol].type & 0x40) {
        if (sd[define_symbol].type & 0x80) {
          tag_type = 2;
          EncodeWordTag(1);
        }
        else {
          tag_type = 1;
          EncodeWordTag(0);
        }
      }
      else if (define_symbol >= start_my_symbols)
        sd[define_symbol].type |= sd[symbol_array[sd[define_symbol+1].define_symbol_start_index - 2]].type & 0xC0;
    }
    if (define_symbol_instances <= MAX_INSTANCES_FOR_MTF_QUEUE) {
      if (use_mtf != 0) {
        UpFreqMtfQueueNum(char_before_define_is_cap, define_symbol_instances - 2);
        // Handle initial mtf symbol instance
        sd[define_symbol].type |= 8;
        if (mtf_queue_size[define_symbol_instances] < MTF_QUEUE_SIZE)
          mtf_queue[define_symbol_instances][mtf_queue_size[define_symbol_instances]++] = define_symbol;
        else {
          uint32_t symbol_to_move = mtf_queue[define_symbol_instances][0];
          sd[symbol_to_move].type &= 0xF7;
          if (add_dictionary_symbol(symbol_to_move, new_symbol_code_length) == 0)
            return(0);
          uint8_t i;
          for (i = 0 ; i < 63 ; i++)
            mtf_queue[define_symbol_instances][i] = mtf_queue[define_symbol_instances][i+1];
          mtf_queue[define_symbol_instances][63] = define_symbol;
        }
      }
      else if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
        return(0);
    }
    else if (use_mtfg && (new_symbol_code_length >= 11)) {
      if (sd[define_symbol].type & 4) {
        EncodeERG(tag_type, 1);
        add_symbol_to_mtfg_queue(define_symbol);
      }
      else {
        EncodeERG(tag_type, 0);
        if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
          return(0);
      }
    }
    else if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
      return(0);
  }
  return(1);
}


uint8_t GLZAencode(size_t in_size, uint8_t * inbuf, size_t * outsize_ptr, uint8_t * outbuf, FILE * fd, size_t file_size,
    struct param_data * params) {
  const uint8_t INSERT_SYMBOL_CHAR = 0xFE;
  const uint8_t DEFINE_SYMBOL_CHAR = 0xFF;
  const size_t WRITE_SIZE = 0x40000;
  uint8_t temp_char, base_bits, format, verbose, code_length;
  uint8_t *in_char_ptr, *end_char_ptr;
  uint32_t i, j, num_symbols_defined, num_definitions_to_code, grammar_size, num_mtf_symbol_definitions;
  uint32_t UTF8_value, max_UTF8_value, symbol, symbol_count, symbol_inst, prior_repeats, next_symbol, code_length_limit;
  uint32_t min_ranked_symbols, ranked_symbols_save, num_new_symbols, num_regular_definitions, num_symbols_to_code;
  uint32_t mtf_queue_miss_code_space, min_code_space, mtf_symbols, mtfg_symbols_reduced, rules_reduced;
  uint32_t *symbol_ptr, *end_symbol_ptr, *ranked_symbols, *first_define_ptr;
  uint32_t *ranked_symbols_ptr, *end_ranked_symbols_ptr, *min_ranked_symbols_ptr, *max_ranked_symbols_ptr;
  uint32_t *min_one_instance_ranked_symbols_ptr, *next_sorted_symbol_ptr;
  int32_t remaining_symbols_to_code, remaining_code_space, index_last_length[26];
  double d_remaining_symbols_to_code, symbol_inst_factor;


  for (i = 2 ; i <= MAX_INSTANCES_FOR_MTF_QUEUE ; i++) {
    mtf_queue_started[i] = 0;
    mtf_queue_done[i] = 0;
    mtf_queue_peak[i] = 0;
    mtf_queue_size[i] = 0;
    mtf_queue_hits[i] = 0;
  }
  mtfg_queue_8_offset = 0;
  mtfg_queue_16_offset = 0;
  mtfg_queue_32_offset = 0;
  mtfg_queue_64_offset = 0;
  mtfg_queue_128_offset = 0;
  mtfg_queue_192_offset = 0;

  verbose = 0;
  use_mtf = 2;
  if (params != 0) {
    verbose = params->print_dictionary;
    use_mtf = params->use_mtf;
  }
  use_mtfg = 0;
  grammar_size = 0;

  in_char_ptr = inbuf;
  end_char_ptr = inbuf + in_size;
  format = *in_char_ptr++;
  cap_encoded = (format == 1) ? 1 : 0; 
  UTF8_compliant = 1;
  max_UTF8_value = 0x7F;

  // parse the file to determine UTF8_compliant
  while (in_char_ptr != end_char_ptr) {
    if (*in_char_ptr >= INSERT_SYMBOL_CHAR) {
      if (*(in_char_ptr+1) != DEFINE_SYMBOL_CHAR)
        in_char_ptr += 4;
      else {
        UTF8_compliant = 0;
        break;
      }
    }
    else if (*in_char_ptr >= 0x80) {
      if (*in_char_ptr < 0xC0) {
        UTF8_compliant = 0;
        break;
      }
      else if (*in_char_ptr < 0xE0) {
        if ((*(in_char_ptr+1) < 0x80) || (*(in_char_ptr+1) >= 0xC0)) {
          UTF8_compliant = 0;
          break;
        }
        else {
          UTF8_value = 0x40 * (*in_char_ptr & 0x1F) + (*(in_char_ptr+1) & 0x3F);
          if (UTF8_value > max_UTF8_value)
            max_UTF8_value = UTF8_value;
          in_char_ptr += 2;
        }
      }
      else if (*in_char_ptr < 0xF0) {
        if ((*(in_char_ptr+1) < 0x80) || (*(in_char_ptr+1) >= 0xC0)
            || (*(in_char_ptr+2) < 0x80) || (*(in_char_ptr+2) >= 0xC0)) {
          UTF8_compliant = 0;
          break;
        }
        else {
          UTF8_value = 0x1000 * (*in_char_ptr & 0xF) + 0x40 * (*(in_char_ptr+1) & 0x3F) + (*(in_char_ptr+2) & 0x3F);
          if (UTF8_value > max_UTF8_value)
            max_UTF8_value = UTF8_value;
          in_char_ptr += 3;
        }
      }
      else if (*in_char_ptr < 0xF8) {
        if ((*(in_char_ptr+1) < 0x80) || (*(in_char_ptr+1) >= 0xC0) || (*(in_char_ptr+2) < 0x80)
            || (*(in_char_ptr+2) >= 0xC0) || (*(in_char_ptr+3) < 0x80) || (*(in_char_ptr+3) >= 0xC0)) {
          UTF8_compliant = 0;
          break;
        }
        else {
          UTF8_value = 0x40000 * (*in_char_ptr & 0x7) + 0x1000 * (*(in_char_ptr+1) & 0x3F)
              + 0x40 * (*(in_char_ptr+2) & 0x3F) + (*(in_char_ptr+3) & 0x3F);
          if (UTF8_value > max_UTF8_value)
            max_UTF8_value = UTF8_value;
          in_char_ptr += 4;
        }
      }
      else {
        UTF8_compliant = 0;
        break;
      }
    }
    else
      in_char_ptr++;
    grammar_size++;
  }
  in_char_ptr = inbuf + 1;
  end_char_ptr = inbuf + in_size;
  if (UTF8_compliant == 0)
    grammar_size = in_size - 1;

  symbol_array = (uint32_t *)malloc(sizeof(uint32_t) * (grammar_size + 1));
  if (symbol_array == 0) {
    fprintf(stderr,"Symbol memory allocation failed\n");
    return(0);
  }
  symbol_ptr = symbol_array;

  num_symbols_defined = 0;
  first_define_ptr = 0;

  if (UTF8_compliant != 0) {
    base_bits = 7;
    while ((max_UTF8_value >> base_bits) != 0)
      base_bits++;
    start_my_symbols = 1 << base_bits;
    num_base_symbols = start_my_symbols;
    while (in_char_ptr < end_char_ptr) {
      temp_char = *in_char_ptr++;
      if (temp_char == INSERT_SYMBOL_CHAR) {
        symbol = start_my_symbols;
        symbol += 0x10000 * (uint32_t)*in_char_ptr++;
        symbol += 0x100 * (uint32_t)*in_char_ptr++;
        symbol += (uint32_t)*in_char_ptr++;
        *symbol_ptr++ = symbol;
      }
      else if (temp_char == DEFINE_SYMBOL_CHAR) {
        if (first_define_ptr == 0)
          first_define_ptr = symbol_ptr;
        in_char_ptr += 3;
        *symbol_ptr++ = ((uint32_t)DEFINE_SYMBOL_CHAR << 24) + num_symbols_defined++;
      }
      else if (temp_char < START_UTF8_2BYTE_SYMBOLS)
        *symbol_ptr++ = (uint32_t)temp_char;
      else {
        if (temp_char >= 0xF8) { // not a UTF-8 character
          fprintf(stderr,"ERROR - non UTF-8 character %x\n",(unsigned char)temp_char);
          return(0);
        }
        else if (temp_char >= 0xF0) { // 4 byte UTF-8 character
          UTF8_value = 0x40000 * (temp_char & 7);
          UTF8_value += 0x1000 * (*in_char_ptr++ & 0x3F);
          UTF8_value += 0x40 * (*in_char_ptr++ & 0x3F);
        }
        else if (temp_char >= 0xE0) { // 3 byte UTF-8 character
          UTF8_value = 0x1000 * (temp_char & 0xF);
          UTF8_value += 0x40 * (*in_char_ptr++ & 0x3F);
        }
        else // 2 byte UTF-8 character
          UTF8_value = 0x40 * (temp_char & 0x1F);
        UTF8_value += *in_char_ptr++ & 0x3F;
        *symbol_ptr++ = UTF8_value;
      }
    }
  }
  else {
    base_bits = 8;
    start_my_symbols = 0x100;
    num_base_symbols = 0x100;
    while (in_char_ptr < end_char_ptr) {
      temp_char = *in_char_ptr++;
      if (temp_char < INSERT_SYMBOL_CHAR)
        *symbol_ptr++ = (uint32_t)temp_char;
      else if (*in_char_ptr == DEFINE_SYMBOL_CHAR) {
        *symbol_ptr++ = (uint32_t)temp_char;
        in_char_ptr++;
      }
      else if (temp_char == INSERT_SYMBOL_CHAR) {
        symbol = start_my_symbols;
        symbol += 0x10000 * (uint32_t)*in_char_ptr++;
        symbol += 0x100 * (uint32_t)*in_char_ptr++;
        symbol += (uint32_t)*in_char_ptr++;
        *symbol_ptr++ = symbol;
      }
      else {
        if (first_define_ptr == 0)
          first_define_ptr = symbol_ptr;
        in_char_ptr += 3;
        *symbol_ptr++ = ((uint32_t)DEFINE_SYMBOL_CHAR << 24) + num_symbols_defined++;
      }
    }
    grammar_size = symbol_ptr - symbol_array;
  }
#ifdef PRINTON
  fprintf(stderr,"cap encoded %u, UTF8 compliant %u\n",(unsigned int)cap_encoded,(unsigned int)UTF8_compliant);
#endif

  if (first_define_ptr == 0)
    first_define_ptr = symbol_ptr;

  end_symbol_ptr = symbol_ptr;
  *end_symbol_ptr = UNIQUE_CHAR;
  num_codes = start_my_symbols + num_symbols_defined;
#ifdef PRINTON
  fprintf(stderr,"Read %u symbols including %u definition symbols\n",(unsigned int)grammar_size,
      (unsigned int)num_symbols_defined);
#endif

  if (0 == (sd = (struct symbol_data *)malloc(sizeof(struct symbol_data) * (num_codes + 1)))) {
    fprintf(stderr,"Symbol data memory allocation failed\n");
    return(0);
  }

  if (0 == (ranked_symbols = (uint32_t *)malloc(sizeof(uint32_t) * num_codes))) {
    fprintf(stderr,"Ranked symbol array memory allocation failed\n");
    return(0);
  }

  // count the number of instances of each symbol
  for (i = 0 ; i < num_codes ; i++) {
    sd[i].count = 0;
    sd[i].inst_found = 0;
  }
  symbol_ptr = symbol_array;
  num_symbols_defined = 0;
  while (1) {
    if (*symbol_ptr < (uint32_t)DEFINE_SYMBOL_CHAR << 24)
      sd[*symbol_ptr++].count++;
    else if (*symbol_ptr++ != UNIQUE_CHAR)
      sd[start_my_symbols + num_symbols_defined++].define_symbol_start_index = symbol_ptr - symbol_array;
    else
      break;
  }
  sd[start_my_symbols + num_symbols_defined].define_symbol_start_index = symbol_ptr - symbol_array;

  if (cap_encoded != 0) {
    i = 0;
    do {
      sd[i].type = 0;
    } while (++i != 0x61);
    do {
      sd[i].type = 2;
    } while (++i != 0x7B);
    do {
      sd[i].type = 0;
    } while (++i != start_my_symbols);
    sd['B'].type = 1;
    sd['C'].type = 1;
    while (i < num_codes) {
      next_symbol = symbol_array[sd[i].define_symbol_start_index];
      while (next_symbol > i)
        next_symbol = symbol_array[sd[next_symbol].define_symbol_start_index];
      sd[i].type = sd[next_symbol].type & 2;
      next_symbol = symbol_array[sd[i+1].define_symbol_start_index-2];
      while (next_symbol > i)
        next_symbol = symbol_array[sd[next_symbol+1].define_symbol_start_index-2];
      sd[i++].type |= sd[next_symbol].type & 1;
    }
  }
  else {
    i = 0;
    while (i < num_codes)
      sd[i++].type = 0;
  }

  ranked_symbols_ptr = ranked_symbols;
  for (i = 0 ; i < num_codes ; i++)
    if (sd[i].count != 0)
      *ranked_symbols_ptr++ = i;
  end_ranked_symbols_ptr = ranked_symbols_ptr;
  min_ranked_symbols_ptr = ranked_symbols_ptr;

  // move single instance symbols to the end of the sorted symbols array
  ranked_symbols_ptr = ranked_symbols;
  while (ranked_symbols_ptr < min_ranked_symbols_ptr) {
    if (sd[*ranked_symbols_ptr].count == 1) { // move this symbol to the top of the moved to end 1 instance symbols
      ranked_symbols_save = *ranked_symbols_ptr;
      *ranked_symbols_ptr = *--min_ranked_symbols_ptr;
      *min_ranked_symbols_ptr = ranked_symbols_save;
    }
    else
      ranked_symbols_ptr++;
  }
  min_one_instance_ranked_symbols_ptr = min_ranked_symbols_ptr;

  rules_reduced = 0;
  if (num_symbols_defined != 0) {
    for (i = 0 ; i < start_my_symbols + num_symbols_defined; i++)
      if (sd[i].count == 1)
        rules_reduced++;
  }

#ifdef PRINTON
  double order_0_entropy = 0.0;
  double log_file_symbols = log2((double)grammar_size);
  i = 0;
  do {
    if (sd[i].count != 0) {
      double d_symbol_count = (double)sd[i].count;
      order_0_entropy += d_symbol_count * (log_file_symbols - log2(d_symbol_count));
    }
  } while (++i < start_my_symbols);
  if (num_symbols_defined != 0) {
    while (i < start_my_symbols + num_symbols_defined) {
      double d_symbol_count = (double)sd[i++].count;
      order_0_entropy += d_symbol_count * (log_file_symbols - log2(d_symbol_count));
    }
    double d_symbol_count = (double)num_symbols_defined;
    order_0_entropy += d_symbol_count * (log_file_symbols - log2(d_symbol_count));
  }
  fprintf(stderr,"%u syms, dict. size %u, %.4f bits/sym, o0e %.2lf bytes\n",
      (unsigned int)grammar_size, (unsigned int)num_symbols_defined,
      (float)(order_0_entropy / (double)grammar_size), 0.125 * order_0_entropy);
#endif

  grammar_size -= 2 * rules_reduced;

#ifdef PRINTON
  if (rules_reduced != 0) {
    order_0_entropy = 0.0;
    log_file_symbols = log2((double)grammar_size);
    i = 0;
    do {
      if (sd[i].count != 0) {
        double d_symbol_count = (double)sd[i].count;
        order_0_entropy += d_symbol_count * (log_file_symbols - log2(d_symbol_count));
      }
    } while (++i < start_my_symbols);
    if (num_symbols_defined != 0) {
      while (i < start_my_symbols + num_symbols_defined) {
        if (sd[i].count > 1) {
          double d_symbol_count = (double)sd[i].count;
          order_0_entropy += d_symbol_count * (log_file_symbols - log2(d_symbol_count));
        }
        i++;
      }
      double d_symbol_count = (double)(num_symbols_defined - rules_reduced);
      order_0_entropy += d_symbol_count * (log_file_symbols - log2(d_symbol_count));
    }
    fprintf(stderr,"Eliminated %u single appearance grammar rules\n",rules_reduced);
    fprintf(stderr,"%u syms, dict. size %u, %.4f bits/sym, o0e %.2lf bytes\n",
        (unsigned int)grammar_size,(unsigned int)(num_symbols_defined - rules_reduced),
        (float)(order_0_entropy/(double)grammar_size),0.125*order_0_entropy);
  }

  uint32_t len_counts[16];
  uint32_t extra_len_bits = 0;
  for (i = 0 ; i < 16 ; i++)
    len_counts[i] = 0;
  for (i = start_my_symbols ; i < start_my_symbols + num_symbols_defined ; i++) {
    if (sd[i].count > 1) {
      uint32_t dl = sd[i + 1].define_symbol_start_index - sd[i].define_symbol_start_index - 1;
      if (dl < 16)
        len_counts[dl-1]++;
      else {
        len_counts[15]++;
        uint32_t extra_len = dl - 14;
        do {
          extra_len >>= 1;
          extra_len_bits += 2;
        } while (extra_len != 0);
      }
    }
  }
#endif

  grammar_size -= num_symbols_defined - rules_reduced;

#ifdef PRINTON
  order_0_entropy = 0.0;
  log_file_symbols = log2((double)grammar_size);
  i = 0;
  do {
    if (sd[i].count != 0) {
      double d_symbol_count = (double)sd[i].count;
      order_0_entropy += d_symbol_count * (log_file_symbols - log2(d_symbol_count));
    }
  } while (++i < start_my_symbols);
  if (num_symbols_defined != 0) {
    while (i < start_my_symbols + num_symbols_defined) {
      if (sd[i].count > 1) {
        double d_symbol_count = (double)(sd[i].count - 1);
        order_0_entropy += d_symbol_count * (log_file_symbols - log2(d_symbol_count));
      }
      i++;
    }
    double d_symbol_count = (double)(num_symbols_defined - rules_reduced);
    order_0_entropy += d_symbol_count * (log_file_symbols - log2(d_symbol_count));
  }
  num_new_symbols = end_ranked_symbols_ptr - ranked_symbols - rules_reduced;
  double code_entropy = 0.0;
  if (num_symbols_defined != 0) {
    uint32_t len_codes = num_symbols_defined - rules_reduced;
    double log_len_codes = log2((double)len_codes);
    for (i = 0 ; i < 16 ; i++) {
      if (len_counts[i] != 0) {
        double d_symbol_count = (double)len_counts[i];
        code_entropy += d_symbol_count * (log_len_codes - log2(d_symbol_count));
      }
    }
    code_entropy += (double)extra_len_bits;
    fprintf(stderr,"Finished embedding grammar rules\n");
    fprintf(stderr,"Final grammar size: %u (%u terminals + %u rule symbols + %u repeats)\n",
      grammar_size, num_new_symbols + rules_reduced - num_symbols_defined, num_symbols_defined - rules_reduced,
      grammar_size - num_new_symbols);
    fprintf(stderr,"%.4f bits/symbol, plus %u length codes %.4f bits/code, o0e %.2lf bytes\n",
        (float)(order_0_entropy/(double)grammar_size), (unsigned int)(num_symbols_defined - rules_reduced),
        (float)(code_entropy/(double)len_codes), 0.125 * (order_0_entropy + code_entropy));
  }
#endif

  // sort symbols with 800 or fewer instances by putting them at the end of the sorted symbols array
  for (i = 2 ; i < 801 ; i++) {
    ranked_symbols_ptr = ranked_symbols;
    while (ranked_symbols_ptr < min_ranked_symbols_ptr) {
      if (sd[*ranked_symbols_ptr].count == i) {
        ranked_symbols_save = *ranked_symbols_ptr;
        *ranked_symbols_ptr = *--min_ranked_symbols_ptr;
        *min_ranked_symbols_ptr = ranked_symbols_save;
      }
      else
        ranked_symbols_ptr++;
    }
  }

  // sort the remaining symbols by moving the most frequent symbols to the top of the sorted symbols array
  min_ranked_symbols = min_ranked_symbols_ptr - ranked_symbols;
  for (i = 0 ; i < min_ranked_symbols ; i++) {
    uint32_t max_symbol_count = 0;
    ranked_symbols_ptr = &ranked_symbols[i];
    while (ranked_symbols_ptr < min_ranked_symbols_ptr) {
      if (sd[*ranked_symbols_ptr].count > max_symbol_count) {
        max_symbol_count = sd[*ranked_symbols_ptr].count;
        max_ranked_symbols_ptr = ranked_symbols_ptr;
      }
      ranked_symbols_ptr++;
    }
    if (max_symbol_count > 0) {
      ranked_symbols_save = ranked_symbols[i];
      ranked_symbols[i] = *max_ranked_symbols_ptr;
      *max_ranked_symbols_ptr = ranked_symbols_save;
    }
  }

  num_definitions_to_code = min_one_instance_ranked_symbols_ptr - ranked_symbols;

  remaining_symbols_to_code = grammar_size - num_new_symbols - rules_reduced;
  remaining_code_space = (1 << 30) - (1 << (30 - MAX_BITS_IN_CODE)); // reserve space for EOF

  for (i = 2 ; i < 5 ; i++)
    mtf_queue_miss_code_length[i] = 25;
  for (i = 5 ; i < 10 ; i++)
    mtf_queue_miss_code_length[i] = 24;
  for (i = 10 ; i <= MAX_INSTANCES_FOR_MTF_QUEUE ; i++)
    mtf_queue_miss_code_length[i] = 23;

  max_regular_code_length = 2;
  num_regular_definitions = 0;

  prior_repeats = 0;
  i = 0;
  while (i < num_definitions_to_code) {
    symbol_inst = sd[ranked_symbols[i]].count - 1;
    if (symbol_inst != prior_repeats) {
      if (symbol_inst < MAX_INSTANCES_FOR_MTF_QUEUE)
        break;
      prior_repeats = symbol_inst;
      symbol_inst_factor = (double)0x5A827999 / (double)symbol_inst; /* 0x40000000 * sqrt(2.0) */
    }
    d_remaining_symbols_to_code = (double)remaining_symbols_to_code;
    code_length = (uint8_t)(log2(d_remaining_symbols_to_code * symbol_inst_factor / (double)remaining_code_space));
    if (code_length < 2) // limit so files with less than 2 bit symbols (ideally) work
      code_length = 2;
    num_regular_definitions++;
    if (code_length > 24)
      code_length = 24;
    if (code_length > max_regular_code_length)
      max_regular_code_length = code_length;
    sd[ranked_symbols[i]].code_length = code_length;
    remaining_code_space -= (1 << (30 - code_length));
    remaining_symbols_to_code -= symbol_inst;
    i++;
  }

  mtfg_queue_8_offset = 0;
  mtfg_queue_16_offset = 0;
  mtfg_queue_32_offset = 0;
  mtfg_queue_64_offset = 0;
  mtfg_queue_128_offset = 0;
  mtfg_queue_192_offset = 0;
  for (i = 0 ; i < 8 ; i++)
    mtfg_queue_0[i] = num_codes;
  for (i = 0 ; i < 8 ; i++)
    mtfg_queue_8[i] = num_codes;
  for (i = 0 ; i < 16 ; i++)
    mtfg_queue_16[i] = num_codes;
  for (i = 0 ; i < 32 ; i++)
    mtfg_queue_32[i] = num_codes;
  for (i = 0 ; i < 64 ; i++)
    mtfg_queue_64[i] = num_codes;
  for (i = 0 ; i < 64 ; i++)
    mtfg_queue_128[i] = num_codes;
  for (i = 0 ; i < 64 ; i++)
    mtfg_queue_192[i] = num_codes;

  symbol_ptr = symbol_array;

  for (i = start_my_symbols ; i < num_codes ; i++) {
    sd[i].starts = 0;
    sd[i].ends = 0;
  }

  if (UTF8_compliant != 0) {
    i = 0;
    while (i < 0x80) {
      sd[i].starts = (uint8_t)i;
      sd[i].ends = (uint8_t)i;
      i++;
    }
    uint32_t temp_UTF8_limit = 0x250;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x80;
      sd[i].ends = 0x80;
      i++;
    }
    temp_UTF8_limit = 0x370;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x81;
      sd[i].ends = 0x81;
      i++;
    }
    temp_UTF8_limit = 0x400;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x82;
      sd[i].ends = 0x82;
      i++;
    }
    temp_UTF8_limit = 0x530;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x83;
      sd[i].ends = 0x83;
      i++;
    }
    temp_UTF8_limit = 0x590;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x84;
      sd[i].ends = 0x84;
      i++;
    }
    temp_UTF8_limit = 0x600;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x85;
      sd[i].ends = 0x85;
      i++;
    }
    temp_UTF8_limit = 0x700;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x86;
      sd[i].ends = 0x86;
      i++;
    }
    temp_UTF8_limit = START_UTF8_3BYTE_SYMBOLS;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x87;
      sd[i].ends = 0x87;
      i++;
    }
    temp_UTF8_limit = 0x1000;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x88;
      sd[i].ends = 0x88;
      i++;
    }
    temp_UTF8_limit = 0x2000;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x89;
      sd[i].ends = 0x89;
      i++;
    }
    temp_UTF8_limit = 0x3000;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x8A;
      sd[i].ends = 0x8A;
      i++;
    }
    temp_UTF8_limit = 0x3040;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x8B;
      sd[i].ends = 0x8B;
      i++;
    }
    temp_UTF8_limit = 0x30A0;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x8C;
      sd[i].ends = 0x8C;
      i++;
    }
    temp_UTF8_limit = 0x3100;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x8D;
      sd[i].ends = 0x8D;
      i++;
    }
    temp_UTF8_limit = 0x3200;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x8E;
      sd[i].ends = 0x8E;
      i++;
    }
    temp_UTF8_limit = 0xA000;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x8F;
      sd[i].ends = 0x8F;
      i++;
    }
    temp_UTF8_limit = START_UTF8_4BYTE_SYMBOLS;
    if (max_UTF8_value < temp_UTF8_limit)
      temp_UTF8_limit = max_UTF8_value + 1;
    while (i < temp_UTF8_limit) {
      sd[i].starts = 0x8E;
      sd[i].ends = 0x8E;
      i++;
    }
    while (i <= max_UTF8_value) {
      sd[i].starts = 0x90;
      sd[i].ends = 0x90;
      i++;
    }
    if (cap_encoded != 0)
      sd['B'].ends = 'C';
    i = start_my_symbols;
    while (i < num_codes) {
      if (sd[i].starts == 0)
        sd[i].starts = find_first_UTF8(i);
      if (sd[i].ends == 0)
        sd[i].ends = find_last_UTF8(i);
      i++;
    }
  }
  else {
    i = 0;
    while (i < 0x100) {
      sd[i].starts = (uint8_t)i;
      sd[i].ends = (uint8_t)i;
      i++;
    }
    if (cap_encoded != 0)
      sd['B'].ends = 'C';
    i = start_my_symbols;
    while (i < num_codes) {
      if (sd[i].starts == 0)
        sd[i].starts = find_first(i);
      if (sd[i].ends == 0)
        sd[i].ends = find_last(i);
      i++;
    }
  }

  for (i = 0 ; i < num_codes; i++)
    sd[i].space_score = 0;
  prior_symbol = (uint32_t)-1;

  while (symbol_ptr < first_define_ptr) {
#ifdef PRINTON
    if (((symbol_ptr - symbol_array) & 0x3FFFFF) == 0)
      fprintf(stderr,"Parsed %u of %u level 0 symbols\r",
          (unsigned int)(symbol_ptr - symbol_array),(unsigned int)(first_define_ptr - symbol_array));
#endif
    symbol = *symbol_ptr++;
    symbol_inst = sd[symbol].inst_found++;
    if (symbol_inst == 0)
      count_embedded_definition_symbols(symbol);
    else {
      if (prior_symbol >= 0) {
        if (sd[prior_symbol].type & 0x20) {
          if (sd[symbol].starts == 0x20)
            sd[prior_symbol].space_score += 1;
          else
            sd[prior_symbol].space_score -= 4;
        }
      }
      if (sd[symbol].count <= MAX_INSTANCES_FOR_MTF_QUEUE)
        update_mtf_queue(symbol, symbol_inst, sd[symbol].count);
      else {
        if (sd[symbol].code_length >= 11) {
          if ((sd[symbol].type & 8) != 0) {
            manage_mtfg_queue1(symbol);
            sd[symbol].mtfg_hits++;
          }
          else
            add_symbol_to_mtfg_queue1(symbol);
        }
      }
      prior_symbol = symbol;
    }
  }
#ifdef PRINTON
  fprintf(stderr,"Parsed %u level 0 symbols              \r",(unsigned int)(first_define_ptr - symbol_array));
#endif

  num_symbols_to_code = grammar_size - num_new_symbols - rules_reduced;
  mtfg_symbols_reduced = 0;
  if (use_mtf == 2) {
    use_mtf = 0;
    double sum_expected_peak = 0.0;
    double sum_actual_peak = 0.0;
    for (i = 2 ; i <= 15 ; i++) {
      sum_expected_peak += (double)(i - 1) * (double)mtf_queue_started[i] * (1.0 - (1.0 / (double)(1 << (i - 1))));
      sum_actual_peak += (double)(i - 1) * (double)mtf_queue_peak[i];
    }
    double score1, score2;
    score1 = 5.75 * (double)mtf_queue_started[2] / ((double)mtf_queue_peak[2] * (32.8 - log2((double)num_symbols_to_code)));
    score2 = sum_expected_peak / sum_actual_peak;
    if (score1 + score2 > 2.08)
      use_mtf = 1;
  }

  if ((use_mtf != 0) && (max_regular_code_length >= 11)) {
    use_mtfg = 1;
    for (i = 0 ; i < num_codes ; i++) {
      if ((sd[i].count > MAX_INSTANCES_FOR_MTF_QUEUE) && (sd[i].code_length >= 11)
          && (sd[i].hit_score > sd[i].count * (165 - 3 * max_regular_code_length) / 50)) {
        sd[i].type |= 4;
        if (sd[i].count - sd[i].mtfg_hits <= MAX_INSTANCES_FOR_MTF_QUEUE) {
          mtfg_symbols_reduced += sd[i].count - MAX_INSTANCES_FOR_MTF_QUEUE - 1;
          sd[i].count = MAX_INSTANCES_FOR_MTF_QUEUE + 1;
        }
        else {
          mtfg_symbols_reduced += sd[i].mtfg_hits;
          sd[i].count -= sd[i].mtfg_hits;
        }
      }
    }
  }

  // sort symbols with 800 or fewer instances by putting them at the end of the sorted symbols array
  next_sorted_symbol_ptr = ranked_symbols + num_regular_definitions - 1;
  for (i = MAX_INSTANCES_FOR_MTF_QUEUE + 1 ; i < 801 ; i++) {
    while ((next_sorted_symbol_ptr > ranked_symbols) && (sd[*next_sorted_symbol_ptr].count == i))
      next_sorted_symbol_ptr--;
    ranked_symbols_ptr = next_sorted_symbol_ptr - 1;
    while (ranked_symbols_ptr >= ranked_symbols) {
      if (sd[*ranked_symbols_ptr].count == i) {
        ranked_symbols_save = *ranked_symbols_ptr;
        *ranked_symbols_ptr-- = *next_sorted_symbol_ptr;
        *next_sorted_symbol_ptr-- = ranked_symbols_save;
      }
      else
        ranked_symbols_ptr--;
    }
  }

  for (i = 1 ; i < num_regular_definitions ; i++) {
    uint32_t temp_symbol = ranked_symbols[i];
    uint32_t temp_symbol_count = sd[temp_symbol].count;
    if (temp_symbol_count > sd[ranked_symbols[i-1]].count) {
      j = i - 1;
      ranked_symbols[i] = ranked_symbols[j];
      while ((j != 0) && (temp_symbol_count > sd[ranked_symbols[j-1]].count)) {
        ranked_symbols[j] = ranked_symbols[j-1];
        j--;
      }
      ranked_symbols[j] = temp_symbol;
    }
  }

  mtfg_queue_8_offset = 0;
  mtfg_queue_16_offset = 0;
  mtfg_queue_32_offset = 0;
  mtfg_queue_64_offset = 0;
  mtfg_queue_128_offset = 0;
  mtfg_queue_192_offset = 0;
  for (i = 0 ; i < 8 ; i++)
    mtfg_queue_0[i] = num_codes;
  for (i = 0 ; i < 8 ; i++)
    mtfg_queue_8[i] = num_codes;
  for (i = 0 ; i < 16 ; i++)
    mtfg_queue_16[i] = num_codes;
  for (i = 0 ; i < 32 ; i++)
    mtfg_queue_32[i] = num_codes;
  for (i = 0 ; i < 64 ; i++)
    mtfg_queue_64[i] = num_codes;
  for (i = 0 ; i < 64 ; i++)
    mtfg_queue_128[i] = num_codes;
  for (i = 0 ; i < 64 ; i++)
    mtfg_queue_192[i] = num_codes;

  num_symbols_to_code -= mtfg_symbols_reduced;
  if (use_mtf != 0)
    for (i = 2 ; i <= MAX_INSTANCES_FOR_MTF_QUEUE ; i++)
      num_symbols_to_code -= mtf_queue_hits[i];

  if (mtf_queue_peak[2] > MTF_QUEUE_SIZE) {
    if (use_mtf != 0)
      mtf_queue_miss_code_length[2] = (uint32_t)(0.5 + log2((double)num_symbols_to_code
          * (double)(mtf_queue_peak[2] - MTF_QUEUE_SIZE) / (double)(mtf_queue_started[2] - mtf_queue_hits[2])));
    else
      mtf_queue_miss_code_length[2] = (uint32_t)(0.5 + log2((double)num_symbols_to_code
          * (double)mtf_queue_peak[2] / (double)mtf_queue_started[2]));
    if (mtf_queue_miss_code_length[2] > 25)
      mtf_queue_miss_code_length[2] = 25;
  }
  else if (mtf_queue_peak[2] != 0) {
    if (use_mtf != 0)
      mtf_queue_miss_code_length[2] = (uint32_t)(0.5 + log2((double)num_symbols_to_code));
    else
      mtf_queue_miss_code_length[2] = (uint32_t)(0.5 + log2((double)num_symbols_to_code
          * (double)mtf_queue_peak[2] / (double)mtf_queue_started[2]));
    if (mtf_queue_miss_code_length[2] > 25)
      mtf_queue_miss_code_length[2] = 25;
  }
  else
    mtf_queue_miss_code_length[2] = 25;

  for (i = 3 ; i <= MAX_INSTANCES_FOR_MTF_QUEUE ; i++) {
    if (use_mtf != 0) {
      if (mtf_queue_peak[i] > MTF_QUEUE_SIZE) {
        mtf_queue_miss_code_length[i] = (uint32_t)(0.5 + log2((double)num_symbols_to_code
            * (double)(mtf_queue_peak[i] - MTF_QUEUE_SIZE)
            / (double)(mtf_queue_started[i] * (i - 1) - mtf_queue_hits[i])));
        if (mtf_queue_miss_code_length[i] > mtf_queue_miss_code_length[i - 1])
          mtf_queue_miss_code_length[i] = mtf_queue_miss_code_length[i - 1];
        else if (mtf_queue_miss_code_length[i] < mtf_queue_miss_code_length[i - 1] - 1)
          mtf_queue_miss_code_length[i] = mtf_queue_miss_code_length[i - 1] - 1;
      }
      else
        mtf_queue_miss_code_length[i] = mtf_queue_miss_code_length[i - 1];
    }
    else {
      if (mtf_queue_peak[i] != 0) {
        mtf_queue_miss_code_length[i] = (uint32_t)(0.5 + log2((double)num_symbols_to_code
            * (double)mtf_queue_peak[i] / (double)(mtf_queue_started[i] * (i - 1))));
        if (mtf_queue_miss_code_length[i] > mtf_queue_miss_code_length[i - 1])
          mtf_queue_miss_code_length[i] = mtf_queue_miss_code_length[i - 1];
        else if (mtf_queue_miss_code_length[i] < mtf_queue_miss_code_length[i - 1] - 1)
          mtf_queue_miss_code_length[i] = mtf_queue_miss_code_length[i - 1] - 1;
      }
      else
        mtf_queue_miss_code_length[i] = mtf_queue_miss_code_length[i - 1];
    }
  }

  if (mtf_queue_miss_code_length[10] == max_regular_code_length)
    max_regular_code_length--;
  for (i = 2 ; i < 16 ; i++)
    if (mtf_queue_miss_code_length[i] <= max_regular_code_length)
      mtf_queue_miss_code_length[i] = max_regular_code_length + 1;
  if (mtf_queue_miss_code_length[10] == max_regular_code_length)
    max_regular_code_length--;

  num_mtf_symbol_definitions = 0;
  mtf_symbols = 0;
  for (i = 2 ; i <= MAX_INSTANCES_FOR_MTF_QUEUE  ; i++) {
    num_mtf_symbol_definitions += mtf_queue_started[i];
    mtf_symbols += (i-1) * mtf_queue_started[i];
    if (mtf_queue_miss_code_length[i] <= max_regular_code_length)
      mtf_queue_miss_code_length[i] = max_regular_code_length + 1;
  }
  max_code_length = mtf_queue_miss_code_length[2];
  mtf_queue_miss_code_space = 0;
  if (use_mtf != 0) {
    for (i = 2 ; i <= MAX_INSTANCES_FOR_MTF_QUEUE ; i++) {
      mtf_queue_size[i] = 0;
      if (mtf_queue_peak[i] > MTF_QUEUE_SIZE)
        mtf_queue_miss_code_space += (1 << (30 - mtf_queue_miss_code_length[i])) * (mtf_queue_peak[i] - MTF_QUEUE_SIZE);
    }
  }
  else {
    for (i = 2 ; i <= MAX_INSTANCES_FOR_MTF_QUEUE ; i++)
      mtf_queue_miss_code_space += (1 << (30 - mtf_queue_miss_code_length[i])) * mtf_queue_peak[i];
  }

  // Recalculate code lengths knowing how many symbols are needed for 2 - 15 instance symbols that fall out of mtf queues
  remaining_symbols_to_code = grammar_size - num_new_symbols - mtf_symbols - mtfg_symbols_reduced;
  remaining_code_space = (1 << 30) - (1 << (30 - max_code_length)) - mtf_queue_miss_code_space;
  double codes_per_code_space = (double)remaining_symbols_to_code / (double)remaining_code_space;
  max_regular_code_length = 1;
  min_code_space = 0x40000000 >> (mtf_queue_miss_code_length[MAX_INSTANCES_FOR_MTF_QUEUE] - 1);
  prior_repeats = 0;
  for (i = 0 ; i <= 25 ; i++)
    index_last_length[i] = -1;

  for (i = 0 ; i < num_definitions_to_code - num_mtf_symbol_definitions ; i++) {
    sd[ranked_symbols[i]].type &= 0xF7;
    symbol_inst = sd[ranked_symbols[i]].count;
    num_regular_definitions--;
    d_remaining_symbols_to_code = (double)remaining_symbols_to_code;
    if (--symbol_inst != prior_repeats) {
      prior_repeats = symbol_inst;
      symbol_inst_factor = (double)0x5A827999 / (double)symbol_inst; /* 0x40000000 * sqrt(2.0) */
      code_length_limit = (uint32_t)log2(symbol_inst_factor * codes_per_code_space);
      if (code_length_limit < 2)
        code_length_limit = 2;
    }
    code_length = (uint8_t)(0.5 + log2(d_remaining_symbols_to_code * symbol_inst_factor / (double)remaining_code_space));
    if (code_length < code_length_limit)
      code_length = code_length_limit;
    if (code_length > max_code_length)
      code_length = max_code_length;
    while (remaining_code_space - (1 << (30 - code_length))
        < (int32_t)((num_definitions_to_code - i - 1 - num_mtf_symbol_definitions) * min_code_space))
      code_length++;
    if (code_length > max_regular_code_length) {
      if (code_length >= mtf_queue_miss_code_length[MAX_INSTANCES_FOR_MTF_QUEUE])
        code_length = mtf_queue_miss_code_length[MAX_INSTANCES_FOR_MTF_QUEUE] - 1;
      max_regular_code_length = code_length;
    }
    if (code_length < 11)
      sd[ranked_symbols[i]].type &= 0xFB;
    sd[ranked_symbols[i]].code_length = code_length;
    remaining_code_space -= 1 << (30 - code_length);
    remaining_symbols_to_code -= symbol_inst;

    if ((i != 0) && (sd[ranked_symbols[i - 1]].code_length > code_length)) {
      sd[ranked_symbols[++index_last_length[code_length]]].code_length = code_length;
      while (index_last_length[++code_length] == -1) ;
      index_last_length[code_length]++;
      sd[ranked_symbols[i]].code_length = code_length;
    }
    else
      index_last_length[code_length] = i;
  }

  for (i = num_definitions_to_code - num_mtf_symbol_definitions ; i < num_definitions_to_code ; i++) {
    sd[ranked_symbols[i]].type &= 0xF7;
    sd[ranked_symbols[i]].code_length = mtf_queue_miss_code_length[sd[ranked_symbols[i]].count];
  }

  if (verbose != 0) {
    if (verbose == 1) {
      for (i = 0 ; i < num_definitions_to_code ; i++) {
        if ((sd[ranked_symbols[i]].code_length >= 11)
            && (sd[ranked_symbols[i]].inst_found > MAX_INSTANCES_FOR_MTF_QUEUE))
          printf("%u: #%u %u L%u D%02x: \"",(unsigned int)i,(unsigned int)sd[ranked_symbols[i]].inst_found,
              (unsigned int)sd[ranked_symbols[i]].count,(unsigned int)sd[ranked_symbols[i]].code_length,
              (unsigned int)sd[ranked_symbols[i]].type & 0xF4);
        else
          printf("%u: #%u L%u: \"",(unsigned int)i,(unsigned int)sd[ranked_symbols[i]].inst_found,
              (unsigned int)sd[ranked_symbols[i]].code_length);
        print_string(ranked_symbols[i]);
        printf("\"\n");
      }
    }
    else {
      for (i = 0 ; i < start_my_symbols + num_symbols_defined ; i++) {
        if (sd[i].inst_found != 0) {
          if ((sd[i].code_length >= 11) && (sd[i].inst_found > MAX_INSTANCES_FOR_MTF_QUEUE))
            printf("%u: #%u %u L%u D%02x: \"",(unsigned int)i,(unsigned int)sd[i].inst_found,
                (unsigned int)sd[i].count,(unsigned int)sd[i].code_length,(unsigned int)sd[i].type & 0xF4);
          else
            printf("%u: #%u L%u: \"",(unsigned int)i,(unsigned int)sd[i].inst_found,(unsigned int)sd[i].code_length);
          print_string(i);
          printf("\"\n");
        }
      }
    }
  }
  if (num_definitions_to_code == 0) {
    max_regular_code_length = 24;
    sd[ranked_symbols[0]].code_length = 25;
  }
  else if (sd[ranked_symbols[0]].count <= MAX_INSTANCES_FOR_MTF_QUEUE)
    max_regular_code_length = sd[ranked_symbols[0]].code_length - 1;

  sd[num_codes].type = 0;
  if (max_code_length >= 14) {
    i = 0;
    while ((i < num_definitions_to_code) && (sd[ranked_symbols[i]].count > MAX_INSTANCES_FOR_MTF_QUEUE)) {
      if (sd[ranked_symbols[i]].type & 0x20) {
        if (sd[ranked_symbols[i]].space_score > 0)
          sd[ranked_symbols[i]].type |= 0xC0;
        else
          sd[ranked_symbols[i]].type |= 0x40;
      }
      i++;
    }
    for (i = start_my_symbols ; i < num_codes; i++) {
      if (sd[i].type & 0x40) {
        uint32_t last_symbol = symbol_array[sd[i + 1].define_symbol_start_index - 2];
        while (last_symbol >= start_my_symbols) {
          if (sd[last_symbol].type & 0x80) {
            sd[i].type &= 0x3F;
            break;
          }
          last_symbol = symbol_array[sd[last_symbol + 1].define_symbol_start_index - 2];
        }
      }
    }
  }
  else {
    for (i = 0 ; i < num_definitions_to_code ; i++)
      sd[ranked_symbols[i]].type &= 0xF;
  }

  if (use_mtfg != 0) {
    if (max_regular_code_length >= 11) {
      for (i = 0 ; i < num_codes ; i++) {
        if ((sd[i].count > MAX_INSTANCES_FOR_MTF_QUEUE) && (sd[i].code_length >= 11)
            && (sd[i].hit_score > sd[i].count * (165 - 3 * max_regular_code_length) / 50))
          sd[i].type |= 4;
        else
          sd[i].type &= 0xFB;
      }
    }
    else {
      use_mtfg = 0;
      for (i = 0 ; i < num_codes ; i++)
        sd[i].type &= 0xFB;
    }
  }

  for (i = 0 ; i < num_codes ; i++)
    sd[i].inst_found = 0;
  symbol_ptr = symbol_array;
  prior_is_cap = 0;
  InitEncoder(max_regular_code_length, 
      MAX_INSTANCES_FOR_MTF_QUEUE + (uint32_t)(max_regular_code_length - sd[ranked_symbols[0]].code_length) + 1,
      cap_encoded, UTF8_compliant, use_mtf, use_mtfg);

  if (fd != 0) {
    if ((outbuf = (uint8_t *)malloc(in_size * 2 + 100000)) == 0) {
      fprintf(stderr,"Encoded data memory allocation failed\n");
      return(0);
    }
  }

  // HEADER:
  // BYTE 0:  4.0 * log2(file_size)
  // BYTE 1:  7=cap_encoded, 6=UTF8_compliant, 5=use_mtf, 4-0=max_code_length-1
  // BYTE 2:  7=M4D, 6=M3D, 5=use_delta, 4-0=min_code_length-1
  // BYTE 3:  7=M7D, 6=M6D, 5=M5D, 4-0=max_code_length-max_regular_code_length
  // BYTE 4:  7=M15D, 6=M14D, 5=M13D, 4=M12D, 3=M11D, 2=M10D, 1=M9D, 0=M8D
  // if UTF8_compliant
  // BYTE 5:  7-5=unused, 4-0=base_bits
  // else if use_delta
  //   if stride <= 4
  // BYTE 5:  7=0, 6-5=unused, 4=two channel, 3=little endian, 2=any endian, 1-0=stride-1
  //   else
  // BYTE 5:  7=1, 6-0=stride

  SetOutBuffer(outbuf);
  WriteOutCharNum(0);
  WriteOutBuffer((uint8_t)(4.0 * log2((double)file_size) + 1.0));
  WriteOutBuffer((cap_encoded << 7) | (UTF8_compliant << 6) | (use_mtf << 5) | (mtf_queue_miss_code_length[2] - 1));
  temp_char = (((format & 0xFE) != 0) << 5) | (sd[ranked_symbols[0]].code_length - 1);
  if (mtf_queue_miss_code_length[3] != mtf_queue_miss_code_length[2])
    temp_char |= 0x40;
  if (mtf_queue_miss_code_length[4] != mtf_queue_miss_code_length[3])
    temp_char |= 0x80;
  WriteOutBuffer(temp_char);
  i = 7;
  do {
    temp_char = (temp_char << 1) | (mtf_queue_miss_code_length[i] != mtf_queue_miss_code_length[i-1]);
  } while (--i != 4);
  WriteOutBuffer((temp_char << 5) | (mtf_queue_miss_code_length[2] - max_regular_code_length));
  i = 15;
  do {
    temp_char = (temp_char << 1) | (mtf_queue_miss_code_length[i] != mtf_queue_miss_code_length[i-1]);
  } while (--i != 7);
  WriteOutBuffer(temp_char);
  i = 0xFF;
  if (UTF8_compliant != 0) {
    WriteOutBuffer(base_bits);
    i = 0x90;
  }
  else if ((format & 0xFE) != 0) {
    if ((format & 0x80) == 0)
      WriteOutBuffer(((format & 0xF0) >> 2) | (((format & 0xE) >> 1) - 1));
    else
      WriteOutBuffer(format);
  }
  do {
    for (j = 2 ; j <= max_code_length ; j++) {
      sym_list_bits[i][j] = 2;
      if (0 == (sym_list_ptrs[i][j] = (uint32_t *)malloc(sizeof(uint32_t) * 4))) {
        fprintf(stderr,"FATAL ERROR - symbol list malloc failure\n");
        return(0);
      }
      nsob[i][j] = 0;
      nbob[i][j] = 0;
      fbob[i][j] = 0;
    }
    sum_nbob[i] = 0;
    bin_code_length[i] = max_code_length;
    symbol_lengths[i] = 0;
  } while (i--);
  found_first_symbol = 0;
  prior_end = 0;
  num_grammar_rules = 1;

#ifdef PRINTON
  fprintf(stderr,"\nuse_mtf %u, mcl %u mrcl %u \n",
      (unsigned int)use_mtf,(unsigned int)max_code_length,(unsigned int)max_regular_code_length);
#endif

  if ((UTF8_compliant != 0) || (cap_encoded != 0)) {
    cap_symbol_defined = 0;
    cap_lock_symbol_defined = 0;
    while (symbol_ptr < first_define_ptr) {
      symbol = *symbol_ptr++;
      symbol_count = sd[symbol].count;
      symbol_inst = sd[symbol].inst_found++;
      if (symbol_inst == 0) {
        if (embed_define(symbol, 0) == 0)
          return(0);
      }
      else if (symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf != 0) {
          if (manage_mtf_queue(symbol, symbol_inst, symbol_count, 0) == 0)
            return(0);
        }
        else
          manage_mtf_symbol(symbol, symbol_inst, symbol_count, 0);
        prior_symbol = symbol;
      }
      else {
        if ((sd[symbol].type & 8) != 0) {
          if (prior_is_cap == 0)
            manage_mtfg_queue(symbol, 0);
          else
            manage_mtfg_queue_prior_cap(symbol, 0);
        }
        else {
          if (prior_is_cap == 0)
            EncodeDictType(LEVEL0);
          else
            EncodeDictType(LEVEL0_CAP);
          encode_dictionary_symbol(symbol);
          if (sd[symbol].type & 4) {
            remove_dictionary_symbol(symbol, sd[symbol].code_length);
            add_symbol_to_mtfg_queue(symbol);
          }
        }
        prior_is_cap = sd[symbol].type & 1;
        prior_symbol = symbol;
      }
      prior_end = sd[symbol].ends;
#ifdef PRINTON
      if (((symbol_ptr - symbol_array) & 0x1FFFFF) == 0)
        fprintf(stderr,"Encoded %u of %u level 0 symbols\r",
            (unsigned int)(symbol_ptr - symbol_array),(unsigned int)(first_define_ptr - symbol_array));
#endif
    }
  }
  else {
    while (symbol_ptr < first_define_ptr) {
      symbol = *symbol_ptr++;
      symbol_count = sd[symbol].count;
      symbol_inst = sd[symbol].inst_found++;
      if (symbol_inst == 0) {
        if (embed_define_binary(symbol, 0) == 0)
          return(0);
      }
      else if (symbol_count <= MAX_INSTANCES_FOR_MTF_QUEUE) {
        if (use_mtf != 0) {
          if (manage_mtf_queue(symbol, symbol_inst, symbol_count, 0) == 0)
            return(0);
        }
        else
          manage_mtf_symbol(symbol, symbol_inst, symbol_count, 0);
      }
      else {
        if ((sd[symbol].type & 8) != 0)
          manage_mtfg_queue(symbol, 0);
        else {
          EncodeDictType(LEVEL0);
          encode_dictionary_symbol(symbol);
          if (sd[symbol].type & 4) {
            remove_dictionary_symbol(symbol, sd[symbol].code_length);
            add_symbol_to_mtfg_queue(symbol);
          }
        }
      }
      prior_end = sd[symbol].ends;
#ifdef PRINTON
      if (((symbol_ptr - symbol_array) & 0x1FFFFF) == 0)
        fprintf(stderr,"Encoded %u of %u level 0 symbols\r",
            (unsigned int)(symbol_ptr - symbol_array),(unsigned int)(first_define_ptr - symbol_array));
#endif
    }
  }

  // send EOF and flush output
  if (prior_is_cap == 0)
    EncodeDictType(LEVEL0);
  else
    EncodeDictType(LEVEL0_CAP);
  if (cap_encoded != 0) {
    if (sd[prior_symbol].type & 0x20) {
      if (sd[prior_symbol].type & 0x80)
        EncodeFirstChar(end_char, 2, prior_end);
      else if (sd[prior_symbol].type & 0x40)
        EncodeFirstChar(end_char, 3, prior_end);
      else
        EncodeFirstChar(end_char, 1, prior_end);
    }
    else
      EncodeFirstChar(end_char, 0, prior_end);
  }
  else if (UTF8_compliant != 0)
    EncodeFirstChar(end_char, 0, prior_end);
  else
    EncodeFirstCharBinary(end_char, prior_end);
  code_length = bin_code_length[end_char];
  if (max_code_length != code_length)
    EncodeLongDictionarySymbol(0, fbob[end_char][max_code_length], sum_nbob[end_char], max_code_length - code_length, 1);
  else {
    uint16_t bins_per_symbol
        = (nbob[end_char][code_length] >> (bin_code_length[end_char] - code_length)) / nsob[end_char][code_length];
    if ((nbob[end_char][code_length] >> (bin_code_length[end_char] - code_length))
        - nsob[end_char][code_length] * bins_per_symbol != 0)
      bins_per_symbol++;
    EncodeShortDictionarySymbol(fbob[end_char][max_code_length], sum_nbob[end_char], bins_per_symbol);
  }
  FinishEncoder();
  i = 0xFF;
  if (UTF8_compliant != 0)
    i = 0x90;
  do {
    for (j = 2 ; j <= max_code_length ; j++)
      free(sym_list_ptrs[i][j]);
  } while (i--);
  free(symbol_array);
  free(sd);
  free(ranked_symbols);
  *outsize_ptr = ReadOutCharNum();
  if (fd != 0) {
    size_t writesize = 0;
    while (*outsize_ptr - writesize > WRITE_SIZE) {
      fwrite(outbuf + writesize, 1, WRITE_SIZE, fd);
      writesize += WRITE_SIZE;
      fflush(fd);
    }
    fwrite(outbuf + writesize, 1, *outsize_ptr - writesize, fd);
    fflush(fd);
    free(outbuf);
  }
  return(1);
}
