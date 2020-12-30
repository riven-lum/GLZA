/***********************************************************************

Copyright 2014-2018 Kennon Conrad

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

// GLZAdecode.c
//   Decodes files created by GLZAencode

#include <inttypes.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "GLZA.h"
#include "GLZAmodel.h"

const uint32_t CHARS_TO_WRITE = 0x40000;
const uint32_t MAX_SYMBOLS_DEFINED = 0x00900000;
const uint32_t MAX_U32_VALUE = 0xFFFFFFFF;
const uint16_t FREE_SYMBOL_LIST_SIZE = 0x400;
const uint8_t FREE_SYMBOL_LIST_WAIT_SIZE = 0xFF;

uint32_t num_symbols_defined, symbol, num_base_symbols, dictionary_size, outbuf_index, queue_size, queue_size_cap;
uint32_t *symbol_buffer_write_ptr, *symbol_buffer_end_write_ptr, queue[0x100];
uint32_t free_symbol_list[0x400], free_symbol_list_wait1[0x100], free_symbol_list_wait2[0x100], symbol_buffer[0x800];
uint16_t free_symbol_list_length, sum_nbob[0x100];
uint8_t max_code_length, max_regular_code_length, min_code_length, find_first_symbol, UTF8_compliant, cap_encoded;
uint8_t use_mtf, two_threads, prior_is_cap, prior_end, write_cap_on, write_cap_lock_on, skip_space_on, delta_on;
uint8_t delta_format, stride, out_buffers_sent, cap_symbol_defined, cap_lock_symbol_defined, queue_offset;
uint8_t free_symbol_list_wait1_length, free_symbol_list_wait2_length;
uint8_t symbol_lengths[0x100], bin_code_length[0x100], lookup_bits[0x100][0x1000];
uint8_t out_char0[0x40064], out_char1[0x40064], temp_buf[0x30000], queue_miss_code_length[15];
uint8_t *out_char_ptr, *start_char_ptr, *end_outbuf, *outbuf, *symbol_strings;
atomic_uchar done_parsing, symbol_buffer_owner[2];
FILE * fd;


struct bin_data {
  uint32_t nsob;
  uint16_t nbob;
  uint16_t fbob;
  uint32_t * sym_list;
  uint32_t sym_list_size;
} bin_data[0x100][26];

struct sym_data {
  uint8_t type;  // bit 0: string starts a-z, bit1: nonergodic, bit2: wordness determined, bit3: sent mtf
  uint8_t type2; // 0: not a word, 1: word, 2: word & >= 15 repeats (ending sub)symbol & likely followed by ' ',
                 // 3: word & >= 15 repeats (ending sub)symbol
  uint8_t code_length;
  uint8_t repeats;
  uint8_t remaining;
  uint8_t starts;
  uint8_t ends;
  uint32_t string_index;
  uint32_t string_length;
  uint32_t dictionary_index;
} *symbol_data;


void dadd_dictionary_symbol(uint32_t index, uint8_t bits) {
  uint8_t first_char = symbol_data[index].starts;
  struct bin_data * bin_info = &bin_data[first_char][bits];
  if (bin_info->nsob == bin_info->sym_list_size) {
    bin_info->sym_list_size <<= 1;
    if (0 == (bin_info->sym_list
        = (uint32_t *)realloc(bin_info->sym_list, sizeof(uint32_t) * bin_info->sym_list_size))) {
      fprintf(stderr, "ERROR - memory allocation failed\n");
      exit(EXIT_FAILURE);
    }
  }
  symbol_data[index].dictionary_index = bin_info->nsob;
  bin_info->sym_list[bin_info->nsob] = index;
  if ((bin_info->nsob++ << (32 - bits)) == ((uint32_t)bin_info->nbob << (32 - bin_code_length[first_char]))) {
    if (bits >= bin_code_length[first_char]) { /* add one bin */
      bin_info->nbob++;
      if (sum_nbob[first_char] < 0x1000) {
        sum_nbob[first_char]++;
        if (bits != max_code_length) {
          lookup_bits[first_char][bin_data[first_char][bits + 1].fbob] = bits;
          while (++bits != max_code_length) {
            if (bin_data[first_char][bits].nbob != 0)
              lookup_bits[first_char][bin_data[first_char][bits + 1].fbob] = bits;
            bin_data[first_char][bits].fbob++;
          }
          bin_data[first_char][max_code_length].fbob++;
        }
      }
      else {
        bin_code_length[first_char]--;
        uint16_t first_max_code_length = bin_data[first_char][max_code_length].fbob;
        sum_nbob[first_char]
            = (bin_data[first_char][min_code_length].nbob = (bin_data[first_char][min_code_length].nbob + 1) >> 1);
        for (bits = min_code_length + 1 ; bits <= max_code_length ; bits++) {
          bin_data[first_char][bits].fbob = sum_nbob[first_char];
          sum_nbob[first_char] += (bin_data[first_char][bits].nbob = (bin_data[first_char][bits].nbob + 1) >> 1);
        }
        uint16_t bin = bin_data[first_char][min_code_length].fbob;
        for (bits = min_code_length ; bits < max_code_length ; bits++)
          while (bin < bin_data[first_char][bits + 1].fbob)
            lookup_bits[first_char][bin++] = bits;
        while (bin < first_max_code_length)
          lookup_bits[first_char][bin++] = max_code_length;
      }
    }
    else { /* add multiple bins */
      uint32_t new_bins = 1 << (bin_code_length[first_char] - bits);
      if (sum_nbob[first_char] + new_bins <= 0x1000) {
        bin_info->nbob += new_bins;
        sum_nbob[first_char] += new_bins;
        if (bits != max_code_length) {
          uint8_t code_length = max_code_length;
          do {
            bin_data[first_char][code_length--].fbob += new_bins;
            uint16_t bin;
            if (bin_data[first_char][code_length].nbob >= new_bins)
              for (bin = bin_data[first_char][code_length + 1].fbob - new_bins ;
                  bin < bin_data[first_char][code_length + 1].fbob ; bin++)
                lookup_bits[first_char][bin] = code_length;
            else
              for (bin = bin_data[first_char][code_length].fbob + new_bins ;
                  bin < bin_data[first_char][code_length].fbob + new_bins + bin_data[first_char][code_length].nbob ; bin++)
                lookup_bits[first_char][bin] = code_length;
          } while (code_length > bits);
        }
      }
      else if (new_bins <= 0x1000) {
        bin_info->nbob += new_bins;
        uint16_t first_max_code_length = bin_data[first_char][max_code_length].fbob;
        do {
          bin_code_length[first_char]--;
          sum_nbob[first_char]
              = (bin_data[first_char][min_code_length].nbob = (bin_data[first_char][min_code_length].nbob + 1) >> 1);
          for (bits = min_code_length + 1 ; bits <= max_code_length ; bits++)
            sum_nbob[first_char] += (bin_data[first_char][bits].nbob = (bin_data[first_char][bits].nbob + 1) >> 1);
        } while (sum_nbob[first_char] > 0x1000);
        uint16_t bin = bin_data[first_char][min_code_length].nbob;
        for (bits = min_code_length + 1 ; bits <= max_code_length ; bits++) {
          bin_data[first_char][bits].fbob = bin;
          bin += bin_data[first_char][bits].nbob;
        }
        bin = bin_data[first_char][min_code_length].fbob;
        for (bits = min_code_length ; bits < max_code_length ; bits++)
          while (bin < bin_data[first_char][bits + 1].fbob)
            lookup_bits[first_char][bin++] = bits;
        while (bin < first_max_code_length)
          lookup_bits[first_char][bin++] = max_code_length;
      }
      else if (sum_nbob[first_char] == 0) {
        uint8_t bin_shift = bin_code_length[first_char] - 12 - bits;
        bin_code_length[first_char] -= bin_shift;
        bin_info->nbob = (new_bins >>= bin_shift);
        sum_nbob[first_char] = new_bins;
        uint16_t bin = 0;
        while (bin < sum_nbob[first_char])
          lookup_bits[first_char][bin++] = bits;
        while (++bits <= max_code_length)
          bin_data[first_char][bits].fbob = sum_nbob[first_char];
      }
      else {
        uint16_t first_max_code_length = bin_data[first_char][max_code_length].fbob;
        uint8_t bin_shift = bin_code_length[first_char] - 11 - bits;
        bin_code_length[first_char] -= bin_shift;
        bin_data[first_char][min_code_length].nbob = ((bin_data[first_char][min_code_length].nbob - 1) >> bin_shift) + 1;
        sum_nbob[first_char] = bin_data[first_char][min_code_length].nbob;
        uint8_t code_length;
        for (code_length = min_code_length + 1 ; code_length <= max_code_length ; code_length++)
          sum_nbob[first_char]
              += bin_data[first_char][code_length].nbob = ((bin_data[first_char][code_length].nbob - 1) >> bin_shift) + 1;
        bin_info->nbob += (new_bins >>= bin_shift);
        sum_nbob[first_char] += new_bins;
        uint16_t bin = 0;
        for (bits = min_code_length + 1 ; bits <= max_code_length ; bits++)
          bin_data[first_char][bits].fbob = (bin += bin_data[first_char][bits - 1].nbob);
        bin = bin_data[first_char][min_code_length].fbob;
        for (bits = min_code_length ; bits < max_code_length ; bits++)
          while (bin < bin_data[first_char][bits + 1].fbob)
            lookup_bits[first_char][bin++] = bits;
        while (bin < first_max_code_length)
          lookup_bits[first_char][bin++] = max_code_length;
      }
    }
  }
  return;
}


void dremove_dictionary_symbol(uint32_t symbol) {
  struct bin_data * bin_info = &bin_data[symbol_data[symbol].starts][symbol_data[symbol].code_length];
  uint32_t last_symbol = bin_info->sym_list[--bin_info->nsob];
  bin_info->sym_list[symbol_data[symbol].dictionary_index] = last_symbol;
  symbol_data[last_symbol].dictionary_index = symbol_data[symbol].dictionary_index;
  return;
}


void dadd_symbol_to_queue(uint32_t symbol_number) {
  symbol_data[symbol_number].type |= 8;
  *(queue + --queue_offset) = symbol_number;
  if ((symbol_data[symbol_number].type & 1) != 0)
    queue_size_cap++;
  queue_size++;
  return;
}


uint32_t dupdate_queue(uint8_t queue_position) {
  uint32_t symbol_number;
  symbol_number = *(queue + (uint8_t)(queue_position + queue_offset));
  if ((symbol_data[symbol_number].repeats < MAX_INSTANCES_FOR_REMOVE) && (--symbol_data[symbol_number].remaining == 0)) {
    queue_size--;
    if ((symbol_data[symbol_number].type & 1) != 0)
      queue_size_cap--;
    if (queue_position <= (queue_size >> 1)) {
      while (queue_position != 0) {
        *(queue + (uint8_t)(queue_offset + queue_position)) = *(queue + (uint8_t)(queue_offset + queue_position - 1));
        queue_position--;
      }
      queue_offset++;
    }
    else {
      while (queue_position != queue_size) {
        *(queue + (uint8_t)(queue_offset + queue_position)) = *(queue + (uint8_t)(queue_offset + queue_position + 1));
        queue_position++;
      }
    }
    if (free_symbol_list_wait2_length < FREE_SYMBOL_LIST_WAIT_SIZE)
      free_symbol_list_wait2[free_symbol_list_wait2_length++] = symbol_number;
  }
  else if (DecodeGoMtf(symbol_data[symbol_number].repeats, 1) == 0) {
    queue_size--;
    if ((symbol_data[symbol_number].type & 1) != 0)
      queue_size_cap--;
    dadd_dictionary_symbol(symbol_number, symbol_data[symbol_number].code_length);
    if (queue_position <= (queue_size >> 1)) {
      queue_position += queue_offset;
      while (queue_position != queue_offset) {
        *(queue + queue_position) = *(queue + (uint8_t)(queue_position - 1));
        queue_position--;
      }
      queue_offset++;
    }
    else {
      queue_position += queue_offset;
      while (queue_position != (uint8_t)(queue_offset + queue_size)) {
        *(queue + queue_position) = *(queue + (uint8_t)(queue_position + 1));
        queue_position++;
      }
    }
  }
  else {
    if (queue_position <= (queue_size >> 1)) {
      queue_position += queue_offset;
      while (queue_position != queue_offset) {
        *(queue + queue_position) = *(queue + (uint8_t)(queue_position - 1));
        queue_position--;
      }
      *(queue + queue_offset) = symbol_number;
    }
    else {
      queue_position += queue_offset;
      while (queue_position != (uint8_t)(queue_offset + queue_size)) {
        *(queue + queue_position) = *(queue + (uint8_t)(queue_position + 1));
        queue_position++;
      }
      *(queue + --queue_offset) = symbol_number;
    }
  }
  return(symbol_number);
}


uint32_t get_queue_symbol_cap() {
  uint8_t queue_position = DecodeMtfPos(CAP, queue_size_cap);
  uint8_t find_caps = queue_position + 1;
  uint8_t cap_queue_position = queue_offset;
  do {
    if ((symbol_data[*(queue + cap_queue_position)].type & 1) != 0) {
      if (--find_caps == 0)
        return(dupdate_queue(queue_position));
    }
    else 
      queue_position++;
    cap_queue_position++;
  } while (1);
}


uint32_t get_dictionary_symbol(uint16_t bin_num, uint8_t code_length, uint8_t first_char) {
  uint32_t temp_index;
  uint16_t bins_per_symbol, extra_bins, end_extra_index;
  struct bin_data * bin_info = &bin_data[first_char][code_length];
  uint32_t num_symbols = bin_info->nsob;
  uint16_t num_bins = bin_info->nbob;
  uint32_t symbol_index = bin_num - bin_info->fbob;
  if (code_length > bin_code_length[first_char]) {
    uint32_t min_extra_reduce_index;
    int8_t index_bits = code_length - bin_code_length[first_char];
    uint32_t shifted_max_symbols = num_bins << (index_bits - 1);
    if (shifted_max_symbols >= num_symbols) {
      shifted_max_symbols >>= 1;
      while (shifted_max_symbols >= num_symbols) {
        shifted_max_symbols >>= 1;
        index_bits--;
      }
      if (--index_bits <= 0) {
        if (index_bits == 0) {
          extra_bins = num_bins - num_symbols;
          if (symbol_index >= 2 * extra_bins)
            symbol_index -= extra_bins;
          else {
            IncreaseRange(symbol_index & 1, 2);
            symbol_index >>= 1;
          }
        }
        else {
          bins_per_symbol = num_bins / num_symbols;
          extra_bins = num_bins - num_symbols * bins_per_symbol;
          end_extra_index = extra_bins * (bins_per_symbol + 1);
          if (symbol_index >= end_extra_index) {
            temp_index = symbol_index - end_extra_index;
            symbol_index = temp_index / bins_per_symbol;
            IncreaseRange(temp_index - symbol_index * bins_per_symbol, bins_per_symbol);
            symbol_index += extra_bins;
          }
          else {
            temp_index = symbol_index;
            symbol_index = temp_index / ++bins_per_symbol;
            IncreaseRange(temp_index - symbol_index * bins_per_symbol, bins_per_symbol);
          }
        }
        return(bin_info->sym_list[symbol_index]);
      }
    }
    min_extra_reduce_index = (num_symbols - shifted_max_symbols) << 1;
    symbol_index <<= index_bits;
    uint32_t bin_code = DecodeBinCode(index_bits);
    symbol_index += bin_code;
    if (symbol_index >= min_extra_reduce_index) {
      symbol_index = (symbol_index + min_extra_reduce_index) >> 1;
      IncreaseRange(bin_code & 1, 2);
    }
    return(bin_info->sym_list[symbol_index]);
  }
  uint8_t bin_shift = bin_code_length[first_char] - code_length;
  if ((num_symbols << bin_shift) == num_bins) {  // the bins are full
    temp_index = symbol_index;
    IncreaseRange(temp_index - ((symbol_index >>= bin_shift) << bin_shift), 1 << bin_shift);
    return(bin_info->sym_list[symbol_index]);
  }
  if (num_bins < 2 * num_symbols) {
    extra_bins = num_bins - num_symbols;
    if (symbol_index >= 2 * extra_bins)
      return(bin_info->sym_list[symbol_index - extra_bins]);
    IncreaseRange(symbol_index & 1, 2);
    return(bin_info->sym_list[symbol_index >> 1]);
  }
  bins_per_symbol = num_bins / num_symbols;
  extra_bins = num_bins - num_symbols * bins_per_symbol;
  end_extra_index = extra_bins * (bins_per_symbol + 1);
  if (symbol_index >= end_extra_index) {
    temp_index = symbol_index - end_extra_index;
    symbol_index = temp_index / bins_per_symbol;
    IncreaseRange(temp_index - symbol_index * bins_per_symbol, bins_per_symbol);
    symbol_index += extra_bins;
  }
  else {
    temp_index = symbol_index;
    symbol_index /= ++bins_per_symbol;
    IncreaseRange(temp_index - symbol_index * bins_per_symbol, bins_per_symbol);
  }
  return(bin_info->sym_list[symbol_index]);
}


uint32_t get_extra_length() {
  uint8_t extras = 0;
  uint32_t SymsInDef;
  uint8_t code;
  do {
    extras++;
    code = DecodeExtraLength();
  } while (code == 3);
  if (code == 2) {
    extras++;
    SymsInDef = 1;
  }
  else
    SymsInDef = 2 + code;
  while (--extras != 0)
    SymsInDef = (SymsInDef << 2) + DecodeExtraLength();
  return(SymsInDef + 14);
}


void delta_transform(uint8_t * buffer, uint32_t len) {
  uint8_t * char_ptr = buffer;
  if (delta_on == 0) {
    if (len > stride) {
      if (stride > 4) {
        char_ptr = buffer + 1;
        do {
          *char_ptr += *(char_ptr - 1);
        } while (++char_ptr < buffer + stride);
      }
      delta_on = 1;
      char_ptr = buffer + stride;
      len -= stride;
    }
    else {
      if (stride > 4) {
        char_ptr = buffer + 1;
        do {
          *char_ptr += *(char_ptr - 1);
        } while (++char_ptr < buffer + len);
      }
      else
        char_ptr = buffer + len;
      len = 0;
    }
  }
  if (stride == 1) {
    while (len-- != 0) {
      *char_ptr += *(char_ptr - 1);
      char_ptr++;
    }
  }
  else if (stride == 2) {
    while (len-- != 0) {
      if ((delta_format & 4) == 0) {
        *char_ptr += *(char_ptr - 2);
        char_ptr++;
      }
      else {
        char_ptr++;
        if (((char_ptr - buffer) & 1) == 0) {
          if ((delta_format & 8) == 0) {
            uint32_t value = (*(char_ptr - 4) << 8) + *(char_ptr - 3) + (*(char_ptr - 2) << 8) + *(char_ptr - 1) - 0x80;
            *(char_ptr - 2) = (value >> 8) & 0xFF;
            *(char_ptr - 1) = value & 0xFF;
          }
          else {
            uint32_t value = (*(char_ptr - 3) << 8) + *(char_ptr - 4) + (*(char_ptr - 1) << 8) + *(char_ptr - 2) - 0x80;
            *(char_ptr - 1) = (value >> 8) & 0xFF;
            *(char_ptr - 2) = value & 0xFF;
          }
        }
      }
    }
  }
  else if (stride == 3) {
    while (len-- != 0) {
      *char_ptr += *(char_ptr - 3);
      char_ptr++;
    }
  }
  else if (stride == 4) {
    while (len-- != 0) {
      char_ptr++;
      if ((delta_format & 4) == 0) {
        *(char_ptr - 1) += *(char_ptr - 5);
      }
      else if ((delta_format & 0x10) != 0) {
        if (((char_ptr - buffer) & 1) == 0) {
          if ((delta_format & 8) == 0) {
            uint32_t value = (*(char_ptr - 6) << 8) + *(char_ptr - 5) + (*(char_ptr - 2) << 8) + *(char_ptr - 1) - 0x80;
            *(char_ptr - 2) = (value >> 8) & 0xFF;
            *(char_ptr - 1) = value & 0xFF;
          }
          else {
            uint32_t value = (*(char_ptr - 5) << 8) + *(char_ptr - 6) + (*(char_ptr - 1) << 8) + *(char_ptr - 2) - 0x80;
            *(char_ptr - 1) = (value >> 8) & 0xFF;
            *(char_ptr - 2) = value & 0xFF;
          }
        }
      }
      else {
        if (((char_ptr - buffer) & 3) == 0) {
          if ((delta_format & 8) == 0) {
            uint32_t value = (*(char_ptr - 8) << 24) + (*(char_ptr - 7) << 16) + (*(char_ptr - 6) << 8) + *(char_ptr - 5)
                + (*(char_ptr - 4) << 24) + (*(char_ptr - 3) << 16) + (*(char_ptr - 2) << 8) + *(char_ptr - 1) - 0x808080;
            *(char_ptr - 4) = value >> 24;
            *(char_ptr - 3) = (value >> 16) & 0xFF;
            *(char_ptr - 2) = (value >> 8) & 0xFF;
            *(char_ptr - 1) = value & 0xFF;
          }
          else {
            uint32_t value = (*(char_ptr - 5) << 24) + (*(char_ptr - 6) << 16) + (*(char_ptr - 7) << 8) + *(char_ptr - 8)
                + (*(char_ptr - 1) << 24) + (*(char_ptr - 2) << 16) + (*(char_ptr - 3) << 8) + *(char_ptr - 4) - 0x808080;
            *(char_ptr - 1) = value >> 24;
            *(char_ptr - 2) = (value >> 16) & 0xFF;
            *(char_ptr - 3) = (value >> 8) & 0xFF;
            *(char_ptr - 4) = value & 0xFF;
          }
        }
      }
    }
  }
  else {
    while (len-- != 0) {
      *char_ptr += *(char_ptr - stride);
      char_ptr++;
    }
  }
}


uint8_t create_extended_UTF8_symbol(uint32_t base_symbol, uint32_t * string_index_ptr) {
  if (base_symbol < START_UTF8_3BYTE_SYMBOLS) {
    symbol_strings[(*string_index_ptr)++] = (uint8_t)(base_symbol >> 6) + 0xC0;
    symbol_strings[(*string_index_ptr)++] = (uint8_t)(base_symbol & 0x3F) + 0x80;
    if (base_symbol < 0x250)
      return(0x80);
    else if (base_symbol < 0x370)
      return(0x81);
    else if (base_symbol < 0x400)
      return(0x82);
    else if (base_symbol < 0x530)
      return(0x83);
    else if (base_symbol < 0x590)
      return(0x84);
    else if (base_symbol < 0x600)
      return(0x85);
    else if (base_symbol < 0x700)
      return(0x86);
    else
      return(0x87);
  }
  else if (base_symbol < START_UTF8_4BYTE_SYMBOLS) {
    symbol_strings[(*string_index_ptr)++] = (uint8_t)(base_symbol >> 12) + 0xE0;
    symbol_strings[(*string_index_ptr)++] = (uint8_t)((base_symbol >> 6) & 0x3F) + 0x80;
    symbol_strings[(*string_index_ptr)++] = (uint8_t)(base_symbol & 0x3F) + 0x80;
    if (base_symbol < 0x1000)
      return(0x88);
    else if (base_symbol < 0x2000)
      return(0x89);
    else if (base_symbol < 0x3000)
      return(0x8A);
    else if (base_symbol < 0x3040)
      return(0x8B);
    else if (base_symbol < 0x30A0)
      return(0x8C);
    else if (base_symbol < 0x3100)
      return(0x8D);
    else if (base_symbol < 0x3200)
      return(0x8E);
    else if (base_symbol < 0xA000)
      return(0x8F);
    else
      return(0x8E);
  }
  else {
    symbol_strings[(*string_index_ptr)++] = (uint8_t)(base_symbol >> 18) + 0xF0;
    symbol_strings[(*string_index_ptr)++] = (uint8_t)((base_symbol >> 12) & 0x3F) + 0x80;
    symbol_strings[(*string_index_ptr)++] = (uint8_t)((base_symbol >> 6) & 0x3F) + 0x80;
    symbol_strings[(*string_index_ptr)++] = (uint8_t)(base_symbol & 0x3F) + 0x80;
    return(0x90);
  }
}


uint8_t get_first_char(uint32_t symbol) {
  uint32_t index = symbol_data[symbol].string_index;
  uint32_t UTF8_chars = (symbol_strings[index] << 8) + symbol_strings[index + 1];
  if (UTF8_chars < 0xE000) {
    if (UTF8_chars < 0xC990)
      return(0x80);
    else if (UTF8_chars < 0xCDB0)
      return(0x81);
    else if (UTF8_chars < 0xD000)
      return(0x82);
    else if (UTF8_chars < 0xD4B0)
      return(0x83);
    else if (UTF8_chars < 0xD690)
      return(0x84);
    else if (UTF8_chars < 0xD800)
      return(0x85);
    else if (UTF8_chars < 0xDC00)
      return(0x86);
    else
      return(0x87);
  }
  else if (UTF8_chars < 0xE100)
    return(0x88);
  else if (UTF8_chars < 0xE200)
    return(0x89);
  else if (UTF8_chars < 0xE300)
    return(0x8A);
  else if (UTF8_chars < 0xE381)
    return(0x8B);
  else {
    UTF8_chars = (UTF8_chars << 8) + symbol_strings[index + 2];
    if (UTF8_chars < 0xE382A0)
      return(0x8C);
    else if (UTF8_chars < 0xE38400)
      return(0x8D);
    else if (UTF8_chars < 0xE38800)
      return(0x8E);
    else if (UTF8_chars < 0xEA0000)
      return(0x8F);
    else if (UTF8_chars < 0xF00000)
      return(0x8E);
    else
      return(0x90);
  }
}


void decode_new(uint32_t * symbol_number_ptr, uint32_t * define_string_index_ptr) {
  uint8_t new_symbol_code_length, SID_symbol, repeats, sym_type;
  uint32_t symbols_in_definition;
  uint32_t symbol_number = *symbol_number_ptr;
  uint32_t define_string_index = *define_string_index_ptr;
  uint32_t end_define_string_index = define_string_index;

  SID_symbol = DecodeSID(NOT_CAP);
  if (SID_symbol == 0) {
    repeats = DecodeINST(NOT_CAP, SID_symbol);
    if (repeats < MAX_INSTANCES_FOR_REMOVE - 1)
      new_symbol_code_length = queue_miss_code_length[++repeats];
    else if (repeats >= MAX_INSTANCES_FOR_REMOVE) {
      new_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_REMOVE - repeats;
      repeats = new_symbol_code_length + MAX_INSTANCES_FOR_REMOVE - 1;
    }
    else {
      repeats = 0;
      new_symbol_code_length = 0x20;
    }

    uint32_t base_symbol = DecodeBaseSymbol(num_base_symbols);
    if ((UTF8_compliant == 0) || (base_symbol < START_UTF8_2BYTE_SYMBOLS)) {
      if ((base_symbol & 1) != 0) {
        if (symbol_lengths[base_symbol] != 0) {
          base_symbol--;
          DoubleRangeDown();
        }
        else if (symbol_lengths[base_symbol - 1] != 0)
          DoubleRangeDown();
      }
      else if (symbol_lengths[base_symbol] != 0) {
        base_symbol++;
        DoubleRange();
      }
      else if (symbol_lengths[base_symbol + 1] != 0)
        DoubleRange();
    }

    if (free_symbol_list_length == 0)
      symbol_number = num_symbols_defined++;
    else
      symbol_number = free_symbol_list[--free_symbol_list_length];
    symbol_data[symbol_number].string_index = define_string_index;
    symbol_data[symbol_number].string_length = 1;
    symbol_data[symbol_number].type = 0;
    if (UTF8_compliant != 0) {
      if (base_symbol < START_UTF8_2BYTE_SYMBOLS) {
        symbol_strings[end_define_string_index++]
            = symbol_data[symbol_number].starts = symbol_data[symbol_number].ends = prior_end = (uint8_t)base_symbol;
        symbol_lengths[prior_end] = new_symbol_code_length;
        uint8_t j1 = 0x90;
        do {
          InitFirstCharBin(j1, prior_end, new_symbol_code_length, cap_symbol_defined, cap_lock_symbol_defined);
        } while (j1-- != 0);
        j1 = 0x90;
        do {
          if (symbol_lengths[j1] != 0)
            InitTrailingCharBin(prior_end, j1, symbol_lengths[j1]);
        } while (j1-- != 0);
      }
      else {
        prior_end = create_extended_UTF8_symbol(base_symbol, &end_define_string_index);
        symbol_data[symbol_number].starts = symbol_data[symbol_number].ends = prior_end;
        if (symbol_lengths[prior_end] == 0) {
          symbol_lengths[prior_end] = new_symbol_code_length;
          uint8_t j1 = 0x90;
          do {
            InitFirstCharBin(j1, prior_end, new_symbol_code_length, cap_symbol_defined, cap_lock_symbol_defined);
          } while (j1-- != 0);
          j1 = 0x90;
          do {
            if (symbol_lengths[j1] != 0)
              InitTrailingCharBin(prior_end, j1, symbol_lengths[j1]);
          } while (j1-- != 0);
          InitFreqFirstChar(prior_end, prior_end);
        }
      }
    }
    else {
      symbol_strings[end_define_string_index++]
          = symbol_data[symbol_number].starts = symbol_data[symbol_number].ends = prior_end = (uint8_t)base_symbol;
      symbol_lengths[prior_end] = new_symbol_code_length;
      uint8_t j1 = 0xFF;
      do {
        InitFirstCharBinBinary(j1, prior_end, new_symbol_code_length);
      } while (j1-- != 0);
      InitTrailingCharBinary(prior_end, symbol_lengths);
    }

    if (find_first_symbol != 0) {
      find_first_symbol = 0;
      sum_nbob[prior_end] = bin_data[prior_end][max_code_length].nbob = 1;
    }

    if (repeats == 0) {
      symbol_data[num_symbols_defined].string_index = end_define_string_index;
      *define_string_index_ptr = end_define_string_index;
      *symbol_number_ptr = symbol_number;
      return;
    }
    if (repeats < MAX_INSTANCES_FOR_REMOVE) {
      if ((use_mtf != 0) && (DecodeERG(repeats + 2) != 0)) {
        symbol_data[symbol_number].type = 2;
        if ((repeats == 1) || (DecodeGoMtf(repeats, 2) != 0))
          dadd_symbol_to_queue(symbol_number);
        else
          dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
      }
      else
        dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
    }
    else {
      if ((new_symbol_code_length >= 11) && (use_mtf != 0) && (DecodeERG(0) != 0)) {
        symbol_data[symbol_number].type = 2;
        if (DecodeGoMtf(repeats, 2) != 0)
          dadd_symbol_to_queue(symbol_number);
        else
          dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
      }
      else
        dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
    }
  }
  else {
    symbols_in_definition = SID_symbol + 1;
    if (symbols_in_definition == 16)
      symbols_in_definition = get_extra_length();

    do { // Build the symbol string from the next symbols_in_definition symbols
      if ((sym_type = DecodeSymType(LEVEL1)) == 0) {
        uint8_t first_char;
        if (UTF8_compliant != 0)
          first_char = DecodeFirstChar(0, prior_end);
        else
          first_char = DecodeFirstCharBinary(prior_end);
        uint16_t bin_num = DecodeBin(sum_nbob[first_char]);
        uint8_t code_length = lookup_bits[first_char][bin_num];
        symbol_number = get_dictionary_symbol(bin_num, code_length, first_char);
        if (symbol_data[symbol_number].remaining < MAX_INSTANCES_FOR_REMOVE) {
          if (--symbol_data[symbol_number].remaining == 0) {
            dremove_dictionary_symbol(symbol_number);
            if (free_symbol_list_wait2_length < FREE_SYMBOL_LIST_WAIT_SIZE)
              free_symbol_list_wait2[free_symbol_list_wait2_length++] = symbol_number;
          }
          else if (((symbol_data[symbol_number].type & 2) != 0)
              && (((symbol_data[symbol_number].remaining == 1) && ((symbol_data[symbol_number].type & 8) == 0))
                || (DecodeGoMtf(symbol_data[symbol_number].repeats, 0) != 0))) {
            dremove_dictionary_symbol(symbol_number);
            dadd_symbol_to_queue(symbol_number);
          }
        }
        else if (((symbol_data[symbol_number].type & 2) != 0)
            && (DecodeGoMtf(symbol_data[symbol_number].remaining, 0) != 0)) {
          dremove_dictionary_symbol(symbol_number);
          dadd_symbol_to_queue(symbol_number);
        }
        prior_end = symbol_data[symbol_number].ends;
        uint8_t * symbol_string_ptr = &symbol_strings[symbol_data[symbol_number].string_index];
        uint8_t * end_symbol_string_ptr = symbol_string_ptr + symbol_data[symbol_number].string_length;
        do {
          symbol_strings[end_define_string_index++] = *symbol_string_ptr++;
        } while (symbol_string_ptr != end_symbol_string_ptr);
      }
      else if (sym_type == 1)
        decode_new(&symbol_number, &end_define_string_index);
      else {
        symbol_number = dupdate_queue(DecodeMtfPos(NOT_CAP, queue_size));
        prior_end = symbol_data[symbol_number].ends;
        uint8_t * symbol_string_ptr = &symbol_strings[symbol_data[symbol_number].string_index];
        uint8_t * end_symbol_string_ptr = symbol_string_ptr + symbol_data[symbol_number].string_length;
        do {
          symbol_strings[end_define_string_index++] = *symbol_string_ptr++;
        } while (symbol_string_ptr != end_symbol_string_ptr);
      }
    } while (--symbols_in_definition);
    if (free_symbol_list_length == 0)
      symbol_number = num_symbols_defined++;
    else
      symbol_number = free_symbol_list[--free_symbol_list_length];
    symbol_data[symbol_number].string_index = define_string_index;
    if ((symbol_strings[*define_string_index_ptr] < 0x80) || (UTF8_compliant == 0))
      symbol_data[symbol_number].starts = symbol_strings[*define_string_index_ptr];
    else
      symbol_data[symbol_number].starts = get_first_char(symbol_number);
    symbol_data[symbol_number].ends = prior_end;
    symbol_data[symbol_number].string_length = end_define_string_index - define_string_index;

    repeats = DecodeINST(NOT_CAP, SID_symbol);
    if (repeats <= MAX_INSTANCES_FOR_REMOVE - 2) {
      new_symbol_code_length = queue_miss_code_length[++repeats];
      if ((use_mtf != 0) && (DecodeERG(repeats + 2) != 0)) {
        symbol_data[symbol_number].type = 2;
        if ((repeats == 1) || (DecodeGoMtf(repeats, 2) != 0))
          dadd_symbol_to_queue(symbol_number);
        else
          dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
      }
      else {
        symbol_data[symbol_number].type = 0;
        dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
      }
    }
    else {
      new_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_REMOVE - 1 - repeats;
      repeats = new_symbol_code_length + MAX_INSTANCES_FOR_REMOVE - 1;
      if ((new_symbol_code_length >= 11) && (use_mtf != 0) && (DecodeERG(0) != 0)) {
        symbol_data[symbol_number].type = 2;
        if (DecodeGoMtf(repeats, 2) != 0)
          dadd_symbol_to_queue(symbol_number);
        else
          dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
      }
      else {
        symbol_data[symbol_number].type = 0;
        dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
      }
    }
  }
  symbol_data[symbol_number].code_length = new_symbol_code_length;
  symbol_data[symbol_number].repeats = repeats;
  symbol_data[symbol_number].remaining = repeats;
  symbol_data[num_symbols_defined].string_index = end_define_string_index;
  *define_string_index_ptr = end_define_string_index;
  *symbol_number_ptr = symbol_number;
  return;
}


void decode_new_cap_encoded(uint32_t * symbol_number_ptr, uint32_t * define_string_index_ptr) {
  uint8_t new_symbol_code_length, SID_symbol, repeats, sym_type, saved_prior_is_cap;
  uint8_t tag_type = 0;
  uint32_t symbols_in_definition;
  uint32_t symbol_number = *symbol_number_ptr;
  uint32_t define_string_index = *define_string_index_ptr;
  uint32_t end_define_string_index = define_string_index;

  SID_symbol = DecodeSID(prior_is_cap);
  if (SID_symbol == 0) {
    repeats = DecodeINST(prior_is_cap, SID_symbol);
    if (repeats < MAX_INSTANCES_FOR_REMOVE - 1) {
      new_symbol_code_length = queue_miss_code_length[++repeats];
    }
    else if (repeats >= MAX_INSTANCES_FOR_REMOVE) {
      new_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_REMOVE - repeats;
      repeats = new_symbol_code_length + MAX_INSTANCES_FOR_REMOVE - 1;
    }
    else {
      repeats = 0;
      new_symbol_code_length = 0x20;
    }

    uint32_t base_symbol = DecodeBaseSymbolCap(num_base_symbols);
    if (base_symbol > 0x42)
      base_symbol += 24;
    else if (base_symbol > 0x40)
      base_symbol += 1;

    if (free_symbol_list_length == 0)
      symbol_number = num_symbols_defined++;
    else
      symbol_number = free_symbol_list[--free_symbol_list_length];
    symbol_data[symbol_number].string_index = define_string_index;
    symbol_data[symbol_number].type = 0;
    symbol_data[symbol_number].type2 = 0;
    prior_is_cap = 0;

    if ((UTF8_compliant == 0) || (base_symbol < START_UTF8_2BYTE_SYMBOLS)) {
      if ((base_symbol & 1) != 0) {
        if (symbol_lengths[base_symbol] != 0) {
          base_symbol--;
          DoubleRangeDown();
        }
        else if (symbol_lengths[base_symbol - 1] != 0)
          DoubleRangeDown();
      }
      else if (symbol_lengths[base_symbol] != 0) {
        base_symbol++;
        DoubleRange();
      }
      else if (symbol_lengths[base_symbol + 1] != 0)
        DoubleRange();

      symbol_lengths[base_symbol] = new_symbol_code_length;
      InitBaseSymbolCap(base_symbol, new_symbol_code_length, &cap_symbol_defined, &cap_lock_symbol_defined,
          symbol_lengths);
      symbol_strings[end_define_string_index++]
          = symbol_data[symbol_number].starts = symbol_data[symbol_number].ends = prior_end = base_symbol;
      symbol_data[symbol_number].string_length = 1;

      if (prior_end < START_UTF8_2BYTE_SYMBOLS) {
        if (base_symbol == 'C') {
          symbol_data[symbol_number].type = 4;
          prior_is_cap = 1;
        }
        else if (base_symbol == 'B') {
          symbol_data[symbol_number].type = 4;
          prior_is_cap = 1;
          symbol_data[symbol_number].ends = prior_end = 'C';
        }
        else {
          if (base_symbol == ' ')
            symbol_data[symbol_number].type = 4;
          else if ((base_symbol >= 0x61) && (base_symbol <= 0x7A))
            symbol_data[symbol_number].type = 1;
        }
      }
    }
    else {
      prior_end = create_extended_UTF8_symbol(base_symbol, &end_define_string_index);
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
          if (symbol_lengths[j1] != 0)
            InitTrailingCharBin(prior_end, j1, symbol_lengths[j1]);
        } while (j1-- != 0);
      }
      symbol_data[symbol_number].starts = symbol_data[symbol_number].ends = prior_end;
      symbol_data[symbol_number].string_length = end_define_string_index - define_string_index;
    }

    if (find_first_symbol != 0) {
      find_first_symbol = 0;
      sum_nbob[prior_end] = bin_data[prior_end][max_code_length].nbob = 1;
    }
    if (repeats == 0) {
      symbol_data[num_symbols_defined].string_index = end_define_string_index;
      *define_string_index_ptr = end_define_string_index;
      *symbol_number_ptr = symbol_number;
      return;
    }

    if (repeats < MAX_INSTANCES_FOR_REMOVE) {
      if ((use_mtf != 0) && (DecodeERG(repeats + 2) != 0)) {
        symbol_data[symbol_number].type |= 2;
        if ((repeats == 1) || (DecodeGoMtf(repeats, 2) != 0))
          dadd_symbol_to_queue(symbol_number);
        else
          dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
      }
      else
        dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
    }
    else {
      if ((new_symbol_code_length >= 11) && (use_mtf != 0) && (DecodeERG(tag_type) != 0)) {
        symbol_data[symbol_number].type |= 2;
        if (DecodeGoMtf(repeats, 2) != 0)
          dadd_symbol_to_queue(symbol_number);
        else
          dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
      }
      else
        dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
    }
  }
  else {
    symbols_in_definition = SID_symbol + 1;
    if (symbols_in_definition == 16)
      symbols_in_definition = get_extra_length();
    saved_prior_is_cap = prior_is_cap;

    do { // Build the symbol string from the next symbols_in_definition symbols
      if (prior_is_cap == 0) {
        if ((sym_type = DecodeSymType(LEVEL1)) == 0) {
          uint8_t first_char;
          if (prior_end != 0xA)
            first_char = DecodeFirstChar(symbol_data[symbol_number].type2, prior_end);
          else
            first_char = 0x20;
          uint16_t bin_num = DecodeBin(sum_nbob[first_char]);
          uint8_t code_length = lookup_bits[first_char][bin_num];
          symbol_number = get_dictionary_symbol(bin_num, code_length, first_char);
          if (symbol_data[symbol_number].remaining < MAX_INSTANCES_FOR_REMOVE) {
            if (--symbol_data[symbol_number].remaining == 0) {
              dremove_dictionary_symbol(symbol_number);
              if (free_symbol_list_wait2_length < FREE_SYMBOL_LIST_WAIT_SIZE)
                free_symbol_list_wait2[free_symbol_list_wait2_length++] = symbol_number;
            }
            else if (((symbol_data[symbol_number].type & 2) != 0)
                && (((symbol_data[symbol_number].remaining == 1) && ((symbol_data[symbol_number].type & 8) == 0))
                  || (DecodeGoMtf(symbol_data[symbol_number].repeats, 0) != 0))) {
              dremove_dictionary_symbol(symbol_number);
              dadd_symbol_to_queue(symbol_number);
            }
          }
          else if (((symbol_data[symbol_number].type & 2) != 0)
              && (DecodeGoMtf(symbol_data[symbol_number].remaining, 0) != 0)) {
            dremove_dictionary_symbol(symbol_number);
            dadd_symbol_to_queue(symbol_number);
          }
          prior_is_cap = ((prior_end = symbol_data[symbol_number].ends) == 'C');
          uint8_t * symbol_string_ptr = &symbol_strings[symbol_data[symbol_number].string_index];
          uint8_t * end_symbol_string_ptr = symbol_string_ptr + symbol_data[symbol_number].string_length;
          do {
            symbol_strings[end_define_string_index++] = *symbol_string_ptr++;
          } while (symbol_string_ptr != end_symbol_string_ptr);
        }
        else if (sym_type == 1)
          decode_new_cap_encoded(&symbol_number, &end_define_string_index);
        else {
          symbol_number = dupdate_queue(DecodeMtfPos(NOT_CAP, queue_size));
          prior_is_cap = ((prior_end = symbol_data[symbol_number].ends) == 'C');
          uint8_t * symbol_string_ptr = &symbol_strings[symbol_data[symbol_number].string_index];
          uint8_t * end_symbol_string_ptr = symbol_string_ptr + symbol_data[symbol_number].string_length;
          do {
            symbol_strings[end_define_string_index++] = *symbol_string_ptr++;
          } while (symbol_string_ptr != end_symbol_string_ptr);
        }
      }
      else { // prior_is_cap
        if ((sym_type = DecodeSymType(LEVEL1_CAP)) == 0) {
          uint8_t first_char = DecodeFirstChar(0, 'C');
          uint16_t bin_num = DecodeBin(sum_nbob[first_char]);
          uint8_t code_length = lookup_bits[first_char][bin_num];
          symbol_number = get_dictionary_symbol(bin_num, code_length, first_char);
          if ((symbol_data[symbol_number].repeats < MAX_INSTANCES_FOR_REMOVE)
              && (--symbol_data[symbol_number].remaining == 0)) {
            dremove_dictionary_symbol(symbol_number);
            if (free_symbol_list_wait2_length < FREE_SYMBOL_LIST_WAIT_SIZE)
              free_symbol_list_wait2[free_symbol_list_wait2_length++] = symbol_number;
          }
          else if (((symbol_data[symbol_number].type & 2) != 0)
              && (((symbol_data[symbol_number].repeats < MAX_INSTANCES_FOR_REMOVE)
                  && (symbol_data[symbol_number].remaining == 1) && ((symbol_data[symbol_number].type & 8) == 0))
                || (DecodeGoMtf(symbol_data[symbol_number].repeats, 0) != 0))) {
            dremove_dictionary_symbol(symbol_number);
            dadd_symbol_to_queue(symbol_number);
          }
          prior_is_cap = ((prior_end = symbol_data[symbol_number].ends) == 'C');
          uint8_t * symbol_string_ptr = &symbol_strings[symbol_data[symbol_number].string_index];
          uint8_t * end_symbol_string_ptr = symbol_string_ptr + symbol_data[symbol_number].string_length;
          do {
            symbol_strings[end_define_string_index++] = *symbol_string_ptr++;
          } while (symbol_string_ptr != end_symbol_string_ptr);
        }
        else if (sym_type == 1)
          decode_new_cap_encoded(&symbol_number, &end_define_string_index);
        else {
          symbol_number = get_queue_symbol_cap();
          prior_is_cap = ((prior_end = symbol_data[symbol_number].ends) == 'C');
          uint8_t * symbol_string_ptr = &symbol_strings[symbol_data[symbol_number].string_index];
          uint8_t * end_symbol_string_ptr = symbol_string_ptr + symbol_data[symbol_number].string_length;
          do {
            symbol_strings[end_define_string_index++] = *symbol_string_ptr++;
          } while (symbol_string_ptr != end_symbol_string_ptr);
        }
      }
    } while (--symbols_in_definition != 0);

    uint32_t last_symbol_number = symbol_number;
    if (free_symbol_list_length == 0)
      symbol_number = num_symbols_defined++;
    else
      symbol_number = free_symbol_list[--free_symbol_list_length];
    symbol_data[symbol_number].type2 = 0;
    symbol_data[symbol_number].ends = prior_end;
    symbol_data[symbol_number].string_length = end_define_string_index - define_string_index;
    symbol_data[symbol_number].string_index = define_string_index;
    if ((symbol_strings[define_string_index] < 0x80) || (UTF8_compliant == 0)) {
      symbol_data[symbol_number].starts = symbol_strings[define_string_index];
      symbol_data[symbol_number].type = ((symbol_strings[define_string_index] >= 'a')
          && (symbol_strings[define_string_index] <= 'z'));
    }
    else {
      symbol_data[symbol_number].starts = get_first_char(symbol_number);
      symbol_data[symbol_number].type = 0;
    }

    repeats = DecodeINST(saved_prior_is_cap, SID_symbol);
    if (repeats <= MAX_INSTANCES_FOR_REMOVE - 2) {
      new_symbol_code_length = queue_miss_code_length[++repeats];
      if ((symbol_data[last_symbol_number].type & 4) != 0) {
        symbol_data[symbol_number].type |= 4;
        symbol_data[symbol_number].type2 = symbol_data[last_symbol_number].type2;
      }
      else if (max_code_length >= 14) {
        uint8_t * symbol_string_ptr = &symbol_strings[end_define_string_index - 2];
        do {
          if (*symbol_string_ptr == ' ') {
            symbol_data[symbol_number].type |= 4;
            symbol_data[symbol_number].type2 = 1;
            break;
          }
        } while (symbol_string_ptr-- != &symbol_strings[define_string_index]);
      }
      if ((use_mtf != 0) && (DecodeERG(repeats + 2) != 0)) {
        symbol_data[symbol_number].type |= 2;
        if ((repeats == 1) || (DecodeGoMtf(repeats, 2) != 0))
          dadd_symbol_to_queue(symbol_number);
        else
          dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
      }
      else
        dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
    }
    else {
      new_symbol_code_length = max_regular_code_length + MAX_INSTANCES_FOR_REMOVE - 1 - repeats;
      repeats = new_symbol_code_length + MAX_INSTANCES_FOR_REMOVE - 1;
      if ((symbol_data[last_symbol_number].type & 4) != 0) {
        symbol_data[symbol_number].type |= 4;
        symbol_data[symbol_number].type2 = symbol_data[last_symbol_number].type2;
        if (((symbol_data[last_symbol_number].type2 & 1) != 0) && (repeats >= MAX_INSTANCES_FOR_REMOVE)) {
          tag_type = 1 + DecodeWordTag();
          symbol_data[symbol_number].type2 = 4 - tag_type;
        }
      }
      else if (max_code_length >= 14) {
        uint8_t * symbol_string_ptr = &symbol_strings[end_define_string_index - 2];
        do {
          if (*symbol_string_ptr == ' ') {
            symbol_data[symbol_number].type |= 4;
            symbol_data[symbol_number].type2 = 1;
            if (repeats >= MAX_INSTANCES_FOR_REMOVE) {
              tag_type = 1 + DecodeWordTag();
              symbol_data[symbol_number].type2 = 4 - tag_type;
            }
            break;
          }
        } while (symbol_string_ptr-- != &symbol_strings[define_string_index]);
      }
      if ((new_symbol_code_length >= 11) && (use_mtf != 0) && (DecodeERG(tag_type) != 0)) {
        symbol_data[symbol_number].type |= 2;
        if (DecodeGoMtf(repeats, 2) != 0)
          dadd_symbol_to_queue(symbol_number);
        else
          dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
      }
      else
        dadd_dictionary_symbol(symbol_number, new_symbol_code_length);
    }
  }
  symbol_data[symbol_number].code_length = new_symbol_code_length;
  symbol_data[symbol_number].repeats = repeats;
  symbol_data[symbol_number].remaining = repeats;
  symbol_data[num_symbols_defined].string_index = end_define_string_index;
  *define_string_index_ptr = end_define_string_index;
  *symbol_number_ptr = symbol_number;
  return;
}


void transpose2(uint8_t * buffer, uint32_t len) {
  uint8_t *char_ptr, *char2_ptr;
  uint32_t block1_len = len - (len >> 1);
  memcpy(temp_buf, buffer + block1_len, len - block1_len);
  char2_ptr = buffer + 2 * block1_len;
  char_ptr = buffer + block1_len;
  while (char_ptr != buffer) {
    char2_ptr -= 2;
    *char2_ptr = *--char_ptr;
  }
  char2_ptr = buffer + 1;
  char_ptr = temp_buf;
  while (char2_ptr < buffer + len) {
    *char2_ptr = *char_ptr++;
    char2_ptr += 2;
  }
  return;
}


void transpose4(uint8_t * buffer, uint32_t len) {
  uint8_t *char_ptr, *char2_ptr;
  uint32_t block1_len = (len + 3) >> 2;
  memcpy(temp_buf, buffer + block1_len, len - block1_len);
  char2_ptr = buffer + 4 * block1_len;
  char_ptr = buffer + block1_len;
  while (char_ptr != buffer) {
    char2_ptr -= 4;
    *char2_ptr = *--char_ptr;
  }
  char2_ptr = buffer + 1;
  char_ptr = temp_buf;
  while (char2_ptr < buffer + len) {
    *char2_ptr = *char_ptr++;
    char2_ptr += 4;
  }
  char2_ptr = buffer + 2;
  while (char2_ptr < buffer + len) {
    *char2_ptr = *char_ptr++;
    char2_ptr += 4;
  }
  char2_ptr = buffer + 3;
  while (char2_ptr < buffer + len) {
    *char2_ptr = *char_ptr++;
    char2_ptr += 4;
  }
  return;
}


void write_output_buffer() {
  uint32_t chars_to_write = out_char_ptr - start_char_ptr;
  if (fd != 0) {
    fflush(fd);
    fwrite(start_char_ptr, 1, chars_to_write, fd);
    if ((out_buffers_sent & 1) == 0)
      out_char_ptr = out_char1;
    else
      out_char_ptr = out_char0;
  }
  outbuf_index += chars_to_write;
  start_char_ptr = out_char_ptr;
  end_outbuf = out_char_ptr + CHARS_TO_WRITE;
#ifdef PRINTON
  if ((out_buffers_sent & 0x7F) == 0)
    fprintf(stderr, "%u\r", (unsigned int)outbuf_index);
#endif
  out_buffers_sent++;
  return;
}


void write_output_buffer_delta() {
  uint32_t chars_to_write = out_char_ptr - start_char_ptr;
  uint32_t len = out_char_ptr - start_char_ptr;
  if (stride == 4) {
    transpose4(start_char_ptr, len);
    len = out_char_ptr - start_char_ptr;
  }
  else if (stride == 2) {
    transpose2(start_char_ptr, len);
    len = out_char_ptr - start_char_ptr;
  }
  delta_transform(start_char_ptr, len);
  if (fd != 0) {
    fflush(fd);
    fwrite(start_char_ptr, 1, chars_to_write, fd);
    if ((out_buffers_sent & 1) == 0) {
      uint8_t k;
      for (k = 1 ; k <= stride ; k++)
        out_char1[100 - k] = *(out_char_ptr - k);
      out_char_ptr = out_char1 + 100;
    }
    else {
      uint8_t k;
      for (k = 1 ; k <= stride ; k++)
        out_char0[100 - k] = *(out_char_ptr - k);
      out_char_ptr = out_char0 + 100;
    }
  }
  outbuf_index += chars_to_write;
  start_char_ptr = out_char_ptr;
  end_outbuf = out_char_ptr + CHARS_TO_WRITE;
#ifdef PRINTON
  if ((out_buffers_sent & 0x7F) == 0)
    fprintf(stderr, "%u\r", (unsigned int)outbuf_index);
#endif
  out_buffers_sent++;
  return;
}


#define write_string(len) { \
  while (out_char_ptr + len >= end_outbuf) { \
    uint32_t temp_len = end_outbuf - out_char_ptr; \
    len -= temp_len; \
    memcpy(out_char_ptr, symbol_string_ptr, temp_len); \
    out_char_ptr += temp_len; \
    symbol_string_ptr += temp_len; \
    write_output_buffer(); \
  } \
  memcpy(out_char_ptr, symbol_string_ptr, len); \
  out_char_ptr += len; \
}


#define write_string_cap_encoded(len) { \
  while (out_char_ptr + len >= end_outbuf) { \
    uint32_t temp_len = end_outbuf - out_char_ptr; \
    len -= temp_len; \
    while (temp_len-- != 0) { \
      if (write_cap_on == 0) { \
        if (skip_space_on == 0) { \
          if ((*symbol_string_ptr & 0xFE) == 0x42) { \
            write_cap_on = 1; \
            if (*symbol_string_ptr++ == 'B') \
              write_cap_lock_on = 1; \
          } \
          else { \
            *out_char_ptr++ = *symbol_string_ptr; \
            if (*symbol_string_ptr++ == 0xA) \
              skip_space_on = 1; \
          } \
        } \
        else { \
          symbol_string_ptr++; \
          skip_space_on = 0; \
        } \
      } \
      else { \
        if (write_cap_lock_on != 0) { \
          if ((*symbol_string_ptr >= 'a') && (*symbol_string_ptr <= 'z')) \
            *out_char_ptr++ = *symbol_string_ptr++ - 0x20; \
          else { \
            write_cap_lock_on = 0; \
            write_cap_on = 0; \
            if (*symbol_string_ptr == 'C') \
              symbol_string_ptr++; \
            else { \
              *out_char_ptr++ = *symbol_string_ptr; \
              if (*symbol_string_ptr++ == 0xA) \
                skip_space_on = 1; \
            } \
          } \
        } \
        else { \
          write_cap_on = 0; \
          *out_char_ptr++ = *symbol_string_ptr++ - 0x20; \
        } \
      } \
    } \
    write_output_buffer(); \
  } \
  while (len-- != 0) { \
    if (write_cap_on == 0) { \
      if (skip_space_on == 0) { \
        if ((*symbol_string_ptr & 0xFE) == 0x42) { \
          write_cap_on = 1; \
          if (*symbol_string_ptr++ == 'B') \
            write_cap_lock_on = 1; \
        } \
        else { \
          *out_char_ptr++ = *symbol_string_ptr; \
          if (*symbol_string_ptr++ == 0xA) \
            skip_space_on = 1; \
        } \
      } \
      else { \
        symbol_string_ptr++; \
        skip_space_on = 0; \
      } \
    } \
    else { \
      if (write_cap_lock_on != 0) { \
        if ((*symbol_string_ptr >= 'a') && (*symbol_string_ptr <= 'z')) \
          *out_char_ptr++ = *symbol_string_ptr++ - 0x20; \
        else { \
          write_cap_lock_on = 0; \
          write_cap_on = 0; \
          if (*symbol_string_ptr == 'C') { \
            symbol_string_ptr++; \
          } \
          else { \
            *out_char_ptr++ = *symbol_string_ptr; \
            if (*symbol_string_ptr++ == 0xA) \
              skip_space_on = 1; \
          } \
        } \
      } \
      else { \
        write_cap_on = 0; \
        *out_char_ptr++ = *symbol_string_ptr++ - 0x20; \
      } \
    } \
  } \
}


#define write_string_delta(len) { \
  while (out_char_ptr + len >= end_outbuf) { \
    uint32_t temp_len = end_outbuf - out_char_ptr; \
    len -= temp_len; \
    memcpy(out_char_ptr, symbol_string_ptr, temp_len); \
    out_char_ptr += temp_len; \
    symbol_string_ptr += temp_len; \
    write_output_buffer_delta(); \
  } \
  memcpy(out_char_ptr, symbol_string_ptr, len); \
  out_char_ptr += len; \
}


void write_single_threaded_output() {
  uint8_t * symbol_string_ptr;
  uint32_t * read_ptr = symbol_buffer;
  if (cap_encoded != 0) {
    while (read_ptr != symbol_buffer_write_ptr) {
      symbol = *read_ptr++;
      symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
      uint32_t string_length = symbol_data[symbol].string_length;
      write_string_cap_encoded(string_length);
    }
  }
  else if (stride == 0) {
    while (read_ptr != symbol_buffer_write_ptr) {
      symbol = *read_ptr++;
      symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
      uint32_t string_length = symbol_data[symbol].string_length;
      write_string(string_length);
    }
  }
  else {
    while (read_ptr != symbol_buffer_write_ptr) {
      symbol = *read_ptr++;
      symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
      uint32_t string_length = symbol_data[symbol].string_length;
      write_string_delta(string_length);
    }
  }
  return;
}


void write_symbol_buffer(uint8_t * buffer_number_ptr) {
  while ((free_symbol_list_length < FREE_SYMBOL_LIST_SIZE) && (free_symbol_list_wait1_length != 0))
    free_symbol_list[free_symbol_list_length++] = free_symbol_list_wait1[--free_symbol_list_wait1_length];
  while ((free_symbol_list_wait1_length < FREE_SYMBOL_LIST_WAIT_SIZE) && (free_symbol_list_wait2_length != 0))
    free_symbol_list_wait1[free_symbol_list_wait1_length++] = free_symbol_list_wait2[--free_symbol_list_wait2_length];
  if (two_threads == 0) {
    write_single_threaded_output();
    symbol_buffer_write_ptr = symbol_buffer;
  }
  else {
    if (*buffer_number_ptr != 0)
      symbol_buffer_write_ptr = symbol_buffer;
    symbol_buffer_end_write_ptr = symbol_buffer_write_ptr + 0x400;
    atomic_store_explicit(&symbol_buffer_owner[*buffer_number_ptr], 1, memory_order_release);
    *buffer_number_ptr ^= 1;
    while (atomic_load_explicit(&symbol_buffer_owner[*buffer_number_ptr], memory_order_acquire) != 0) ;
  }
  return;
}


void *write_output_thread() {
  uint8_t write_cap_on, write_cap_lock_on, skip_space_on, next_buffer, *symbol_string_ptr;
  uint32_t symbol, *buffer_ptr, *buffer_end_ptr;

  next_buffer = write_cap_on = write_cap_lock_on = skip_space_on = 0;
  if (fd != 0)
    out_char_ptr = out_char0 + 100;
  else
    out_char_ptr = outbuf;
  start_char_ptr = out_char_ptr;
  end_outbuf = out_char_ptr + CHARS_TO_WRITE;
  buffer_ptr = &symbol_buffer[0];
  buffer_end_ptr = buffer_ptr + 0x400;

  if (cap_encoded != 0) {
    while ((atomic_load_explicit(&done_parsing, memory_order_acquire) == 0)
        || (atomic_load_explicit(&symbol_buffer_owner[next_buffer], memory_order_acquire) != 0)) {
      if (atomic_load_explicit(&symbol_buffer_owner[next_buffer], memory_order_acquire) != 0) {
        do {
          symbol = *buffer_ptr++;
          symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
          uint32_t string_length = symbol_data[symbol].string_length;
          write_string_cap_encoded(string_length);
        } while (buffer_ptr != buffer_end_ptr);
        atomic_store_explicit(&symbol_buffer_owner[next_buffer], 0, memory_order_release);
        next_buffer ^= 1;
        buffer_ptr = symbol_buffer + ((buffer_ptr - symbol_buffer) & 0x7FF);
        buffer_end_ptr = buffer_ptr + 0x400;
      }
    }
    while ((symbol = *buffer_ptr++) != MAX_U32_VALUE) {
      symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
      uint32_t string_length = symbol_data[symbol].string_length;
      write_string_cap_encoded(string_length);
    }
  }
  else if (stride == 0) {
    while ((atomic_load_explicit(&done_parsing, memory_order_acquire) == 0)
        || (atomic_load_explicit(&symbol_buffer_owner[next_buffer], memory_order_acquire) != 0)) {
      if (atomic_load_explicit(&symbol_buffer_owner[next_buffer], memory_order_acquire) != 0) {
        do {
          symbol = *buffer_ptr++;
          symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
          uint32_t string_length = symbol_data[symbol].string_length;
          write_string(string_length);
        } while (buffer_ptr != buffer_end_ptr);
        atomic_store_explicit(&symbol_buffer_owner[next_buffer], 0, memory_order_release);
        next_buffer ^= 1;
        buffer_ptr = symbol_buffer + ((buffer_ptr - symbol_buffer) & 0x7FF);
        buffer_end_ptr = buffer_ptr + 0x400;
      }
    }
    while ((symbol = *buffer_ptr++) != MAX_U32_VALUE) {
      symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
      uint32_t string_length = symbol_data[symbol].string_length;
      write_string(string_length);
    }
  }
  else {
    while ((atomic_load_explicit(&done_parsing, memory_order_acquire) == 0)
        || (atomic_load_explicit(&symbol_buffer_owner[next_buffer], memory_order_acquire) != 0)) {
      if (atomic_load_explicit(&symbol_buffer_owner[next_buffer], memory_order_acquire) != 0) {
        do {
          symbol = *buffer_ptr++;
          symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
          uint32_t string_length = symbol_data[symbol].string_length;
          write_string_delta(string_length);
        } while (buffer_ptr != buffer_end_ptr);
        atomic_store_explicit(&symbol_buffer_owner[next_buffer], 0, memory_order_release);
        next_buffer ^= 1;
        buffer_ptr = symbol_buffer + ((buffer_ptr - symbol_buffer) & 0x7FF);
        buffer_end_ptr = buffer_ptr + 0x400;
      }
    }
    while ((symbol = *buffer_ptr++) != MAX_U32_VALUE) {
      symbol_string_ptr = &symbol_strings[symbol_data[symbol].string_index];
      uint32_t string_length = symbol_data[symbol].string_length;
      write_string_delta(string_length);
    }
  }
  uint32_t chars_to_write = out_char_ptr - start_char_ptr;
  if (stride != 0) {
    if (stride == 4)
      transpose4(start_char_ptr, chars_to_write);
    else if (stride == 2)
      transpose2(start_char_ptr, chars_to_write);
    delta_transform(start_char_ptr, chars_to_write);
  }
  if (fd != 0)
    fwrite(start_char_ptr, 1, chars_to_write, fd);
  outbuf_index += chars_to_write;
  return(0);
}


uint8_t * GLZAdecode(size_t in_size, uint8_t * inbuf, size_t * outsize_ptr, uint8_t * outbuf, FILE * fd_out,
    struct param_data * params) {
  uint8_t sym_type, next_write_buffer, i, j;
  uint32_t symbol_number, max_symbols_defined, string_index;
  pthread_t output_thread;

  fd = fd_out;
  delta_on = stride = outbuf_index = out_buffers_sent = next_write_buffer = two_threads = 0;
  dictionary_size = (uint32_t)(pow(2.0, 10.0 + 0.08 * (double)inbuf[0]));
  cap_encoded = inbuf[1] >> 7;
  UTF8_compliant = (inbuf[1] >> 6) & 1;
  use_mtf = (inbuf[1] >> 5) & 1;
  max_code_length = (inbuf[1] & 0x1F) + 1;
  queue_miss_code_length[1] = max_code_length;
  min_code_length = (inbuf[2] & 0x1F) + 1;
  max_regular_code_length = max_code_length - (inbuf[3] & 0x1F);
  i = 2;
  do {
    queue_miss_code_length[i] = queue_miss_code_length[i - 1] - ((inbuf[2] >> (i + 4)) & 1);
  } while (++i != 4);
  do {
    queue_miss_code_length[i] = queue_miss_code_length[i - 1] - ((inbuf[3] >> (i + 1)) & 1);
  } while (++i != 7);
  do {
    queue_miss_code_length[i] = queue_miss_code_length[i - 1] - ((inbuf[4] >> (i - 7)) & 1);
  } while (++i != 15);
  if (UTF8_compliant != 0) {
    if (in_size < 6) {
      *outsize_ptr = 0;
      return(outbuf);
    }
    WriteInCharNum(6);
    num_base_symbols = 1 << inbuf[5];
    i = 0x90;
  }
  else {
    num_base_symbols = 0x100;
    delta_format = (inbuf[2] & 0x20) >> 5;
    if (delta_format != 0) {
      if (in_size < 6) {
        *outsize_ptr = 0;
        return(outbuf);
      }
      WriteInCharNum(6);
      delta_format = inbuf[5];
      if ((delta_format & 0x80) == 0)
        stride = (delta_format & 0x3) + 1;
      else
        stride = delta_format & 0x7F;
    }
    else {
      if (in_size < 5) {
        *outsize_ptr = 0;
        return(outbuf);
      }
      WriteInCharNum(5);
    }
    i = 0xFF;
  }

  max_symbols_defined = dictionary_size >> 1;
  if (max_symbols_defined > MAX_SYMBOLS_DEFINED)
    max_symbols_defined = MAX_SYMBOLS_DEFINED;
  if ((0 == (symbol_strings = (uint8_t *)malloc(dictionary_size)))
      || (0 == (symbol_data = (struct sym_data *)malloc(max_symbols_defined * sizeof(struct sym_data))))) {
    fprintf(stderr, "ERROR - memory allocation failed\n");
    return(0);
  }

  do {
    for (j = max_code_length ; j >= min_code_length ; j--) {
      bin_data[i][j].nsob = bin_data[i][j].nbob = bin_data[i][j].fbob = 0;
      bin_data[i][j].sym_list_size = 4;
      if (0 == (bin_data[i][j].sym_list = (uint32_t *)malloc(sizeof(uint32_t) * 4))) {
        fprintf(stderr, "ERROR - memory allocation failed\n");
        return(0);
      }
    }
    sum_nbob[i] = 0;
    symbol_lengths[i] = 0;
    bin_code_length[i] = max_code_length;
  } while (i-- != 0);

  uint8_t * lookup_bits_ptr = &lookup_bits[0][0] + 0x100000;
  while (lookup_bits_ptr-- != &lookup_bits[0][0])
    *lookup_bits_ptr = max_code_length;

  symbol_buffer_write_ptr = symbol_buffer;
  symbol_buffer_end_write_ptr = symbol_buffer_write_ptr + 0x400;
  find_first_symbol = 1;
  free_symbol_list_length = free_symbol_list_wait1_length = free_symbol_list_wait2_length = 0;
  queue_offset = queue_size = queue_size_cap = prior_is_cap = num_symbols_defined = 0;
  symbol_data[0].string_index = 0;

  InitDecoder(max_code_length, i, MAX_INSTANCES_FOR_REMOVE + 1 + max_regular_code_length - min_code_length,
      cap_encoded, UTF8_compliant, use_mtf, inbuf);

  if ((params == 0) || (params->two_threads != 0)) {
    two_threads = 1;
    atomic_init(&done_parsing, 0);
    atomic_init(&symbol_buffer_owner[0], 0);
    atomic_init(&symbol_buffer_owner[1], 0);
    pthread_create(&output_thread, NULL, write_output_thread, outbuf);
  }
  else {
    write_cap_on = write_cap_lock_on = skip_space_on = 0;
    if (fd != 0)
      out_char_ptr = out_char0 + 100;
    else
      out_char_ptr = outbuf;
    start_char_ptr = out_char_ptr;
    end_outbuf = out_char_ptr + CHARS_TO_WRITE;
  }

  // main decoding loop
  DecodeSymType(LEVEL0);
  string_index = symbol_data[0].string_index;
  if (cap_encoded != 0) {
    cap_symbol_defined = cap_lock_symbol_defined = 0;
    decode_new_cap_encoded(&symbol_number, &string_index);
    while (1) {
      *symbol_buffer_write_ptr++ = symbol_number;
      if (symbol_buffer_write_ptr == symbol_buffer_end_write_ptr)
        write_symbol_buffer(&next_write_buffer);
      if (prior_is_cap == 0) {
        if ((sym_type = DecodeSymType(LEVEL0)) == 0) { // dictionary symbol
          uint8_t first_char = ' ';
          if (prior_end != 0xA)
            first_char = DecodeFirstChar(symbol_data[symbol_number].type2, prior_end);
          uint16_t bin_num = DecodeBin(sum_nbob[first_char]);
          uint8_t code_length = lookup_bits[first_char][bin_num];
          if (bin_data[first_char][code_length].nsob == 0)
            break; // EOF
          symbol_number = get_dictionary_symbol(bin_num, code_length, first_char);
          prior_is_cap = ((prior_end = symbol_data[symbol_number].ends) == 'C');
          if (symbol_data[symbol_number].remaining < MAX_INSTANCES_FOR_REMOVE) {
            if (--symbol_data[symbol_number].remaining == 0) {
              dremove_dictionary_symbol(symbol_number);
              if (free_symbol_list_wait2_length < FREE_SYMBOL_LIST_WAIT_SIZE)
                free_symbol_list_wait2[free_symbol_list_wait2_length++] = symbol_number;
            }
            else if (((symbol_data[symbol_number].type & 2) != 0)
                && (((symbol_data[symbol_number].remaining == 1) && ((symbol_data[symbol_number].type & 8) == 0))
                  || (DecodeGoMtf(symbol_data[symbol_number].repeats, 0) != 0))) {
              dremove_dictionary_symbol(symbol_number);
              dadd_symbol_to_queue(symbol_number);
            }
          }
          else if (((symbol_data[symbol_number].type & 2) != 0)
              && (DecodeGoMtf(symbol_data[symbol_number].remaining, 0) != 0)) {
            dremove_dictionary_symbol(symbol_number);
            dadd_symbol_to_queue(symbol_number);
          }
        }
        else if (sym_type == 1) {
          string_index = symbol_data[num_symbols_defined].string_index;
          decode_new_cap_encoded(&symbol_number, &string_index);
        }
        else {
          symbol_number = dupdate_queue(DecodeMtfPos(NOT_CAP, queue_size));
          prior_is_cap = ((prior_end = symbol_data[symbol_number].ends) == 'C');
        }
      }
      else { // prior_is_cap
        if ((sym_type = DecodeSymType(LEVEL0_CAP)) == 0) { // dictionary symbol
          uint8_t first_char = DecodeFirstChar(0, 'C');
          uint16_t bin_num = DecodeBin(sum_nbob[first_char]);
          uint8_t code_length = lookup_bits[first_char][bin_num];
          symbol_number = get_dictionary_symbol(bin_num, code_length, first_char);
          prior_is_cap = ((prior_end = symbol_data[symbol_number].ends) == 'C');
          if (symbol_data[symbol_number].remaining < MAX_INSTANCES_FOR_REMOVE) {
            if (--symbol_data[symbol_number].remaining == 0) {
              dremove_dictionary_symbol(symbol_number);
              if (free_symbol_list_wait2_length < FREE_SYMBOL_LIST_WAIT_SIZE)
                free_symbol_list_wait2[free_symbol_list_wait2_length++] = symbol_number;
            }
            else if (((symbol_data[symbol_number].type & 2) != 0)
                && (((symbol_data[symbol_number].remaining == 1) && ((symbol_data[symbol_number].type & 8) == 0))
                  || (DecodeGoMtf(symbol_data[symbol_number].repeats, 0) != 0))) {
              dremove_dictionary_symbol(symbol_number);
              dadd_symbol_to_queue(symbol_number);
            }
          }
          else if (((symbol_data[symbol_number].type & 2) != 0)
              && (DecodeGoMtf(symbol_data[symbol_number].remaining, 0) != 0)) {
            dremove_dictionary_symbol(symbol_number);
            dadd_symbol_to_queue(symbol_number);
          }
        }
        else if (sym_type == 1) {
          string_index = symbol_data[num_symbols_defined].string_index;
          decode_new_cap_encoded(&symbol_number, &string_index);
        }
        else {
          symbol_number = get_queue_symbol_cap();
          prior_is_cap = ((prior_end = symbol_data[symbol_number].ends) == 'C');
        }
      }
    }
  }
  else { // not cap encoded
    decode_new(&symbol_number, &string_index);
    while (1) {
      *symbol_buffer_write_ptr++ = symbol_number;
      if (symbol_buffer_write_ptr == symbol_buffer_end_write_ptr)
        write_symbol_buffer(&next_write_buffer);
      if ((sym_type = DecodeSymType(LEVEL0)) == 0) { // dictionary symbol
        uint8_t first_char;
        if (UTF8_compliant != 0)
          first_char = DecodeFirstChar(0, prior_end);
        else
          first_char = DecodeFirstCharBinary(prior_end);
        uint16_t bin_num = DecodeBin(sum_nbob[first_char]);
        uint8_t code_length = lookup_bits[first_char][bin_num];
        if (bin_data[first_char][code_length].nsob == 0)
          break; // EOF
        symbol_number = get_dictionary_symbol(bin_num, code_length, first_char);
        prior_end = symbol_data[symbol_number].ends;
        if (symbol_data[symbol_number].remaining < MAX_INSTANCES_FOR_REMOVE) {
          if (--symbol_data[symbol_number].remaining == 0) {
            dremove_dictionary_symbol(symbol_number);
            if (free_symbol_list_wait2_length < FREE_SYMBOL_LIST_WAIT_SIZE)
              free_symbol_list_wait2[free_symbol_list_wait2_length++] = symbol_number;
          }
          else if (((symbol_data[symbol_number].type & 2) != 0)
              && (((symbol_data[symbol_number].remaining == 1) && ((symbol_data[symbol_number].type & 8) == 0))
                || (DecodeGoMtf(symbol_data[symbol_number].repeats, 0) != 0))) {
            dremove_dictionary_symbol(symbol_number);
            dadd_symbol_to_queue(symbol_number);
          }
        }
        else if (((symbol_data[symbol_number].type & 2) != 0)
            && (DecodeGoMtf(symbol_data[symbol_number].remaining, 0) != 0)) {
          dremove_dictionary_symbol(symbol_number);
          dadd_symbol_to_queue(symbol_number);
        }
      }
      else if (sym_type == 1) {
        uint32_t string_index = symbol_data[num_symbols_defined].string_index;
        decode_new(&symbol_number, &string_index);
      }
      else {
        symbol_number = dupdate_queue(DecodeMtfPos(NOT_CAP, queue_size));
        prior_end = symbol_data[symbol_number].ends;
      }
    }
  }

  *symbol_buffer_write_ptr = MAX_U32_VALUE;
  if (two_threads != 0)
    atomic_store_explicit(&done_parsing, 1, memory_order_release);
  i = 0xFF;
  if (UTF8_compliant != 0)
    i = 0x90;
  do {
    for (j = max_code_length ; j >= min_code_length ; j--)
      free(bin_data[i][j].sym_list);
  } while (i--);
  if (two_threads != 0)
    pthread_join(output_thread,NULL);
  else {
    write_single_threaded_output();
    uint32_t chars_to_write = out_char_ptr - start_char_ptr;
    if (stride != 0) {
      if (stride == 4)
        transpose4(start_char_ptr, chars_to_write);
      else if (stride == 2)
        transpose2(start_char_ptr, chars_to_write);
      delta_transform(start_char_ptr, chars_to_write);
    }
    if (fd != 0)
      fwrite(start_char_ptr, 1, chars_to_write, fd);
    outbuf_index += chars_to_write;
  }
  free(symbol_strings);
  *outsize_ptr = outbuf_index;
  return(outbuf);
}
