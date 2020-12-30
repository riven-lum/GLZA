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

// GLZAencode.c
//   Encodes files created by GLZAcompress


#include <inttypes.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "GLZA.h"
#include "GLZAmodel.h"

const uint8_t MAX_BITS_IN_CODE = 25;
const uint32_t UNIQUE_SYMBOL = 0xFFFFFFFF;
const uint32_t READ_SIZE = 0x80000;

uint8_t UTF8_compliant, cap_encoded, prior_is_cap, end_char, prior_end, use_mtf, queue_offset;
uint8_t max_code_length, max_regular_code_length, found_first_symbol, cap_symbol_defined, cap_lock_symbol_defined;
uint8_t symbol_lengths[0x100], bin_code_length[0x100], sym_list_bits[0x100][26], queue_miss_code_length[16];
uint16_t nbob[0x100][26], sum_nbob[0x100], fbob[0x100][26];
uint32_t prior_symbol, num_grammar_rules, num_codes, num_base_symbols, num_transmits, queue_size, queue_size_cap;
uint32_t queue[0x1A0], nsob[0x100][26], *sym_list_ptrs[0x100][26], *symbol_array;

struct transmit_symbols {
  uint32_t symbol;
  uint32_t distance;
  uint32_t previous_index;
  uint32_t hurts;
  float score;
} *transmits;


// type:  bit 0: string ends 'C' or 'B' (cap symbol/cap lock symbol), bit 1: string starts a-z, bit 2: non-ergodic,
//        bit 3: in queue, bit 4: "word" ending determined, bit 7: sent MTF
// bits 6-5: 0: not a word, 1: word, 2: word & >= 15 repeats (ending sub)symbol,
//           3: word & >= 15 repeats (ending sub)symbol & likely followed by ' '

struct symbol_data {
  uint8_t starts, ends, code_length, type;
  uint32_t count, hits, array_index, define_symbol_start_index, previous;
  int32_t space_score;
} *sd;


void print_string(uint32_t symbol_number) {
  if (symbol_number < num_base_symbols) {
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
    uint32_t *symbol_ptr, *next_symbol_ptr;
    symbol_ptr = symbol_array + sd[symbol_number].define_symbol_start_index;
    next_symbol_ptr = symbol_array + sd[symbol_number + 1].define_symbol_start_index - 1;
    while (symbol_ptr != next_symbol_ptr)
      print_string(*symbol_ptr++);
  }
  return;
}


uint32_t get_dictionary_size(uint32_t symbol_number) {
  uint32_t symbol_size = 0;
  if (symbol_number < num_base_symbols) {
    if (UTF8_compliant != 0) {
      if (symbol_number < START_UTF8_2BYTE_SYMBOLS)
        symbol_size = 1;
      else if (symbol_number < START_UTF8_3BYTE_SYMBOLS)
        symbol_size = 2;
      else if (symbol_number < START_UTF8_4BYTE_SYMBOLS)
        symbol_size = 3;
      else
        symbol_size = 4;
    }
    else
      symbol_size = 1;
  }
  else {
    uint32_t *symbol_ptr, *next_symbol_ptr;
    symbol_ptr = symbol_array + sd[symbol_number].define_symbol_start_index;
    next_symbol_ptr = symbol_array + sd[symbol_number + 1].define_symbol_start_index - 1;
    while (symbol_ptr != next_symbol_ptr)
      symbol_size += get_dictionary_size(*symbol_ptr++);
  }
  return(symbol_size);
}


void get_symbol_category(uint32_t symbol_number, uint8_t *sym_type_ptr) {
  if (symbol_number >= num_base_symbols) {
    if ((sd[symbol_number].type & 0x20) != 0) {
      *sym_type_ptr |= 0x30;
      return;
    }
    uint32_t * string_ptr = symbol_array + sd[symbol_number + 1].define_symbol_start_index - 2;
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
  if (first_symbol >= num_base_symbols) {
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
  if (first_symbol >= num_base_symbols) {
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
  uint32_t last_symbol = symbol_array[sd[symbol_number + 1].define_symbol_start_index - 2];
  if (last_symbol >= num_base_symbols) {
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
  uint32_t last_symbol = symbol_array[sd[symbol_number + 1].define_symbol_start_index - 2];
  if (last_symbol >= num_base_symbols) {
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
      fprintf(stderr, "FATAL ERROR - symbol list realloc failure\n");
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
  uint32_t last_symbol = sym_list_ptrs[first_char][bits][--nsob[first_char][bits]];
  sym_list_ptrs[first_char][bits][sd[symbol].array_index] = last_symbol;
  sd[last_symbol].array_index = sd[symbol].array_index;
  return;
}


void add_symbol_to_queue(uint32_t symbol_number) {
  sd[symbol_number].type |= 0x88;
  *(queue + --queue_offset) = symbol_number;
  if ((sd[symbol_number].type & 2) != 0)
    queue_size_cap++;
  queue_size++;
  return;
}


void update_queue(uint32_t symbol_number, uint8_t in_definition) {
  uint8_t queue_position = 0;
  while (symbol_number != *(queue + (uint8_t)(queue_position + queue_offset)))
    queue_position++;
  EncodeMtfType(2 * in_definition);
  EncodeMtfPos(NOT_CAP, queue_position, queue_size);
  while (queue_position != 0) {
    *(queue + (uint8_t)(queue_offset + queue_position))
        = *(queue + (uint8_t)(queue_offset + queue_position - 1));
    queue_position--;
  }
  if (transmits[num_transmits].distance != 0xFFFFFFFF) {
    EncodeGoMtf(sd[symbol_number].count, 1, 1);
    *(queue + queue_offset) = symbol_number;
  }
  else {
    queue_size--;
    if ((sd[symbol_number].type & 2) != 0)
      queue_size_cap--;
    queue_offset++;
    if ((sd[symbol_number].count > MAX_INSTANCES_FOR_REMOVE)
        || (sd[symbol_number].hits != sd[symbol_number].count)) {
      EncodeGoMtf(sd[symbol_number].count, 1, 0);
      sd[symbol_number].type &= 0xF7;
      add_dictionary_symbol(symbol_number, sd[symbol_number].code_length);
    }
  }
  return;
}


void update_queue_prior_cap(uint32_t symbol_number, uint8_t in_definition) {
  uint8_t queue_position = 0;
  uint8_t cap_queue_position = 0;
  while (symbol_number != *(queue + (uint8_t)(queue_position + queue_offset)))
    if ((sd[*(queue + (uint8_t)(queue_position++ + queue_offset))].type & 2) != 0)
      cap_queue_position++;
  while (queue_position != 0) {
    *(queue + (uint8_t)(queue_offset + queue_position))
        = *(queue + (uint8_t)(queue_offset + queue_position - 1));
    queue_position--;
  }
  EncodeMtfType(2 * in_definition + 1);
  EncodeMtfPos(CAP, cap_queue_position, queue_size_cap);
  if (transmits[num_transmits].distance != 0xFFFFFFFF) {
    EncodeGoMtf(sd[symbol_number].count, 1, 1);
    *(queue + queue_offset) = symbol_number;
  }
  else {
    queue_size--;
    queue_size_cap--;
    queue_offset++;
    if ((sd[symbol_number].count > MAX_INSTANCES_FOR_REMOVE)
        || (sd[symbol_number].hits != sd[symbol_number].count)) {
      EncodeGoMtf(sd[symbol_number].count, 1, 0);
      sd[symbol_number].type &= 0xF7;
      add_dictionary_symbol(symbol_number, sd[symbol_number].code_length);
    }
  }
  return;
}


uint16_t get_mtf_overflow_position(struct symbol_data * sd, uint32_t * queue, uint16_t queue_position,
    uint32_t num_transmits_over_sqrt2) {
  uint16_t limit_position = 0;
  if ((queue_position > 0x1C) && ((sd[queue[0x1C]].count <= (num_transmits_over_sqrt2 >> 10))
      && (sd[queue[0x1C]].count > (num_transmits_over_sqrt2 >> 11))))
    limit_position = 0x1C;
  else if ((queue_position > 0x30) && ((sd[queue[0x30]].count <= (num_transmits_over_sqrt2 >> 11))
      && (sd[queue[0x30]].count > (num_transmits_over_sqrt2 >> 12))))
    limit_position = 0x30;
  else if ((queue_position > 0x44) && ((sd[queue[0x44]].count <= (num_transmits_over_sqrt2 >> 12))
      && (sd[queue[0x44]].count > (num_transmits_over_sqrt2 >> 13))))
    limit_position = 0x44;
  else if ((queue_position > 0x48) && ((sd[queue[0x48]].count <= (num_transmits_over_sqrt2 >> 13))
      && (sd[queue[0x48]].count > (num_transmits_over_sqrt2 >> 14))))
    limit_position = 0x48;
  else if ((queue_position > 0x88) && ((sd[queue[0x88]].count <= (num_transmits_over_sqrt2 >> 14))
      && (sd[queue[0x88]].count > (num_transmits_over_sqrt2 >> 15))))
    limit_position = 0x88;
  else if ((queue_position > 0xB0) && ((sd[queue[0xB0]].count <= (num_transmits_over_sqrt2 >> 15))
      && (sd[queue[0xB0]].count > (num_transmits_over_sqrt2 >> 16))))
    limit_position = 0xB0;
  else if ((queue_position > 0xD8) && ((sd[queue[0xD8]].count <= (num_transmits_over_sqrt2 >> 16))
      && (sd[queue[0xD8]].count > (num_transmits_over_sqrt2 >> 17))))
    limit_position = 0xD8;
  else if ((queue_position > 0xF0) && ((sd[queue[0xF0]].count <= (num_transmits_over_sqrt2 >> 17))
      && (sd[queue[0xF0]].count > (num_transmits_over_sqrt2 >> 18))))
    limit_position = 0xF0;
  else if ((queue_position > 0x108) && ((sd[queue[0x108]].count <= (num_transmits_over_sqrt2 >> 18))
      && (sd[queue[0x108]].count > (num_transmits_over_sqrt2 >> 19))))
    limit_position = 0x108;
  else if ((queue_position > 0x120) && ((sd[queue[0x120]].count <= (num_transmits_over_sqrt2 >> 19))
      && (sd[queue[0x120]].count > (num_transmits_over_sqrt2 >> 20))))
    limit_position = 0x120;
  else if ((queue_position > 0x138) && ((sd[queue[0x138]].count <= (num_transmits_over_sqrt2 >> 20))
      && (sd[queue[0x138]].count > (num_transmits_over_sqrt2 >> 21))))
    limit_position = 0x138;
  return(limit_position);
}


float get_mtf_score_limit(uint32_t count, uint32_t num_transmits_over_sqrt2) {
  float score_limit;
  if (count > (num_transmits_over_sqrt2 >> 11))
    score_limit = 16.0;
  else if (count > (num_transmits_over_sqrt2 >> 12))
    score_limit = 9.5;
  else if (count > (num_transmits_over_sqrt2 >> 13))
    score_limit = 8.0;
  else if (count > (num_transmits_over_sqrt2 >> 14))
    score_limit = 6.4;
  else if (count > (num_transmits_over_sqrt2 >> 15))
    score_limit = 4.8;
  else if (count > (num_transmits_over_sqrt2 >> 16))
    score_limit = 3.7;
  else if (count > (num_transmits_over_sqrt2 >> 17))
    score_limit = 2.9;
  else if (count > (num_transmits_over_sqrt2 >> 18))
    score_limit = 2.5;
  else if (count > (num_transmits_over_sqrt2 >> 19))
    score_limit = 2.3;
  else if (count > (num_transmits_over_sqrt2 >> 20))
    score_limit = 2.2;
  else if (count > (num_transmits_over_sqrt2 >> 21))
    score_limit = 2.1;
  else if (count > (num_transmits_over_sqrt2 >> 22))
    score_limit = 2.0;
  else if (count > (num_transmits_over_sqrt2 >> 23))
    score_limit = 1.9;
  else
    score_limit = 1.8;
  return(score_limit);
}


void add_mtf_hit_scores(struct symbol_data * sd, uint16_t queue_position, uint32_t num_transmits_over_sqrt2) {
  if (queue_position <= 4)
    sd->hits += 61 - 3 * queue_position;
  else if (queue_position <= 7)
    sd->hits += 56 - 2 * queue_position;
  else if (queue_position <= 0xF)
    sd->hits += 48 - queue_position;
  else if (queue_position <= 0x1F) {
    if (sd->count <= (num_transmits_over_sqrt2 >> 12))
      sd->hits += 40 - (queue_position >> 1);
  }
  else if (queue_position <= 0x3F) {
    if (sd->count <= (num_transmits_over_sqrt2 >> 13))
      sd->hits += 28 - (queue_position >> 3);
  }
  else if (queue_position <= 0x7F) {
    if (sd->count <= (num_transmits_over_sqrt2 >> 14))
      sd->hits += 22 - (queue_position >> 5);
  }
  else if (queue_position <= 0xFF) {
    if (sd->count <= (num_transmits_over_sqrt2 >> 15))
      sd->hits += 20 - (queue_position >> 6);
  }
}


void encode_dictionary_symbol(uint32_t symbol) {
  uint32_t symbol_index, bin_code;
  uint16_t bin_num;
  uint8_t first_char, code_length, bin_shift;

  first_char = sd[symbol].starts;
  symbol_index = sd[symbol].array_index;
  code_length = sd[symbol].code_length;
  if (cap_encoded != 0) {
    if (prior_end != 0xA)
      EncodeFirstChar(first_char, (sd[prior_symbol].type & 0x60) >> 5, prior_end);
  }
  else if (UTF8_compliant != 0)
    EncodeFirstChar(first_char, 0, prior_end);
  else 
    EncodeFirstCharBinary(first_char, prior_end);

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
    if (bin_shift > reduce_bits) {
      bin_num = fbob[first_char][code_length];
      uint32_t min_extra_reduce_index = 2 * nsob[first_char][code_length] - (max_codes_in_bins >> reduce_bits);
      uint16_t symbol_bins, code_bin;
      code_length = bin_shift - reduce_bits;
      if (symbol_index >= min_extra_reduce_index) {
        bin_code = 2 * symbol_index - min_extra_reduce_index;
        code_bin = (uint16_t)(bin_code >> code_length);
        bin_code -= (uint32_t)code_bin << code_length;
        symbol_bins = 2;
      }
      else {
        bin_code = symbol_index;
        code_bin = (uint16_t)(symbol_index >> code_length);
        bin_code -= (uint32_t)code_bin << code_length;
        symbol_bins = 1;
      }
      bin_num += code_bin;
      EncodeLongDictionarySymbol(bin_code, bin_num, sum_nbob[first_char], code_length, symbol_bins);
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


uint32_t count_symbols(uint32_t symbol) {
  uint32_t string_symbols, *symbol_string_ptr, *end_symbol_string_ptr;
  if (symbol < num_base_symbols)
    return(1);
  symbol_string_ptr = symbol_array + sd[symbol].define_symbol_start_index;
  end_symbol_string_ptr = symbol_array + sd[symbol + 1].define_symbol_start_index - 1;
  string_symbols = 0;
  while (symbol_string_ptr != end_symbol_string_ptr) {
    if ((sd[*symbol_string_ptr].count == 1) && (*symbol_string_ptr >= num_base_symbols))
      string_symbols += count_symbols(*symbol_string_ptr);
    else
      string_symbols++;
    symbol_string_ptr++;
  }
  return(string_symbols);
}


void get_embedded_symbols(uint32_t define_symbol) {
  uint32_t symbol;
  uint32_t *define_string_ptr, *define_string_end_ptr;

  if (define_symbol >= num_base_symbols) {
    define_string_ptr = symbol_array + sd[define_symbol].define_symbol_start_index;
    define_string_end_ptr = symbol_array + sd[define_symbol + 1].define_symbol_start_index - 1;
    do {
      symbol = *define_string_ptr++;
      sd[symbol].hits++;
      if (sd[symbol].previous == 0xFFFFFFFF)
        get_embedded_symbols(symbol);
      else {
        transmits[sd[symbol].previous].distance = num_transmits - sd[symbol].previous;
        transmits[num_transmits].previous_index = sd[symbol].previous;
        transmits[num_transmits].distance = 0xFFFFFFFF;
        sd[symbol].previous = num_transmits++;
      }
    } while (define_string_ptr != define_string_end_ptr);
  }
  if (sd[define_symbol].count != 1) {
    sd[define_symbol].previous = num_transmits;
    transmits[num_transmits++].previous_index = 0xFFFFFFFF;
  }
  return;
}


void get_embedded_symbols2(uint32_t define_symbol) {
  uint32_t symbol;
  uint32_t *define_string_ptr, *define_string_end_ptr;

  if (define_symbol >= num_base_symbols) {
    define_string_ptr = symbol_array + sd[define_symbol].define_symbol_start_index;
    define_string_end_ptr = symbol_array + sd[define_symbol + 1].define_symbol_start_index - 1;
    do {
      symbol = *define_string_ptr++;
      if (sd[symbol].previous == 0xFFFFFFFF)
        get_embedded_symbols2(symbol);
      else {
        transmits[sd[symbol].previous].distance = num_transmits - sd[symbol].previous;
        transmits[num_transmits].previous_index = sd[symbol].previous;
        transmits[num_transmits].symbol = symbol;
        transmits[num_transmits].distance = 0xFFFFFFFF;
        sd[symbol].previous = num_transmits++;
        if ((sd[prior_symbol].type & 0x20) != 0) {
          if (sd[symbol].starts == 0x20)
            sd[prior_symbol].space_score++;
          else
            sd[prior_symbol].space_score -= 4;
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
  prior_symbol = define_symbol;
  if (sd[define_symbol].count != 1) {
    sd[define_symbol].previous = num_transmits;
    transmits[num_transmits].symbol = define_symbol;
    transmits[num_transmits++].previous_index = 0xFFFFFFFF;
  }
  return;
}


uint8_t embed_define_binary(uint32_t define_symbol, uint8_t in_definition) {
  uint32_t *define_string_ptr, *define_symbol_start_ptr, *define_string_end_ptr;
  uint32_t define_symbol_instances, symbols_in_definition, symbol, symbol_inst;
  uint8_t new_symbol_code_length, SID_symbol;

  EncodeNewType(2 * in_definition);
  define_symbol_instances = sd[define_symbol].count;
  if (define_symbol_instances != 1)
    new_symbol_code_length = sd[define_symbol].code_length;
  else
    new_symbol_code_length = 0x20;

  // send symbol length, instances and ergodicity bit
  if (define_symbol < num_base_symbols) {
    symbol_lengths[define_symbol] = new_symbol_code_length;
    EncodeSID(NOT_CAP, 0);
    if (define_symbol_instances == 1)
      EncodeINST(NOT_CAP, 0, MAX_INSTANCES_FOR_REMOVE - 1);
    else if (define_symbol_instances <= MAX_INSTANCES_FOR_REMOVE)
      EncodeINST(NOT_CAP, 0, define_symbol_instances - 2);
    else
      EncodeINST(NOT_CAP, 0, MAX_INSTANCES_FOR_REMOVE + max_regular_code_length - new_symbol_code_length);
    EncodeBaseSymbol(define_symbol, 0x100, 0x100);
    if ((define_symbol & 1) != 0) {
      if (symbol_lengths[define_symbol - 1] != 0)
        DoubleRangeDown();
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
      nbob[end_char][max_code_length] = 1;
      sum_nbob[end_char] = 1;
    }
    if (define_symbol_instances == 1)
      return(1);
  }
  else {
    num_grammar_rules++;
    define_symbol_start_ptr = symbol_array + sd[define_symbol].define_symbol_start_index;
    define_string_ptr = define_symbol_start_ptr;
    define_string_end_ptr = symbol_array + sd[define_symbol + 1].define_symbol_start_index - 1;

    // count the symbols in the definition
    symbols_in_definition = 0;
    while (define_string_ptr != define_string_end_ptr) {
      if ((sd[*define_string_ptr].count != 1) || (*define_string_ptr < num_base_symbols))
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
      while (data_bits != 0) {
        data_bits -= 2;
        EncodeExtraLength((extra_symbols >> data_bits) & 3);
      }
    }

    // write the symbol string
    define_string_ptr = define_symbol_start_ptr;
    while (define_string_ptr != define_string_end_ptr) {
      symbol = *define_string_ptr++;
      symbol_inst = sd[symbol].hits++;
      if (symbol_inst == 0) {
        if (embed_define_binary(symbol, 1) == 0)
          return(0);
      }
      else {
        if ((sd[symbol].type & 8) != 0) {
          if (prior_is_cap == 0)
            update_queue(symbol, 1);
          else
            update_queue_prior_cap(symbol, 1);
        }
        else {
          EncodeDictType(2);
          encode_dictionary_symbol(symbol);
          if (sd[symbol].count <= MAX_INSTANCES_FOR_REMOVE) {
            if (sd[symbol].count == sd[symbol].hits)
              remove_dictionary_symbol(symbol, sd[symbol].code_length);
            else if (use_mtf != 0) {
              if ((sd[symbol].type & 4) != 0) {
                if (transmits[num_transmits].distance != 0xFFFFFFFF) {
                  if ((sd[symbol].hits + 1 != sd[symbol].count) || ((sd[symbol].type & 0x80) != 0))
                    EncodeGoMtf(sd[symbol].count, 0, 1);
                  remove_dictionary_symbol(symbol, sd[symbol].code_length);
                  add_symbol_to_queue(symbol);
                }
                else
                  EncodeGoMtf(sd[symbol].count, 0, 0);
              }
            }
          }
          else if ((sd[symbol].type & 4) != 0) {
            if (transmits[num_transmits].distance != 0xFFFFFFFF) {
              EncodeGoMtf(sd[symbol].code_length + MAX_INSTANCES_FOR_REMOVE, 0, 1);
              remove_dictionary_symbol(symbol, sd[symbol].code_length);
              add_symbol_to_queue(symbol);
            }
            else
              EncodeGoMtf(sd[symbol].code_length + MAX_INSTANCES_FOR_REMOVE, 0, 0);
          }
        }
        num_transmits++;
      }
      prior_end = sd[symbol].ends;
    }

    if (define_symbol_instances <= MAX_INSTANCES_FOR_REMOVE)
      EncodeINST(NOT_CAP, SID_symbol, define_symbol_instances - 2);
    else
      EncodeINST(NOT_CAP, SID_symbol,
          MAX_INSTANCES_FOR_REMOVE - 1 + max_regular_code_length - new_symbol_code_length);
  }

  if ((use_mtf != 0) && ((new_symbol_code_length >= 11) || (define_symbol_instances <= MAX_INSTANCES_FOR_REMOVE))) {
    if (define_symbol_instances > MAX_INSTANCES_FOR_REMOVE) {
      if ((sd[define_symbol].type & 4) != 0) {
        EncodeERG(0, 1);
        if (transmits[num_transmits].distance != 0xFFFFFFFF) {
          EncodeGoMtf(new_symbol_code_length + MAX_INSTANCES_FOR_REMOVE, 2, 1);
          add_symbol_to_queue(define_symbol);
        }
        else {
          EncodeGoMtf(new_symbol_code_length + MAX_INSTANCES_FOR_REMOVE, 2, 0);
          if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
            return(0);
        }
      }
      else {
        EncodeERG(0, 0);
        if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
          return(0);
      }
    }
    else if ((sd[define_symbol].type & 4) != 0) {
      EncodeERG(define_symbol_instances + 1, 1);
      if (transmits[num_transmits].distance != 0xFFFFFFFF) {
        if (define_symbol_instances > 2)
          EncodeGoMtf(define_symbol_instances, 2, 1);
        add_symbol_to_queue(define_symbol);
      }
      else {
        if (define_symbol_instances > 2)
          EncodeGoMtf(define_symbol_instances, 2, 0);
        if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
          return(0);
      }
    }
    else {
      EncodeERG(define_symbol_instances + 1, 0);
      if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
        return(0);
    }
  }
  else if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
    return(0);
  num_transmits++;
  return (1);
}


uint8_t embed_define(uint32_t define_symbol, uint8_t in_definition) {
  uint32_t *define_string_ptr, *define_symbol_start_ptr, *define_string_end_ptr;
  uint32_t define_symbol_instances, symbols_in_definition, symbol, symbol_inst;
  uint8_t new_symbol_code_length, SID_symbol;
  uint8_t tag_type = 0;

  EncodeNewType(2 * in_definition + prior_is_cap);
  define_symbol_instances = sd[define_symbol].count;
  if (define_symbol_instances != 1)
    new_symbol_code_length = sd[define_symbol].code_length;
  else
    new_symbol_code_length = 0x20;

  // send symbol length, instances and ergodicity bit
  if (define_symbol < num_base_symbols) {
    EncodeSID(prior_is_cap, 0);
    if (define_symbol_instances == 1)
      EncodeINST(prior_is_cap, 0, MAX_INSTANCES_FOR_REMOVE - 1);
    else if (define_symbol_instances <= MAX_INSTANCES_FOR_REMOVE)
      EncodeINST(prior_is_cap, 0, define_symbol_instances - 2);
    else
      EncodeINST(prior_is_cap, 0, MAX_INSTANCES_FOR_REMOVE + max_regular_code_length - new_symbol_code_length);
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
          InitBaseSymbolCap(prior_end, new_symbol_code_length, &cap_symbol_defined, &cap_lock_symbol_defined,
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
              if (symbol_lengths[j1] != 0)
                InitTrailingCharBin(prior_end, j1, symbol_lengths[j1]);
              else if ((j1 == 'C') && (cap_symbol_defined != 0))
                InitTrailingCharBin(prior_end, 'C', symbol_lengths[j1]);
              else if ((j1 == 'B') && (cap_lock_symbol_defined != 0))
                InitTrailingCharBin(prior_end, 'B', symbol_lengths[j1]);
            } while (j1-- != 0);
          }
        }
      }
      else {
        prior_end = (uint8_t)define_symbol;
        symbol_lengths[prior_end] = new_symbol_code_length;
        InitBaseSymbolCap(prior_end, new_symbol_code_length, &cap_symbol_defined, &cap_lock_symbol_defined,
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
            if (symbol_lengths[j1] != 0)
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
              if (symbol_lengths[j1] != 0)
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
          if (symbol_lengths[j1] != 0)
            InitTrailingCharBin(prior_end, j1, symbol_lengths[j1]);
        } while (j1-- != 0);
      }
    }
    prior_symbol = define_symbol;
    prior_is_cap = sd[define_symbol].type & 1;
    if (found_first_symbol == 0) {
      found_first_symbol = 1;
      end_char = prior_end;
      nbob[end_char][max_code_length] = 1;
      sum_nbob[end_char] = 1;
    }
    if (define_symbol_instances == 1)
      return(1);
  }
  else {
    num_grammar_rules++;
    define_symbol_start_ptr = symbol_array + sd[define_symbol].define_symbol_start_index;
    define_string_ptr = define_symbol_start_ptr;
    define_string_end_ptr = symbol_array + sd[define_symbol + 1].define_symbol_start_index - 1;

    // count the symbols in the definition
    symbols_in_definition = 0;
    while (define_string_ptr != define_string_end_ptr) {
      if ((sd[*define_string_ptr].count != 1) || (*define_string_ptr < num_base_symbols))
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
    uint8_t saved_prior_is_cap = prior_is_cap;

    // write the symbol string
    define_string_ptr = define_symbol_start_ptr;
    while (define_string_ptr != define_string_end_ptr) {
      symbol = *define_string_ptr++;
      symbol_inst = sd[symbol].hits++;
      if (symbol_inst == 0) {
        if (embed_define(symbol, 1) == 0)
          return(0);
      }
      else {
        if ((sd[symbol].type & 8) != 0) {
          if (prior_is_cap == 0)
            update_queue(symbol, 1);
          else
            update_queue_prior_cap(symbol, 1);
        }
        else {
          EncodeDictType(2 + prior_is_cap);
          encode_dictionary_symbol(symbol);
          if (sd[symbol].count <= MAX_INSTANCES_FOR_REMOVE) {
            if (sd[symbol].count == sd[symbol].hits)
              remove_dictionary_symbol(symbol, sd[symbol].code_length);
            else if (use_mtf != 0) {
              if ((sd[symbol].type & 4) != 0) {
                if (transmits[num_transmits].distance != 0xFFFFFFFF) {
                  if ((sd[symbol].hits + 1 != sd[symbol].count) || ((sd[symbol].type & 0x80) != 0))
                    EncodeGoMtf(sd[symbol].count, 0, 1);
                  remove_dictionary_symbol(symbol, sd[symbol].code_length);
                  add_symbol_to_queue(symbol);
                }
                else
                  EncodeGoMtf(sd[symbol].count, 0, 0);
              }
            }
          }
          else if ((sd[symbol].type & 4) != 0) {
            if (transmits[num_transmits].distance != 0xFFFFFFFF) {
              EncodeGoMtf(sd[symbol].code_length + MAX_INSTANCES_FOR_REMOVE, 0, 1);
              remove_dictionary_symbol(symbol, sd[symbol].code_length);
              add_symbol_to_queue(symbol);
            }
            else
              EncodeGoMtf(sd[symbol].code_length + MAX_INSTANCES_FOR_REMOVE, 0, 0);
          }
        }
        prior_is_cap = sd[symbol].type & 1;
        prior_symbol = symbol;
        num_transmits++;
      }
      prior_end = sd[symbol].ends;
    }
    prior_symbol = define_symbol;

    if (define_symbol_instances <= MAX_INSTANCES_FOR_REMOVE)
      EncodeINST(saved_prior_is_cap, SID_symbol, define_symbol_instances - 2);
    else
      EncodeINST(saved_prior_is_cap, SID_symbol,
          MAX_INSTANCES_FOR_REMOVE - 1 + max_regular_code_length - new_symbol_code_length);

    if (cap_encoded != 0) {
      if ((sd[define_symbol].type & 0x40) != 0) {
        if ((sd[define_symbol].type & 0x20) != 0)
          tag_type++;
        EncodeWordTag(tag_type++);
      }
      else if ((sd[symbol_array[sd[define_symbol + 1].define_symbol_start_index - 2]].type & 0x60)
            > (sd[define_symbol].type & 0x60))
        sd[define_symbol].type
            += (sd[symbol_array[sd[define_symbol + 1].define_symbol_start_index - 2]].type & 0x60) - 0x20;
    }
  }

  if ((use_mtf != 0) && ((new_symbol_code_length >= 11) || (define_symbol_instances <= MAX_INSTANCES_FOR_REMOVE))) {
    if (define_symbol_instances > MAX_INSTANCES_FOR_REMOVE) {
      if ((sd[define_symbol].type & 4) != 0) {
        EncodeERG(tag_type, 1);
        if (transmits[num_transmits].distance != 0xFFFFFFFF) {
          EncodeGoMtf(new_symbol_code_length + MAX_INSTANCES_FOR_REMOVE, 2, 1);
          add_symbol_to_queue(define_symbol);
        }
        else {
          EncodeGoMtf(new_symbol_code_length + MAX_INSTANCES_FOR_REMOVE, 2, 0);
          if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
            return(0);
        }
      }
      else {
        EncodeERG(tag_type, 0);
        if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
          return(0);
      }
    }
    else if ((sd[define_symbol].type & 4) != 0) {
      EncodeERG(define_symbol_instances + 1, 1);
      if (transmits[num_transmits].distance != 0xFFFFFFFF) {
        if (define_symbol_instances > 2)
          EncodeGoMtf(define_symbol_instances, 2, 1);
        add_symbol_to_queue(define_symbol);
      }
      else {
        if (define_symbol_instances > 2)
          EncodeGoMtf(define_symbol_instances, 2, 0);
        if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
          return(0);
      }
    }
    else {
      EncodeERG(define_symbol_instances + 1, 0);
      if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
        return(0);
    }
  }
  else if (add_dictionary_symbol(define_symbol, new_symbol_code_length) == 0)
    return(0);
  num_transmits++;
  return(1);
}


void replace_symbol(uint32_t * symbol_array, uint32_t symbol, uint32_t ** symbol2_ptr_ptr,
    uint32_t * num_more_than_15_inst_definitions_ptr) {
  uint32_t * define_string_ptr = symbol_array + sd[symbol].define_symbol_start_index;
  uint32_t * define_string_end_ptr = symbol_array + sd[symbol + 1].define_symbol_start_index - 1;
  while (define_string_ptr != define_string_end_ptr) {
    uint32_t symbol2 = *define_string_ptr++;
    if ((symbol2 >= num_base_symbols) && (sd[symbol2].code_length != 0))
      replace_symbol(symbol_array, symbol2, symbol2_ptr_ptr, num_more_than_15_inst_definitions_ptr);
    else {
      *((*symbol2_ptr_ptr)++) = symbol2;
      if ((sd[symbol2].code_length != 2) && (sd[symbol2].count++ == MAX_INSTANCES_FOR_REMOVE))
        (*num_more_than_15_inst_definitions_ptr)++;
    }
  }
  return;
}


uint8_t GLZAencode(size_t in_size, uint8_t * inbuf, size_t * outsize_ptr, uint8_t * outbuf, FILE * fd, size_t file_size,
    struct param_data * params) {
  const uint8_t INSERT_SYMBOL_CHAR = 0xFE;
  const uint8_t DEFINE_SYMBOL_CHAR = 0xFF;
  const size_t WRITE_SIZE = 0x40000;
  uint8_t temp_char, base_bits, format, verbose, code_length, increase_length, decrease_length;
  uint8_t *in_char_ptr, *end_char_ptr;
  uint16_t queue_position;
  uint32_t i, j, num_symbols_defined, num_definitions_to_code, grammar_size, dictionary_size;
  uint32_t num_more_than_15_inst_definitions, num_greater_500, num_transmits_over_sqrt2, num_mtfs;
  uint32_t UTF8_value, max_UTF8_value, symbol, symbol_inst, prior_repeats, next_symbol;
  uint32_t min_ranked_symbols, ranked_symbols_save, num_new_symbols, num_symbols_to_code, num_rules_reversed;
  uint32_t code_length_limit, mtf_miss_code_space, min_code_space, rules_reduced;
  uint32_t mtf_started[MAX_INSTANCES_FOR_REMOVE + 1], mtf_hits[MAX_INSTANCES_FOR_REMOVE + 1];
  uint32_t mtf_peak[MAX_INSTANCES_FOR_REMOVE + 1], mtf_peak_mtf[MAX_INSTANCES_FOR_REMOVE + 1];
  uint32_t mtf_in_dictionary[MAX_INSTANCES_FOR_REMOVE + 1], mtf_active[MAX_INSTANCES_FOR_REMOVE + 1];
  uint32_t *symbol_ptr, *symbol2_ptr, *symbol_array2, *end_symbol_ptr, *first_define_ptr, *max_ptr;
  uint32_t *ranked_symbols, *ranked_symbols2, *ranked_symbols_ptr, *ranked_symbols2_ptr, *end_ranked_symbols_ptr;
  uint32_t *min_ranked_symbols_ptr, *max_ranked_symbols_ptr, *min_one_instance_ranked_symbols_ptr, *peak_array;
  int32_t remaining_symbols_to_code, remaining_code_space, max_len_adj_profit;
  int32_t index_last_length[26], index_first_length[26];
  double symbol_inst_factor, codes_per_code_space;


  verbose = cap_encoded = UTF8_compliant = num_symbols_defined = 0;
  first_define_ptr = 0;
  base_bits = 8;
  use_mtf = 2;
  if (params != 0) {
    verbose = params->print_dictionary;
    use_mtf = params->use_mtf;
  }
  in_char_ptr = inbuf;
  end_char_ptr = inbuf + in_size;
  format = *in_char_ptr++;
  if ((format & 0x81) == 1) {
    cap_encoded = (format >> 1) & 1;
    UTF8_compliant = (format >> 2) & 1;
    format = 1;
    if (UTF8_compliant != 0) {
      base_bits = *in_char_ptr++;
      max_UTF8_value = 0x7F;
    }
  }
  if ((symbol_array = (uint32_t *)malloc(sizeof(uint32_t) * in_size)) == 0) {
    fprintf(stderr, "Symbol memory allocation failed\n");
    return(0);
  }
  symbol_ptr = symbol_array;

  if (UTF8_compliant != 0) {
    num_base_symbols = 1 << base_bits;
    while (in_char_ptr < end_char_ptr) {
      temp_char = *in_char_ptr++;
      if (temp_char == INSERT_SYMBOL_CHAR) {
        symbol = num_base_symbols;
        symbol += 0x10000 * (uint32_t)*in_char_ptr++;
        symbol += 0x100 * (uint32_t)*in_char_ptr++;
        symbol += (uint32_t)*in_char_ptr++;
        *symbol_ptr++ = symbol;
      }
      else if (temp_char == DEFINE_SYMBOL_CHAR) {
        if (first_define_ptr == 0)
          first_define_ptr = symbol_ptr;
        in_char_ptr += 3;
        *symbol_ptr++ = 0x80000000 + num_symbols_defined++;
      }
      else if (temp_char < START_UTF8_2BYTE_SYMBOLS)
        *symbol_ptr++ = (uint32_t)temp_char;
      else {
        if (temp_char >= 0xF0) { // 4 byte UTF-8 character
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
        if (UTF8_value > max_UTF8_value)
          max_UTF8_value = UTF8_value;
      }
    }
  }
  else {
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
        symbol = num_base_symbols;
        symbol += 0x10000 * (uint32_t)*in_char_ptr++;
        symbol += 0x100 * (uint32_t)*in_char_ptr++;
        symbol += (uint32_t)*in_char_ptr++;
        *symbol_ptr++ = symbol;
      }
      else {
        if (first_define_ptr == 0)
          first_define_ptr = symbol_ptr;
        in_char_ptr += 3;
        *symbol_ptr++ = 0x80000000 + num_symbols_defined++;
      }
    }
  }

  end_symbol_ptr = symbol_ptr;
  *end_symbol_ptr = UNIQUE_SYMBOL;
  num_codes = num_base_symbols + num_symbols_defined;
  grammar_size = symbol_ptr - symbol_array;
  if (first_define_ptr == 0)
    first_define_ptr = symbol_ptr;

  if ((0 == (symbol_array2 = (uint32_t *)malloc(sizeof(uint32_t) * (end_symbol_ptr - symbol_array))))
      || (0 == (sd = (struct symbol_data *)malloc(sizeof(struct symbol_data) * (num_codes + 1))))
      || (0 == (ranked_symbols = (uint32_t *)malloc(sizeof(uint32_t) * num_codes)))
      || (0 == (ranked_symbols2 = (uint32_t *)malloc(sizeof(uint32_t) * num_codes)))
      || (0 == (transmits = (struct transmit_symbols *)malloc(sizeof(struct transmit_symbols) * grammar_size)))) {
    fprintf(stderr, "Memory allocation failed\n");
    return(0);
  }

  // count the number of instances of each symbol
  for (i = 0 ; i < num_codes ; i++)
    sd[i].count = 0;
  symbol_ptr = symbol_array;
  while (symbol_ptr != end_symbol_ptr) {
    symbol = *symbol_ptr++;
    if ((int32_t)symbol >= 0)
      sd[symbol].count++;
    else
      sd[symbol - 0x80000000 + num_base_symbols].define_symbol_start_index = symbol_ptr - symbol_array;
  }
  sd[num_codes].define_symbol_start_index = symbol_ptr - symbol_array + 1;

  if (cap_encoded != 0) {
    i = 0;
    do {
      sd[i++].type = 0;
    } while (i != 0x61);
    do {
      sd[i++].type = 2;
    } while (i != 0x7B);
    do {
      sd[i++].type = 0;
    } while (i != num_base_symbols);
    sd[' '].type = 0x10;
    sd['B'].type = 0x11;
    sd['C'].type = 0x11;
    while (i < num_codes) {
      next_symbol = symbol_array[sd[i].define_symbol_start_index];
      while (next_symbol > i)
        next_symbol = symbol_array[sd[next_symbol].define_symbol_start_index];
      sd[i].type = sd[next_symbol].type & 2;
      next_symbol = symbol_array[sd[i + 1].define_symbol_start_index - 2];
      while (next_symbol > i)
        next_symbol = symbol_array[sd[next_symbol + 1].define_symbol_start_index - 2];
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
    for (i = num_base_symbols ; i < num_codes; i++)
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
  } while (++i < num_base_symbols);
  if (num_symbols_defined != 0) {
    while (i < num_codes) {
      double d_symbol_count = (double)sd[i++].count;
      order_0_entropy += d_symbol_count * (log_file_symbols - log2(d_symbol_count));
    }
    double d_symbol_count = (double)num_symbols_defined;
    order_0_entropy += d_symbol_count * (log_file_symbols - log2(d_symbol_count));
  }
  fprintf(stderr, "%u syms, dict. size %u, %.4f bits/sym, o0e %.2lf bytes\n",
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
    } while (++i < num_base_symbols);
    if (num_symbols_defined != 0) {
      while (i < num_codes) {
        if (sd[i].count > 1) {
          double d_symbol_count = (double)sd[i].count;
          order_0_entropy += d_symbol_count * (log_file_symbols - log2(d_symbol_count));
        }
        i++;
      }
      double d_symbol_count = (double)(num_symbols_defined - rules_reduced);
      order_0_entropy += d_symbol_count * (log_file_symbols - log2(d_symbol_count));
    }
    fprintf(stderr, "Eliminated %u single appearance grammar rules\n", rules_reduced);
    fprintf(stderr, "%u syms, dict. size %u, %.4f bits/sym, o0e %.2lf bytes\n",
        (unsigned int)grammar_size, (unsigned int)(num_symbols_defined - rules_reduced),
        (float)(order_0_entropy/(double)grammar_size), 0.125 * order_0_entropy);
  }

  uint32_t len_counts[16];
  uint32_t extra_len_bits = 0;
  for (i = 0 ; i < 16 ; i++)
    len_counts[i] = 0;
  for (i = num_base_symbols ; i < num_codes ; i++) {
    if (sd[i].count > 1) {
      uint32_t dl = sd[i + 1].define_symbol_start_index - sd[i].define_symbol_start_index - 1;
      if (dl < 16)
        len_counts[dl - 1]++;
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
  } while (++i < num_base_symbols);
  if (num_symbols_defined != 0) {
    while (i < num_codes) {
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
    fprintf(stderr, "Finished embedding grammar rules\n");
    fprintf(stderr, "Reduced grammar size: %u (%u terminals + %u rule symbols + %u repeats)\n",
      grammar_size, num_new_symbols + rules_reduced - num_symbols_defined, num_symbols_defined - rules_reduced,
      grammar_size - num_new_symbols);
    fprintf(stderr, "%.4f bits/symbol, plus %u length codes %.4f bits/code, o0e %.2lf bytes\n",
        (float)(order_0_entropy/(double)grammar_size), (unsigned int)(num_symbols_defined - rules_reduced),
        (float)(code_entropy/(double)len_codes), 0.125 * (order_0_entropy + code_entropy));
  }
#endif

  // sort symbols with 800 or fewer instances by putting them at the end of the sorted symbols array
  for (i = 2 ; i <= MAX_INSTANCES_FOR_REMOVE ; i++) {
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

  num_more_than_15_inst_definitions = min_ranked_symbols_ptr - ranked_symbols;

  for (i = MAX_INSTANCES_FOR_REMOVE ; i < 801 ; i++) {
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
  max_regular_code_length = 2;
  if (sd[ranked_symbols[0]].count > MAX_INSTANCES_FOR_REMOVE)
    max_regular_code_length = (uint8_t)log2((double)(grammar_size - num_new_symbols) * 0.094821); // sqrt(2) / 15

  for (i = num_base_symbols ; i < num_codes ; i++) {
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
    i = num_base_symbols;
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
    i = num_base_symbols;
    while (i < num_codes) {
      if (sd[i].starts == 0)
        sd[i].starts = find_first(i);
      if (sd[i].ends == 0)
        sd[i].ends = find_last(i);
      i++;
    }
  }

  num_transmits = 0;
  dictionary_size = 0;
  for (i = 0 ; i < num_codes ; i++) {
    sd[i].hits = 0;
    sd[i].previous = 0xFFFFFFFF;
  }
  symbol_ptr = symbol_array;

  while (symbol_ptr < first_define_ptr) {
    symbol = *symbol_ptr++;
    if (sd[symbol].previous == 0xFFFFFFFF) {
      get_embedded_symbols(symbol);
      dictionary_size += get_dictionary_size(symbol);
    }
    else {
      transmits[sd[symbol].previous].distance = num_transmits - sd[symbol].previous;
      transmits[num_transmits].previous_index = sd[symbol].previous;
      transmits[num_transmits].distance = 0xFFFFFFFF;
      sd[symbol].previous = num_transmits++;
    }
  }
#ifdef PRINTON
  fprintf(stderr, "Parsed %u level 0 symbols\n", (unsigned int)(first_define_ptr - symbol_array));
#endif

  num_transmits_over_sqrt2 = (uint32_t)((float)num_transmits * 0.7071);
  if (((num_transmits_over_sqrt2 >> 10) < MAX_INSTANCES_FOR_REMOVE) && (use_mtf == 2))
    use_mtf = 0;

  for (i = 0 ; i < num_base_symbols ; i++) {
    if (sd[i].count == 1)
      sd[i].code_length = 2;
    else
      sd[i].code_length = 0;
  }
  for (i = num_base_symbols ; i < num_codes ; i++) {
    if (sd[i].count == 1)
      sd[i].code_length = 1;
    else
      sd[i].code_length = 0;
  }

  i = num_more_than_15_inst_definitions;
  while ((i < num_definitions_to_code) && (sd[ranked_symbols[i]].count > 2))
    i++;
  uint32_t num_2_inst_definitions = num_definitions_to_code - i;
  num_rules_reversed = 0;
  while (i < num_definitions_to_code) {
    uint32_t * define_string_ptr = symbol_array + sd[ranked_symbols[i]].define_symbol_start_index;
    uint32_t * define_string_end_ptr = symbol_array + sd[ranked_symbols[i] + 1].define_symbol_start_index - 1;
    if (define_string_end_ptr - define_string_ptr == 2) {
      uint32_t last_transmit = sd[ranked_symbols[i]].previous;
      uint32_t distance = last_transmit - transmits[last_transmit].previous_index;
      float score = 0.0;
      if ((distance <= num_transmits / 20))
        score = (float)log2((double)num_transmits / (2.0 * (double)distance)) - 1.5 * log2((double)distance) + 10.5;
      if (score <= 0.0) {
        float cost = 1.0 + (float)log2(((double)(sd[*define_string_ptr].count - 1)
            * (double)(sd[*(define_string_ptr + 1)].count - 1)) / (double)num_2_inst_definitions);
        if (sd[ranked_symbols[i]].hits != 0)
          cost -= (float)sd[ranked_symbols[i]].hits;
        if (cost >= 0.0) {
          sd[ranked_symbols[i]].code_length = 1;
          num_rules_reversed++;
        }
      }
    }
    i++;
  }

  // unmark rules that contain reversed rules
  i = num_definitions_to_code - num_2_inst_definitions;
  while (i < num_definitions_to_code) {
    if (sd[ranked_symbols[i]].code_length != 0) {
      uint32_t * define_string_ptr = symbol_array + sd[ranked_symbols[i]].define_symbol_start_index;
      if ((sd[*define_string_ptr].code_length != 0) || (sd[*(define_string_ptr + 1)].code_length != 0)) {
        sd[ranked_symbols[i]].code_length = 0;
        num_rules_reversed--;
      }
    }
    i++;
  }

  symbol2_ptr = symbol_array2;
  symbol_ptr = symbol_array;
  while (symbol_ptr < end_symbol_ptr) {
    symbol = *symbol_ptr++;
    if ((symbol & 0x80000000) == 0) {
      if ((symbol >= num_base_symbols) && (sd[symbol].code_length != 0))
        replace_symbol(symbol_array, symbol, &symbol2_ptr, &num_more_than_15_inst_definitions);
      else
        *symbol2_ptr++ = symbol;
    }
    else if (sd[symbol - 0x80000000 + num_base_symbols].code_length != 0) {
      do {
        if ((sd[*symbol_ptr].code_length != 2) && (--sd[*symbol_ptr].count == MAX_INSTANCES_FOR_REMOVE))
          num_more_than_15_inst_definitions--;
      } while (*++symbol_ptr < 0x80000000);
    }
    else
      *symbol2_ptr++ = symbol;
  }
  memcpy(symbol_array, symbol_array2, sizeof(uint32_t) * (symbol2_ptr - symbol_array2));
  end_symbol_ptr = symbol_array + (symbol2_ptr - symbol_array2);
  *end_symbol_ptr = UNIQUE_SYMBOL;

#ifdef PRINTON
  fprintf(stderr, "Eliminated %u two instance rules\n", num_rules_reversed);
#endif

  prior_symbol = num_base_symbols - 1;
  symbol_ptr = first_define_ptr;
  while (symbol_ptr < end_symbol_ptr) {
    symbol = *symbol_ptr++;
    if ((symbol & 0x80000000) != 0) {
      symbol += num_base_symbols - 0x80000000;
      sd[symbol].define_symbol_start_index = symbol_ptr - symbol_array;
      if (++prior_symbol == num_base_symbols)
        first_define_ptr = symbol_ptr - 1;
      if (prior_symbol != symbol) {
        sd[prior_symbol].define_symbol_start_index = symbol_ptr - symbol_array;
        prior_symbol = symbol;
      }
    }
  }
  if (++prior_symbol != num_codes)
    sd[prior_symbol].define_symbol_start_index = symbol2_ptr - symbol_array2 + 1;
  sd[num_codes].define_symbol_start_index = symbol2_ptr - symbol_array2 + 1;

  i = 0;
  while (i < num_definitions_to_code) {
    if (sd[ranked_symbols[i]].code_length != 0) {
      num_definitions_to_code--;
      num_new_symbols--;
      uint32_t bad_symbol = ranked_symbols[i];
      ranked_symbols[i] = ranked_symbols[num_definitions_to_code];
      ranked_symbols[num_definitions_to_code] = bad_symbol;
    }
    else {
      if ((i != 0) && (sd[ranked_symbols[i]].count > sd[ranked_symbols[i - 1]].count)) {
        uint32_t temp_symbol = ranked_symbols[i];
        uint32_t temp_count = sd[temp_symbol].count;
        uint32_t new_rank = i - 1;
        while ((new_rank != 0) && (temp_count > sd[ranked_symbols[new_rank - 1]].count)) {
          ranked_symbols[new_rank + 1] = ranked_symbols[new_rank];
          new_rank--;
        }
        ranked_symbols[new_rank + 1] = ranked_symbols[new_rank];
        ranked_symbols[new_rank] = temp_symbol;
      }
      i++;
    }
  }

  num_transmits = 0;
  for (i = 0 ; i < num_codes ; i++) {
    sd[i].space_score = 0;
    sd[i].previous = 0xFFFFFFFF;
  }
  prior_symbol = (uint32_t)-1;
  symbol_ptr = symbol_array;

  while (symbol_ptr < first_define_ptr) {
    symbol = *symbol_ptr++;
    if (sd[symbol].previous == 0xFFFFFFFF)
      get_embedded_symbols2(symbol);
    else {
      transmits[sd[symbol].previous].distance = num_transmits - sd[symbol].previous;
      transmits[num_transmits].previous_index = sd[symbol].previous;
      transmits[num_transmits].symbol = symbol;
      transmits[num_transmits].distance = 0xFFFFFFFF;
      sd[symbol].previous = num_transmits++;
      if (sd[prior_symbol].type >= 0x20) {
        if (sd[symbol].starts == 0x20)
          sd[prior_symbol].space_score++;
        else
          sd[prior_symbol].space_score -= 4;
      }
      prior_symbol = symbol;
    }
  }

  num_symbols_to_code = grammar_size - num_new_symbols - rules_reduced;
  num_transmits_over_sqrt2 = (uint32_t)((float)num_transmits * 0.7071);
  num_mtfs = 0;

  if (use_mtf != 0) {
    for (i = 0 ; i < num_codes ; i++) {
      if ((sd[i].count <= (num_transmits_over_sqrt2 >> 10)) || (sd[i].count <= MAX_INSTANCES_FOR_REMOVE))
        sd[i].type |= 4;
    }
    for (i = 0 ; i < num_codes ; i++)
      sd[i].hits = 0;

    for (i = 0 ; i < num_transmits ; i++) {
      uint32_t distance = transmits[i].distance;
      if (distance != 0xFFFFFFFF) {
        uint32_t symbol = transmits[i].symbol;
        if (((sd[symbol].type & 4) != 0) && (distance <= num_transmits / (10 * sd[symbol].count))) {
          transmits[i].score = (float)log2((double)num_transmits / ((double)sd[symbol].count * (double)distance))
              - 1.5 * log2((double)distance) + 10.5;
          if (transmits[i].score < 0.0) {
            transmits[i + transmits[i].distance].previous_index = 0xFFFFFFFF;
            transmits[i].distance = 0xFFFFFFFF;
          }
          else
            num_mtfs++;
        }
        else {
          transmits[i + transmits[i].distance].previous_index = 0xFFFFFFFF;
          transmits[i].distance = 0xFFFFFFFF;
        }
      }
    }
#ifdef PRINTON
  fprintf(stderr, "Found %u MTF candidates, ", (unsigned int)num_mtfs);
#endif

    queue_size = 0;
    for (i = 0 ; i < num_transmits ; i++) {
      uint16_t limit_position;
      uint32_t symbol = transmits[i].symbol;
      sd[symbol].previous = i;

      if ((sd[symbol].type & 8) != 0) {
        queue_position = 0;
        while (queue[queue_position] != symbol)
          queue_position++;
        add_mtf_hit_scores(&sd[symbol], queue_position, num_transmits_over_sqrt2);
        if (transmits[i].distance != 0xFFFFFFFF) {
          limit_position = get_mtf_overflow_position(sd, queue, queue_position, num_transmits_over_sqrt2);
          if (limit_position != 0) {
            sd[queue[limit_position]].type &= 0xF7;
            queue_size--;
            while (queue_position != queue_size) {
              queue[queue_position] = queue[queue_position + 1];
              queue_position++;
            }
            queue_position = limit_position;
          }
          while (queue_position-- != 0)
            queue[queue_position + 1] = queue[queue_position];
          queue[0] = symbol;
        }
        else {
          sd[symbol].type &= 0xF7;
          queue_size--;
          while (queue_position != queue_size) {
            queue[queue_position] = queue[queue_position + 1];
            queue_position++;
          }
        }
      }
      else if (transmits[i].distance != 0xFFFFFFFF) {
        sd[symbol].type |= 8;
        limit_position = get_mtf_overflow_position(sd, queue, queue_size, num_transmits_over_sqrt2);
        if (limit_position != 0) {
          sd[queue[limit_position]].type &= 0xF7;
          queue_position = limit_position;
        }
        else {
          if (queue_size == 0x1A0) {
            float low_score = transmits[sd[queue[0x19F]].previous].score;
            uint16_t low_score_pos = 0x19F;
            for (j = 0 ; j < 0x19F ; j++) {
              if (transmits[sd[queue[j]].previous].score < low_score) {
                low_score = transmits[sd[queue[j]].previous].score;
                low_score_pos = j;
              }
            }
            sd[queue[low_score_pos]].type &= 0xF7;
            queue_position = low_score_pos;
          }
          else {
            queue_position = queue_size++;
          }
        }
        while (queue_position-- != 0)
          queue[queue_position + 1] = queue[queue_position];
        queue[0] = symbol;
      }
    }
    for (i = 0 ; i < num_codes ; i++) {
      if (((sd[i].type & 4) != 0) && (sd[i].count > MAX_INSTANCES_FOR_REMOVE)
          && ((float)sd[i].hits < get_mtf_score_limit(sd[i].count, num_transmits_over_sqrt2) * (float)(sd[i].count - 1)))
        sd[i].type &= 0xFB;
      sd[i].hits = 0;
    }

    queue_size = 0;
    for (i = 0 ; i < num_transmits ; i++) {
      uint32_t symbol = transmits[i].symbol;
      sd[symbol].previous = i;
      if ((sd[symbol].type & 8) != 0) {
        queue_position = 0;
        while (queue[queue_position] != symbol)
          queue_position++;
        add_mtf_hit_scores(&sd[symbol], queue_position, num_transmits_over_sqrt2);
        if (transmits[i].distance != 0xFFFFFFFF) {
          while (queue_position-- != 0)
            queue[queue_position + 1] = queue[queue_position];
          queue[0] = symbol;
        }
        else {
          sd[symbol].type &= 0xF7;
          queue_size--;
          while (queue_position != queue_size) {
            queue[queue_position] = queue[queue_position + 1];
            queue_position++;
          }
        }
      }
      else if (transmits[i].distance != 0xFFFFFFFF) {
        if ((sd[symbol].type & 4) != 0) {
          sd[symbol].type |= 8;
          if (queue_size == 0x100) {
            float low_score = transmits[sd[queue[0xFF]].previous].score;
            uint16_t low_score_pos = 0xFF;
            for (j = 0 ; j < 0xFF ; j++) {
              if (transmits[sd[queue[j]].previous].score < low_score) {
                low_score = transmits[sd[queue[j]].previous].score;
                low_score_pos = j;
              }
            }
            sd[queue[low_score_pos]].type &= 0xF7;
            j = sd[queue[low_score_pos]].previous;
            transmits[j + transmits[j].distance].previous_index = 0xFFFFFFFF;
            transmits[j].distance = 0xFFFFFFFF;
            queue_position = low_score_pos;
          }
          else
            queue_position = queue_size++;
          while (queue_position-- != 0)
            queue[queue_position + 1] = queue[queue_position];
          queue[0] = symbol;
        }
        else {
          transmits[i + transmits[i].distance].previous_index = 0xFFFFFFFF;
          transmits[i].distance = 0xFFFFFFFF;
        }
      }
    }
    for (i = 0 ; i < num_codes ; i++) {
      if ((sd[i].count > MAX_INSTANCES_FOR_REMOVE) && (sd[i].count <= (num_transmits_over_sqrt2 >> 10))
          && ((sd[i].type & 4) != 0)
          && ((float)sd[i].hits < get_mtf_score_limit(sd[i].count, num_transmits_over_sqrt2) * (float)(sd[i].count - 1)))
        sd[i].type &= 0xFB;
      sd[i].hits = 0;
    }

    num_mtfs = 0;
    queue_size = 0;
    for (i = 0 ; i < num_transmits ; i++) {
      transmits[i].hurts = 0;
      uint32_t symbol = transmits[i].symbol;
      sd[symbol].previous = i;
      if ((sd[symbol].type & 8) != 0) {
        queue_position = 0;
        while (queue[queue_position] != symbol)
          queue_position++;
        if (queue_position + transmits[transmits[i].previous_index].hurts
            >= 10 + (uint32_t)(30.0 * (log2((double)num_transmits / (double)sd[transmits[i].symbol].count) - 9.0))) {
          transmits[transmits[i].previous_index].distance = 0xFFFFFFFF;
          transmits[i].previous_index = 0xFFFFFFFF;
        }
        else {
          if (queue_position > 0x10)
            for (j = 0 ; j < queue_position ; j++)
              transmits[sd[queue[j]].previous].hurts += 1;
          else if (queue_position > 5)
            for (j = 0 ; j < queue_position ; j++)
              transmits[sd[queue[j]].previous].hurts += 2;
          else if (queue_position > 1)
            for (j = 0 ; j < queue_position ; j++)
              transmits[sd[queue[j]].previous].hurts += 3;
          sd[symbol].hits++;
          num_mtfs++;
        }
        if (transmits[i].distance != 0xFFFFFFFF) {
          while (queue_position-- != 0)
            queue[queue_position + 1] = queue[queue_position];
          queue[0] = symbol;
        }
        else {
          sd[symbol].type &= 0xF7;
          queue_size--;
          while (queue_position != queue_size) {
            queue[queue_position] = queue[queue_position + 1];
            queue_position++;
          }
        }
      }
      else if (transmits[i].distance != 0xFFFFFFFF) {
        if ((sd[symbol].type & 4) != 0) {
          sd[symbol].type |= 8;
          queue_position = queue_size++;
          while (queue_position-- != 0)
            queue[queue_position + 1] = queue[queue_position];
          queue[0] = symbol;
        }
        else {
          transmits[i + transmits[i].distance].previous_index = 0xFFFFFFFF;
          transmits[i].distance = 0xFFFFFFFF;
        }
      }
    }
    for (i = 0 ; i < num_codes ; i++)
      if (sd[i].hits == 0)
        sd[i].type &= 0xFB;
  }

#ifdef PRINTON
  fprintf(stderr, "%u MTF symbols\n", (unsigned int)num_mtfs);
#endif

  for (i = 2 ; i <= MAX_INSTANCES_FOR_REMOVE ; i++) {
    mtf_started[i] = 0;
    mtf_peak[i] = 0;
    mtf_peak_mtf[i] = 0;
    mtf_active[i] = 0;
    mtf_hits[i] = 0;
    mtf_in_dictionary[i] = 0;
  }

  for (i = 0 ; i < num_codes ; i++)
    sd[i].previous = 0;

  for (i = 0 ; i < num_transmits ; i++) {
    uint32_t symbol = transmits[i].symbol;
    sd[symbol].previous++;
    uint32_t count = sd[symbol].count;
    if (count <= MAX_INSTANCES_FOR_REMOVE) {
      if (mtf_in_dictionary[count] > mtf_peak_mtf[count])
        mtf_peak_mtf[count] = mtf_in_dictionary[count];
      if (mtf_active[count] > mtf_peak[count])
        mtf_peak[count] = mtf_active[count];
      if (sd[symbol].previous == 1) {
        mtf_started[count]++;
        mtf_active[count]++;
        if (transmits[i].distance != 0xFFFFFFFF)
          sd[symbol].type |= 8;
        else
          mtf_in_dictionary[count]++;
      }
      else if (sd[symbol].previous == count) {
        mtf_active[count]--;
        if ((sd[symbol].type & 8) != 0) {
          sd[symbol].type &= 0xF7;
          mtf_hits[count]++;
        }
        else
          mtf_in_dictionary[count]--;
      }
      else {
        if ((sd[symbol].type & 8) != 0) {
          mtf_hits[count]++;
          if (transmits[i].distance == 0xFFFFFFFF) {
            sd[symbol].type &= 0xF7;
            mtf_in_dictionary[count]++;
          }
        }
        else if (transmits[i].distance != 0xFFFFFFFF) {
          sd[symbol].type |= 8;
          mtf_in_dictionary[count]--;
        }
      }
    }
    else if ((transmits[i].distance != 0xFFFFFFFF) && ((sd[symbol].type & 4) == 0)) {
      transmits[i + transmits[i].distance].previous_index = 0xFFFFFFFF;
      transmits[i].distance = 0xFFFFFFFF;
    }
  }

  if (use_mtf == 2) {
    use_mtf = 0;
    double sum_expected_peak = 0.0;
    double sum_actual_peak = 0.0;
    for (i = 2 ; i <= 15 ; i++) {
      sum_expected_peak += (double)(i - 1) * (double)mtf_started[i] * (1.0 - (1.0 / (double)(1 << (i - 1))));
      sum_actual_peak += (double)(i - 1) * (double)mtf_peak_mtf[i];
    }
    double score1, score2;
    score1 = 5.75 * (double)mtf_started[2] / ((double)mtf_peak_mtf[2] * (32.8 - log2((double)num_symbols_to_code)));
    score2 = sum_expected_peak / sum_actual_peak;
    if (score1 + score2 > 2.08)
      use_mtf = 1;
  }

  if (use_mtf != 0) {
    for (i = 0 ; i < num_codes ; i++) {
      if (sd[i].count > MAX_INSTANCES_FOR_REMOVE) {
        if ((sd[i].type & 4) != 0) {
          if (sd[i].count - sd[i].hits <= MAX_INSTANCES_FOR_REMOVE) {
            num_symbols_to_code -= sd[i].count - (MAX_INSTANCES_FOR_REMOVE + 1);
            sd[i].count = MAX_INSTANCES_FOR_REMOVE + 1;
          }
          else {
            num_symbols_to_code -= sd[i].hits;
            sd[i].count -= sd[i].hits;
          }
        }
      }
      else
        num_symbols_to_code -= sd[i].hits;
    }
#ifdef PRINTON
    fprintf(stderr, "Updating symbol ranks\r");
#endif

    // update the symbol ranks
    max_ptr = ranked_symbols + num_more_than_15_inst_definitions;
    ranked_symbols2_ptr = ranked_symbols2 + num_more_than_15_inst_definitions;
    for (i = MAX_INSTANCES_FOR_REMOVE + 1 ; i < 501 ; i++) {
      ranked_symbols_ptr = max_ptr;
      while ((--ranked_symbols_ptr >= ranked_symbols) && (sd[*ranked_symbols_ptr].count == i))
        *--ranked_symbols2_ptr = *ranked_symbols_ptr;
      max_ptr = ranked_symbols_ptr + 1;
      while (--ranked_symbols_ptr >= ranked_symbols) {
        if (sd[*ranked_symbols_ptr].count == i)
          *--ranked_symbols2_ptr = *ranked_symbols_ptr;
      }
    }
    num_greater_500 = ranked_symbols2_ptr - ranked_symbols2;
    ranked_symbols_ptr = max_ptr;
    while (--ranked_symbols_ptr >= ranked_symbols) {
      if (sd[*ranked_symbols_ptr].count >= 501)
        *--ranked_symbols2_ptr = *ranked_symbols_ptr;
    }
    for (i = 1 ; i < num_greater_500 ; i++) {
      uint32_t temp_symbol = ranked_symbols2[i];
      uint32_t temp_count = sd[temp_symbol].count;
      if (temp_count > sd[ranked_symbols2[i - 1]].count) {
        ranked_symbols2[i] = ranked_symbols2[i - 1];
        j = i - 1;
        while ((j != 0) && (temp_count > sd[ranked_symbols2[j - 1]].count)) {
          ranked_symbols2[j] = ranked_symbols2[j - 1];
          j--;
        }
        ranked_symbols2[j] = temp_symbol;
      }
    }
    for (i = 0 ; i < num_more_than_15_inst_definitions ; i++)
      ranked_symbols[i] = ranked_symbols2[i];
    peak_array = mtf_peak_mtf;
  }
  else {
    for (i = 0 ; i < num_codes ; i++)
      sd[i].type &= 0xFB;
    for (i = 2 ; i <= MAX_INSTANCES_FOR_REMOVE ; i++)
      mtf_hits[i] = 0;
    peak_array = mtf_peak;
  }

  // Calculate dictionary code lengths
  if (peak_array[2] != 0) {
    queue_miss_code_length[2] = (uint32_t)(0.5 + log2((double)num_symbols_to_code
        * (double)peak_array[2] / (double)(mtf_started[2] - mtf_hits[2])));
    if (queue_miss_code_length[2] > 25)
      queue_miss_code_length[2] = 25;
  }
  else
    queue_miss_code_length[2] = 25;
  for (i = 3 ; i <= MAX_INSTANCES_FOR_REMOVE ; i++) {
    if (peak_array[i] != 0) {
      queue_miss_code_length[i] = (uint32_t)(0.5 + log2((double)num_symbols_to_code
          * (double)peak_array[i] / (double)(mtf_started[i] * (i - 1) - mtf_hits[i])));
      if (queue_miss_code_length[i] > queue_miss_code_length[i - 1])
        queue_miss_code_length[i] = queue_miss_code_length[i - 1];
      else if (queue_miss_code_length[i] < queue_miss_code_length[i - 1] - 1)
        queue_miss_code_length[i] = queue_miss_code_length[i - 1] - 1;
    }
    else
      queue_miss_code_length[i] = queue_miss_code_length[i - 1];
  }
  if ((use_mtf != 0) && (queue_miss_code_length[12] <= max_regular_code_length))
    max_regular_code_length--;

  remaining_symbols_to_code = 0;
  for (i = 0 ; i < num_more_than_15_inst_definitions ; i++)
    remaining_symbols_to_code += sd[ranked_symbols[i]].count - 1;
  mtf_miss_code_space = 0;
  for (i = 2 ; i <= MAX_INSTANCES_FOR_REMOVE; i++) {
    if (queue_miss_code_length[i] <= max_regular_code_length)
      queue_miss_code_length[i] = max_regular_code_length + 1;
    mtf_miss_code_space += (1 << (30 - queue_miss_code_length[i])) * peak_array[i];
  }
  max_code_length = queue_miss_code_length[2];
  remaining_code_space = (1 << 30) - (1 << (30 - max_code_length)) - mtf_miss_code_space;
  min_code_space = 1 << (30 - (queue_miss_code_length[MAX_INSTANCES_FOR_REMOVE] - 1));
  codes_per_code_space = (double)remaining_symbols_to_code / (double)remaining_code_space;
  max_regular_code_length = 1;
  prior_repeats = 0;
  for (i = 0 ; i <= 25 ; i++)
    index_last_length[i] = -1;

  // optimize code lengths
  for (i = 0 ; i < num_more_than_15_inst_definitions ; i++) {
    symbol_inst = sd[ranked_symbols[i]].count;
    if (--symbol_inst != prior_repeats) {
      prior_repeats = symbol_inst;
      symbol_inst_factor = (double)0x5A827999 / (double)symbol_inst; // 0x40000000 * sqrt(2.0)
      code_length_limit = (uint32_t)log2(symbol_inst_factor * codes_per_code_space);
      if (code_length_limit < 2)
        code_length_limit = 2;
    }
    code_length = (uint8_t)log2(symbol_inst_factor
        * (1.0 + (double)(remaining_symbols_to_code - 15 * (num_more_than_15_inst_definitions - i - 1)))
        / (double)(remaining_code_space - min_code_space * (num_more_than_15_inst_definitions - i - 1)));
    if (code_length < code_length_limit)
      code_length = code_length_limit;
    if (code_length > max_code_length)
      code_length = max_code_length;
    if (code_length > max_regular_code_length) {
      if (code_length >= queue_miss_code_length[MAX_INSTANCES_FOR_REMOVE])
        code_length = queue_miss_code_length[MAX_INSTANCES_FOR_REMOVE] - 1;
      max_regular_code_length = code_length;
    }
    sd[ranked_symbols[i]].code_length = code_length;
    remaining_code_space -= 1 << (30 - code_length);
    remaining_symbols_to_code -= symbol_inst;

    if ((i != 0) && (sd[ranked_symbols[i - 1]].code_length > code_length)) {
      sd[ranked_symbols[++index_last_length[code_length]]].code_length = code_length;
      while (index_last_length[++code_length] == -1); // do nothing
      index_last_length[code_length]++;
      sd[ranked_symbols[i]].code_length = code_length;
    }
    else
      index_last_length[code_length] = i;
  }

  do {
    uint8_t min_code_length = sd[ranked_symbols[0]].code_length;
    for (i = min_code_length ; i < max_regular_code_length ; i++)
      if (index_last_length[i] == -1)
        min_code_length = i + 1;
    max_len_adj_profit = 0;  
    for (i = min_code_length ; i < max_regular_code_length ; i++) {
      int32_t len_adj_profit = -(sd[ranked_symbols[index_last_length[i]]].count - 1);
      for (j = i + 2 ; j <= max_regular_code_length ; j++) {
        len_adj_profit += sd[ranked_symbols[index_last_length[j - 1] + 1]].count - 1;
        if (index_last_length[j] != index_last_length[j - 1] + 1) {
          int32_t next_symbol_profit = sd[ranked_symbols[index_last_length[j - 1] + 2]].count - 1;
          if (len_adj_profit + next_symbol_profit > max_len_adj_profit) {
            max_len_adj_profit = len_adj_profit + next_symbol_profit;
            increase_length = i;
            decrease_length = j;
          }
        }
      }
    }
    if (max_len_adj_profit != 0) {
      sd[ranked_symbols[index_last_length[increase_length]--]].code_length++;
      for (j = increase_length + 2 ; j <= decrease_length ; j++)
        sd[ranked_symbols[++index_last_length[j - 1]]].code_length--;
      sd[ranked_symbols[++index_last_length[decrease_length - 1]]].code_length--;
      if (index_last_length[decrease_length - 1] == index_last_length[decrease_length])
        index_last_length[decrease_length] = -1;
    }
  } while (max_len_adj_profit != 0);

  j = 0;
  for (i = sd[ranked_symbols[0]].code_length ; i < max_regular_code_length ; i++) {
    if (index_last_length[i] >= 0) {
      index_first_length[i] = j;
      j = index_last_length[i] + 1;
    }
    else
      index_first_length[i] = -1;
  }

  do {
    max_len_adj_profit = 0;  
    for (i = sd[ranked_symbols[0]].code_length ; i < max_regular_code_length ; i++) {
      if (index_last_length[i] - index_first_length[i] >= 2) {
        int32_t len_adj_profit = sd[ranked_symbols[index_first_length[i]]].count - 1;
        len_adj_profit -= sd[ranked_symbols[index_last_length[i]]].count - 1;
        len_adj_profit -= sd[ranked_symbols[index_last_length[i] - 1]].count - 1;
        if (len_adj_profit > max_len_adj_profit) {
          max_len_adj_profit = len_adj_profit;
          decrease_length = i;
        }
      }
    }
    if (max_len_adj_profit != 0) {
      sd[ranked_symbols[index_first_length[decrease_length]]].code_length--;
      sd[ranked_symbols[index_last_length[decrease_length] - 1]].code_length++;
      sd[ranked_symbols[index_last_length[decrease_length]]].code_length++;
      if (index_first_length[decrease_length - 1] < 0)
        index_first_length[decrease_length - 1] = index_first_length[decrease_length];
      index_last_length[decrease_length - 1] = index_first_length[decrease_length];
      if (index_first_length[decrease_length + 1] < 0)
        index_last_length[decrease_length + 1] = index_last_length[decrease_length];
      index_first_length[decrease_length + 1] = index_last_length[decrease_length] - 1;
      if (index_last_length[i] - index_first_length[i] == 2) {
        index_first_length[decrease_length] = -1;
        index_last_length[decrease_length] = -1;
      }
      else {
        index_first_length[decrease_length] += 1;
        index_last_length[decrease_length] -= 2;
      }
    }
  } while (max_len_adj_profit != 0);

  for (i = 0 ; i < num_more_than_15_inst_definitions ; i++)
    if (sd[ranked_symbols[i]].code_length < 11)
      sd[ranked_symbols[i]].type &= 0xFB;

  for (i = num_more_than_15_inst_definitions ; i < num_definitions_to_code ; i++) {
    sd[ranked_symbols[i]].type &= 0xF7;
    sd[ranked_symbols[i]].code_length = queue_miss_code_length[sd[ranked_symbols[i]].count];
  }

  if (num_definitions_to_code == 0) {
    max_regular_code_length = 24;
    sd[ranked_symbols[0]].code_length = 25;
  }
  else if (sd[ranked_symbols[0]].count <= MAX_INSTANCES_FOR_REMOVE)
    max_regular_code_length = sd[ranked_symbols[0]].code_length - 1;

  sd[num_codes].type = 0;
  if (max_code_length >= 14) {
    i = 0;
    while (i < num_more_than_15_inst_definitions) {
     if ((sd[ranked_symbols[i]].type & 0x20) != 0) {
        if (sd[ranked_symbols[i]].space_score > 0)
          sd[ranked_symbols[i]].type += 0x40;
        else
          sd[ranked_symbols[i]].type += 0x20;
      }
      i++;
    }
    for (i = num_base_symbols ; i < num_codes; i++) {
      if ((sd[i].type & 0x40) != 0) {
        uint32_t last_symbol = symbol_array[sd[i + 1].define_symbol_start_index - 2];
        while (last_symbol >= num_base_symbols) {
          if ((sd[last_symbol].type & 0x60) == 0x60) {
            sd[i].type = (sd[i].type & 0x3F) | 0x20;
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

#ifdef PRINTON
  if (verbose != 0) {
    if (verbose == 1) {
      for (i = 0 ; i < num_definitions_to_code ; i++) {
        if (sd[ranked_symbols[i]].code_length >= 11) {
          if (use_mtf != 0)
            printf("%u: #%u %u L%u D%02x: \"", (unsigned int)i + 1, (unsigned int)sd[ranked_symbols[i]].previous,
                (unsigned int)sd[ranked_symbols[i]].count, (unsigned int)sd[ranked_symbols[i]].code_length,
                (unsigned int)sd[ranked_symbols[i]].type & 0xF4);
          else
            printf("%u: #%u L%u D%02x: \"", (unsigned int)i + 1, (unsigned int)sd[ranked_symbols[i]].count,
                (unsigned int)sd[ranked_symbols[i]].code_length, (unsigned int)sd[ranked_symbols[i]].type & 0xF4);
        }
        else
          printf("%u: #%u L%u: \"", (unsigned int)i + 1, (unsigned int)sd[ranked_symbols[i]].count,
              (unsigned int)sd[ranked_symbols[i]].code_length);
        print_string(ranked_symbols[i]);
        printf("\"\n");
      }
      uint32_t temp_rank = num_definitions_to_code;
      for (i = 0 ; i < num_base_symbols ; i++) {
        if (sd[i].count == 1) {
          printf("%u: #1: \"", ++temp_rank);
          print_string(i);
          printf("\"\n");
        }
      }
    }
    else {
      for (i = 0 ; i < num_codes ; i++) {
        if (sd[i].hits != 0) {
          if (sd[i].code_length >= 11) {
            if (use_mtf != 0)
              printf("%u: #%u %u L%u D%02x: \"", (unsigned int)i + 1, (unsigned int)sd[ranked_symbols[i]].previous,
                  (unsigned int)sd[i].count, (unsigned int)sd[i].code_length, (unsigned int)sd[i].type & 0xF4);
            else
              printf("%u: #%u L%u D%02x: \"",(unsigned int)i + 1, (unsigned int)sd[i].count,
                  (unsigned int)sd[i].code_length, (unsigned int)sd[i].type & 0xF4);
          }
          else
            printf("%u: #%u L%u: \"", (unsigned int)i + 1, (unsigned int)sd[i].count, (unsigned int)sd[i].code_length);
          print_string(i);
          printf("\"\n");
        }
      }
    }
  }
#endif

  symbol_ptr = symbol_array;
  prior_is_cap = 0;
  temp_char = 0xFF;
  if (UTF8_compliant != 0)
    temp_char = 0x90;
  InitEncoder(max_code_length, temp_char,
      MAX_INSTANCES_FOR_REMOVE + (uint32_t)(max_regular_code_length - sd[ranked_symbols[0]].code_length) + 1,
      cap_encoded, UTF8_compliant, use_mtf);

  if (fd != 0) {
    if ((outbuf = (uint8_t *)malloc(in_size * 2 + 100000)) == 0) {
      fprintf(stderr, "Error - encoded data memory allocation failed\n");
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
  WriteOutBuffer((uint8_t)(12.5 * (log2((double)(dictionary_size + 0x400)) - 10.0)) + 1);
  WriteOutBuffer((cap_encoded << 7) | (UTF8_compliant << 6) | (use_mtf << 5) | (queue_miss_code_length[2] - 1));
  temp_char = (((format & 0xFE) != 0) << 5) | (sd[ranked_symbols[0]].code_length - 1);
  if (queue_miss_code_length[3] != queue_miss_code_length[2])
    temp_char |= 0x40;
  if (queue_miss_code_length[4] != queue_miss_code_length[3])
    temp_char |= 0x80;
  WriteOutBuffer(temp_char);
  i = 7;
  do {
    temp_char = (temp_char << 1) | (queue_miss_code_length[i] != queue_miss_code_length[i - 1]);
  } while (--i != 4);
  WriteOutBuffer((temp_char << 5) | (queue_miss_code_length[2] - max_regular_code_length));
  i = 15;
  do {
    temp_char = (temp_char << 1) | (queue_miss_code_length[i] != queue_miss_code_length[i - 1]);
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
        fprintf(stderr, "Error - symbol list memory allocation failed\n");
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

#ifdef PRINTON
  fprintf(stderr, "use_mtf %u, mcl %u mrcl %u\n",
      (unsigned int)use_mtf, (unsigned int)max_code_length, (unsigned int)max_regular_code_length);
#endif

  for (i = 0 ; i < num_more_than_15_inst_definitions ; i++)
    sd[ranked_symbols[i]].count = sd[ranked_symbols[i]].code_length + MAX_INSTANCES_FOR_REMOVE;
  for (i = 0 ; i < num_codes ; i++)
    sd[i].hits = 0;
  num_transmits = queue_size = queue_size_cap = queue_offset = found_first_symbol = prior_end = 0;
  num_grammar_rules = 1;

  if ((UTF8_compliant != 0) || (cap_encoded != 0)) {
    cap_symbol_defined = 0;
    cap_lock_symbol_defined = 0;
    while (symbol_ptr < first_define_ptr) {
      symbol = *symbol_ptr++;
      symbol_inst = sd[symbol].hits++;
      if (symbol_inst == 0) {
        if (embed_define(symbol, 0) == 0)
          return(0);
      }
      else {
        if ((sd[symbol].type & 8) != 0) {
          if (prior_is_cap == 0)
            update_queue(symbol, 0);
          else
            update_queue_prior_cap(symbol, 0);
        }
        else {
          EncodeDictType(prior_is_cap);
          encode_dictionary_symbol(symbol);
          if (sd[symbol].count <= MAX_INSTANCES_FOR_REMOVE) {
            if (sd[symbol].count == sd[symbol].hits)
              remove_dictionary_symbol(symbol, sd[symbol].code_length);
            else if (use_mtf != 0) {
              if ((sd[symbol].type & 4) != 0) {
                if (transmits[num_transmits].distance != 0xFFFFFFFF) {
                  if ((sd[symbol].hits + 1 != sd[symbol].count) || ((sd[symbol].type & 0x80) != 0))
                    EncodeGoMtf(sd[symbol].count, 0, 1);
                  remove_dictionary_symbol(symbol, sd[symbol].code_length);
                  add_symbol_to_queue(symbol);
                }
                else
                  EncodeGoMtf(sd[symbol].count, 0, 0);
              }
            }
          }
          else if ((sd[symbol].type & 4) != 0) {
            if (transmits[num_transmits].distance != 0xFFFFFFFF) {
              EncodeGoMtf(sd[symbol].code_length + MAX_INSTANCES_FOR_REMOVE, 0, 1);
              remove_dictionary_symbol(symbol, sd[symbol].code_length);
              add_symbol_to_queue(symbol);
            }
            else
              EncodeGoMtf(sd[symbol].code_length + MAX_INSTANCES_FOR_REMOVE, 0, 0);
          }
        }
        prior_is_cap = sd[symbol].type & 1;
        prior_symbol = symbol;
        num_transmits++;
      }
      prior_end = sd[symbol].ends;
#ifdef PRINTON
      if (((symbol_ptr - symbol_array) & 0x1FFFFF) == 0)
        fprintf(stderr, "Encoded %u of %u level 0 symbols\r",
            (unsigned int)(symbol_ptr - symbol_array), (unsigned int)(first_define_ptr - symbol_array));
#endif
    }
  }
  else {
    while (symbol_ptr < first_define_ptr) {
      symbol = *symbol_ptr++;
      symbol_inst = sd[symbol].hits++;
      if (symbol_inst == 0) {
        if (embed_define_binary(symbol, 0) == 0)
          return(0);
      }
      else {
        if ((sd[symbol].type & 8) != 0)
          update_queue(symbol, 0);
        else {
          EncodeDictType(0);
          encode_dictionary_symbol(symbol);
          if (sd[symbol].count <= MAX_INSTANCES_FOR_REMOVE) {
            if (sd[symbol].count == sd[symbol].hits)
              remove_dictionary_symbol(symbol, sd[symbol].code_length);
            else if (use_mtf != 0) {
              if ((sd[symbol].type & 4) != 0) {
                if (transmits[num_transmits].distance != 0xFFFFFFFF) {
                  if ((sd[symbol].hits + 1 != sd[symbol].count) || ((sd[symbol].type & 0x80) != 0))
                    EncodeGoMtf(sd[symbol].count, 0, 1);
                  remove_dictionary_symbol(symbol, sd[symbol].code_length);
                  add_symbol_to_queue(symbol);
                }
                else
                  EncodeGoMtf(sd[symbol].count, 0, 0);
              }
            }
          }
          else if ((sd[symbol].type & 4) != 0) {
            if (transmits[num_transmits].distance != 0xFFFFFFFF) {
              EncodeGoMtf(sd[symbol].code_length + MAX_INSTANCES_FOR_REMOVE, 0, 1);
              remove_dictionary_symbol(symbol, sd[symbol].code_length);
              add_symbol_to_queue(symbol);
            }
            else
              EncodeGoMtf(sd[symbol].code_length + MAX_INSTANCES_FOR_REMOVE, 0, 0);
          }
        }
        num_transmits++;
      }
      prior_end = sd[symbol].ends;
#ifdef PRINTON
      if (((symbol_ptr - symbol_array) & 0x1FFFFF) == 0)
        fprintf(stderr, "Encoded %u of %u level 0 symbols\r",
            (unsigned int)(symbol_ptr - symbol_array), (unsigned int)(first_define_ptr - symbol_array));
#endif
    }
  }

  // send EOF and flush output
  EncodeDictType(0);
  if (cap_encoded != 0)
    EncodeFirstChar(end_char, (sd[prior_symbol].type & 0x60) >> 5, prior_end);
  else if (UTF8_compliant != 0)
    EncodeFirstChar(end_char, 0, prior_end);
  else
    EncodeFirstCharBinary(end_char, prior_end);
  code_length = bin_code_length[end_char];
  EncodeShortDictionarySymbol(fbob[end_char][max_code_length], sum_nbob[end_char], nbob[end_char][code_length]);
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
  free(ranked_symbols2);
  free(transmits);
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
