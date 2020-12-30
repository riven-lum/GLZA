/***********************************************************************

Copyright 2015 - 2018 Kennon Conrad

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

#include <inttypes.h>
#include <math.h>
#include "GLZAmodel.h"

uint32_t InCharNum, OutCharNum, RangeLow, RangeHigh, count, code, low, range;
uint16_t last_queue_size, last_queue_size_cap, unused_queue_freq, unused_queue_freq_cap;
uint16_t RangeScaleSID[2], FreqSID[2][16], RangeScaleINST[2][16], FreqINST[2][16][38];
uint16_t RangeScaleFirstCharSection[0x100][7], FreqFirstCharBinary[0x100][0x100];
uint16_t RangeScaleFirstChar[4][0x100], FreqFirstChar[4][0x100][0x100];
uint16_t RangeScaleMtfPos[2], FreqMtfPos[2][0x100], FreqSymType[4][3];
uint8_t SymbolFirstChar[4][0x100][0x100], RangeScaleERG[17], FreqERG[17], RangeScaleGoMtf[40][3], FreqGoMtf[40][3];
uint8_t RangeScaleWordTag, FreqWordTag, MaxBaseCode, MaxInstCode, *InBuffer, *OutBuffer;

uint32_t ReadLow() {return(low);}
uint32_t ReadRange() {return(range);}

void StartModelSymType(uint8_t use_mtf) {
  uint8_t i = 3;
  do {
    if (use_mtf != 0) {
      FreqSymType[i][0] = 0x1C00;
      FreqSymType[i][1] = 0x2000;
      FreqSymType[i][2] = 0x400;
      }
    else {
      FreqSymType[i][0] = 0x2000;
      FreqSymType[i][1] = 0x2000;
      FreqSymType[i][2] = 0;
    }
  } while (i-- != 0);
  return;
}

void StartModelMtfQueuePos(uint8_t max_code_length) {
  RangeScaleMtfPos[0] = RangeScaleMtfPos[1] = 0;
  uint16_t j = 0;
  do {
    FreqMtfPos[0][j] = FreqMtfPos[1][j] = 0x200 / (j + 2);
    RangeScaleMtfPos[0] = RangeScaleMtfPos[1] += FreqMtfPos[0][j];
  } while (++j != 0x100);
  last_queue_size = last_queue_size_cap = 0;
  unused_queue_freq_cap = unused_queue_freq = RangeScaleMtfPos[0];
  return;
}

void StartModelSID() {
  uint8_t i = 1;
  do {
    uint8_t j = 15;
    do {
      FreqSID[i][j] = 1;
    } while (j-- != 0);
    RangeScaleSID[i] = 16;
  } while (i-- != 0);
  return;
}

void StartModelINST(uint8_t num_inst_codes) {
  uint8_t i = 1;
  do {
    uint8_t j = 15;
    do {
      uint8_t k = num_inst_codes;
      if (j != 0)
        k--;
      RangeScaleINST[i][j] = k--;
      do {
        FreqINST[i][j][k] = 1;
      } while (k-- != 0);
    } while (j-- != 0);
  } while (i-- != 0);
  return;
}

void StartModelERG() {
  uint8_t i = 16;
  do {
    FreqERG[i] = 1;
    RangeScaleERG[i] = 2;
  } while (i-- != 0);
  return;
}

void StartModelGoQueue() {
  uint8_t i = 39;
  do {
    uint8_t j = 2;
    do {
      FreqGoMtf[i][j] = 1;
      RangeScaleGoMtf[i][j] = 2;
    } while (j-- != 0);
  } while (i-- != 0);
  return;
}

void StartModelWordTag() {
  FreqWordTag = 1;
  RangeScaleWordTag = 2;
  return;
}

void StartModelFirstChar() {
  uint8_t i = 0xFF;
  do {
    uint8_t j = 0xFF;
    do {
      FreqFirstChar[0][i][j] = 0;
      FreqFirstChar[1][i][j] = 0;
      FreqFirstChar[2][i][j] = 0;
      FreqFirstChar[3][i][j] = 0;
      SymbolFirstChar[0][i][j] = j;
      SymbolFirstChar[1][i][j] = j;
      SymbolFirstChar[2][i][j] = j;
      SymbolFirstChar[3][i][j] = j;
    } while (j-- != 0);
    RangeScaleFirstChar[0][i] = 0;
    RangeScaleFirstChar[1][i] = 0;
    RangeScaleFirstChar[2][i] = 0;
    RangeScaleFirstChar[3][i] = 0;
  } while (i-- != 0);
  return;
}

void StartModelFirstCharBinary() {
  uint8_t i = 0xFF;
  do {
    uint8_t j = 0xFF;
    do {
      FreqFirstCharBinary[i][j] = 0;
    } while (j-- != 0);
    j = 6;
    do {
      RangeScaleFirstCharSection[i][j] = 0;
    } while (j-- != 0);
    RangeScaleFirstChar[0][i] = 0;
  } while (i-- != 0);
  return;
}

void rescaleMtfQueuePos(uint8_t Context) {
  uint8_t i = 1;
  RangeScaleMtfPos[Context] = FreqMtfPos[Context][0] = (FreqMtfPos[Context][0] + 1) >> 1;
  do {
    RangeScaleMtfPos[Context] += FreqMtfPos[Context][i] = (FreqMtfPos[Context][i] + 1) >> 1;
  } while (++i != 0);
  uint8_t qp = 0xFF;
  if (Context == 0) {
    unused_queue_freq = 0;
    while (qp >= last_queue_size)
      unused_queue_freq += FreqMtfPos[0][qp--];
  }
  else {
    unused_queue_freq_cap = 0;
    while (qp >= last_queue_size_cap)
      unused_queue_freq_cap += FreqMtfPos[1][qp--];
  }
  return;
}

void rescaleSID(uint8_t Context) {
  uint8_t i = 14;
  RangeScaleSID[Context] = FreqSID[Context][15] = (FreqSID[Context][15] + 1) >> 1;
  do {
    RangeScaleSID[Context] += FreqSID[Context][i] = (FreqSID[Context][i] + 1) >> 1;
  } while (i-- != 0);
  return;
}

void rescaleINST(uint8_t Context, uint8_t SIDSymbol) {
  RangeScaleINST[Context][SIDSymbol] = 0;
  uint8_t i = MaxInstCode;
  do {
    RangeScaleINST[Context][SIDSymbol] += FreqINST[Context][SIDSymbol][i] = (FreqINST[Context][SIDSymbol][i] + 1) >> 1;
  } while (i-- != 0);
  return;
}

void rescaleFirstChar(uint8_t SymType, uint8_t Context) {
  uint8_t i = MaxBaseCode;
  RangeScaleFirstChar[SymType][Context] = 0;
  do {
    RangeScaleFirstChar[SymType][Context] += FreqFirstChar[SymType][Context][i]
        = (FreqFirstChar[SymType][Context][i] + 1) >> 1;
  } while (i-- != 0);
  return;
}

void rescaleFirstCharBinary(uint8_t Context) {
  RangeScaleFirstChar[0][Context] = FreqFirstCharBinary[Context][0] = (FreqFirstCharBinary[Context][0] + 1) >> 1;
  uint8_t i = 1;
  do {
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;
  } while (++i != 0x20);
  RangeScaleFirstCharSection[Context][0] = RangeScaleFirstChar[0][Context];
  do {
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;
  } while (++i != 0x40);
  RangeScaleFirstCharSection[Context][1] = RangeScaleFirstChar[0][Context];
  do {
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;
  } while (++i != 0x60);
  RangeScaleFirstCharSection[Context][2] = RangeScaleFirstChar[0][Context] - RangeScaleFirstCharSection[Context][1];
  do {
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;
  } while (++i != 0x80);
  RangeScaleFirstCharSection[Context][3] = RangeScaleFirstChar[0][Context];
  do {
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;
  } while (++i != 0xA0);
  RangeScaleFirstCharSection[Context][4] = RangeScaleFirstChar[0][Context] - RangeScaleFirstCharSection[Context][3];
  do {
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;
  } while (++i != 0xC0);
  RangeScaleFirstCharSection[Context][5] = RangeScaleFirstChar[0][Context] - RangeScaleFirstCharSection[Context][3];
  do {
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;
  } while (++i != 0xE0);
  RangeScaleFirstCharSection[Context][6] = RangeScaleFirstChar[0][Context] - RangeScaleFirstCharSection[Context][5]
      - RangeScaleFirstCharSection[Context][3];
  do {
    RangeScaleFirstChar[0][Context] += FreqFirstCharBinary[Context][i] = (FreqFirstCharBinary[Context][i] + 1) >> 1;
  } while (++i != 0);
  return;
}

void InitFreqFirstChar(uint8_t trailing_char, uint8_t leading_char) {
  FreqFirstChar[0][trailing_char][leading_char] = 1;
  FreqFirstChar[1][trailing_char][leading_char] = 1;
  FreqFirstChar[2][trailing_char][leading_char] = 1;
  FreqFirstChar[3][trailing_char][leading_char] = 1;
  RangeScaleFirstChar[0][trailing_char]++;
  RangeScaleFirstChar[1][trailing_char]++;
  RangeScaleFirstChar[2][trailing_char]++;
  RangeScaleFirstChar[3][trailing_char]++;
  return;
}

void InitFirstCharBin(uint8_t trailing_char, uint8_t leading_char, uint8_t code_length, uint8_t cap_symbol_defined,
    uint8_t cap_lock_symbol_defined) {
  if ((RangeScaleFirstChar[0][trailing_char] != 0)
      || ((trailing_char == 'C') && (cap_symbol_defined || cap_lock_symbol_defined))) {
    uint16_t freq = 1;
    if (code_length < 8)
      freq = 1 << (8 - code_length);
    uint8_t k;
    for (k = 0 ; k < 4 ; k++) {
      uint8_t j2 = leading_char;
      while (SymbolFirstChar[k][trailing_char][j2] != (uint8_t)leading_char)
        j2++;
      FreqFirstChar[k][trailing_char][j2] = freq;
      RangeScaleFirstChar[k][trailing_char] += freq;
      if (RangeScaleFirstChar[k][trailing_char] > FREQ_FIRST_CHAR_BOT)
        rescaleFirstChar(k, trailing_char);
    }
  }
  return;
}

void InitFirstCharBinBinary(uint8_t trailing_char, uint8_t leading_char, uint8_t code_length) {
  if (RangeScaleFirstChar[0][trailing_char]) {
    if (code_length < 8) {
      FreqFirstCharBinary[trailing_char][leading_char] = 1 << (8 - code_length);
      RangeScaleFirstChar[0][trailing_char] += 1 << (8 - code_length);
      if (leading_char < 0x80) {
        RangeScaleFirstCharSection[trailing_char][3] += 1 << (8 - code_length);
        if (leading_char < 0x40) {
          RangeScaleFirstCharSection[trailing_char][1] += 1 << (8 - code_length);
          if (leading_char < 0x20)
            RangeScaleFirstCharSection[trailing_char][0] += 1 << (8 - code_length);
        }
        else if (leading_char < 0x60)
          RangeScaleFirstCharSection[trailing_char][2] += 1 << (8 - code_length);
      }
      else if (leading_char < 0xC0) {
        RangeScaleFirstCharSection[trailing_char][5] += 1 << (8 - code_length);
        if (leading_char < 0xA0)
          RangeScaleFirstCharSection[trailing_char][4] += 1 << (8 - code_length);
      }
      else if (leading_char < 0xE0)
        RangeScaleFirstCharSection[trailing_char][6] += 1 << (8 - code_length);
    }
    else {
      FreqFirstCharBinary[trailing_char][leading_char] = 1;
      RangeScaleFirstChar[0][trailing_char] += 1;
      if (leading_char < 0x80) {
        RangeScaleFirstCharSection[trailing_char][3] += 1;
        if (leading_char < 0x40) {
          RangeScaleFirstCharSection[trailing_char][1] += 1;
          if (leading_char < 0x20)
            RangeScaleFirstCharSection[trailing_char][0] += 1;
        }
        else if (leading_char < 0x60)
          RangeScaleFirstCharSection[trailing_char][2] += 1;
      }
      else if (leading_char < 0xC0) {
        RangeScaleFirstCharSection[trailing_char][5] += 1;
        if (leading_char < 0xA0)
          RangeScaleFirstCharSection[trailing_char][4] += 1;
      }
      else if (leading_char < 0xE0)
        RangeScaleFirstCharSection[trailing_char][6] += 1;
    }
    if (RangeScaleFirstChar[0][trailing_char] > FREQ_FIRST_CHAR_BOT)
      rescaleFirstCharBinary(trailing_char);
  }
  return;
}

void InitTrailingCharBin(uint8_t trailing_char, uint8_t leading_char, uint8_t code_length) {
  uint16_t freq = 1;
  if (code_length < 8)
    freq = 1 << (8 - code_length);
  FreqFirstChar[0][trailing_char][leading_char] = freq;
  RangeScaleFirstChar[0][trailing_char] += freq;
  FreqFirstChar[1][trailing_char][leading_char] = freq;
  RangeScaleFirstChar[1][trailing_char] += freq;
  FreqFirstChar[2][trailing_char][leading_char] = freq;
  RangeScaleFirstChar[2][trailing_char] += freq;
  FreqFirstChar[3][trailing_char][leading_char] = freq;
  RangeScaleFirstChar[3][trailing_char] += freq;
  return;
}

void InitTrailingCharBinary(uint8_t trailing_char, uint8_t * symbol_lengths) {
  uint8_t leading_char = 0xFF;
  do {
    uint16_t freq = 1;
    if (symbol_lengths[leading_char] < 8)
      freq = 1 << (8 - symbol_lengths[leading_char]);
    if (RangeScaleFirstChar[0][leading_char] || (leading_char == trailing_char)) {
      FreqFirstCharBinary[trailing_char][leading_char] = freq;
      RangeScaleFirstChar[0][trailing_char] += freq;
      if (leading_char < 0x80) {
        RangeScaleFirstCharSection[trailing_char][3] += freq;
        if (leading_char < 0x40) {
          RangeScaleFirstCharSection[trailing_char][1] += freq;
          if (leading_char < 0x20)
            RangeScaleFirstCharSection[trailing_char][0] += freq;
        }
        else if (leading_char < 0x60)
          RangeScaleFirstCharSection[trailing_char][2] += freq;
      }
      else if (leading_char < 0xC0) {
        RangeScaleFirstCharSection[trailing_char][5] += freq;
        if (leading_char < 0xA0)
          RangeScaleFirstCharSection[trailing_char][4] += freq;
      }
      else if (leading_char < 0xE0)
        RangeScaleFirstCharSection[trailing_char][6] += freq;
    }
  } while (leading_char-- != 0);
  return;
}

void InitBaseSymbolCap(uint8_t BaseSymbol, uint8_t new_symbol_code_length, uint8_t * cap_symbol_defined_ptr,
    uint8_t * cap_lock_symbol_defined_ptr, uint8_t * symbol_lengths) {
  uint8_t j1 = MaxBaseCode;
  do {
    InitFirstCharBin(j1, BaseSymbol, new_symbol_code_length, *cap_symbol_defined_ptr, *cap_lock_symbol_defined_ptr);
  } while (--j1 != 'Z');
  j1 = 'A' - 1;
  do {
    InitFirstCharBin(j1, BaseSymbol, new_symbol_code_length, *cap_symbol_defined_ptr, *cap_lock_symbol_defined_ptr);
  } while (j1--);
  if ((BaseSymbol & 0xFE) == 0x42) {
    j1 = 'z';
    if ((*cap_symbol_defined_ptr | *cap_lock_symbol_defined_ptr) == 0) {
      do {
        if (RangeScaleFirstChar[0][j1] != 0)
          InitTrailingCharBin('C', j1, symbol_lengths[j1]);
      } while (j1-- != 'a');
    }
    if (BaseSymbol == 'C')
      *cap_symbol_defined_ptr = 1;
    else
      *cap_lock_symbol_defined_ptr = 1;
  }
  else {
    if ((BaseSymbol >= 'a') && (BaseSymbol <= 'z'))
      InitFirstCharBin('C', BaseSymbol, new_symbol_code_length, *cap_symbol_defined_ptr, *cap_lock_symbol_defined_ptr);
    j1 = MaxBaseCode;
    do {
      if (symbol_lengths[j1] != 0)
        InitTrailingCharBin(BaseSymbol, j1, symbol_lengths[j1]);
    } while (j1--);
  }
  return;
}

void IncreaseRange(uint32_t low_ranges, uint32_t ranges) {
  low -= range * low_ranges;
  range *= ranges;
}

void DoubleRange() {
  range *= 2;
}

void DoubleRangeDown() {
  low -= range;
  range *= 2;
}

void SetOutBuffer(uint8_t * bufptr) {
  OutBuffer = bufptr;
}

void WriteOutBuffer(uint8_t value) {
  OutBuffer[OutCharNum++] = value;
}

void NormalizeEncoder(uint32_t bot) {
  while ((low ^ (low + range)) < TOP || (range < bot && ((range = -low & (bot - 1)), 1))) {
    OutBuffer[OutCharNum++] = (uint8_t)(low >> 24);
    range <<= 8;
    low <<= 8;
  }
  return;
}

void EncodeDictType(uint8_t Context) {
  NormalizeEncoder(FREQ_SYM_TYPE_BOT);
  uint32_t extra_range = range & (FREQ_SYM_TYPE_BOT - 1);
  range = FreqSymType[Context][0] * (range >> 14) + extra_range;
  uint16_t sum = FreqSymType[Context][1] >> 6;
  FreqSymType[Context][0] += sum + ((FREQ_SYM_TYPE_BOT - FreqSymType[Context][0] - FreqSymType[Context][1]) >> 6);
  FreqSymType[Context][1] -= sum;
  return;
}

void EncodeNewType(uint8_t Context) {
  NormalizeEncoder(FREQ_SYM_TYPE_BOT);
  uint32_t extra_range = range & (FREQ_SYM_TYPE_BOT - 1);
  low += FreqSymType[Context][0] * (range >>= 14) + extra_range;
  range *= FreqSymType[Context][1];
  uint16_t sum = FreqSymType[Context][0] >> 6;
  FreqSymType[Context][1] += sum + ((FREQ_SYM_TYPE_BOT - FreqSymType[Context][0] - FreqSymType[Context][1]) >> 6);
  FreqSymType[Context][0] -= sum;
  return;
}

void EncodeMtfType(uint8_t Context) {
  NormalizeEncoder(FREQ_SYM_TYPE_BOT);
  uint32_t extra_range = range & (FREQ_SYM_TYPE_BOT - 1);
  uint16_t sum = FreqSymType[Context][0] + FreqSymType[Context][1];
  low += sum * (range >>= 14) + extra_range;
  range *= FREQ_SYM_TYPE_BOT - sum;
  FreqSymType[Context][0] -= FreqSymType[Context][0] >> 6;
  FreqSymType[Context][1] -= FreqSymType[Context][1] >> 6;
  return;
}

void EncodeMtfPos(uint8_t Context, uint8_t position, uint16_t QueueSize) {
  NormalizeEncoder(FREQ_MTF_POS_BOT);
  if (Context == 0) {
    if (last_queue_size > QueueSize) {
      do {
        unused_queue_freq += FreqMtfPos[0][--last_queue_size];
      } while (last_queue_size != QueueSize);
    }
    else if (last_queue_size < QueueSize) {
      do {
        unused_queue_freq -= FreqMtfPos[0][last_queue_size++];
      } while (last_queue_size != QueueSize);
    }
  }
  else {
    if (last_queue_size_cap > QueueSize) {
      do {
        unused_queue_freq_cap += FreqMtfPos[1][--last_queue_size_cap];
      } while (last_queue_size_cap != QueueSize);
    }
    else if (last_queue_size_cap < QueueSize) {
      do {
        unused_queue_freq_cap -= FreqMtfPos[1][last_queue_size_cap++];
      } while (last_queue_size_cap != QueueSize);
    }
  }
  if (position == 0) {
    if (Context == 0)
      range = FreqMtfPos[0][0] * (range / (RangeScaleMtfPos[0] - unused_queue_freq));
    else
      range = FreqMtfPos[1][0] * (range / (RangeScaleMtfPos[1] - unused_queue_freq_cap));
    FreqMtfPos[Context][0] += UP_FREQ_MTF_POS;
  }
  else {
    uint16_t * FreqPtr = &FreqMtfPos[Context][0];
    uint16_t * StopFreqPtr = &FreqMtfPos[Context][position];
    RangeLow = *FreqPtr++;
    while (FreqPtr != StopFreqPtr)
      RangeLow += *FreqPtr++;
    if (Context == 0)
      low += RangeLow * (range /= (RangeScaleMtfPos[0] - unused_queue_freq));
    else
      low += RangeLow * (range /= (RangeScaleMtfPos[1] - unused_queue_freq_cap));
    range *= *FreqPtr;
    if (position >= 4) {
      if (position == 4) {
        *FreqPtr += UP_FREQ_MTF_POS - 2;
        *(FreqPtr + 1) += 2;
        if (position + 1 == QueueSize) {
          if (Context == 0)
            unused_queue_freq += 2;
          else 
            unused_queue_freq_cap += 2;
        }
      }
      else if (position == 255) {
        *(FreqPtr - 1) += 2;
        *FreqPtr += UP_FREQ_MTF_POS - 2;
      }
      else {
        *(FreqPtr - 1) += 2;
        *FreqPtr += UP_FREQ_MTF_POS - 4;
        *(FreqPtr + 1) += 2;
        if (position + 1 == QueueSize) {
          if (Context == 0)
            unused_queue_freq += 2;
          else 
            unused_queue_freq_cap += 2;
        }
      }
    }
    else
      *FreqPtr += UP_FREQ_MTF_POS;
  }
  if ((RangeScaleMtfPos[Context] += UP_FREQ_MTF_POS) > FREQ_MTF_POS_BOT)
    rescaleMtfQueuePos(Context);
  return;
}

void EncodeSID(uint8_t Context, uint8_t SIDSymbol) {
  NormalizeEncoder(FREQ_SID_BOT);
  if (SIDSymbol == 0) {
    range = FreqSID[Context][0] * (range / RangeScaleSID[Context]);
    FreqSID[Context][0] += UP_FREQ_SID;
  }
  else {
    RangeLow = FreqSID[Context][0];
    uint8_t Symbol = 1;
    while (Symbol != SIDSymbol)
      RangeLow += FreqSID[Context][Symbol++];
    low += RangeLow * (range /= RangeScaleSID[Context]);
    range *= FreqSID[Context][SIDSymbol];
    FreqSID[Context][SIDSymbol] += UP_FREQ_SID;
  }
  if ((RangeScaleSID[Context] += UP_FREQ_SID) > FREQ_SID_BOT)
    rescaleSID(Context);
  return;
}

void EncodeExtraLength(uint8_t Symbol) {
  NormalizeEncoder(1 << 2);
  range >>= 2;
  low += Symbol * range;
  return;
}

void EncodeINST(uint8_t Context, uint8_t SIDSymbol, uint8_t Symbol) {
  NormalizeEncoder(FREQ_INST_BOT);
  if (Symbol == 0) {
    range = FreqINST[Context][SIDSymbol][0] * (range / RangeScaleINST[Context][SIDSymbol]);
    if (RangeScaleINST[Context][SIDSymbol] >= (FREQ_INST_BOT >> 1)) {
      FreqINST[Context][SIDSymbol][0] += RangeScaleINST[Context][SIDSymbol] >> 11;
      if ((RangeScaleINST[Context][SIDSymbol] += (RangeScaleINST[Context][SIDSymbol]) >> 11) > FREQ_INST_BOT)
        rescaleINST(Context, SIDSymbol);
    }
    else {
      FreqINST[Context][SIDSymbol][0] += UP_FREQ_INST;
      RangeScaleINST[Context][SIDSymbol] += UP_FREQ_INST;
    }
  }
  else {
    RangeLow = FreqINST[Context][SIDSymbol][0];
    uint8_t FoundIndex = 1;
    while (FoundIndex != Symbol)
      RangeLow += FreqINST[Context][SIDSymbol][FoundIndex++];
    low += RangeLow * (range /= RangeScaleINST[Context][SIDSymbol]);
    range *= FreqINST[Context][SIDSymbol][FoundIndex];
    if (RangeScaleINST[Context][SIDSymbol] >= (FREQ_INST_BOT >> 1)) {
      FreqINST[Context][SIDSymbol][FoundIndex] += RangeScaleINST[Context][SIDSymbol] >> 11;
      if ((RangeScaleINST[Context][SIDSymbol] += (RangeScaleINST[Context][SIDSymbol]) >> 11) > FREQ_INST_BOT)
        rescaleINST(Context, SIDSymbol);
    }
    else {
      FreqINST[Context][SIDSymbol][FoundIndex] += UP_FREQ_INST;
      RangeScaleINST[Context][SIDSymbol] += UP_FREQ_INST;
    }
  }
  return;
}

void EncodeERG(uint8_t Context, uint8_t Symbol) {
  NormalizeEncoder(FREQ_ERG_BOT);
  if (Symbol == 0) {
    range = FreqERG[Context] * (range / RangeScaleERG[Context]);
    FreqERG[Context] += UP_FREQ_ERG;
  }
  else {
    low += FreqERG[Context] * (range /= RangeScaleERG[Context]);
    range *= RangeScaleERG[Context] - FreqERG[Context];
  }
  if ((RangeScaleERG[Context] += UP_FREQ_ERG) > FREQ_ERG_BOT) {
    RangeScaleERG[Context] = (FREQ_ERG_BOT >> 1) + 1;
    FreqERG[Context] = (FreqERG[Context] + 1) >> 1;
  }
  return;
}

void EncodeGoMtf(uint8_t Context, uint8_t InQueue, uint8_t Symbol) {
  NormalizeEncoder(FREQ_GO_MTF_BOT);
  if (Symbol == 0) {
    range = FreqGoMtf[Context][InQueue] * (range / RangeScaleGoMtf[Context][InQueue]);
    FreqGoMtf[Context][InQueue] += UP_FREQ_GO_MTF;
  }
  else {
    low += FreqGoMtf[Context][InQueue] * (range /= RangeScaleGoMtf[Context][InQueue]);
    range *= RangeScaleGoMtf[Context][InQueue] - FreqGoMtf[Context][InQueue];
  }
  if ((RangeScaleGoMtf[Context][InQueue] += UP_FREQ_GO_MTF) > FREQ_GO_MTF_BOT) {
    RangeScaleGoMtf[Context][InQueue] = (FREQ_GO_MTF_BOT >> 1) + 1;
    FreqGoMtf[Context][InQueue] = (FreqGoMtf[Context][InQueue] + 1) >> 1;
  }
  return;
}

void EncodeWordTag(uint8_t Symbol) {
  NormalizeEncoder(FREQ_WORD_TAG_BOT);
  if (Symbol == 0) {
    range = FreqWordTag * (range / RangeScaleWordTag);
    FreqWordTag += UP_FREQ_WORD_TAG;
  }
  else {
    low += FreqWordTag * (range /= RangeScaleWordTag);
    range *= RangeScaleWordTag - FreqWordTag;
  }
  if ((RangeScaleWordTag += UP_FREQ_WORD_TAG) > FREQ_WORD_TAG_BOT) {
    RangeScaleWordTag = (FREQ_WORD_TAG_BOT >> 1) + 1;
    FreqWordTag = (FreqWordTag + 1) >> 1;
  }
  return;
}

void EncodeShortDictionarySymbol(uint16_t BinNum, uint16_t DictionaryBins, uint16_t CodeBins) {
  NormalizeEncoder((uint32_t)1 << 12);
  low += BinNum * (range /= DictionaryBins);
  range *= (uint32_t)CodeBins;
  return;
}

void EncodeLongDictionarySymbol(uint32_t BinCode, uint16_t BinNum, uint16_t DictionaryBins, uint8_t CodeLength,
    uint16_t CodeBins) {
  NormalizeEncoder((uint32_t)1 << 12);
  low += BinNum * (range /= DictionaryBins);
  NormalizeEncoder((uint32_t)1 << CodeLength);
  low += BinCode * (range >>= CodeLength);
  range *= (uint32_t)CodeBins;
  return;
}

void EncodeBaseSymbol(uint32_t BaseSymbol, uint32_t NumBaseSymbols, uint32_t NormBaseSymbols) {
  NormalizeEncoder(NormBaseSymbols);
  low += BaseSymbol * (range /= NumBaseSymbols);
  return;
}

void EncodeFirstChar(uint8_t Symbol, uint8_t SymType, uint8_t LastChar) {
  NormalizeEncoder(FREQ_FIRST_CHAR_BOT);
  if (Symbol == SymbolFirstChar[SymType][LastChar][0]) {
    range = FreqFirstChar[SymType][LastChar][0] * (range / RangeScaleFirstChar[SymType][LastChar]);
    if (RangeScaleFirstChar[SymType][LastChar] >= (FREQ_FIRST_CHAR_BOT >> 1)) {
      FreqFirstChar[SymType][LastChar][0] += RangeScaleFirstChar[SymType][LastChar] >> 9;
      if ((RangeScaleFirstChar[SymType][LastChar] += (RangeScaleFirstChar[SymType][LastChar] >> 9)) > FREQ_FIRST_CHAR_BOT)
        rescaleFirstChar(SymType, LastChar);
    }
    else {
      FreqFirstChar[SymType][LastChar][0] += UP_FREQ_FIRST_CHAR;
      RangeScaleFirstChar[SymType][LastChar] += UP_FREQ_FIRST_CHAR;
    }
  }
  else {
    RangeLow = FreqFirstChar[SymType][LastChar][0];
    uint8_t FoundIndex = 1;
    while (SymbolFirstChar[SymType][LastChar][FoundIndex] != Symbol)
      RangeLow += FreqFirstChar[SymType][LastChar][FoundIndex++];
    low += RangeLow * (range /= RangeScaleFirstChar[SymType][LastChar]);
    range *= FreqFirstChar[SymType][LastChar][FoundIndex];
    if (RangeScaleFirstChar[SymType][LastChar] >= (FREQ_FIRST_CHAR_BOT >> 1)) {
      FreqFirstChar[SymType][LastChar][FoundIndex] += RangeScaleFirstChar[SymType][LastChar] >> 9;
      if ((RangeScaleFirstChar[SymType][LastChar] += (RangeScaleFirstChar[SymType][LastChar] >> 9)) > FREQ_FIRST_CHAR_BOT)
        rescaleFirstChar(SymType, LastChar);
    }
    else {
      FreqFirstChar[SymType][LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;
      RangeScaleFirstChar[SymType][LastChar] += UP_FREQ_FIRST_CHAR;
    }
    if (FreqFirstChar[SymType][LastChar][FoundIndex] > FreqFirstChar[SymType][LastChar][FoundIndex - 1]) {
      uint16_t SavedFreq = FreqFirstChar[SymType][LastChar][FoundIndex];
      do {
        FreqFirstChar[SymType][LastChar][FoundIndex] = FreqFirstChar[SymType][LastChar][FoundIndex - 1];
        SymbolFirstChar[SymType][LastChar][FoundIndex] = SymbolFirstChar[SymType][LastChar][FoundIndex - 1];
      } while ((--FoundIndex) && (SavedFreq > FreqFirstChar[SymType][LastChar][FoundIndex - 1]));
      FreqFirstChar[SymType][LastChar][FoundIndex] = SavedFreq;
      SymbolFirstChar[SymType][LastChar][FoundIndex] = Symbol;
    }
  }
  return;
}

void EncodeFirstCharBinary(uint8_t Symbol, uint8_t LastChar) {
  NormalizeEncoder(FREQ_FIRST_CHAR_BOT);
  if (RangeScaleFirstCharSection[LastChar][3] > count) {
    RangeScaleFirstCharSection[LastChar][3] += UP_FREQ_FIRST_CHAR;
    if (RangeScaleFirstCharSection[LastChar][1] > count) {
      RangeScaleFirstCharSection[LastChar][1] += UP_FREQ_FIRST_CHAR;
      if (RangeScaleFirstCharSection[LastChar][0] > count) {
        RangeScaleFirstCharSection[LastChar][0] += UP_FREQ_FIRST_CHAR;
        if (Symbol == 0) {
          range = FreqFirstCharBinary[LastChar][0] * (range / RangeScaleFirstChar[0][LastChar]);
          FreqFirstCharBinary[LastChar][0] += UP_FREQ_FIRST_CHAR;
        }
        else {
          RangeLow = FreqFirstCharBinary[LastChar][0];
          uint8_t FoundIndex = 1;
          while (FoundIndex != Symbol)
            RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];
          low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);
          range *= FreqFirstCharBinary[LastChar][FoundIndex];
          FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;
        }
      }
      else {
        RangeLow = RangeScaleFirstCharSection[LastChar][0];
        uint8_t FoundIndex = 0x20;
        while (FoundIndex != Symbol)
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);
        range *= FreqFirstCharBinary[LastChar][FoundIndex];
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;
      }
    }
    else {
      RangeLow = RangeScaleFirstCharSection[LastChar][1];
      if (RangeScaleFirstCharSection[LastChar][2] > count) {
        RangeScaleFirstCharSection[LastChar][2] += UP_FREQ_FIRST_CHAR;
        uint8_t FoundIndex = 0x40;
        while (FoundIndex != Symbol)
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);
        range *= FreqFirstCharBinary[LastChar][FoundIndex];
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;
      }
      else {
        RangeLow += RangeScaleFirstCharSection[LastChar][2];
        uint8_t FoundIndex = 0x60;
        while (FoundIndex != Symbol)
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);
        range *= FreqFirstCharBinary[LastChar][FoundIndex];
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;
      }
    }
  }
  else {
    RangeLow = RangeScaleFirstCharSection[LastChar][3];
    if (RangeLow + RangeScaleFirstCharSection[LastChar][5] > count) {
      RangeScaleFirstCharSection[LastChar][5] += UP_FREQ_FIRST_CHAR;
      if (RangeScaleFirstCharSection[LastChar][4] > count) {
        RangeScaleFirstCharSection[LastChar][4] += UP_FREQ_FIRST_CHAR;
        uint8_t FoundIndex = 0x80;
        while (FoundIndex != Symbol)
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);
        range *= FreqFirstCharBinary[LastChar][FoundIndex];
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;
      }
      else {
        RangeLow += RangeScaleFirstCharSection[LastChar][4];
        uint8_t FoundIndex = 0xA0;
        while (FoundIndex != Symbol)
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);
        range *= FreqFirstCharBinary[LastChar][FoundIndex];
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;
      }
    }
    else {
      RangeLow += RangeScaleFirstCharSection[LastChar][5];
      if (RangeScaleFirstCharSection[LastChar][6] > count) {
        RangeScaleFirstCharSection[LastChar][6] += UP_FREQ_FIRST_CHAR;
        uint8_t FoundIndex = 0xC0;
        while (FoundIndex != Symbol)
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);
        range *= FreqFirstCharBinary[LastChar][FoundIndex];
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;
      }
      else {
        RangeLow += RangeScaleFirstCharSection[LastChar][6];
        uint8_t FoundIndex = 0xE0;
        while (FoundIndex != Symbol)
          RangeLow += FreqFirstCharBinary[LastChar][FoundIndex++];
        low += RangeLow * (range /= RangeScaleFirstChar[0][LastChar]);
        range *= FreqFirstCharBinary[LastChar][FoundIndex];
        FreqFirstCharBinary[LastChar][FoundIndex] += UP_FREQ_FIRST_CHAR;
      }
    }
  }
  if ((RangeScaleFirstChar[0][LastChar] += UP_FREQ_FIRST_CHAR) > FREQ_FIRST_CHAR_BOT)
    rescaleFirstCharBinary(LastChar);
  return;
}

void WriteInCharNum(uint32_t value) {
  InCharNum = value;
}

uint32_t ReadOutCharNum() {
  return(OutCharNum);
}

void InitEncoder(uint8_t max_code_length, uint8_t max_base_code, uint8_t num_inst_codes, uint8_t cap_encoded,
    uint8_t UTF8_compliant, uint8_t use_mtf) {
  MaxBaseCode = max_base_code;
  MaxInstCode = num_inst_codes - 1;
  OutCharNum = 0;
  low = 0, range = -1;
  StartModelSymType(use_mtf);
  StartModelMtfQueuePos(max_code_length);
  StartModelSID();
  StartModelINST(num_inst_codes);
  StartModelERG();
  StartModelGoQueue();
  StartModelWordTag();
  if (cap_encoded || UTF8_compliant)
    StartModelFirstChar();
  else
    StartModelFirstCharBinary();
}

void FinishEncoder() {
  while (low != 0) {
    OutBuffer[OutCharNum++] = (uint8_t)(low >> 24);
    low <<= 8;
  }
}

void NormalizeDecoder(uint32_t bot) {
  while ((low ^ (low + range)) < TOP || (range < (bot) && ((range = -low & ((bot) - 1)), 1))) {
    code = (code << 8) | InBuffer[InCharNum++];
    low <<= 8;
    range <<= 8;
  }
}

uint8_t DecodeSymType(uint8_t Context) {
  uint32_t dict_range;
  NormalizeDecoder(FREQ_SYM_TYPE_BOT);
  uint32_t extra_range = range & (FREQ_SYM_TYPE_BOT - 1);
  if ((dict_range = (range >>= 14) * FreqSymType[Context][0] + extra_range) > code - low) {
    range = dict_range;
    uint8_t delta = FreqSymType[Context][1] >> 6;
    FreqSymType[Context][0] += delta + ((FREQ_SYM_TYPE_BOT - FreqSymType[Context][0] - FreqSymType[Context][1]) >> 6);
    FreqSymType[Context][1] -= delta;
    return(0);
  }
  else if (dict_range + range * FreqSymType[Context][1] > code - low) {
    low += dict_range;
    range *= FreqSymType[Context][1];
    uint8_t delta = FreqSymType[Context][0] >> 6;
    FreqSymType[Context][1] += delta + ((FREQ_SYM_TYPE_BOT - FreqSymType[Context][0] - FreqSymType[Context][1]) >> 6);
    FreqSymType[Context][0] -= delta;
    return(1);
  }
  else {
    low += dict_range + range * FreqSymType[Context][1];
    range *= (FREQ_SYM_TYPE_BOT - FreqSymType[Context][0] - FreqSymType[Context][1]);
    FreqSymType[Context][0] -= FreqSymType[Context][0] >> 6;
    FreqSymType[Context][1] -= FreqSymType[Context][1] >> 6;
    return(2);
  }
}

uint8_t DecodeMtfPos(uint8_t Context, uint16_t QueueSize) {
  NormalizeDecoder(FREQ_MTF_POS_BOT);
  if (Context == 0) {
    if (last_queue_size > QueueSize) {
      do {
        unused_queue_freq += FreqMtfPos[0][--last_queue_size];
      } while (last_queue_size != QueueSize);
    }
    else if (last_queue_size < QueueSize) {
      do {
        unused_queue_freq -= FreqMtfPos[0][last_queue_size++];
      } while (last_queue_size != QueueSize);
    }
    count = (code - low) / (range /= (RangeScaleMtfPos[0] - unused_queue_freq));
  }
  else {
    if (last_queue_size_cap > QueueSize) {
      do {
        unused_queue_freq_cap += FreqMtfPos[1][--last_queue_size_cap];
      } while (last_queue_size_cap != QueueSize);
    }
    else if (last_queue_size_cap < QueueSize) {
      do {
        unused_queue_freq_cap -= FreqMtfPos[1][last_queue_size_cap++];
      } while (last_queue_size_cap != QueueSize);
    }
    count = (code - low) / (range /= (RangeScaleMtfPos[1] - unused_queue_freq_cap));
  }
  if ((RangeHigh = FreqMtfPos[Context][0]) > count) {
    range *= RangeHigh;
    FreqMtfPos[Context][0] = RangeHigh + UP_FREQ_MTF_POS;
    if ((RangeScaleMtfPos[Context] += UP_FREQ_MTF_POS) > FREQ_MTF_POS_BOT)
      rescaleMtfQueuePos(Context);
    return(0);
  }
  else {
    uint16_t * FreqPtr = &FreqMtfPos[Context][1];
    while ((RangeHigh += *FreqPtr) <= count)
      FreqPtr++;
    uint8_t position = FreqPtr - &FreqMtfPos[Context][0];
    low += range * (RangeHigh - *FreqPtr);
    range *= *FreqPtr;
    if (position >= 4) {
      if (position == 4) {
        *FreqPtr += UP_FREQ_MTF_POS - 2;
        *(FreqPtr + 1) += 2;
        if (position == QueueSize - 1) {
          if (Context == 0)
            unused_queue_freq += 2;
          else 
            unused_queue_freq_cap += 2;
        }
      }
      else if (position == 255) {
        *(FreqPtr - 1) += 2;
        *FreqPtr += UP_FREQ_MTF_POS - 2;
      }
      else {
        *(FreqPtr - 1) += 2;
        *FreqPtr += UP_FREQ_MTF_POS - 4;
        *(FreqPtr + 1) += 2;
        if (position == QueueSize - 1) {
          if (Context == 0)
            unused_queue_freq += 2;
          else 
            unused_queue_freq_cap += 2;
        }
      }
    }
    else
       *FreqPtr += UP_FREQ_MTF_POS;
    if ((RangeScaleMtfPos[Context] += UP_FREQ_MTF_POS) > FREQ_MTF_POS_BOT)
      rescaleMtfQueuePos(Context);
    return(position);
  }
}

uint8_t DecodeSID(uint8_t Context) {
  NormalizeDecoder(FREQ_SID_BOT);
  count = (code - low) / (range /= RangeScaleSID[Context]);
  if ((RangeHigh = FreqSID[Context][0]) > count) {
    range *= RangeHigh;
    FreqSID[Context][0] = RangeHigh + UP_FREQ_SID;
    if ((RangeScaleSID[Context] += UP_FREQ_SID) > FREQ_SID_BOT)
      rescaleSID(Context);
    return(0);
  }
  else {
    uint8_t SIDSymbol = 1;
    while ((RangeHigh += FreqSID[Context][SIDSymbol]) <= count)
      SIDSymbol++;
    low += range * (RangeHigh - FreqSID[Context][SIDSymbol]);
    range *= FreqSID[Context][SIDSymbol];
    FreqSID[Context][SIDSymbol] += UP_FREQ_SID;
    if ((RangeScaleSID[Context] += UP_FREQ_SID) > FREQ_SID_BOT)
      rescaleSID(Context);
    return(SIDSymbol);
  }
}

uint8_t DecodeExtraLength() {
  NormalizeDecoder((uint32_t)1 << 2);
  uint32_t Symbol = (code - low) / (range >>= 2);
  low += range * Symbol;
  return((uint8_t)Symbol);
}

uint8_t DecodeINST(uint8_t Context, uint8_t SIDSymbol) {
  NormalizeDecoder(FREQ_INST_BOT);
  range /= RangeScaleINST[Context][SIDSymbol];
  RangeHigh = FreqINST[Context][SIDSymbol][0];
  if (RangeHigh * range > code - low) {
    range *= RangeHigh;
    if (RangeScaleINST[Context][SIDSymbol] >= (FREQ_INST_BOT >> 1)) {
      FreqINST[Context][SIDSymbol][0] += RangeScaleINST[Context][SIDSymbol] >> 11;
      if ((RangeScaleINST[Context][SIDSymbol] += RangeScaleINST[Context][SIDSymbol] >> 11) > FREQ_INST_BOT)
        rescaleINST(Context, SIDSymbol);
    }
    else {
      FreqINST[Context][SIDSymbol][0] += UP_FREQ_INST;
      RangeScaleINST[Context][SIDSymbol] += UP_FREQ_INST;
    }
    return(0);
  }
  else {
    count = (code - low) / range;
    uint8_t Instances = 1;
    while ((RangeHigh += FreqINST[Context][SIDSymbol][Instances]) <= count)
      Instances++;
    low += range * (RangeHigh - FreqINST[Context][SIDSymbol][Instances]);
    range *= FreqINST[Context][SIDSymbol][Instances];
    if (RangeScaleINST[Context][SIDSymbol] >= (FREQ_INST_BOT >> 1)) {
      FreqINST[Context][SIDSymbol][Instances] += RangeScaleINST[Context][SIDSymbol] >> 11;
      if ((RangeScaleINST[Context][SIDSymbol] += (RangeScaleINST[Context][SIDSymbol] >> 11)) > FREQ_INST_BOT)
        rescaleINST(Context, SIDSymbol);
    }
    else {
      FreqINST[Context][SIDSymbol][Instances] += UP_FREQ_INST;
      RangeScaleINST[Context][SIDSymbol] += UP_FREQ_INST;
    }
    return(Instances);
  }
/*
  count = (code - low) / (range /= RangeScaleINST[Context][SIDSymbol]);
  if ((RangeHigh = FreqINST[Context][SIDSymbol][0]) > count) {
    range *= RangeHigh;
    if (RangeScaleINST[Context][SIDSymbol] >= (FREQ_INST_BOT >> 1)) {
      FreqINST[Context][SIDSymbol][0] += RangeScaleINST[Context][SIDSymbol] >> 11;
      if ((RangeScaleINST[Context][SIDSymbol] += RangeScaleINST[Context][SIDSymbol] >> 11) > FREQ_INST_BOT)
        rescaleINST(Context, SIDSymbol);
    }
    else {
      FreqINST[Context][SIDSymbol][0] += UP_FREQ_INST;
      RangeScaleINST[Context][SIDSymbol] += UP_FREQ_INST;
    }
    return(0);
  }
  else {
    uint8_t Instances = 1;
    while ((RangeHigh += FreqINST[Context][SIDSymbol][Instances]) <= count)
      Instances++;
    low += range * (RangeHigh - FreqINST[Context][SIDSymbol][Instances]);
    range *= FreqINST[Context][SIDSymbol][Instances];
    if (RangeScaleINST[Context][SIDSymbol] >= (FREQ_INST_BOT >> 1)) {
      FreqINST[Context][SIDSymbol][Instances] += RangeScaleINST[Context][SIDSymbol] >> 11;
      if ((RangeScaleINST[Context][SIDSymbol] += (RangeScaleINST[Context][SIDSymbol] >> 11)) > FREQ_INST_BOT)
        rescaleINST(Context, SIDSymbol);
    }
    else {
      FreqINST[Context][SIDSymbol][Instances] += UP_FREQ_INST;
      RangeScaleINST[Context][SIDSymbol] += UP_FREQ_INST;
    }
    return(Instances);
  }
*/
}

uint8_t DecodeERG(uint8_t Context) {
  uint8_t nonergodic;
  NormalizeDecoder(FREQ_ERG_BOT);
  if (FreqERG[Context] * (range /= RangeScaleERG[Context]) > code - low) {
    range *= FreqERG[Context];
    FreqERG[Context] += UP_FREQ_ERG;
    nonergodic = 0;
  }
  else {
    low += range * FreqERG[Context];
    range *= RangeScaleERG[Context] - FreqERG[Context];
    nonergodic = 1;
  }
  if ((RangeScaleERG[Context] += UP_FREQ_ERG) > FREQ_ERG_BOT) {
    RangeScaleERG[Context] = (FREQ_ERG_BOT >> 1) + 1;
    FreqERG[Context] = (FreqERG[Context] + 1) >> 1;
  }
  return(nonergodic);
}

uint8_t DecodeGoMtf(uint8_t Context, uint8_t InQueue) {
  uint8_t go_mtf;
  NormalizeDecoder(FREQ_GO_MTF_BOT);
  if (FreqGoMtf[Context][InQueue] * (range /= RangeScaleGoMtf[Context][InQueue]) > code - low) {
    range *= FreqGoMtf[Context][InQueue];
    FreqGoMtf[Context][InQueue] += UP_FREQ_GO_MTF;
    go_mtf = 0;
  }
  else {
    low += range * FreqGoMtf[Context][InQueue];
    range *= RangeScaleGoMtf[Context][InQueue] - FreqGoMtf[Context][InQueue];
    go_mtf = 1;
  }
  if ((RangeScaleGoMtf[Context][InQueue] += UP_FREQ_GO_MTF) > FREQ_GO_MTF_BOT) {
    RangeScaleGoMtf[Context][InQueue] = (FREQ_GO_MTF_BOT >> 1) + 1;
    FreqGoMtf[Context][InQueue] = (FreqGoMtf[Context][InQueue] + 1) >> 1;
  }
  return(go_mtf);
}

uint8_t DecodeWordTag() {
  uint8_t Tag;
  NormalizeDecoder(FREQ_WORD_TAG_BOT);
  if (FreqWordTag * (range /= RangeScaleWordTag) > code - low) {
    range *= FreqWordTag;
    FreqWordTag += UP_FREQ_WORD_TAG;
    Tag = 0;
  }
  else {
    low += range * FreqWordTag;
    range *= RangeScaleWordTag - FreqWordTag;
    Tag = 1;
  }
  if ((RangeScaleWordTag += UP_FREQ_WORD_TAG) > FREQ_WORD_TAG_BOT) {
    RangeScaleWordTag = (FREQ_WORD_TAG_BOT >> 1) + 1;
    FreqWordTag = (FreqWordTag + 1) >> 1;
  }
  return(Tag);
}

uint16_t DecodeBin(uint16_t Bins) {
  uint16_t BinNum;
  NormalizeDecoder((uint32_t)1 << 12);
  BinNum = (code - low) / (range /= Bins);
  low += range * BinNum;
  return(BinNum);
}

uint32_t DecodeBinCode(uint8_t Bits) {
  NormalizeDecoder((uint32_t)1 << Bits);
  uint32_t BinCode = (code - low) / (range >>= Bits);
  low += BinCode * range;
  return(BinCode);
}

uint32_t DecodeBaseSymbol(uint32_t NumBaseSymbols) {
  NormalizeDecoder(NumBaseSymbols);
  range /= NumBaseSymbols;
  uint32_t BaseSymbol = (code - low) / range;
  low += range * BaseSymbol;
  return(BaseSymbol);
}

uint32_t DecodeBaseSymbolCap(uint32_t NumBaseSymbols) {
  NormalizeDecoder(NumBaseSymbols);
  range /= NumBaseSymbols - 24;
  uint32_t BaseSymbol = (code - low) / range;
  low += range * BaseSymbol;
  return(BaseSymbol);
}

uint8_t DecodeFirstChar(uint8_t SymType, uint8_t LastChar) {
  NormalizeDecoder(FREQ_FIRST_CHAR_BOT);
  range /= RangeScaleFirstChar[SymType][LastChar];
  uint16_t * FreqPtr = &FreqFirstChar[SymType][LastChar][0];
  if ((RangeHigh = *FreqPtr) * range > code - low) {
    range *= RangeHigh;
    if (RangeScaleFirstChar[SymType][LastChar] >= (FREQ_FIRST_CHAR_BOT >> 1)) {
      *FreqPtr += RangeScaleFirstChar[SymType][LastChar] >> 9;
      if ((RangeScaleFirstChar[SymType][LastChar] += (RangeScaleFirstChar[SymType][LastChar] >> 9)) > FREQ_FIRST_CHAR_BOT)
        rescaleFirstChar(SymType, LastChar);
    }
    else {
      *FreqPtr += UP_FREQ_FIRST_CHAR;
      RangeScaleFirstChar[SymType][LastChar] += UP_FREQ_FIRST_CHAR;
    }
    return(SymbolFirstChar[SymType][LastChar][0]);
  }
  else {
    count = (code - low) / range;
    uint16_t temp_range;
    while ((temp_range = RangeHigh + *++FreqPtr) <= count)
      RangeHigh = temp_range;
    low += range * RangeHigh;
    range *= *FreqPtr;
    if (RangeScaleFirstChar[SymType][LastChar] >= (FREQ_FIRST_CHAR_BOT >> 1)) {
      *FreqPtr += RangeScaleFirstChar[SymType][LastChar] >> 9;
      if ((RangeScaleFirstChar[SymType][LastChar] += (RangeScaleFirstChar[SymType][LastChar] >> 9)) > FREQ_FIRST_CHAR_BOT)
        rescaleFirstChar(SymType, LastChar);
    }
    else {
      *FreqPtr += UP_FREQ_FIRST_CHAR;
      RangeScaleFirstChar[SymType][LastChar] += UP_FREQ_FIRST_CHAR;
    }
    uint8_t FoundIndex = FreqPtr - &FreqFirstChar[SymType][LastChar][0];
    uint32_t FirstChar = SymbolFirstChar[SymType][LastChar][FoundIndex];
    if (*FreqPtr > *(FreqPtr - 1)) {
      uint16_t SavedFreq = *FreqPtr;
      uint8_t * SymbolPtr = &SymbolFirstChar[SymType][LastChar][FoundIndex];
      do {
        *FreqPtr = *(FreqPtr - 1);
        FreqPtr--;
        *SymbolPtr = *(SymbolPtr - 1);
        SymbolPtr--;
      } while ((FreqPtr != &FreqFirstChar[SymType][LastChar][0]) && (SavedFreq > *(FreqPtr - 1)));
      *FreqPtr = SavedFreq;
      *SymbolPtr = FirstChar;
    }
    return(FirstChar);
  }
}

uint8_t DecodeFirstCharBinary(uint8_t LastChar) {
  NormalizeDecoder(FREQ_FIRST_CHAR_BOT);
  count = (code - low) / (range /= RangeScaleFirstChar[0][LastChar]);
  uint16_t * FreqPtr;
  if (RangeScaleFirstCharSection[LastChar][3] > count) {
    RangeScaleFirstCharSection[LastChar][3] += UP_FREQ_FIRST_CHAR;
    if (RangeScaleFirstCharSection[LastChar][1] > count) {
      RangeScaleFirstCharSection[LastChar][1] += UP_FREQ_FIRST_CHAR;
      if (RangeScaleFirstCharSection[LastChar][0] > count) {
        RangeHigh = 0;
        RangeScaleFirstCharSection[LastChar][0] += UP_FREQ_FIRST_CHAR;
        FreqPtr = &FreqFirstCharBinary[LastChar][0];
      }
      else {
        RangeHigh = RangeScaleFirstCharSection[LastChar][0];
        FreqPtr = &FreqFirstCharBinary[LastChar][0x20];
      }
    }
    else {
      RangeHigh = RangeScaleFirstCharSection[LastChar][1];
      if (RangeHigh + RangeScaleFirstCharSection[LastChar][2] > count) {
        RangeScaleFirstCharSection[LastChar][2] += UP_FREQ_FIRST_CHAR;
        FreqPtr = &FreqFirstCharBinary[LastChar][0x40];
      }
      else {
        RangeHigh += RangeScaleFirstCharSection[LastChar][2];
        FreqPtr = &FreqFirstCharBinary[LastChar][0x60];
      }
    }
  }
  else {
    RangeHigh = RangeScaleFirstCharSection[LastChar][3];
    if (RangeHigh + RangeScaleFirstCharSection[LastChar][5] > count) {
      RangeScaleFirstCharSection[LastChar][5] += UP_FREQ_FIRST_CHAR;
      if (RangeHigh + RangeScaleFirstCharSection[LastChar][4] > count) {
        RangeScaleFirstCharSection[LastChar][4] += UP_FREQ_FIRST_CHAR;
        FreqPtr = &FreqFirstCharBinary[LastChar][0x80];
      }
      else {
        RangeHigh += RangeScaleFirstCharSection[LastChar][4];
        FreqPtr = &FreqFirstCharBinary[LastChar][0xA0];
      }
    }
    else {
      RangeHigh += RangeScaleFirstCharSection[LastChar][5];
      if (RangeHigh + RangeScaleFirstCharSection[LastChar][6] > count) {
        RangeScaleFirstCharSection[LastChar][6] += UP_FREQ_FIRST_CHAR;
        FreqPtr = &FreqFirstCharBinary[LastChar][0xC0];
      }
      else {
        RangeHigh += RangeScaleFirstCharSection[LastChar][6];
        FreqPtr = &FreqFirstCharBinary[LastChar][0xE0];
      }
    }
  }
  while ((RangeHigh += *FreqPtr) <= count)
    FreqPtr++;
  uint32_t FirstChar = FreqPtr - &FreqFirstCharBinary[LastChar][0];
  low += range * (RangeHigh - *FreqPtr);
  range *= *FreqPtr;
  *FreqPtr += UP_FREQ_FIRST_CHAR;
  if ((RangeScaleFirstChar[0][LastChar] += UP_FREQ_FIRST_CHAR) > FREQ_FIRST_CHAR_BOT)
    rescaleFirstCharBinary(LastChar);
  return(FirstChar);
}

void InitDecoder(uint8_t max_code_length, uint8_t max_base_code, uint8_t num_inst_codes, uint8_t cap_encoded,
    uint8_t UTF8_compliant, uint8_t use_mtf, uint8_t * inbuf) {
  MaxBaseCode = max_base_code;
  MaxInstCode = num_inst_codes - 1;
  InBuffer = inbuf;
  code = 0, range = -1;
  for (low = 4; low != 0; low--)
    code = (code << 8) | InBuffer[InCharNum++];
  StartModelSymType(use_mtf);
  StartModelMtfQueuePos(max_code_length);
  StartModelSID();
  StartModelINST(num_inst_codes);
  StartModelERG();
  StartModelGoQueue();
  StartModelWordTag();
  if (cap_encoded || UTF8_compliant)
    StartModelFirstChar();
  else
    StartModelFirstCharBinary();
}