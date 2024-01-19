#ifndef HASHTABLE_H
#define HASHTABLE_H

#include <stdbool.h>
#include <stdint.h>

#define MAXCAPACITY   30  // 2^30 * (8Byte + 16Byte) Pointer & History_Entry
#define STARTCAPACITY 25

typedef struct History_Entry {
   uint64_t key;
   uint32_t level;
} History_Entry;

typedef struct History {
   uint16_t       capacity; // Actual capacity is 2^capacity
   uint64_t       size;
   History_Entry *value[];
} History;

History *history_create(uint16_t cap);
bool     history_contained(History *his, uint64_t a, uint32_t level);
bool     history_insert(History **his, uint64_t a, uint32_t level);
void     history_free(History *his);
void     history_increaseLevel(History *his);
uint16_t history_size(History *his);
void     history_dump(History *his);

#endif
