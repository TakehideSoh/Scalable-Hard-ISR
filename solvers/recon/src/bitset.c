#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bitset.h"

int8_t bitset_compare(Bitset *a, Bitset *b)
{
   if (a->hash0 != b->hash0) {
      if (a->hash0 < b->hash0)
         return -1;
      return 1;
   }
   if (a->hash1 != b->hash1) {
      if (a->hash1 < b->hash1)
         return -1;
      return 1;
   }
   for (uint32_t i = 0; i < nwords; i++) {
      if (a->words[i] != b->words[i]) {
         if (a->words[i] < b->words[i]) {
            return -1;
         }
         return 1;
      }
   }
   return 0;
}

void bitset_dump(Bitset *b)
{
   if (b == NULL) {
      printf("Wieso NULL?\n");
      return;
   }
   for (uint32_t i = 0; i < nwords; i++) {
      Word_t w = b->words[i];
      for (uint32_t j = 0; j < BITS_PER_Word; j++) {
         if (w & 1) {
            printf("%d ", i * BITS_PER_Word + j + 1);
         }
         w >>= 1;
      }
   }
   printf("\n");
}

Bitset *bitset_alloc()
{
   Bitset *b = (Bitset *)malloc(sizeof(Bitset) + nwords * sizeof(Word_t));
   if (b == NULL) {
      perror("Failed to alloc bitv");
      exit(EXIT_FAILURE);
   }
   memset(b->words, 0, sizeof(Word_t) * nwords);
   return b;
}

void bitset_clearall(Bitset *b)
{
   if (b != NULL)
      memset(b->words, 0, sizeof(*b->words) * nwords);
}

bool bitset_equal(Bitset *a, Bitset *b)
{
   for (uint32_t i = 0; i < nwords; i++) {
      Word_t wa = a->words[i], wb = b->words[i];
      if ((wa != wb)) {
         return false;
      }
   }
   return true;
}

void bitset_assign(Bitset *b, Bitset *v)
{
   for (uint32_t i = 0; i < nwords; i++) {
      b->words[i] = v->words[i];
   }
}

Bitset *bitset_copy(Bitset *v)
{
   Bitset *b = bitset_alloc();
   memcpy(b, v, sizeof(Bitset) + nwords * sizeof(Word_t));
   return b;
}

void bitset_free(Bitset *b)
{
   if (b != NULL) {
      free(b);
   }
}

bool bitset_disjoint(Bitset *a, Bitset *b)
{
   for (uint32_t i = 0; i < nwords; i++)
      if ((a->words[i] & b->words[i]) != 0) {
         return false;
      }
   return true;
}

Row *row_alloc()
{
   Row *b = (Row *)malloc(sizeof(Row) + nwords * sizeof(Word_t));
   if (b == NULL) {
      perror("Failed to alloc row");
      exit(EXIT_FAILURE);
   }
   memset(b->words, 0, sizeof(Word_t) * nwords);

   b->first = 0;
   b->last  = nwords - 1;
   return b;
}

bool row_disjoint(Bitset *a, Row *b)
{
   bool result = true;
   for (uint32_t i = b->first; i <= b->last; i++)
      if ((a->words[i] & b->words[i]) != 0) {
         result = false;
         break;
      }
   return result;
}

uint32_t bitset_count(Bitset *b)
{
   uint32_t count = 0;
   for (uint32_t i = 0; i < nwords; i++) {
      Word_t w = b->words[i];
      for (uint32_t j = 0; j < BITS_PER_Word; j++) {
         if (w & 1)
            count++;
         w >>= 1;
      }
   }
   return count;
}

uint32_t estimate(Bitset *cur, Bitset *goal)
{
   uint32_t count = 0;
   Word_t   wcur, wgoal;
   for (uint32_t i = 0; i < nwords; i++) {
      wcur  = cur->words[i];
      wgoal = goal->words[i];
      count += __builtin_popcountll(wcur ^ wgoal);
   }
   return count >> 1;
}

uint64_t bitset_hash(Bitset *a, uint32_t c)
{
   uint64_t result = 0;
   for (uint32_t i = c; i < nwords; i = i + 2)
      result = result ^ a->words[i];
   return result;
}

uint64_t bitset_updateHash(Bitset *a, uint16_t from, uint16_t to, uint32_t c)
{
   if (c == 0) {
      uint64_t hash0 = a->hash0;
      if (from % 2 == 0)
         hash0 = hash0 ^ (1L << (from % BITS_PER_Word));
      if (to % 2 == 0)
         hash0 = hash0 ^ (1L << (to % BITS_PER_Word));
      return hash0;
   } else {
      uint64_t hash1 = a->hash1;
      if (from % 2 == 1)
         hash1 = hash1 ^ (1L << (from % BITS_PER_Word));
      if (to % 2 == 1)
         hash1 = hash1 ^ (1L << (to % BITS_PER_Word));
      return hash1;
   }
}

uint64_t bitset_hash_comp(Bitset *a)
{
   const uint64_t m = 0xc6a4a7935bd1e995LLU;
   const int      r = 47;
   uint64_t       h = m;

   for (uint32_t i = 0; i < nwords; i++) {
      uint64_t k = a->words[i];
      k *= m;
      k ^= k >> r;
      k *= m;
      h ^= k;
      h *= m;
   }
   h ^= h >> r;
   h *= m;
   h ^= h >> r;
   return h;
}

int32_t bitset_overlap(Bitset *cur, Row *goal)
{
   uint32_t count = 0;
   bool     first = true;
   int32_t  pos   = -1;
   for (uint32_t i = goal->first; i <= goal->last; i++) {
      count += __builtin_popcountll(cur->words[i] & goal->words[i]);
      if (count > 0 && first) {
         first = false;
         pos   = i;
      }
      if (count > 1)
         return TWOORMORE;
   }
   if (count == 0)
      return NONE;
   Word_t fin = cur->words[pos] & goal->words[pos];
   return pos * BITS_PER_Word + __builtin_ffsll(fin) - 1;
}
