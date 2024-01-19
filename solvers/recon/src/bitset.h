#ifndef BITSET_H
#define BITSET_H

#include <stdbool.h>
#include <stdint.h>

#define TWOORMORE (-2)
#define NONE (-1)

#define LOGWORD 6
typedef uint64_t Word_t;

typedef struct {
   uint64_t hash0;
   uint64_t hash1;
   uint64_t estim;
   Word_t   words[];
} Bitset;

typedef struct {
   uint64_t first, last;
   Word_t   words[];
} Row;

extern uint32_t nwords;
extern uint32_t nbits;

enum { BITS_PER_Word = sizeof(Word_t) * 8 };

#define mod(x) (0x000000000000003FUL & x)
#define setBit(x, y) ((x)->words[(y) >> LOGWORD] |= 1UL << mod(y))
#define clearBit(x, y) ((x)->words[(y) >> LOGWORD] &= ~(1UL << mod(y)))
#define testBit(x, y) (((x)->words[(y) >> LOGWORD] & (1UL << mod(y))) != 0)

int8_t   bitset_compare(Bitset *a, Bitset *b);
void     bitset_dump(Bitset *b);
Bitset  *bitset_alloc();
void     bitset_clearall(Bitset *b);
bool     bitset_equal(Bitset *a, Bitset *b);
void     bitset_assign(Bitset *b, Bitset *v);
Bitset  *bitset_copy(Bitset *v);
void     bitset_free(Bitset *b);
bool     bitset_disjoint(Bitset *a, Bitset *b);
uint32_t bitset_count(Bitset *b);
uint64_t bitset_hash_comp(Bitset *a);
uint64_t bitset_hash(Bitset *a, uint32_t c);
uint64_t bitset_updateHash(Bitset *a, uint16_t from, uint16_t to, uint32_t c);

uint32_t estimate(Bitset *cur, Bitset *goal);
int32_t  bitset_overlap(Bitset *cur, Row *goal);

Row *row_alloc();
bool row_test(Row *b, uint32_t bit);
bool row_disjoint(Bitset *a, Row *b);
#endif
