#ifndef STACK_H
#define STACK_H

#include "bitset.h"
#include "runtime.h"
#include "task.h"

#define STACKINC 1000

typedef struct Jump {
   uint32_t     node;
   uint32_t     pos;
   struct Jump *next;
} Jump;

typedef struct Entry {
   Bitset       *indSet;
   uint32_t      from;
   uint32_t      to;
   Jump         *jump;
   int32_t      *overlap;
   struct Entry *pred;
} Entry;

typedef struct Stack {
   int32_t  top;
   uint32_t size;
   Entry   *data[];
} Stack;

Entry *stack_pop(Stack *stack);
bool   stack_push(Entry *entry, Stack *stack);
Entry *stack_peek(Stack *stack);
bool   stack_contains(Bitset *is, Stack *stack);
bool   stack_empty(Stack *stack);
void   stack_dump(uint32_t j, Stack *stack);
void   stack_free(Stack *stack);
Stack *stack_init(Entry *initial, uint32_t s);
void   stack_prepare(Stack *stack, Entry *initial);

void entry_free(Entry *entry);
void entry_update(Entry *entry, Task *task);

void  jump_insert(Entry *entry, uint32_t node, uint32_t pos);
Jump *jump_remove(Entry *entry);
void  jump_print(Entry *entry);
void  jump_computeSimple(Entry *entry, Task *task);
void  jump_compute(Entry *entry, Task *task, uint32_t rnew);

#endif
