#include "stack.h"
#include "runtime.h"
#include "task.h"
#include <stdio.h>
#include <stdlib.h>

Entry *stack_pop(Stack *stack)
{
   if (stack->top <= -1) {
      return NULL;
   } else {
      return (stack->data)[stack->top--];
   }
}

bool stack_push(Entry *e, Stack *stack)
{
   (stack->data)[++stack->top] = e;
   return true;
}

Entry *stack_peek(Stack *stack)
{
   if (stack->top == -1)
      return NULL;
   else
      return (stack->data)[stack->top];
}

bool stack_contains(Bitset *is, Stack *stack)
{
   for (int32_t i = 0; i < stack->top; i++)
      if (bitset_equal((stack->data)[i]->indSet, is)) {
         return true;
      }
   return false;
}

bool stack_empty(Stack *stack) { return stack->top == -1; }

void stack_dump(uint32_t j, Stack *stack)
{
   printf("\n Stack %d \n", j);
   for (int32_t i = 0; i <= stack->top; i++)
      bitset_dump((stack->data)[i]->indSet);
}

void stack_free(Stack *stack)
{
   for (int32_t i = 0; i <= stack->top; i++) {
      entry_free(stack->data[i]);
   }
   free(stack);
}

Stack *stack_init(Entry *initial, uint32_t s)
{
   Stack *stack = (Stack *)malloc(sizeof(Stack) + s * sizeof(Entry *));
   if (stack == NULL) {
      perror("Failed to alloc stack");
      exit(EXIT_FAILURE);
   }
   stack_prepare(stack, initial);
   stack->size = s;
   return stack;
}

void stack_prepare(Stack *stack, Entry *initial)
{
   (stack->data)[0] = initial;
   stack->top       = 0;
}

/* Entry Operations  */

void entry_free(Entry *e)
{
   if (e != NULL) {
      bitset_free(e->indSet);
      if (e->overlap != NULL)
         free(e->overlap);
      Jump *j = e->jump;
      while (j != NULL) {
         Jump *next = j->next;
         free(j);
         j = next;
      }
      free(e);
   }
}

void entry_update(Entry *e, Task *task)
{
   e->overlap = (int32_t *)malloc(sizeof(int32_t) * task->nodes);
   if (e->overlap == NULL) {
      perror("Failed to alloc overlap vector");
      exit(EXIT_FAILURE);
   }
   Row *from = task->graph[e->from];
   Row *to   = task->graph[e->to];
   for (uint32_t i = 0; i < task->nodes; i++) {
      e->overlap[i] = e->pred->overlap[i];
      if (testBit(from, i))
         e->overlap[i]--;
      if (testBit(to, i))
         e->overlap[i]++;
   }
}

void jump_insert(Entry *e, uint32_t node, uint32_t pos)
{
   Jump *jump = (Jump *)malloc(sizeof(Jump));
   if (jump == NULL) {
      perror("Failed to alloc jump");
      exit(EXIT_FAILURE);
   }
   jump->node = node;
   jump->pos  = pos;
   jump->next = e->jump;
   e->jump    = jump;
}

Jump *jump_remove(Entry *e)
{
   if (e->jump == NULL)
      return NULL;
   Jump *jump      = e->jump;
   Jump *next_jump = jump->next;
   e->jump         = next_jump;
   return jump;
}

void jump_print(Entry *e)
{
   Jump *cur = e->jump;
   printf("From %u to %u\n", e->from + 1, e->to + 1);
   while (cur != NULL) {
      printf("(%u,%u), ", cur->node + 1, cur->pos + 1);
      cur = cur->next;
   }
   printf("\n");
}

bool jump_skip(Entry *e, Task *task, uint32_t i, bool jumpTarget, uint32_t rnew)
{
   uint32_t result = e->indSet->estim;
   if (testBit(task->target, i))
      result++;
   if (jumpTarget)
      result--;
   return (result >= rnew);
}

uint32_t findInNB(uint32_t j, Entry *e, Task *task)
{
   Row *row = task->graph[j];
   for (uint32_t i = row->first; i <= row->last; i++) {
      Word_t fin = (e->indSet)->words[i] & row->words[i];
      if (fin != 0)
         return i * BITS_PER_Word + __builtin_ffsll(fin) - 1;
   }
   return 0; // Never happens
}

void jump_compute(Entry *e, Task *task, uint32_t rnew)
{
   for (uint32_t i = 0; i < task->nodes; i++) {
      if (testBit(e->indSet, i))
         continue;
      int32_t overlap;
      if (e->overlap[i] == 1) {
         overlap = findInNB(i, e, task);
      } else {
         if (e->overlap[i] == 0)
            overlap = NONE;
         else
            overlap = TWOORMORE;
      }

      bool jumpTarget = testBit(e->indSet, i);
      if (overlap >= 0 && (e->to != (uint32_t)overlap || e->from != i)) {
         if (!jump_skip(e, task, overlap, jumpTarget, rnew)) {
            jump_insert(e, overlap, i);
         }
      } else if (overlap == NONE) {
         for (uint32_t j = 0; j < task->nodes; j++) {
            if (testBit(e->indSet, j) && (e->to != j || e->from != i)) {
               if (!jump_skip(e, task, j, jumpTarget, rnew))
                  jump_insert(e, j, i);
            }
         }
      }
   }
}

void jump_computeSimple(Entry *e, Task *task)
{
   for (uint32_t i = 0; i < task->nodes; i++) {
      if (testBit(e->indSet, i))
         continue;
      int32_t overlap = bitset_overlap(e->indSet, task->graph[i]);
      if (overlap >= 0 && (e->to != (uint32_t)overlap || e->from != i))
         jump_insert(e, overlap, i);
      else if (overlap == NONE) {
         for (uint32_t j = 0; j < task->nodes; j++) {
            if (testBit(e->indSet, j) && (e->to != j || e->from != i))
               jump_insert(e, j, i);
         }
      }
   }
}
