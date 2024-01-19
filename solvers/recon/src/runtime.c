#include "runtime.h"
#include "AVLtree.h"
#include "bitset.h"
#include "hashtable.h"
#include "reconio.h"
#include "stack.h"
#include "task.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void runtime_free(Runtime *rt)
{
   history_free(rt->history);
   rt->history = NULL;
   stack_free(rt->stack);
   free(rt);
}

void runtime_reset(Runtime *rt, Task *task, uint32_t r)
{
   Entry *initial = malloc(sizeof(Entry));
   if (initial == NULL) {
      perror("Failed to alloc entry");
      exit(EXIT_FAILURE);
   }
   initial->indSet = bitset_copy(task->start);
   initial->from   = UINT32_MAX;
   initial->to     = UINT32_MAX;
   initial->jump   = NULL;
   initial->pred   = NULL;

   initial->overlap = (int32_t *)malloc(sizeof(int32_t) * task->nodes);
   if (initial->overlap == NULL) {
      perror("Failed to alloc overlap vector");
      exit(EXIT_FAILURE);
   }
   memset(initial->overlap, 0, sizeof(int32_t) * task->nodes);
   for (uint32_t i = 0; i < task->nodes; i++) {
      if (testBit(task->start, i)) {
         for (uint32_t j = 0; j < task->nodes; j++) {
            if (testBit(task->graph[i], j))
               initial->overlap[j]++;
         }
      }
   }
   jump_computeSimple(initial, task);
   history_increaseLevel(rt->history);
   if (r >= (rt->stack)->size) {
      Stack *oldStack = rt->stack;
      rt->stack       = stack_init(initial, (rt->stack)->size + STACKINC);
      stack_free(oldStack);
   } else {
      stack_prepare(rt->stack, initial);
   }
}

Runtime *runtime_init(Task *task, uint32_t r)
{
   Runtime *runtime = malloc(sizeof *runtime);
   if (runtime == NULL) {
      perror("Failed to alloc runtime");
      exit(EXIT_FAILURE);
   }

   Entry *initial = malloc(sizeof *initial);
   if (initial == NULL) {
      perror("Failed to alloc entry");
      exit(EXIT_FAILURE);
   }
   initial->indSet = bitset_copy(task->start);
   initial->from   = UINT16_MAX;
   initial->to     = UINT16_MAX;
   initial->jump   = NULL;
   initial->pred   = NULL;

   initial->overlap = (int32_t *)calloc(task->nodes, sizeof(int32_t));
   if (initial->overlap == NULL) {
      perror("Failed to alloc overlap vector");
      exit(EXIT_FAILURE);
   }
   for (uint32_t i = 0; i < task->nodes; i++) {
      if (testBit(task->start, i)) {
         for (uint32_t j = 0; j < task->nodes; j++) {
            if (testBit(task->graph[i], j))
               initial->overlap[j]++;
         }
      }
   }

   runtime->stack   = stack_init(initial, max(r, STACKINC));
   runtime->history = history_create(STARTCAPACITY);
   history_insert(&(runtime->history), bitset_hash_comp(task->start), 0);
   return runtime;
}

Task *initTask(char *graph_file, char *dat_file)
{
   Task *task = malloc(sizeof *task);
   if (task == NULL) {
      perror("Failed to alloc task");
      exit(EXIT_FAILURE);
   }
   task->graph_file = graph_file;
   task->dat_file   = dat_file;
   initGraph(task);
   initParam(task);
   return task;
}

void freeTask(Task *task)
{
   free(task->start);
   free(task->target);
   free(task->targetPos);
   for (uint32_t i = 0; i < task->nodes; i++)
      free(task->graph[i]);
   free(task->graph);
   free(task);
}
