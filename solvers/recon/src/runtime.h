#ifndef RUNTIME_H
#define RUNTIME_H

//#include "AVLtree.h"
#include "bitset.h"
//#include "stack.h"
#include "hashtable.h"
#include "task.h"

typedef struct Runtime {
   History      *history;
   struct Stack *stack;
} Runtime;

extern uint32_t nwords;
extern uint32_t nbits;

void     runtime_free(Runtime *rt);
void     runtime_reset(Runtime *rt, Task *task, uint32_t r);
Runtime *runtime_init(Task *task, uint32_t r);
Task    *initTask(char *graph_file, char *dat_file);
void     freeTask(Task *task);

#endif
