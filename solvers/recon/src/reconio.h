#ifndef RECONIO_H
#define RECONIO_H

#include "bitset.h"
#include "runtime.h"

#define MAXLINE 2048

#define BFS 6
#define IDA 7

extern uint32_t nwords;
extern uint32_t nbits;

void initParam(Task *task);
void initGraph(Task *task);
void outputHeader(Task *task);
void output(Bitset **path, uint32_t depth, uint8_t algo);

#endif
