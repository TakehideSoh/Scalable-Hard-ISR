#ifndef TASK_H
#define TASK_H

#include "bitset.h"

typedef struct Task {
   Bitset   *start;
   Bitset   *target;
   uint16_t  isSize;
   uint16_t *targetPos;
   uint32_t  nodes;
   uint32_t  edges;
   char     *graph_file;
   char     *dat_file;
   Row     **graph;
} Task;

#endif
