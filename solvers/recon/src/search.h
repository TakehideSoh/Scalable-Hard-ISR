#ifndef SEARCH_H
#define SEARCH_H
#include "runtime.h"
#include "stack.h"

#define FOUND 2
#define NOTFOUND 3
#define DISCONNECTED 4
#define STARTEQUALGOAL 5

#define RMAX UINT32_MAX

// #define MAXBFS 10737418240L  // 10 GiB
// #define MAXBFS  2147483648L  // 2 GiB
// #define MAXBFS  1073741824L  // 1 GiB
// #define MAXBFS   419430400L  // 400 MiB
// #define MAXBFS   246579200L  // 200 MiB
#define MAXBFS 21474836480L  // 20 GiB

#define btoa(x) ((x) ? "true" : "false")

Bitset **minReconfiguration(Task *task, uint32_t *depth);
uint8_t  reachable(Task *task, uint32_t *level, Bitset ***path);
bool     isTarget(Task *task, Bitset *ind);
bool     isIndependent(Bitset *m, Task *task);

#endif
