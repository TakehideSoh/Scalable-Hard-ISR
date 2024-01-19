#include "search.h"
#include "AVLtree.h"
#include "hashtable.h"
#include "reconio.h"
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

uint32_t newEstimate(uint32_t old, uint32_t out, uint32_t in, Task *task)
{
   uint32_t result = old;
   if (testBit(task->target, out))
      result++;
   if (testBit(task->target, in))
      result--;
   return result;
}

uint32_t isNb(Bitset *cur, Bitset *goal)
{
   uint32_t count = 0;
   Word_t   wcur, wgoal;
   for (uint32_t i = 0; i < nwords; i++) {
      wcur  = cur->words[i];
      wgoal = goal->words[i];
      count += __builtin_popcountll(wcur ^ wgoal);
      if (count > 2)
         return false;
   }
   return (count == 2);
}

bool nbInStack(Runtime *rt, Bitset *b)
{
   for (int32_t i = 0; i < (rt->stack)->top; i++)
      if (isNb(((rt->stack->data)[i])->indSet, b))
         return true;
   return false;
}

Entry *nextNeighIDA(Entry *e, Task *task)
{
   Jump *jump = jump_remove(e);
   if (jump == NULL)
      return NULL;
   Entry *result = malloc(sizeof(Entry));
   if (result == NULL) {
      perror("Failed to alloc entry");
      exit(EXIT_FAILURE);
   }
   result->indSet = bitset_copy(e->indSet);
   clearBit(result->indSet, jump->node);
   setBit(result->indSet, jump->pos);
   (result->indSet)->estim = newEstimate((e->indSet)->estim, jump->node, jump->pos, task);
   result->from            = jump->node;
   result->to              = jump->pos;
   result->jump            = NULL;
   result->overlap         = NULL;
   result->pred            = e;
   free(jump);
   return result;
}

Entry *nextNeighBFS(Entry *e)
{
   Jump *jump = jump_remove(e);
   if (jump == NULL)
      return NULL;
   Entry *result = malloc(sizeof(Entry));
   if (result == NULL) {
      perror("Failed to alloc entry");
      exit(EXIT_FAILURE);
   }
   result->indSet = bitset_copy(e->indSet);
   clearBit(result->indSet, jump->node);
   setBit(result->indSet, jump->pos);
   result->from          = jump->node;
   result->to            = jump->pos;
   result->jump          = NULL;
   result->overlap       = NULL;
   result->pred          = e;
   result->indSet->hash0 = bitset_updateHash(e->indSet, jump->node, jump->pos, 0);
   result->indSet->hash1 = bitset_updateHash(e->indSet, jump->node, jump->pos, 1);
   free(jump);
   return result;
}

bool isIndependent(Bitset *m, Task *task)
{
   for (uint32_t i = 0; i < task->nodes; i++) {
      if (testBit(m, i)) {
         if (!row_disjoint(m, task->graph[i])) {
            return false;
         }
      }
   }
   return true;
}

bool iterativeA(Task *task, Runtime **rt)
{
   uint32_t R     = (task->start)->estim;
   *rt            = runtime_init(task, R + 1);
   Entry *initial = stack_peek((*rt)->stack);

   jump_compute(initial, task, RMAX);
   uint32_t Rnew, r;

   while (R < RMAX) {
      Stack *stack = (*rt)->stack;
      printf("c R=%d\n", R);
      fflush(stdout);
      Rnew = RMAX;

      while (!stack_empty(stack)) {
         pthread_testcancel();
         Entry *e    = stack_peek(stack);
         Entry *next = nextNeighIDA(e, task);
         if (next == NULL) {
            Entry *e = stack_pop(stack);
            if (e != NULL) {
               entry_free(e);
            }
         } else {
            uint32_t dist = stack->top + 1;
            if (isTarget(task, next->indSet)) {
               stack_push(next, stack);
               return true;
            } else {
               r = dist + (next->indSet)->estim;
               if (r > R) {
                  if (r < Rnew) {
                     Rnew = r;
                  }
                  entry_free(next);
                  continue;
               }
               uint64_t key = bitset_hash_comp(next->indSet);
               if (history_contained((*rt)->history, key, dist)) {
                  entry_free(next);
                  continue;
               }
               entry_update(next, task);
               jump_compute(next, task, Rnew - dist);
               stack_push(next, stack);
               history_insert(&((*rt)->history), key, stack->top);
            }
         }
      }
      R = Rnew;

      runtime_reset(*rt, task, R);
   }
   return false;
}

Bitset **minReconfiguration(Task *task, uint32_t *depth)
{
   Runtime *rt    = NULL;
   Bitset **path  = NULL;
   bool     found = iterativeA(task, &rt);

   if (found) {
      *depth = rt->stack->top;
      path   = malloc(sizeof(Bitset *) * (*depth + 1));
      if (path == NULL) {
         perror("Failed to alloc bitset");
         exit(EXIT_FAILURE);
      }
      for (uint32_t i = 0; i <= *depth; i++) {
         path[i] = bitset_copy(((rt->stack->data)[i])->indSet);
         if (!isIndependent((((rt->stack->data)[i])->indSet), task))
            printf("Error not independent %u\n", i);
      }
   } else {
      path = NULL;
   }
   if ((rt) != NULL) {
      runtime_free(rt);
   }
   return path;
}

bool isTarget(Task *task, Bitset *ind)
{
   for (uint16_t i = 0; i < task->isSize; i++)
      if (!testBit(ind, *(task->targetPos + i)))
         return false;
   return true;
}

uint8_t reachable(Task *task, uint32_t *level, Bitset ***path)
{
   uint32_t count = 0;
   Node    *root  = NULL;
   *level         = 1;
   if (bitset_equal(task->start, task->target)) {
      *path      = malloc(sizeof(Bitset *) * (2));
      (*path)[0] = bitset_copy(task->start);
      (*path)[1] = bitset_copy(task->target);
      *level     = 1;
      return STARTEQUALGOAL;
   }
   Node_list *odd    = NULL;
   Node_list *even   = NULL;
   uint32_t   number = 1;

   root = tree_insert(root, task->start, &count, UINT16_MAX, UINT16_MAX, NULL);

   Node **result = (Node **)malloc(sizeof(Node *) * (*level + 1));
   if (result == NULL) {
      perror("Failed to alloc space for BFS tree");
      exit(EXIT_FAILURE);
   }
   result[0]            = root;
   struct Node *newRoot = NULL;
   bool         found   = false;

   uint32_t     max_count = (MAXBFS / (sizeof(Node) + sizeof(Bitset) + nwords * sizeof(Word_t)));

   while (!found) {
      newRoot  = NULL;
      Entry *e = malloc(sizeof *e);
      if (e == NULL) {
         perror("Failed to alloc entry");
         exit(EXIT_FAILURE);
      }

      Node   **allNodes = tree_allNodes(result[*level - 1], number);
      uint32_t index    = 0;
      Node    *node     = NULL;

      while (index < number && count < max_count && !found) {
         node       = allNodes[index++];
         e->indSet  = node->key;
         e->to      = node->to;
         e->from    = node->from;
         e->jump    = NULL;
         e->overlap = NULL;
         e->pred    = NULL;
         jump_computeSimple(e, task);
         Entry *next;
         while ((next = nextNeighBFS(e)) != NULL) {
            pthread_testcancel();
            if (isTarget(task, next->indSet)) {
               found = true;
               *path = malloc(sizeof(Bitset *) * (*level + 1));
               if (*path == NULL) {
                  perror("Failed to alloc result path");
                  exit(EXIT_FAILURE);
               }
               (*path)[*level] = bitset_copy(task->target);
               uint32_t l      = *level - 1;
               Node    *p      = node;
               while (p != NULL) {
                  if (!isIndependent(p->key, task))
                     printf("ERROR: result is not independent\n");
                  (*path)[l--] = bitset_copy(p->key);
                  p            = p->pathParent;
               }
               entry_free(next);
               break;
            }

            if ((*level) == 1) {
               if (!tree_contained(result[(*level) - 1], next->indSet)) {
                  newRoot = tree_insert(newRoot, next->indSet, &count, next->from,
                                        next->to, node);
               }
            } else { // Which one to test first, (*level)-1 or (*level)-2 ?
               if (!tree_contained(result[(*level) - 1], next->indSet) &&
                   !tree_contained(result[(*level) - 2], next->indSet)) {
                  newRoot = tree_insert(newRoot, next->indSet, &count, next->from,
                                        next->to, node);
               }
            }
            entry_free(next);
         }
         if (node->refs == 0) {
            if ((*level) % 2 == 0)
               node_insert(&even, node);
            else
               node_insert(&odd, node);
         }
      }
      // consume the rest of nodes in allNodes
      Node_list *rest = NULL;
      while (index < number)
         node_insert(&rest, allNodes[index++]);
      prune(&rest);

      free(allNodes);
      free(e);
      result[*level] = newRoot;

      if (found || count >= max_count) {
         printf("c BFS exiting found=%s count=%u max_count=%u\n", btoa(found), count, max_count);
         fflush(stdout);
         break;
      }
      number = tree_size(newRoot);
      printf("c BFS found %u new nodes in level %u (total %u/%u)\n", number, *level, count, max_count);
      fflush(stdout);
      if (number == 0) {
         break;
      }

      uint64_t l = 0;
      if (*level > 2) {
         if ((*level) % 2 == 0)
            l = prune(&odd);
         else
            l = prune(&even);
         // printf("c Pruned %lu nodes of level %u\n", l, *level - 2);
      }

      count -= l;
      // printf("c Total number of nodes in tree %u\n", count);

      root = newRoot;
      (*level)++;
      result = (Node **)realloc(result, sizeof(Node *) * (*level + 1));
      if (result == NULL) {
         perror("Failed to alloc space for BFS tree");
         exit(EXIT_FAILURE);
      }
   }

   // Freeing memory
   // This part can be skipped, if function is not used in another function
   if ((*level) % 2 == 0) {
      prune(&odd);
      prune(&even);
   } else {
      prune(&even);
      prune(&odd);
   }
   // Free stuff in last level and all depending nodes
   number              = tree_size(result[*level]);
   Node     **allNodes = tree_allNodes(result[*level], number);
   Node_list *rest     = NULL;
   uint32_t   index    = 0;
   while (index < number)
      node_insert(&rest, allNodes[index++]);
   prune(&rest);

   free(result);
   free(odd);
   free(even);
   free(rest);
   free(allNodes);

   if (found)
      return FOUND;
   if (number == 0)
      return DISCONNECTED;
   else
      return NOTFOUND;
}
