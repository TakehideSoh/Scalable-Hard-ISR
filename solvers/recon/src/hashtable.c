#include "hashtable.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void history_dump(History *his)
{
   for (uint64_t i = 0; i < (1UL << his->capacity); i++)
      if ((his->value)[i] != NULL) {
         printf("Level: %u\n", his->value[i]->level);
         printf("Key: %lu\n", his->value[i]->key);
      }
}

uint64_t find_slot(History *his, uint64_t key)
{
   uint64_t i = key & ((1UL << his->capacity) - 1);
   while ((his->value)[i] != NULL && (his->value)[i]->key != key) {
      i = (i + 1) & ((1UL << his->capacity) - 1);
   }
   return i;
}

bool history_contained(History *his, uint64_t a, uint32_t level)
{
   uint64_t i = find_slot(his, a);
   if (his->value[i] != NULL && his->value[i]->level <= level) {
      return true;
   } else {
      return false;
   }
}

History *history_create(uint16_t cap)
{
   History *temp =
       (History *)malloc(sizeof(History) + (1UL << cap) * sizeof(History_Entry *));
   memset(temp, 0, sizeof(History) + (1UL << cap) * sizeof(History_Entry *));
   temp->capacity = cap;
   return temp;
}

bool history_insert(History **his, uint64_t a, uint32_t level)
{
   static bool open = true;
   if (!open)
      return false;
   if (5 * (1UL << his[0]->capacity) <= 8 * his[0]->size) {
      if (his[0]->capacity == MAXCAPACITY) {
         printf("c History limit reached\n");
         fflush(stdout);
         open = false;
         return false;
      }
      History *temp = (History *)malloc(sizeof(History) + 2 * (1UL << his[0]->capacity) *
                                                              sizeof(History_Entry *));
      if (temp == NULL) {
         perror("Failed to alloc history entry in resize");
         exit(EXIT_FAILURE);
      }
      temp->capacity = his[0]->capacity + 1;
      temp->size     = his[0]->size;

      memset(temp->value, 0, sizeof(History_Entry *) * (1UL << temp->capacity));

      for (uint64_t i = 0; i < (1UL << his[0]->capacity); i++) {
         if (his[0]->value[i] != NULL) {
            history_insert(&temp, his[0]->value[i]->key, his[0]->value[i]->level);
         }
      }
      history_free(*his);
      *his = temp;
      printf("c History level %u %lu\n", his[0]->capacity, his[0]->size);
      fflush(stdout);
   }

   uint64_t i = find_slot(*his, a);
   if (his[0]->value[i] != NULL) {
      if (level < his[0]->value[i]->level)
         his[0]->value[i]->level = level;
      return true;
   } else {
      History_Entry *tmp = (History_Entry *)malloc(sizeof(History_Entry));
      if (tmp == NULL) {
         perror("Failed to alloc history entry");
         exit(EXIT_FAILURE);
      }
      his[0]->value[i]        = tmp;
      his[0]->value[i]->key   = a;
      his[0]->value[i]->level = level;
      his[0]->size++;
   }
   return true;
}

void history_free(History *his)
{
   for (uint64_t i = 0; i < (1UL << his->capacity); i++)
      if (his->value[i] != NULL)
         free(his->value[i]);
   free(his);
}

void history_increaseLevel(History *his)
{
   for (uint64_t i = 0; i < (1UL << his->capacity); i++)
      if (his->value[i] != NULL)
         his->value[i]->level++;
}

uint16_t history_size(History *his) { return his->size; }
