#define _POSIX_C_SOURCE 200809L
#include <ctype.h>
#include <errno.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "reconio.h"
#include "runtime.h"
#include "search.h"

uint32_t nwords;
uint32_t nbits;

/*   ************* Init operations  */
char *trim(char *s)
{
   char *ptr;
   if (!s)
      return NULL;
   if (!*s)
      return s; // handle empty string
   for (ptr = s + strlen(s) - 1; (ptr >= s) && isspace((unsigned char)*ptr); --ptr)
      ;
   ptr[1] = '\0';
   return s;
}

void initParam(Task *task)
{
   FILE    *fp;
   char    *line;
   char     delim[] = " ";
   size_t   len     = MAXLINE;
   uint32_t count_s = 0;
   uint32_t count_t = 0;

   line = (char *)malloc(MAXLINE * sizeof(char));
   if (line == NULL) {
      perror("Failed to alloc line in initParam");
      exit(EXIT_FAILURE);
   }

   fp = fopen(task->dat_file, "r"); // read mode
   if (fp == NULL) {
      perror("Error while opening dat file");
      exit(EXIT_FAILURE);
   }

   while (true) {
      if (getline(&line, &len, fp) == -1) {
         perror("getline() failed");
         exit(EXIT_FAILURE);
      }
      if (line[0] != 'c')
         break;
   }

   if (line[0] != 's') {
      fprintf(stderr, "ERROR: Expect a line beginning with 's'\n");
      exit(EXIT_FAILURE);
   }
   trim(line);

   task->start = bitset_alloc();
   char *ptr   = strtok(line, delim);
   ptr         = strtok(NULL, delim);

   while (ptr != NULL) {
      if (atoi(ptr) < 1 || (uint32_t)atoi(ptr) > task->nodes) {
         fprintf(stderr, "ERROR: Start state contains invalid node id %s\n", ptr);
         exit(EXIT_FAILURE);
      }
      setBit(task->start, (atoi(ptr) - 1));
      count_s++;
      ptr = strtok(NULL, delim);
   }
   if (!isIndependent(task->start, task)) {
      fprintf(stderr, "ERROR: Start state is not an independent set\n");
      exit(EXIT_FAILURE);
   }
   task->start->hash0 = bitset_hash(task->start, 0);
   task->start->hash1 = bitset_hash(task->start, 1);

   task->targetPos = (uint16_t *)malloc(sizeof(uint16_t) * count_s);
   if (task->targetPos == NULL) {
      perror("Failed to alloc target positions");
      exit(EXIT_FAILURE);
   }
   for (uint16_t i = 0; i < count_s; i++)
      *(task->targetPos + i) = 0;

   if (getline(&line, &len, fp) == -1) {
      perror("getline() failed");
      exit(EXIT_FAILURE);
   }

   if (line[0] != 't') {
      fprintf(stderr, "ERROR: Expect a line beginning with 't'\n");
      exit(EXIT_FAILURE);
   }
   trim(line);

   task->target = bitset_alloc();
   ptr          = strtok(line, delim);
   ptr          = strtok(NULL, delim);
   while (ptr != NULL) {
      if (atoi(ptr) < 1 || (uint32_t)atoi(ptr) > task->nodes) {
         fprintf(stderr, "ERROR: Target state contains invalid node id %s\n", ptr);
         exit(EXIT_FAILURE);
      }
      setBit(task->target, (atoi(ptr) - 1));
      *(task->targetPos + count_t) = (atoi(ptr) - 1);
      count_t++;
      ptr = strtok(NULL, delim);
   }
   if (!isIndependent(task->target, task)) {
      fprintf(stderr, "ERROR: Target state is not an independent set\n");
      exit(EXIT_FAILURE);
   }
   if (count_s != count_t) {
      fprintf(stderr, "ERROR: Source and target have different size\n");
      exit(EXIT_FAILURE);
   }

   (task->target)->estim = 0;
   (task->start)->estim  = estimate(task->start, task->target);
   task->isSize          = count_s;
   fclose(fp);
   free(line);
}

void initGraph(Task *task)
{
   FILE  *fp;
   char  *line;
   char   delim[] = " ";
   size_t len     = MAXLINE;

   line = (char *)malloc(MAXLINE * sizeof(char));
   if (line == NULL) {
      perror("Failed to alloc line in initGraph");
      exit(EXIT_FAILURE);
   }

   fp = fopen(task->graph_file, "r"); // read mode
   if (fp == NULL) {
      perror("Error while opening graph file");
      exit(EXIT_FAILURE);
   }

   while (true) {
      if (getline(&line, &len, fp) == -1) {
         perror("getline() failed");
         exit(EXIT_FAILURE);
      }
      if (line[0] != 'c')
         break;
   }

   if (line[0] != 'p') {
      fprintf(stderr, "ERROR: Expect a line beginning with 'p'\n");
      exit(EXIT_FAILURE);
   }
   trim(line);

   char *ptr   = strtok(line, delim);
   ptr         = strtok(NULL, delim);
   task->nodes = atoi(ptr);
   if (task->nodes <= 1) {
      fprintf(stderr, "ERROR: Number of nodes must be greater than one\n");
      exit(EXIT_FAILURE);
   }
   nbits       = task->nodes;
   nwords      = (nbits >> LOGWORD) + 1;
   ptr         = strtok(NULL, delim);
   task->edges = atoi(ptr);
   if (task->edges <= 0) {
      fprintf(stderr, "ERROR: Number of edges must be greater than zero\n");
      exit(EXIT_FAILURE);
   }

   task->graph = malloc(sizeof(Row *) * task->nodes);
   if (task->graph == NULL) {
      perror("Error while alloacting graph");
      exit(EXIT_FAILURE);
   }
   for (uint32_t i = 0; i < task->nodes; i++) {
      task->graph[i] = row_alloc();
   }

   uint32_t k = 0;
   ssize_t  bytes;
   while (true) {
      if ((bytes = getline(&line, &len, fp)) == -1 && errno != 0) {
         perror("getline(edges) failed");
         exit(EXIT_FAILURE);
      }
      if (bytes <= 0) // empty line or end-of-file reached
         break;
      if (line[0] == 'c')
         continue;

      if (line[0] != 'e') {
         fprintf(stderr, "ERROR: Expect a line beginning with 'e'\n");
         exit(EXIT_FAILURE);
      }
      trim(line);

      ptr        = strtok(line, delim);
      ptr        = strtok(NULL, delim);
      uint32_t i = atoi(ptr);
      if (i < 1 || i > task->nodes) {
         fprintf(stderr, "ERROR: found invalid node %u\n", i);
         exit(EXIT_FAILURE);
      }
      ptr        = strtok(NULL, delim);
      uint32_t j = atoi(ptr);
      if (j < 1 || j > task->nodes) {
         fprintf(stderr, "ERROR: found invalid node %u\n", j);
         exit(EXIT_FAILURE);
      }
      setBit(task->graph[i - 1], (j - 1));
      setBit(task->graph[j - 1], (i - 1));

      k++;
   }
   if (k != task->edges) {
      fprintf(stderr, "ERROR: found wrong number of edges\n");
      exit(EXIT_FAILURE);
   }
   free(line);
   fclose(fp);

   for (uint32_t i = 0; i < task->nodes; i++) {
      Row     *r = task->graph[i];
      uint32_t j = 0;
      while (r->words[j] == 0 && j < (nwords - 1))
         j++;
      r->first = j;
      j        = nwords - 1;
      while (r->words[j] == 0 && j > 0)
         j--;
      r->last = j;
   }
}

/*           ********** Output operations *****************  */

void outputHeader(Task *task)
{
   printf("c Copyright Volker Turau & Christoph Weyer, 2022\n");
   printf("c Institute of Telematics\n");
   printf("c Hamburg University of Technology, Hamburg, Germany\n");
   printf("c Contact: turau@tuhh.de\n");
   printf("c Graph file: %s\n", task->graph_file);
   printf("c Target file: %s\n", task->dat_file);
   printf("c Size of independent set: %u\n", task->isSize);
   printf("c Number of nodes of graph: %u\n", task->nodes);
   printf("c Number of edges of graph: %u\n", task->edges);
   printf("c Average degree of graph: %.2f\n", 2.0 * task->edges / task->nodes);
   printf("s ");
   bitset_dump(task->start);
   printf("t ");
   bitset_dump(task->target);
}

void outputPath(Bitset **path, uint32_t l)
{
   for (uint32_t i = 0; i < l; i++) {
      printf("a ");
      bitset_dump(path[i]);
      // printf("level= %u estim= %lu\n",i, path[i]->estim);
   }
}

void output(Bitset **path, uint32_t depth, uint8_t algo)
{
   if (algo == IDA)
      printf("c Found with: Iterative A*-Search\n");
   else if (algo == BFS)
      printf("c Found with: Breadth First Search\n");

   if (path != NULL) {
      printf("a YES\n");
      outputPath(path, depth + 1);
      printf("c Length: %u\n", depth);
   } else {
      printf("a NO\n");
   }
}
