#include "reconio.h"
#include "runtime.h"
#include "search.h"
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
   if (argc != 3) {
      printf("Incorrect number of arguments %d. Usage: recon graph-file dat-file.\n",
             argc);
      return 0;
   }

   uint32_t depth, level;
   Task    *task = initTask(argv[1], argv[2]);
   Bitset **path;

   outputHeader(task);

   uint8_t found = reachable(task, &level, &path);

   if (found == STARTEQUALGOAL || found == FOUND) {
      output(path, level, BFS);
      for (uint32_t i = 0; i <= level; i++)
         free(path[i]);
      free(path);
   } else if (found == DISCONNECTED) {
      output(NULL, level, BFS);
   } else {
      path = minReconfiguration(task, &depth);
      output(path, depth, IDA);
      if (path != NULL) {
         for (uint32_t i = 0; i <= depth; i++)
            free(path[i]);
         free(path);
      }
   }

   freeTask(task);
   return EXIT_SUCCESS;
}
