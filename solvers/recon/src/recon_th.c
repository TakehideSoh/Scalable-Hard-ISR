#define _XOPEN_SOURCE 500

#include "reconio.h"
#include "runtime.h"
#include "search.h"
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

pthread_t       main_th;
pthread_t       thread_th;
pthread_mutex_t startup_mutex;
pthread_cond_t  startup_cond;
bool            startup_flag;
pthread_mutex_t result;

void *check_reachability(void *arg)
{
   Task *task = (Task *)arg;

   uint32_t level;
   Bitset **path;

   pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, NULL);
   pthread_setcanceltype(PTHREAD_CANCEL_DEFERRED, NULL);

   pthread_mutex_lock(&startup_mutex);
   startup_flag = true;
   pthread_cond_signal(&startup_cond);
   pthread_mutex_unlock(&startup_mutex);

   uint8_t found = reachable(task, &level, &path);
   if (found == NOTFOUND)
      pthread_exit(NULL);

   pthread_mutex_lock(&result);
   if (startup_flag) {
      startup_flag = false;
      pthread_cancel(main_th);
   } else {
      pthread_exit(NULL);
   }
   fflush(stdout);
   fflush(stderr);
   pthread_mutex_unlock(&result);
   pthread_testcancel();
   pthread_join(main_th, NULL);

   if (found == STARTEQUALGOAL || found == FOUND) {
      output(path, level, BFS);
      for (uint32_t i = 0; i <= level; i++)
         free(path[i]);
      free(path);
   } else if (found == DISCONNECTED) {
      output(NULL, level, BFS);
   }
   freeTask(task);
   return NULL;
}

int main(int argc, char *argv[])
{
   if (argc != 3) {
      printf("Incorrect number of arguments %d. Usage: recon graph-file "
             "dat-file.\n",
             argc);
      return 0;
   }
   srand(time(NULL));

   Task *task = initTask(argv[1], argv[2]);

   outputHeader(task);

   main_th = pthread_self();

   pthread_mutex_init(&startup_mutex, NULL);
   pthread_cond_init(&startup_cond, NULL);
   startup_flag = false;
   pthread_mutex_init(&result, NULL);

   pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, NULL);
   pthread_setcanceltype(PTHREAD_CANCEL_DEFERRED, NULL);

   pthread_create(&thread_th, NULL, check_reachability, task);

   pthread_mutex_lock(&startup_mutex);
   while (!startup_flag)
      pthread_cond_wait(&startup_cond, &startup_mutex);
   pthread_mutex_unlock(&startup_mutex);

   uint32_t depth;
   Bitset **path;

   path = minReconfiguration(task, &depth);

   pthread_mutex_lock(&result);
   if (startup_flag) {
      startup_flag = false;
      pthread_cancel(thread_th);
   } else {
      pthread_exit(NULL);
   }
   fflush(stdout);
   fflush(stderr);
   pthread_mutex_unlock(&result);
   pthread_testcancel();
   pthread_join(thread_th, NULL);

   output(path, depth, IDA);
   if (path != NULL) {
      for (uint32_t i = 0; i <= depth; i++)
         free(path[i]);
      free(path);
   }
   freeTask(task);
   return EXIT_SUCCESS;
}
