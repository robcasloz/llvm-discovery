#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

#define N 5

pthread_mutex_t lock;

int r, in[N], out[N];

void *square(void * args) {
  int i = (int) args;
  out[i] = in[i] * in[i];
  return NULL;
}

void *sum(void * args) {
  int i = (int) args;
  pthread_mutex_lock(&lock);
  r = r + out[i];
  pthread_mutex_unlock(&lock);
  return NULL;
}

int main(int argc, char *argv[]) {
  pthread_t workerid[N];
  pthread_attr_t attr;
  size_t i;
  pthread_attr_init(&attr);
  pthread_attr_setscope(&attr, PTHREAD_SCOPE_SYSTEM);
  for (i = 0; i < N; i++)
    pthread_create(&workerid[i], &attr, square, (void *) i);
  for (i = 0; i < N; i++)
    pthread_join(workerid[i], NULL);
  pthread_mutex_init(&lock, NULL);
  for (i = 0; i < N; i++)
    pthread_create(&workerid[i], &attr, sum, (void *) i);
  for (i = 0; i < N; i++)
    pthread_join(workerid[i], NULL);
  pthread_mutex_destroy(&lock);
  return r;
}
