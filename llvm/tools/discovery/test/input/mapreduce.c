#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

#define T 2
#define N 4

int in[N], partial[T];

void *sum(void * args) {
  int i, t = (int) args;
  for (i = (N / T) * t; i < (N / T) * (t + 1); i++) {
    partial[t] += in[i];
  }
  return NULL;
}

int main(int argc, char *argv[]) {
  pthread_t workerid[T];
  pthread_attr_t attr;
  int i, t, global;
  for (i = 0; i < N; i++) {
    in[i] = 0;
  }
  for (t = 0; t < T; t++) {
    partial[t] = 0;
  }
  for (i = 0; i < N; i++) {
    in[i] = in[i] * in[i];
  }
  pthread_attr_init(&attr);
  pthread_attr_setscope(&attr, PTHREAD_SCOPE_SYSTEM);
  for (t = 0; t < T; t++)
    pthread_create(&workerid[t], &attr, sum, (void *) t);
  for (t = 0; t < T; t++)
    pthread_join(workerid[t], NULL);
  for (t = 0; t < T; t++) {
    global += partial[t];
  }

  printf("%d\n", global);

  return 0;
}
