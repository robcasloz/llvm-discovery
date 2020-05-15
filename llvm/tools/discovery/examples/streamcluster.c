#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

#define N 4
#define T 2

float r, p[N], out[N];

pthread_barrier_t barrier;

float dist(float p1, float p2) {
  return p1 - p2;
}

void *pkmedian(void * args) {
  int pid = (int) args;
  static float* hizs;

  if( pid==0 )
    hizs = (float*)calloc(T, sizeof(float));
  float hiz = 0.0;

  long bsize = N / T;
  long k1 = bsize * pid;
  long k2 = k1 + bsize;

  pthread_barrier_wait(&barrier);

  float myhiz = 0;
  for (long kk=k1; kk < k2; kk++ ) {
    myhiz += dist(p[kk], p[0]) * p[kk];
  }
  hizs[pid] = myhiz;

  pthread_barrier_wait(&barrier);

  for(int i = 0; i < T; i++)   {
    hiz += hizs[i];
  }

  printf("thread %d: %f\n", pid, hiz);

  return 0;
}

int main(int argc, char *argv[]) {
  pthread_barrier_init(&barrier, NULL, T);
  pthread_t workerid[T];
  pthread_attr_t attr;
  size_t i;
  pthread_attr_init(&attr);
  pthread_attr_setscope(&attr, PTHREAD_SCOPE_SYSTEM);
  for (i = 0; i < T; i++)
    pthread_create(&workerid[i], &attr, pkmedian, (void *) i);
  for (i = 0; i < T; i++)
    pthread_join(workerid[i], NULL);
  pthread_barrier_destroy(&barrier);
  return r;
}
