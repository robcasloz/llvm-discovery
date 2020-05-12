#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

#define T 2
#define N 4

int in[N], partial[T];

int main(int argc, char *argv[]) {
  int i, t, global;
  for (i = 0; i < N; i++) {
    in[i] = 0;
  }
  for (t = 0; t < T; t++) {
    partial[t] = 0;
  }
  // Map.
  for (i = 0; i < N; i++) {
    in[i] = in[i] * in[i];
  }
  // Partial reductions.
  for (t = 0; t < T; t++) {
    // This would be done by each thread, it's sequential here for stability.
    for (i = (N / T) * t; i < (N / T) * (t + 1); i++) {
      partial[t] += in[i];
    }
  }
  // Final reduction.
  for (t = 0; t < T; t++) {
    global += partial[t];
  }

  printf("%d\n", global);

  return 0;
}
