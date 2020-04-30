// Sequential example that generates the DDG of a stateful pipeline where each
// step contains two operations.
#include <stdio.h>

#define M 3 // Number of stages
#define K 2 // Number of data items

int data[K];
int state[M];

int main(int argc, char *argv[]) {
  unsigned int i, j;
  // For each data item.
  for (i = 0; i < K; i++) {
    // For each pipeline stage.
    for (j = 0; j < M; j++) {
      data[i] = data[i] + state[j];
      data[i] = data[i] * data[i];
      state[j] = data[i];
    }
  }
  for (i = 0; i < K; i++) {
    printf("%d\n", data[i]);
  }
}
