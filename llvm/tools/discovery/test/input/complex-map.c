#include <stdio.h>

#define N 5

int in[N], out[N];

int main(int argc, char *argv[]) {
  unsigned int i;
  for (i = 0; i < N; i++) {
    out[i] = (in[i] * in[i]) / 2;
  }
  for (i = 0; i < N; i++) {
    printf("%d\n", out[i]);
  }
}
