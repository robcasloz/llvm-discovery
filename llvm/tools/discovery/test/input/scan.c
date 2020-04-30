#include <stdio.h>

#define N 6

int in[N] = {1,2,3,4,5,6}, out[N];

int main(int argc, char *argv[]) {
  unsigned int i;
  out[0] = in[0];
  for (i = 1; i < N; i++) {
    out[i] = out[i-1] + in[i];
  }
  for (i = 0; i < N; i++) {
    printf("%d\n", out[i]);
  }
}
