#include <stdio.h>

#define N 5

int in[N], out[N];

int main(int argc, char *argv[]) {
  unsigned int i;
  int r;
  for (i = 0; i < N; i++) {
    out[i] = in[i] * in[i];
  }
  r = 0;
  for (i = 0; i < N; i++) {
    r = r + out[i];
  }
  return r;
}
