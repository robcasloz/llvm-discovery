#include <stdio.h>

#define N 5

int in[N], out[N];

int main(int argc, char *argv[]) {
  unsigned int i;
  int r;
  r = 0;
  for (i = 0; i < N; i++) {
   r  = r + i*i;
  }
  return r;
}
