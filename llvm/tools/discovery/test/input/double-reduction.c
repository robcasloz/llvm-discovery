#include <stdio.h>

#define N 4

int v[N];

int main(int argc, char *argv[]) {
  unsigned int i;
  int r;
  r = 0;
  for (i = 0; i < N; i++) {
    r = r + v[i];
    r = r + v[i];
  }
  return r;
}
