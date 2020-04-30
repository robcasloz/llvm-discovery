/* This program illustrates the need for considering data-flow ending in
   internal conditional branches, not only system calls. If we simplify the
   resulting DDG too aggressively (not taking into account conditional
   branches), the reduction subgraph will be gone. */

#include <stdio.h>

#define N 5

int v[N];

int main(int argc, char *argv[]) {
  unsigned int i;
  int r1, r2;
  r1 = 0;
  for (i = 0; i < N; i++) {
    r1 = r1 + v[i];
  }
  if (r1 == 0) {
    printf("r1 is zero\n");
  }
  return 0;
}
