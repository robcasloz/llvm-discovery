#include <stdio.h>

#define N 5

int v[N];

int main(int argc, char *argv[]) {
  unsigned int i;
  int max;
  max = 0;
  for (i = 0; i < N; i++) {
    if (v[i] > max)
      max = v[i];
  }
  return max;
}
