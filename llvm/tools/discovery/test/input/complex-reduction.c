// a foldl-style reduction of a sequence of complex numbers, with complex multiply
// as the operator. The numbers are stored as two arrays (real and imaginary parts)
// and similarly the result as rR and rI. Could abstract as a proper type etc, but that
// shouldn't change the data flow.


#include <stdio.h>

#define N 5

int aR[N] = {1,2,4,1,3}, aI[N] = {1,3,5,1,3}; // real and imaginary parts

int main(int argc, char *argv[]) {
  unsigned int i;
  int rR, rI;     // real and imaginary parts of result
  rR = aR[0];
  rI = aI[0];
  for (i = 1; i < N; i++) {
    int oldR, oldI;
    oldR = rR;
    oldI = rI;
    rR = oldR*aR[i] - (oldI*aI[i]);
    rI = oldR*aI[i] + (oldI*aR[i]);
  }
  printf ("%d %d\n", rR, rI);
}
