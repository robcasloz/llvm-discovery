#include <stdio.h>
#include <sanitizer/dfsan_interface.h>

#define N 5

int in[N], out[N];

int main(int argc, char *argv[]) {

  dfsan_trace_region("prologue");
  unsigned int i;
  int r;
  for (i = 0; i < N; i++) {
    out[i] = in[i] * in[i];
  }
  r = 0;
  for (i = 0; i < N; i++) {
    dfsan_trace_region("loop-body");
    r = r + out[i];
    dfsan_trace_instructions();
  }
  return r;
}
