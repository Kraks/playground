// Author: Guannan Wei
// Derived from CS352/502 lecture notes

#include <stdio.h>

typedef void* (*fun_ptr)(int);
struct { fun_ptr fun; int arg; } resume;

void* odd(int x);

void* even(int x) {
  if (x == 0) return (void*)1;
  resume.fun = odd;
  resume.arg = x - 1;
  return &resume;
}

void* odd(int x) {
  if (x == 0) return (void*)0;
  resume.fun = even;
  resume.arg = x - 1;
  return &resume;
}

int main(int argc, char* argv[]) {
  void* res = even(300000000);
  while (res == &resume)
    res = (resume.fun)(resume.arg);
  printf("%d\n", (int)res);
}
