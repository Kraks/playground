#include <stdio.h>
#include <setjmp.h>
#include <limits.h>

#define TC_LIMIT INT_MAX

typedef int (*fun_ptr)(int, int);

struct { fun_ptr fun; int arg; } resume;

jmp_buf jmp_env;

int odd(int tcc, int x);

int even(int tcc, int x) {
  if (tcc > TC_LIMIT) {
    resume.fun = even; 
    resume.arg = x;
    _longjmp(jmp_env, -1);
  }
  return (x == 0) ? 1 : odd(tcc + 1, x - 1);
}

int odd(int tcc, int x) {
  if (tcc > TC_LIMIT) {
    resume.fun = odd; 
    resume.arg = x;
    _longjmp(jmp_env, -1);
  }
  return (x == 0) ? 1 : even(tcc + 1, x - 1);
}

int main(int argc, char* argv[]) {
  int res = 0;
  if (_setjmp(jmp_env) == 0) {
    res = even(0, 300000000);
  } else {
    res = (resume.fun)(0, resume.arg);
  }

  printf("%d\n",res); 
}
