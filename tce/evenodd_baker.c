#include <stdio.h>
#include <stdlib.h>
#include <setjmp.h>

#define TC_LIMIT 100

typedef void (*cont)(int);
typedef void (*fun_ptr)(cont, int);

int tcc = 0;
struct { fun_ptr fun; int arg; cont k; } resume;
jmp_buf jmp_env;
void odd_cps(cont k, int x);

void even_cps(cont k, int x) {
  if (++tcc > TC_LIMIT) {
    tcc = 0;
    resume.fun = even_cps;
    resume.arg = x;
    resume.k = k;
    _longjmp(jmp_env, -1);
  }
  if (x == 0) (*k)(1); else odd_cps(k, x - 1);
}

void odd_cps(cont k, int x) {
  if (++tcc > TC_LIMIT) {
    tcc = 0;
    resume.fun = odd_cps;
    resume.arg = x;
    resume.k = k;
    _longjmp(jmp_env, -1);
  }
  if (x == 0) (*k)(1); else even_cps(k, x - 1);
}

void main_1(int res) { printf("%d\n", res); exit(0); }

int main(int argc, char* argv[]) {
  if (_setjmp(jmp_env) == 0) 
    even_cps(main_1, 300000000);
  else 
    (resume.fun)(resume.k, resume.arg);
}
