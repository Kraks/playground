// Author: Guannan Wei
// Derived from CS352/502 lecture notes

#include <stdio.h>

typedef enum { fun_even, fun_odd } fun_id;

int wholeprog(fun_id fun, int x) {
  switch (fun) {
    case fun_even: goto even;
    case fun_odd: goto odd;
  }

  even:
    if (x == 0) return 1;
    x = x - 1; goto odd;
  odd:
    if (x == 0) return 0;
    x = x - 1; goto even;
}

int main(int argc, char* argv[]) {
  printf("%d\n", wholeprog(fun_even, 300000000));
}
