#include <stdio.h>

void print_int(long n) {
  printf("%ld", n);
}

long read_int() {
  long n;
  scanf("%ld", &n);
  return n;
}
