#include <stdio.h>

int odd(int x);

int even(int x){return x == 0 ? 1 : odd(x-1);}
int odd(int x){return x == 0 ? 0 : even(x-1);}

int main(int argc, char* argv[]) {
  printf("%d\n", even(300000000));
}
