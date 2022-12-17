.globl main
main:
  movq $10, %rax
  addq $32, %rax
  movq %rax, %rdi
  callq print_int
  movq $0, %rax
  retq
