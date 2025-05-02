.global main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $16, %rsp

  movq $10, -8(%rbp)
  negq -8(%rbp)
  movq $52, %rax
  addq -8(%rbp), %rax

  movq %rax, %rdi
  callq print_int
  addq $16, %rsp
  movq $0, %rax
  popq %rbp
  retq
