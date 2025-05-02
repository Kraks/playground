.global main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $16, %rsp
  movq $10, -16(%rbp) 
  negq -16(%rbp)
  movq $52, -8(%rbp) 
  movq -16(%rbp), %rax 
  addq %rax, -8(%rbp) 
  movq -8(%rbp), %rax 
  movq %rax, %rdi
  callq print_int
  addq $16, %rsp
  popq %rbp
  retq
