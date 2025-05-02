.global main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $32, %rsp
  movq $10, -16(%rbp) 
  negq -16(%rbp)
  movq -16(%rbp), %rax 
  movq %rax, -8(%rbp) 
  addq $11, -8(%rbp) 
  movq -8(%rbp), %rax 
  movq %rax, -24(%rbp) 
  movq -24(%rbp), %rax 
  movq %rax, -32(%rbp) 
  addq $41, -32(%rbp) 
  movq -32(%rbp), %rax 
  movq %rax, %rdi
  callq print_int
  addq $32, %rsp
  popq %rbp
  retq
