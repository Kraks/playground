.global main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $40, %rsp
  movq $1, -8(%rbp) 
  addq $2, -8(%rbp) 
  movq -8(%rbp), %rax 
  movq %rax, -16(%rbp) 
  movq $2, -24(%rbp) 
  addq $3, -24(%rbp) 
  movq -24(%rbp), %rax 
  movq %rax, -32(%rbp) 
  movq -16(%rbp), %rax 
  movq %rax, -40(%rbp) 
  movq -32(%rbp), %rax 
  addq %rax, -40(%rbp) 
  movq -40(%rbp), %rax 
  movq %rax, %rdi
  callq print_int
  addq $40, %rsp
  popq %rbp
  retq
