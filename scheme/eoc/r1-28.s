.global main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $40, %rsp
  movq $5, -24(%rbp) 
  addq $3, -24(%rbp) 
  movq -24(%rbp), %rax 
  movq %rax, -16(%rbp) 
  addq $2, -16(%rbp) 
  movq $7, -40(%rbp) 
  addq $8, -40(%rbp) 
  movq $3, -32(%rbp) 
  movq -40(%rbp), %rax 
  addq %rax, -32(%rbp) 
  movq -16(%rbp), %rax 
  movq %rax, -8(%rbp) 
  movq -32(%rbp), %rax 
  addq %rax, -8(%rbp) 
  movq -8(%rbp), %rax 
  movq %rax, %rdi
  callq print_int
  addq $40, %rsp
  popq %rbp
  retq
