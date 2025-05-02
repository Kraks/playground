.global main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $80, %rsp
  movq $1, -8(%rbp) 
  movq $46, -16(%rbp) 
  movq -8(%rbp), %rax 
  movq %rax, -24(%rbp) 
  addq $7, -24(%rbp) 
  movq -24(%rbp), %rax 
  movq %rax, -32(%rbp) 
  movq $4, -40(%rbp) 
  movq -32(%rbp), %rax 
  addq %rax, -40(%rbp) 
  movq -40(%rbp), %rax 
  movq %rax, -48(%rbp) 
  movq -32(%rbp), %rax 
  movq %rax, -56(%rbp) 
  movq -16(%rbp), %rax 
  addq %rax, -56(%rbp) 
  movq -56(%rbp), %rax 
  movq %rax, -64(%rbp) 
  movq -48(%rbp), %rax 
  movq %rax, -80(%rbp) 
  negq -80(%rbp)
  movq -64(%rbp), %rax 
  movq %rax, -72(%rbp) 
  movq -80(%rbp), %rax 
  addq %rax, -72(%rbp) 
  movq -72(%rbp), %rax 
  movq %rax, %rdi
  callq print_int
  addq $80, %rsp
  popq %rbp
  retq
