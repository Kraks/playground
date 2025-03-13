from math import gcd

h=m=p=0
d=f0=f3=n=q=1
while p**2*(m-f0)<f3:
  d=2*n*d-4*(-1)**n*h
  n=n+1
  g=gcd(n,int(q))
  q=n*q/g
  if g==1: p=p+1
  m=0; g=q
  while g>1:
    g=g//2; m=m+d
  h=f0
  f0=2*n*h
  f3=(2*n+3)*f3
