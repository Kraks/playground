variable {p q r : Prop}

theorem t1 : p -> q -> p :=
  fun hp : p => fun hq : q => hp

#print t1
