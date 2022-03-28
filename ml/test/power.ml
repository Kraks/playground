let rec power x = function k ->
  if k = 1 then x
  else if k mod 2 = 0 then power (x * x) (k / 2)
       else x * power (x * x) (k / 2)
;;
