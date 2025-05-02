let counter () = 
  let count = ref 0 in 
  let inner () = 
    count := !count + 1;
    !count
  in inner
;;

let c = counter();;
print_int(c());
print_int(c());
print_int(c());


