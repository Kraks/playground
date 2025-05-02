open Core.Std

let rec read_and_accumulate acc = 
  let line = In_channel.input_line In_channel.stdin in
  match line with
  | None -> acc
  | Some x -> read_and_accumulate (acc +. Float.of_string x)
;;

let () = 
  printf "Total: %F\n" (read_and_accumulate 0.)
