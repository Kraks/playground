let message = "Hello"
let hello () = print_endline message;;

type date = { day : int; month : int; year : int }
let create d m y = {day = d; month = m; year = y}
let sub d1 d2 = { day = d1.day - d2.day;
                  month = d1.month - d2.month;
                  year = d1.year - d2.year }
let years d = float_of_int d.year
