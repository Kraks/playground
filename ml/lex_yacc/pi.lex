(* pi.lex *)

structure T = Tokens

type pos = int
type svalue = T.svalue
type ('a, 'b) token = ('a, 'b') T.token
type lexresult = (svalue, pos) token
type lexarg = string
type arg = lexarg

val lin = ref 1;
val col = ref 0;
val eolpos = ref 0;

val badCh : string * string * int * int -> unit = fn
  (fileName, bad, line, col) =>
  TextIO.output(TextIO.stdOut, filename ^ "["
      ^ Int.toString line ^ "." ^ Int.toString col
      ^ "] Invalid character \"" ^ bad ^ "\"\n");

val eof = fn fileName => T.EOF (!lin, !col);
