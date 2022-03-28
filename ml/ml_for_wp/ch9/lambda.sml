signature LEXICAL =
sig
  datatype token = Id of string | Key of string
  val scan : string -> token list
end;

signature KEYWORD =
sig
  val alphas : string list
  and symbols : string list
end;

functor Lexical (Keyword: KEYWORD) : LEXICAL =
struct
  datatype token = Key of string | Id of string;

  fun member (x: string, l) =
    List.exists (fn y => x=y) l;

  fun alphaTok a = if member(a, Keyword.alphas) then Key(a)
                   else Id(a);

  (* 扫描符号关键字 *)
  fun symbolic(sy, ss) =
    case Substring.getc ss of
         NONE => (Key sy, ss)
       | SOME(c, ss1) =>
           if member(sy, Keyword.symbols) orelse not (Char.isPunct c)
           then (Key sy, ss)
           else symbolic (sy ^ String.str c, ss1);
  
  fun scanning(toks, ss) = 
    case Substring.getc ss of
         NONE => rev toks
       | SOME(c, ss1) =>
           if Char.isAlphaNum c
           then let val (id, ss2) = Substring.splitl Char.isAlphaNum ss
                    val tok = alphaTok(Substring.string id)
                in
                  scanning(tok::toks, ss2)
                end
           else if Char.isPunct c
           then let val (tok, ss2) = symbolic(String.str c, ss1)
                in scanning(tok::toks, ss2)
                end
           else scanning(toks, Substring.dropl(not o Char.isGraph) ss);

  (* fun scan a = scanning([], Substring.all a); *)
  fun scan a = scanning([], Substring.full a);
end;
