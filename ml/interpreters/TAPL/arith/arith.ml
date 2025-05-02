(* Chapter 4
 * An ML Implementation of Arithmetic Expressions
 *)

exception NoRuleApplies

type term =
    TmTrue
  | TmFalse
  | TmIf of term * term * term
  | TmZero
  | TmSucc of term
  | TmPred of term
  | TmIsZero of term

let rec isNumericVal t = match t with
    TmZero -> true
  | TmSucc(t1) -> isNumericVal t1
  | _ -> false

let rec isVal t = match t with
  | TmTrue | TmFalse -> true
  | t when isNumericVal t -> true
  | _ -> false

let rec eval1 t = match t with
    TmIf(TmTrue, thn, els) -> thn
  | TmIf(TmFalse, thn, els) -> els
  | TmIf(cnd, thn, els) ->
      let cnd' = eval1 cnd in TmIf(cnd', thn, els)
  | TmSucc(t1) -> let t1' = eval1 t1 in TmSucc(t1')
  | TmPred(TmZero) -> TmZero
  | TmPred(TmSucc(t1)) when (isNumericVal t1) -> t1
  | TmPred(t1) -> let t1' = eval1 t1 in TmPred(t1')
  | TmIsZero(TmZero) -> TmTrue
  | TmIsZero(TmSucc(t1)) when (isNumericVal t1) -> TmFalse
  | TmIsZero(t1) -> let t1' = eval1 t1 in TmIsZero(t1')
  | _ -> raise NoRuleApplies

let rec eval t =
  try let t' = eval1 t in
    eval t'
  with NoRuleApplies -> t

(********* Test **********)

let zero = eval (TmIf(TmTrue, TmZero, TmSucc TmZero))
let one = eval (TmIf(TmFalse, TmZero, TmSucc TmZero))
