open Higher

(* Equality *)
type (_, _) eql = Refl : ('a, 'a) eql

(* Type representations *)
type _ tyrep = ..

(* Analogue to the typeable class *)
module type TYPEABLE =
sig
  type t
  val type_rep : t type_rep Lazy.t
  val eqty : 's type_rep -> (t, 's) eql option
end

let (=~~=) {A: TYPEABLE} {B: TYPEABLE} = A.eqty (Lazy.force (B.type_rep))

(* Implicit instances *)

module rec R :
sig
  type genericT = {T: R.DATA} -> T.t -> T.t
  type 'u genericQ = {T: R.DATA} -> T.t -> 'u
  type 'c genericFapp =
    < g: 'b. {T: R.DATA} -> (T.t -> 'b, 'c) app -> T.t -> ('b, 'c) app >
  type 'c genericFunit = < u: 'g. 'g -> ('g, 'c) app >
  module type DATA =
  sig
    type t
    val data_name : string Lazy.t
    module Typeable : TYPEABLE with type t = t
    val gmapT : genericT -> t -> t
    val gmapQ : 'u genericQ -> t -> 'u list
    val gfoldl : 'c genericFapp -> 'c gnericFunit -> t -> (t, 'c) app
    val constructor : t -> Syb_constructor.constructor
  end
end = R
include R
