
type kvar = string

type var = string

type expr =
  | Int     of int
  | Bool    of bool
  | Var     of var
  | Lam     of var * expr
  | Lam_    of var * expr
  | App     of expr * expr
  | S0      of kvar * expr        (* s0 k ->  e とする *)
  | R0      of expr
  | T0      of kvar * expr
  | Code    of expr
  | If      of expr * expr * expr
  | Eq      of int * int
  | Add     of expr * expr
  | PrimOp2 of string * expr * expr
  | Let     of var * expr * expr
  | Fix     of var * var * expr (* let rec fix f n = f (fix f) n *)
type value =                        (* v を value にする *)
  | VLam  of var * expr * env (* 関数定義の時に生成される closure *)
  | VRLam of var * var * expr * env (* rec 関数定義の時に生成される closure *)
  | VCont of kont             (* shift により切り取られる continuation *)
  | VInt of int
  | VBool of bool
  | VCode of expr

and env = (var * value) list
and kont = Kont of (value -> klist -> value)
and klist = kont list
(* and kont = Kont of (v -> klist -> v) *)
(* and klist = kont list *)
