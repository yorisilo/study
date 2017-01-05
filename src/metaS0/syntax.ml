
(**
   evaluator
*)
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
  | Let     of var * expr * expr (* let x = e1 in e2 *)
  | Let_    of var * expr * expr (* let_ x = e1 in_ e2 *)
  | Fix     of var * var * expr  (* let rec fix f n = f (fix f) n *)
type value =                     (* v を value にする *)
  | VLam  of var * expr * env   (* 関数定義の時に生成される closure *)
  | VRLam of var * var * expr * env (* rec 関数定義の時に生成される closure *)
  | VCont of kont          (* shift により切り取られる continuation *)
  | VInt of int
  | VBool of bool
  | VCode of expr

and env = (var * value) list
and kont = Kont of (value -> klist -> value)
and klist = kont list
(* and kont = Kont of (v -> klist -> v) *)
(* and klist = kont list *)


(**
   type infer
*)
type clsfrvar = string
type clsfrT =
  | CVar  of clsfrvar           (* γ *)
  | CPair of clsfrT * clsfrT    (* γ ∪ γ *)

type tyvar  = string
type sgmvar = string
type tyT =
  | TVar of tyvar                 (* x,u,...  lv0 and lv1 mix *)
  | TInt                          (* 0,1,2,... *)
  | TBool                         (* true false *)
  | T0Arrow of tyT * tyT * sgmT   (* t0 - σ -> t0 *)
  | T0Code of tyT * clsfrT        (* <t1>^γ *)
  | T1Arrow of tyT * tyT          (* t1 -> t1 *)
  | TKArrow of (tyT * clsfrT) * (tyT * clsfrT) * sgmT (* <t1>^γ = σ => <t1>^γ *)
and
  sgmT =
  | SNil
  | SVar  of sgmvar
  | SCons of tyT * sgmT

type subtyT = (tyvar * tyT)     (* ex. x := Int *)

type lvT =
  | L0
  | L1 of clsfrT

type tycntxtT =                 (* Γ *)
  | Empty
  | Gtt  of (tyT * tyT)         (* t > t *)
  | Gtc  of (clsfrT * clsfrT)   (* γ > γ *)
  | Tylv of var * tyT * lvT     (* x : t or (u : t)^γ *)

type constrT =
  | CModelGtt of tycntxtT list * (tyT * tyT)       (* Γ |= t0 > t0 *)
  | CModelGtc of tycntxtT list * (clsfrT * clsfrT) (* Γ |= c > c *)
  | CModelGts of tycntxtT list * (sgmT * sgmT)     (* Γ |= σ > σ *)
  | CT0eq     of tyT * tyT                         (* t0 = t0 *)
  | CT1eq     of tyT * tyT                         (* t1 = t1 *)
