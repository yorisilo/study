open Syntax

type clsfrvar = string
type clsfrT =
  | CVar  of clsfrvar           (* γ *)
  | CPair of clsfrT * clsfrT    (* γ ∪ γ *)

type tyvar = string
type tyT =
  | TVar of tyvar                 (* x,u,...  lv0 and lv1 mix *)
  | TInt                          (* 0,1,2,... *)
  | TBool                         (* true false *)
  | T0Arrow of tyT * tyT * sigmaT (* t0 - σ -> t0 *)
  | T0Code of tyT * clsfrT        (* <t1>^γ *)
  | T1Arrow of tyT * tyT          (* t1 -> t1 *)
  | TKArrow of (tyT * clsfrT) * (tyT * clsfrT) * sigmaT (* <t1>^γ = σ => <t1>^γ *)
  | Eps
and
  sigmaT = tyT list

(* let sgm_hd sgm = *)
(*   match sgm with *)
(*   | SEps -> Eps *)
(*   | SCons(t, sgm') -> t *)

(* let sgm_tl sgm = *)
(*   match sgm with *)
(*   | SEps -> SEps *)
(*   | SCons(t, sgm') -> sgm' *)

(* type tykT = *)
(*   | TKArrow of (tyT * clsfrT) * (tyT * clsfrT) * sigmaT (\* tyT1 * clsfrT := T0Code *\) *)

type lvT =
  | L0
  | L1 of clsfrT

(* type geT = *)
(* | Get of (tyT * tyT)          (* t > t *) *)
(* | Gec of (clsfrT * clsfrT)    (* γ > γ *) *)

(* type gtt = (tyT * tyT) *)
(* type gtc = (clsfrT * clsfrT) *)
(* type tylv = (tyvar * tyT * lvT) *)

type tycntxtT =                 (* Γ *)
  | Empty
  | Gtt  of (tyT * tyT)         (* t > t *)
  | Gtc  of (clsfrT * clsfrT)   (* γ > γ *)
  | Tylv of var * tyT * lvT     (* x : t or (u : t)^γ *)

type tyenvT = (var * tyT * lvT) list

let tyenv_ex0 : tyenvT = [("x", TVar("x"), L0); ("u", T0Code(TVar("u"), CVar("γ")), L1(CVar("γ")))]

(* type genvT = expr * tyT list *)

type constrT =
  | CModelGtt of tycntxtT list * (tyT * tyT)       (* Γ |= t0 > t0 *)
  | CModelGtc of tycntxtT list * (clsfrT * clsfrT) (* Γ |= c > c *)
  | CT0eq     of tyT * tyT                         (* t0 = t0 *)
  | CT1eq     of tyT * tyT                         (* t1 = t1 *)

let counter_c = ref 0
let gen_classifier () =
  counter_c := !counter_c + 1;
  CVar ("_γ" ^ (string_of_int !counter_c))

let counter_t = ref 0
let gen_typevar () =
  counter_t := !counter_t + 1;
  TVar ("_t" ^ (string_of_int !counter_t))

let rec lookup_tycntxt x lst =
  match lst with
  | [] -> failwith ("unbound variable: " ^ x)
  | Tylv(x', t, lv) :: lst' -> if x = x' then (t, lv) else lookup_tycntxt x lst'
  | _  -> failwith ("unbound variable: " ^ x)

let rec lookup x tyenv =
  match tyenv with
  | [] -> failwith ("unbound variable: " ^ x)
  | (x', t, lv) :: tyenv' -> if x = x' then (t, lv) else lookup x tyenv'

(* Γ L e t σ -> constr *)
let rec gen_constr (tyct: tycntxtT list) (lv: lvT) (e: expr) (t: tyT) (sgm: sigmaT) (cnstl: constrT list) : constrT list =
  match (e,lv) with
  | Var x, L0 ->
    let (t', L0) = lookup_tycntxt x tyct in
    let new_cnstl = CModelGtt(tyct, (t, t')) :: cnstl in
    new_cnstl
  | Var x, L1(clsfr) ->
    let (t', L1(clsfr')) = lookup_tycntxt x tyct in
    let new_cnstl = CModelGtc(tyct, (clsfr, clsfr')) :: cnstl in
    new_cnstl
  | Lam (x, e), L0              (* σ' どうすればいいのか *)
  | Lam (x, e), L1(clsfr)       (* σ' どうすればいいのか *)
  | Lam_ (x, e), L0 ->
    let cf  = gen_classifier () in
    let cf' = gen_classifier () in
    let t1 = gen_typevar () in
    let t2 = gen_typevar () in
    let new_tyct  = Gtc(cf', cf) :: Tylv(x, T0Code(t1, cf'), L0) :: tyct in
    let new_t   = T0Code(t2, cf') in
    let new_cnstl  = (CModelGtt(tyct, (t, T0Code(T1Arrow(t1, t2), cf))) :: cnstl) in
    gen_constr new_tyct L0 e new_t sgm new_cnstl
  | App(e1, e2), lv ->
    let t1 = gen_typevar () in
    let t2 = gen_typevar () in
    let new_t = T1Arrow(t2, t1) in
    let new_cnstl = (CModelGtt(tyct, (t, t1)) :: cnstl) in
    gen_constr tyct lv e1 new_t sgm new_cnstl @
    gen_constr tyct lv e2 t2    sgm new_cnstl
  | S0(k, e), L0 ->
    let t0  = gen_typevar () in
    let t1  = gen_typevar () in
    let t2  = List.hd sgm in
    let cf0 = gen_classifier () in
    let cf1 = gen_classifier () in
    let new_t = T0Code(t0, cf0) in
    let new_sigma = List.tl sgm in
    let new_tyct = Tylv(k,TKArrow((t1, cf1), (t0, cf0), new_sigma), L0) :: tyct in
    let new_cnstl = CModelGtt(tyct, (t, T0Code(t1, cf1))) :: CT0eq(t2, T0Code(t0, cf0)) :: cnstl
    in
    gen_constr new_tyct L0 e new_t sgm new_cnstl (* Γ |= γ1 > γ0 についてはあとで *)
  | R0 e, L0 ->
    let t' = gen_typevar () in
    let cf = gen_classifier () in
    let new_t = T0Code(t', cf) in
    let new_sgm = new_t :: sgm in
    let new_cnstl = CModelGtt(tyct,( t, T0Code(t', cf))) :: cnstl in
    gen_constr tyct L0 e new_t new_sgm new_cnstl
  | T0
  | Code
  | Int
  | Bool
  | If
  | Eq
  | Add
  | PrimOp2
  | Let
  | Fix
