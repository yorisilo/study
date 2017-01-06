open Syntax

let counter_c = ref 0
let gen_clsfr () =
  counter_c := !counter_c + 1;
  CVar ("γ_" ^ (string_of_int !counter_c))

let counter_t = ref 0
let gen_tyvar () =
  counter_t := !counter_t + 1;
  TVar ("t_" ^ (string_of_int !counter_t))

let counter_s = ref 0
let gen_sgmvar () =
  counter_s := !counter_s + 1;
  SVar ("σ_" ^ (string_of_int !counter_s))

let rec lookup_tycntxt x tl =
  match tl with
  | [] -> failwith ("unbound variable: " ^ x)
  | Tylv(x', t, lv) :: tl' -> if x = x' then (t, lv) else lookup_tycntxt x tl'
  | _ :: tl'  -> lookup_tycntxt x tl'

let rec lookup x tyenv =
  match tyenv with
  | [] -> failwith ("unbound variable: " ^ x)
  | (x', t, lv) :: tyenv' -> if x = x' then (t, lv) else lookup x tyenv'

(* subtyl の pair の 右側は代入を完全に適用したもののみ *)
(* subtyl には型変数の重複がないことが前提 *)
let rec lookup_subtyl (tv: tyvar) subtyl : tyT option =
  match subtyl with
  | [] -> None
  | (tv', ty') :: subtyl' ->
    if tv = tv' then Some ty'
    else lookup_subtyl tv subtyl'

let extend_subtyl s t theta : subtyT list =
  (s,t) :: theta

let rec apply_subtyl ty subtyl : tyT =
  match ty with
  | TVar s ->
    begin
      match lookup_subtyl s subtyl with
      | None -> ty
      | Some ty' -> ty'
    end
  | TInt | TBool -> ty
  | _ -> failwith "not implemented"
  (* | T0Arrow *)
  (* | T0Code *)
  (* | T1Arrow *)
  (* | TKArrow *)

(* Γ L e t σ -> constr *)
let rec gen_constr (tyct: tycntxtT list) (lv: lvT) (e: expr) (t: tyT) (sgm: sgmT) (cnstl: constrT list) : constrT list =
  match e,lv with
  | (Var x), L0 ->
    let (t', L0) = lookup_tycntxt x tyct in
    let c1 = CModelGtt(tyct, (t, t')) in
    let new_cnstl = c1 :: cnstl in
    new_cnstl
  | Var x, L1(clsfr) ->
    let (t', L1(clsfr')) = lookup_tycntxt x tyct in
    let c1 = CModelGtc(tyct, (clsfr, clsfr')) in
    let new_cnstl = c1 :: cnstl in
    new_cnstl
  | Lam (x, e), L0 ->
    let t1 = gen_tyvar () in
    let t2 = gen_tyvar () in
    let sgm' = gen_sgmvar () in
    let c1 = CT0eq(t, T0Arrow(t1, t2, sgm')) in
    let c2 = CModelGts(tyct, (sgm, sgm')) in
    let new_cnstl = c1 :: c2 :: cnstl in
    let new_tyct = Tylv(x, t1, L0) :: tyct in
    gen_constr new_tyct L0 e t2 sgm' new_cnstl
  | Lam (u, e), L1(clsfr) ->
    let t1 = gen_tyvar () in
    let t2 = gen_tyvar () in
    let c1 = CT1eq(t, T1Arrow(t1, t2)) in
    let new_tyct = Tylv(u, t1, L1(clsfr)) :: tyct in
    let new_cnstl = c1 :: cnstl in
    gen_constr new_tyct (L1(clsfr)) e t2 sgm new_cnstl
  | Lam_ (x, e), L0 ->
    let cf  = gen_clsfr () in
    let cf' = gen_clsfr () in
    let t1 = gen_tyvar () in
    let t2 = gen_tyvar () in
    let new_tyct  = Gtc(cf', cf) :: Tylv(x, T0Code(t1, cf'), L0) :: tyct in
    let new_t   = T0Code(t2, cf') in
    let c1 = CModelGtt(tyct, (t, T0Code(T1Arrow(t1, t2), cf))) in
    let new_cnstl  = c1 :: cnstl in
    gen_constr new_tyct L0 e new_t sgm new_cnstl
  | App(e1, e2), lv ->
    let t1 = gen_tyvar () in
    let t2 = gen_tyvar () in
    let new_t = T1Arrow(t2, t1) in
    let new_cnstl = (CModelGtt(tyct, (t, t1)) :: cnstl) in
    gen_constr tyct lv e1 new_t sgm new_cnstl @
    gen_constr tyct lv e2 t2    sgm new_cnstl
  | S0(k, e), L0 ->
    let t0  = gen_tyvar () in
    let t1  = gen_tyvar () in
    let SCons(t2, new_sgm) = sgm in
    let cf0 = gen_clsfr () in
    let cf1 = gen_clsfr () in
    let new_t = T0Code(t0, cf0) in
    let new_tyct = Tylv(k,TKArrow((t1, cf1), (t0, cf0), new_sgm), L0) :: tyct in
    let c1 = CModelGtt(tyct, (t, T0Code(t1, cf1))) in
    let c2 = CT0eq(t2, T0Code(t0, cf0)) in
    let c3 = CModelGtc(tyct, (cf1, cf0)) in
    let new_cnstl = c1 :: c2 :: c3 :: cnstl in
    gen_constr new_tyct L0 e new_t sgm new_cnstl (* Γ |= γ1 > γ0 についてはあとで *)
  | R0 e, L0 ->
    let t' = gen_tyvar () in
    let cf = gen_clsfr () in
    let new_t = T0Code(t', cf) in
    let new_sgm = SCons(new_t, sgm) in
    let c1 = CModelGtt(tyct,(t, T0Code(t', cf))) in
    let new_cnstl = c1 :: cnstl in
    gen_constr tyct L0 e new_t new_sgm new_cnstl
  | T0(k, v), L0 ->
    let (t', L0) = lookup_tycntxt k tyct in
    let t0 = gen_tyvar () in
    let t1 = gen_tyvar () in
    let cf0 = gen_clsfr () in
    let cf1 = gen_clsfr () in
    let cf2 = gen_clsfr () in
    let cf' = gen_clsfr () in
    let new_t = T0Code(t1, cf') in
    let c1 = CModelGtt(tyct, (t, T0Code(t0, cf2))) in
    let c2 = CModelGtc(tyct, (cf2, cf0)) in
    let c3 = CT0eq(t', TKArrow((t1, cf1), (t0, cf0), sgm)) in
    let c4 = CModelGtc(tyct, (CPair(cf1, cf2), cf')) in
    let new_cnstl = c1 :: c2 :: c3 :: c4 :: cnstl in
    gen_constr tyct L0 v new_t sgm new_cnstl
  | Code e, L0 ->
    let new_clsfr = gen_clsfr () in
    let t1 = gen_tyvar () in
    let c1 = CModelGtt(tyct, (t, T0Code(t1, new_clsfr))) in
    let new_cnstl = c1 :: cnstl in
    gen_constr tyct (L1(new_clsfr)) e t1 sgm new_cnstl
  | Int num, L0 -> CT0eq(t, TInt) :: cnstl
  | Int num, _  -> CT1eq(t, TInt) :: cnstl
  | Bool b, L0  -> CT0eq(t, TBool) :: cnstl
  | Bool b, _   -> CT1eq(t, TBool) :: cnstl
  | If (e1, e2, e3), lv ->
    gen_constr tyct lv e1 TBool sgm cnstl @
    gen_constr tyct lv e2 t     sgm cnstl @
    gen_constr tyct lv e3 t     sgm cnstl
  (* | Eq *)
  (* | Add *)
  (* | PrimOp2("Add", e1, e2) -> *)
  (* | PrimOp2("Add_", e1, e2) -> *)
  | Let_ (x, e0, e1), lv ->
    let t' = gen_tyvar () in
    let cf0 = gen_clsfr () in
    let cf1 = gen_clsfr () in
    let t0 = T0Code(t', cf0) in
    let t1 = T0Code(t', cf1) in
    let new_tyct = Gtc(cf1, cf0) :: Tylv(x, t', L1 cf1) :: tyct in
    let c1 = CModelGtt(tyct, (t, (T0Code(t', cf0)))) in
    let new_cnstl = c1 :: cnstl in
    gen_constr tyct lv e0 t0 sgm new_cnstl @
    gen_constr new_tyct lv e1 t1 sgm new_cnstl
  (* | Fix *)
  | _ -> failwith "not implemented"

let cnstrl e = gen_constr [] L0 e (gen_tyvar ()) SNil []
let cnstrl_withtyct e tyct = gen_constr tyct L0 e (gen_tyvar ()) SNil []
