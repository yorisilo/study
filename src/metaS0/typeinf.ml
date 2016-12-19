open Syntax

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

(* type tyenvT = (var * tyT * lvT) list *)

(* let tyenv_ex0 : tyenvT = [("x", TVar("x"), L0); ("u", T0Code(TVar("u"), CVar("γ")), L1(CVar("γ")))] *)

(* type genvT = expr * tyT list *)

type constrT =
  | CModelGtt of tycntxtT list * (tyT * tyT)       (* Γ |= t0 > t0 *)
  | CModelGtc of tycntxtT list * (clsfrT * clsfrT) (* Γ |= c > c *)
  | CModelGts of tycntxtT list * (sgmT * sgmT)     (* Γ |= σ > σ *)
  | CT0eq     of tyT * tyT                         (* t0 = t0 *)
  | CT1eq     of tyT * tyT                         (* t1 = t1 *)

let counter_c = ref 0
let gen_clsfr () =
  counter_c := !counter_c + 1;
  CVar ("_γ" ^ (string_of_int !counter_c))

let counter_t = ref 0
let gen_tyvar () =
  counter_t := !counter_t + 1;
  TVar ("_t" ^ (string_of_int !counter_t))

let counter_s = ref 0
let gen_sgmvar () =
  counter_s := !counter_s + 1;
  SVar ("_σ" ^ (string_of_int !counter_s))

let rec lookup_tycntxt x lst =
  match lst with
  | [] -> failwith ("unbound variable: " ^ x)
  | Tylv(x', t, lv) :: lst' -> if x = x' then (t, lv) else lookup_tycntxt x lst'
  | _  -> failwith ("unbound variable: " ^ x)

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
  (* | PrimOp2 *)
  (* | Let *)
  (* | Fix *)
  | _ -> failwith "not implemented"

let cnstl e = gen_constr [] L0 e (gen_tyvar ()) SNil []
let cnstl_withtyct e tyct = gen_constr tyct L0 e (gen_tyvar ()) SNil []
let _ = cnstl @@ Int 3
let _ = cnstl_withtyct (Var "x") [Tylv("x", gen_tyvar (), L0)]

(* let cnstrl1 = [CT0eq(,)] *)


let rec occurs tx t = (* t の中に tx が含まれるか *)
  if tx = t
  then true
  else match t with
    | T0Arrow(t1, t2, sgm) -> (occurs tx t1) || (occurs tx t2)
    | T1Arrow(t1, t2) -> (occurs tx t1) || (occurs tx t2)
    | _ -> false

(* ex. [x = bool; x -> y = z; y = bool] [] -> [x := bool; y := bool; z := bool -> bool] *)
let rec infer_type (cnstrl: constrT list) (theta: subtyT list) : constrT list * subtyT list =
  let rec unify t1 t2 theta : subtyT list =
    if t1 = t2 then theta
    else
      match t1, t2 with
      | T0Arrow(t01, t02, sgm1), T0Arrow(t03, t04, sgm2) ->
        let s1 = unify t01 t03 theta in
        let s2 = unify t02 t04 s1 in
        let s3 = unifysgm sgm1 sgm2 s2 in
        s3
      | T1Arrow(t11, t12), T1Arrow(t13, t14) ->
        let s1 = unify t11 t13 theta in
        let s2 = unify t12 t14 s1 in
        s2
      | T0Code(t01, cf1), T0Code(t02, cf2) ->
        let s1 = unify t01 t02 theta in
        let s2 = unifycf cf1 cf2 s1 in
        s2
      | (TVar(s), _) ->
        begin
          match lookup_subtyl s theta with
          | None ->
            let t2' = apply_subtyl t2 theta in
            if (occurs t1 t2')
            then failwith "unification failed"
            else extend_subtyl s t2' theta
          | Some t1a -> unify t1a t2 theta
        end
      | (_, TVar(s)) -> unify t2 t1 theta
      | _ -> failwith "not implemented"
  and
    unifysgm sgm1 sgm2 theta =
    match sgm1, sgm2 with
    | SNil, SNil -> theta
    (* | SVar s, *)
    (*   | SCons(ty1, sgm1'), SCons(ty2, sgm2') ->
         let theta' = unify ty1 ty2 theta in
         unifysgm sgm1' sgm2' theta' *)
    | _  -> failwith "not implemented"
  and
    unifycf cf1 cf2 theta =
    match cf1, cf2 with
    | _ -> failwith "not implemented"
  in
  match cnstrl with
  | [] -> (cnstrl, theta)
  | cnstr :: l ->
    let s1 =
      match cnstr with
      | CT0eq(t1, t2) -> unify t1 t2 theta
      | CT1eq(t1, t2) -> unify t1 t2 theta
      | _ -> failwith "not implemented"
    in
    infer_type l s1
