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

let rec print_clsfr ppf cf =
  let printf fmt = Format.fprintf ppf fmt in
  match cf with
  | CVar cf -> printf "%s" cf
  | CPair(g1,g2) -> printf "@[%a U@ %a@]" print_clsfr g1 print_clsfr g2

let rec print_sgm ppf sgm =
  let printf fmt = Format.fprintf ppf fmt in
  match sgm with
  | SNil   -> printf "ε"
  | SVar s -> printf "%s" s
  | SCons(t,s)  -> printf "@[%a, %a@]" print_ty t print_sgm s
and
  print_ty ppf ty =
  let printf fmt = Format.fprintf ppf fmt in
  match ty with
  | TVar tv -> printf "%s" tv
  | TInt -> printf "Int"
  | TBool -> printf "Bool"
  | T0Arrow(t1,t2,sgm) -> printf "@[%a -(%a)-> %a@]" print_ty t1 print_sgm sgm print_ty t2
  | T0Code(t, cf) -> printf "@[@,<%a>^(%a)@]" print_ty t print_clsfr cf
  | T1Arrow(t1, t2) -> printf "@[%a -> %a@]" print_ty t1 print_ty t2
  | TKArrow((t1,cf1), (t2,cf2), sgm) -> printf "@[@,<%a>^(%a) = %a => <%a>^(%a)@]" print_ty t1 print_clsfr cf1 print_sgm sgm print_ty t2 print_clsfr cf2

let rec print_subty ppf (tv, t) =
  let printf fmt = Format.fprintf ppf fmt in
  printf "@[%s := " tv; printf "%a@]" print_ty t

let rec print_lv ppf lv =
  let printf fmt = Format.fprintf ppf fmt in
  match lv with
  | L0 -> printf "lv0"
  | L1 cf -> printf "%a" print_clsfr cf

let rec print_tycntxt ppf tyc =
  let printf fmt = Format.fprintf ppf fmt in
  match tyc with
  | Empty -> ()
  | Gtt(t1, t2) -> printf "@[%a@,>@,%a@]" print_ty t1 print_ty t2
  | Gtc(cf1, cf2) -> printf "@[%a@,>@,%a@]" print_clsfr cf1 print_clsfr cf2
  | Tylv(x, t, l) -> printf "@[%s@,: " x; printf "(%a)^(%a)@]" print_ty t print_lv l

let rec print_tycntxtl ppf tycl =
  let printf fmt = Format.fprintf ppf fmt in
  match tycl with
  | [] -> ()
  | tyc :: l -> printf "@[%a,@,%a@]" print_tycntxt tyc print_tycntxtl l

let print_cnstr ppf c =
  let printf fmt = Format.fprintf ppf fmt in
  match c with
  | CModelGtt(tyctl, (t1, t2)) -> printf "@[%a @,|=@, %a @,>@, %a@]" print_tycntxtl tyctl print_ty t1 print_ty t2
  | CModelGtc(tyctl, (cf1, cf2)) -> printf "@[%a @,|=@, %a @,>@, %a@]" print_tycntxtl tyctl print_clsfr cf1 print_clsfr cf2
  | CModelGts(tyctl, (sgm1, sgm2)) -> printf "@[%a @,|=@, %a @,>@, %a@]" print_tycntxtl tyctl print_sgm sgm1 print_sgm sgm2
  | CT0eq(t1, t2) -> printf "@[%a @,=@, %a@]" print_ty t1 print_ty t2
  | CT1eq(t1, t2) -> printf "@[%a @,=@, %a@]" print_ty t1 print_ty t2

let rec print_cnstrl ppf cl =
  let printf fmt = Format.fprintf ppf fmt in
  match cl with
  | [] -> ()
  | c :: l -> printf "@[%a,\n@,%a@]" print_cnstr c print_cnstrl l

let print_cnstrl' cl = print_cnstrl Format.std_formatter cl

(* let cnstrl1 = [CT0eq(,)] *)

let cnstrl e = gen_constr [] L0 e (gen_tyvar ()) SNil []
let cnstrl_withtyct e tyct = gen_constr tyct L0 e (gen_tyvar ()) SNil []

let pp_cnstrl e = print_cnstrl' @@ cnstrl e
let pp_cnstrl_withtyct e tyct = print_cnstrl' @@ gen_constr tyct L0 e (gen_tyvar ()) SNil []

let _ = pp_cnstrl @@ Int 3
let _ = pp_cnstrl_withtyct (Var "x") [Tylv("x", gen_tyvar (), L0)]
let _ = pp_cnstrl @@ R0(Code(Int 1))
let _ = pp_cnstrl @@ R0(S0("k", T0("k", Code (Int 1))))
let _ = pp_cnstrl @@ R0(S0("k", T0("k", App(Var "k", Code (Int 1)))))
let _ = pp_cnstrl @@ Lam("x", Var "x")
let _ = pp_cnstrl @@ Lam_("x", Var "x")
let _ = cnstrl @@ R0(Let_("x", Code(Int 1), R0(Let_("y", Code(Int 2), S0("k", Let_("z", Var "x", T0("k", App(Var "k", Var "z"))))))))

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
