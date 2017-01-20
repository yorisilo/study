open Syntax

(* combinator *)
let cint  n = fun n -> Code n;;
let cbool b = fun b -> Code b;;
let capp cx cy = Code (cx cy);;

exception Error

let extend (x,v) env = (x,v) :: env

(* get : var * (var * v) list -> v *)
let rec get x env = match env with
  | [] -> failwith ("unbound variable: " ^ x)
  | (x',v)::xvs -> if x = x' then v else get x xvs

(* let id = fun a -> a *)
let id a = a

let add_klist k kl = Kont k :: kl

let decompose_klist kl = match kl with
  | [] -> failwith "shift without reset"
  | k :: ks -> (k, ks)

let un_kcont (Kont k) = k

let id_cont v kl = match kl with
  | [] -> v
  | (Kont k) :: ks -> k v ks

let counter = ref 0
let new_var x =
  counter := !counter + 1;
  "_" ^ x ^ (string_of_int !counter)

let rec eval expr env k kl = match expr with
  | Var(x) -> k (get x env) kl
  | Lam(x, expr) -> k (VLam(x, expr, env)) kl
  | Lam_(x, e) ->
    let y = new_var x in
    eval e (extend (x, VCode (Var y)) env) (fun v0 -> fun kl0 ->
        match v0 with
        | VCode e -> k (VCode(Lam(y, e))) kl
        | _ -> failwith "not Code in Lam_"
      ) kl
  | App(expr0, expr1) ->
    eval expr1 env (fun v1 -> fun kl1 ->
        eval expr0 env (fun v0 -> fun kl0 ->
            (match v0 with
             | VLam(x', expr', env') -> eval expr' (extend (x',v1) env') k kl0
             | VRLam(f, x, e, env') -> eval e (extend (f,v0) (extend (x,v1) env')) k kl0
             | VCont(Kont k') -> k' v1 (add_klist k kl0)
             | _ -> failwith "not apply function"
            )
          ) kl1) kl
  | S0(sk, expr) ->
    let (k1, kl1) = decompose_klist kl in
    eval expr (extend (sk, VCont (Kont k)) env) (un_kcont k1) kl1
  | R0(expr) -> eval expr env id_cont (add_klist k kl)
  | T0(ks, e) -> eval e env id_cont (add_klist k kl)
  | Fix(f, x, e) -> k (VRLam (f, x, e, env)) kl
  | Add(e0, e1) ->
    eval e0 env (fun v0 -> fun kl0 ->
        eval e1 env (fun v1 -> fun kl1 ->
            match (v0, v1) with
            | (VInt n, VInt m) -> k (VInt (n + m)) kl1
            | _ -> failwith "not Integer in Add")
          kl0) kl
  | PrimOp2(op, e0, e1) ->
    eval e0 env (fun v0 -> fun kl0 ->
        eval e1 env (fun v1 -> fun kl1 ->
            match (op, v0, v1) with
            | ("Add", VInt n, VInt m) -> k (VInt (n + m)) kl1
            | ("Add_", VCode e0, VCode e1) -> k (VCode (PrimOp2 ("Add", e0, e1))) kl1
            | ("Min", VInt n, VInt m) -> k (VInt (n - m)) kl1
            | ("Min_", VCode e0, VCode e1) -> k (VCode (PrimOp2 ("Min", e0, e1))) kl1
            | ("Mult", VInt n, VInt m) -> k (VInt (n * m)) kl1
            | ("Mult_", VCode e0, VCode e1) -> k (VCode (PrimOp2 ("Mult", e0, e1))) kl1
            | ("Eq", VInt n, VInt m) when n = m -> k (VBool true) kl1
            | ("Eq", VInt n, VInt m) when n != m -> k (VBool false) kl1
            | _ -> failwith "not Integer in PrimOp2")
          kl0) kl
  | Int(n) -> k (VInt n) kl
  | Bool(b) -> k (VBool b) kl
  | If(e0, e1, e2) ->
    eval e0 env (fun v0 -> fun kl0 ->
        match v0 with
        | VBool(true) ->
          eval e1 env k kl0
        | VBool(false) ->
          eval e2 env k kl0
        | _ -> failwith "not boolean in if"
      ) kl
  | Let(x, e0, e1) ->
    eval e0 env (fun v0 -> fun kl0 ->
        eval e1 (extend (x, v0) env) k kl0) kl
  | Let_(x, e0, e1) ->
    eval e0 env (fun v0 -> fun kl0 ->
        eval e1 (extend (x, v0) env) k kl0) kl
  | Code(e) -> k (VCode e) kl
  | _ -> failwith "unknown expression"

(* eval1 : expr -> v *)
let eval1 expr = eval expr [] id_cont []

let rec print_expr ppf e =
  let printf fmt = Format.fprintf ppf fmt in
  match e with
  | Int n -> printf "%d" n
  | Bool b -> Format.print_bool b
  | Var x -> printf "%s" x
  | Lam(x, e) ->  printf "@[λ%s." x; printf "%a@]" print_expr e
  | Lam_(u, e) ->  printf "@[λ_%s." u; printf "%a@]" print_expr e
  | App(e1, e2) -> printf "@[(%a %a)@]" print_expr e1 print_expr e2
  | S0(k, e) -> printf "@[(S0 %s ->@ " k; printf "%a)@]" print_expr e
  | R0 e -> printf "@[R0(%a)@]" print_expr e
  | T0(k, e) -> printf "@[(T0 " ;printf "%a)@]" print_expr e
  | Add(e1, e2) -> printf "@[%a +@ %a@]" print_expr e1 print_expr e2
  | PrimOp2("Add", e1, e2)  -> printf "@[%a +@ %a@]" print_expr e1 print_expr e2
  | PrimOp2("Add_", e1, e2) -> printf "@[%a +_@ %a@]" print_expr e1 print_expr e2
  | PrimOp2("Min", e1, e2)  -> printf "@[%a -@ %a@]" print_expr e1 print_expr e2
  | PrimOp2("Min_", e1, e2) -> printf "@[%a -_@ %a@]" print_expr e1 print_expr e2
  | PrimOp2("Mult", e1, e2) -> printf "@[%a x@ %a@]" print_expr e1 print_expr e2
  | PrimOp2("Mult_", e1, e2) -> printf "@[%a x_@ %a@]" print_expr e1 print_expr e2
  | PrimOp2("Eq", e1, e2) -> printf "@[%a =@ %a@]" print_expr e1 print_expr e2
  | Let(x, e0, e1) -> printf "@[let %s = " x; printf "%a in %a@]" print_expr e0 print_expr e1
  | Let_(x, e0, e1) -> printf "@[let_ %s = " x; printf "%a in_ %a@]" print_expr e0 print_expr e1
  | Code e -> printf "@[@,<%a>@,@]" print_expr e
  | _ -> failwith "not implemented"

let print_expr' e = print_expr Format.std_formatter e

let rec print_value ppf v =
  let printf fmt = Format.fprintf ppf fmt in
  match v with
  | VInt n -> printf "%d" n
  | VBool b -> Format.print_bool b
  | VCode e -> printf "@[@,<%a>@,@]" print_expr e
  | _ -> failwith "not implemented"

let print_value' v = print_value Format.std_formatter v

let i = Lam ("x", Var "x")

let k = Lam ("x", Lam ("y", Var "x"))

let s = Lam ("x", (Lam ("y", Lam ("z", (App ((App ((Var "x"), (Var "z"))), (App ((Var "y"), (Var "z")))))))))

let skk = App (App (s,k),k)

let ce1 = Code(Int 1)
let ce2 = Code(Int 2)
let ce10 = Code(Int 10)
let ce20 = Code(Int 20)
let _ = eval1 @@ App (skk, (Int 1))
let _ = eval1 @@ R0(Int 1)
let _ = eval1 @@ R0(S0("k", Int 1))
let _ = eval1 @@ R0(S0("k", T0("k", Int 1)))
let _ = eval1 @@ R0(S0("k", App(Var "k", Int 1)))
let _ = eval1 @@ R0(S0("k", T0("k", App(Var "k", Int 1))))
let _ = eval1 @@ R0(S0("k", App(Var "k", Code (Int 1))))
let _ = eval1 @@ R0(Add(Int 1, S0("k", App(Var "k", Int 1))))
let _ = eval1 @@ R0(Add(Int 10, R0(Add(Int 20, S0("k1", S0("k2", App(Var "k2", Int 1)))))))
let _ = eval1 @@ R0(Add(Int 10, R0(Add(Int 20, S0("k1", S0("k2", App(Var "k1", Int 1)))))))
let _ = eval1 @@ R0(Add(Int 10, R0(Add(Int 20, S0("k1", S0("k2", App(Var "k1", App(Var "k2", Int 1))))))))
let _ = print_value' @@ eval1 @@ R0(PrimOp2("Add_", ce10, R0(PrimOp2("Add_", ce20, S0("k1", S0("k2", App(Var "k1", App(Var "k2", ce1))))))))
let _ = eval1 @@ R0(Add(Int 10, R0(Add(Int 20, S0("k1", S0("k2", T0("k1", App(Var "k1", R0(T0("k2", App(Var "k2", Int 1)))))))))))
let _ = eval1 @@ ce1
let _ = eval1 @@ ce2
let _ = eval1 @@ PrimOp2("Add", Int 1, Int 2)
let _ = eval1 @@ PrimOp2("Add_", ce1, ce2)
let _ = eval1 @@ Lam_("x", ce1)
let _ = eval1 @@ Lam_("x", Var "x")
let _ = eval1 @@ Lam_("x", PrimOp2("Add_", ce1, Var "x"))
let _ = eval1 @@ Lam_("x", Lam_("y", PrimOp2("Add_", Var "x", Var "y")))
let _ = eval1 @@ Lam_("x", Lam_("x", PrimOp2("Add_", Var "x", Var "x")))
(* let _ = eval1 @@ Lam_("x", Lam_("x", PrimOp2("Add_", Var "y", Var "x"))) *)

let _ = eval1 @@ Lam("x", Fix("f", "n", If(PrimOp2("Eq", Var "n", Int 0), Int 1, PrimOp2("Mult", Var "x", App(Var "f", PrimOp2("Min", Var "n", Int 1))))))
let _ = eval1 @@ App(App(Lam("x", Fix("f", "n", If(PrimOp2("Eq", Var "n", Int 0), Int 1, PrimOp2("Mult", Var "x", App(Var "f", PrimOp2("Min", Var "n", Int 1)))))), Int 2), Int 10)
(* let _ = eval1 @@ Lam_("x", Fix("f", "n", If(PrimOp2("Eq", Var "n", Int 0), Code(Int 1), PrimOp2("Mult_", Var "x", App(Var "f", PrimOp2("Min", Var "n", Int 1)))))) *)

let _ = eval1 @@ R0(Let_("x_1", Code(Int 3), S0("k", Let_("x_2", Code(Int 4), T0("k", App(Var "k", Code(Int 8)))))))
