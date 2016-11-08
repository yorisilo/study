
type kvar = string

type var = string

type expr =
  | Var   of var
  | Lam   of var * expr
  | Lam_  of var * expr
  | App   of expr * expr
  | S0    of kvar * expr        (* s0 k ->  e とする *)
  | R0      of expr
  | T0      of kvar * expr
  | Code    of expr
  | Int     of int
  | Bool    of bool
  | If      of expr * expr * expr
  | Eq      of int * int
  | Add     of expr * expr
  | PrimOp2 of string * expr * expr
  | Let     of var * expr * expr
  | Fix     of var * var * expr
type value =                        (* v を value にする *)
  | VLam  of var * expr * env (* 関数定義の時に生成される closure *)
  | VClos of var * var * expr * env
  | VCont of kont             (* shift により切り取られる continuation *)
  | VInt of int
  | VBool of bool
  | VCode of expr

and env = (var * value) list
and kont = Kont of (value -> klist -> value)
and klist = kont list
(* and kont = Kont of (v -> klist -> v) *)
(* and klist = kont list *)

(* combinator *)
let cint  n = fun n -> Code n;;
let cbool b = fun b -> Code b;;
let capp cx cy = Code (cx cy);;

exception Not_include_x_in_xs
exception Error

(* get : var * (var * v) list -> v *)
let rec get (x, env) = match env with
  | [] -> raise Not_include_x_in_xs
  | (x',v)::xvs -> if x = x' then v else get (x, xvs)

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

(* eval : expr * (var * v) list * k -> v *)
(* eval : expr * env * kont * kont list -> v *)
let rec eval expr env k kl = match expr with
  | Var(x) -> k (get(x, env)) kl
  | Lam(x, expr) -> k (VLam(x, expr, env)) kl
  | Lam_(x, e) ->
    let y = new_var x in
    eval e ((x, VCode (Var y)) :: env) (fun v0 -> fun kl0 ->
        match v0 with
        | VCode e -> k (VCode(Lam(y, e))) kl
        | _ -> failwith "not Code in Lam_"
      ) kl
  | App(expr0, expr1) ->
    eval expr1 env (fun v1 -> fun kl1 ->
        eval expr0 env (fun v0 -> fun kl0 ->
            (match v0 with
             | VLam(x', expr', env') -> eval expr' ((x', v1) :: env') k kl0 (* env に関する cons を用意する *)
             | VClos(f, x, e, env') -> eval e ((f, v0) :: (x, v1) :: env') k kl0
             | VCont(Kont k') -> k' v1 (add_klist k kl0)
             | _ -> failwith "not apply function"
            )
          ) kl1) kl
  | S0(sk, expr) ->
    let (k1, kl1) = decompose_klist kl in
    eval expr ((sk, VCont (Kont k)) :: env) (un_kcont k1) kl1
  | R0(expr) -> eval expr env id_cont (add_klist k kl)
  | Fix(f, x, e) -> k (VClos (f, x, e, env)) kl
  | Add(e0, e1) ->
    eval e0 env (fun v0 -> fun kl0 ->
        eval e1 env (fun v1 -> fun kl1 ->
            match (v0, v1) with
            | (VInt n, VInt m) -> k (VInt (n + m)) kl1
            | _ -> failwith "not Integer in Add")
          kl0) kl
  | PrimOp2(x, e0, e1) ->
    eval e0 env (fun v0 -> fun kl0 ->
        eval e1 env (fun v1 -> fun kl1 ->
            match (x, v0, v1) with
            | ("Add", VInt n, VInt m) -> k (VInt (n + m)) kl1
            | ("Add_", VCode e0, VCode e1) -> k (VCode (PrimOp2 ("Add", e0, e1))) kl1
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
        eval e1 ((x, v0) :: env) k kl0) kl
  | Code(e) -> k (VCode e) kl
  | _ -> failwith "unknown expression"

(* eval1 : expr -> v *)
let eval1 expr = eval expr [] id_cont []

let i = Lam ("x", Var "x")

let k = Lam ("x", Lam ("y", Var "x"))

let s = Lam ("x", (Lam ("y", Lam ("z", (App ((App ((Var "x"), (Var "z"))), (App ((Var "y"), (Var "z")))))))))

let skk = App (App (s,k),k)

let _ = eval1 @@ App (skk, (Int 1))
let _ = eval1 @@ R0(Int 1)
let _ = eval1 @@ R0(S0("k", Int 1))
let _ = eval1 @@ R0(S0("k", App(Var "k", Int 1)))
let _ = eval1 @@ R0(Add(Int 1, S0("k", App(Var "k", Int 1))))
let e1 = Code(Int 1)
let e2 = Code(Int 2)
let _ = eval1 @@ e1
let _ = eval1 @@ PrimOp2("Add", Int 1, Int 2)
let _ = eval1 @@ PrimOp2("Add_", e1, e2)
let _ = eval1 @@ Lam_("x", e1)
let _ = eval1 @@ Lam_("x", Var "x")
let _ = eval1 @@ Lam_("x", PrimOp2("Add_", e1, Var "x"))
let _ = eval1 @@ Lam_("x", Lam_("y", PrimOp2("Add_", Var "x", Var "y")))
let _ = eval1 @@ Lam_("x", Lam_("x", PrimOp2("Add_", Var "x", Var "x")))
let _ = eval1 @@ Lam_("x", Lam_("x", PrimOp2("Add_", Var "y", Var "x")))
