(* type ('a,'b) c = *)
(*   | I of int *)
(*   | B of bool *)
(*   | Cint of int *)
(*   | Capp of ('a code * 'b code) *)

(* type ('a,'b) v = *)
(*   | VVar of string *)
(*   | Vc of ('a,'b) c *)

(* type ('a,'b) e0 = *)
(*   | E0Var of ('a,'b) v *)
(*   | E0If of ('a,'b) e0 * ('a,'b) e0 * ('a,'b) e0 *)
(*   | E0App of ('a,'b) e0 * ('a,'b) e0 *)
(*   | E0Lam_ of string * ('a,'b) e0 *)
(*   | E0Lam__ of string * ('a,'b) e0 *)
(*   | E0R0 of ('a,'b) e0 *)
(*   | E0S0 of ('a,'b) e0 *)

(* type ('a,'b) e1 = *)
(*   | E1Var of string *)
(*   | E1C of ('a,'b) c *)
(*   | E1Lam of string * ('a,'b) e1 *)
(*   | E1App of ('a,'b) e1 * ('a,'b) e1 *)
(*   | E1If of ('a,'b) e1 * ('a,'b) e1 * ('a,'b) e1 *)

type kvar = string

type var = string

type expr =
  | Var   of var
  | Lam   of var * expr
  | Lam_  of var * expr
  | Lam__ of var * expr
  | App   of expr * expr
  | If    of bool * expr * expr
  | S0    of kvar * expr        (* s0 k ->  e とする *)
  | R0    of expr
  | T0    of kvar * expr
  | Code  of expr
  | Int   of int
  | Bool  of bool
  | Eq    of int * int
  | Add   of expr * expr

type value =                        (* v を value にする *)
  | VLam  of var * expr * env (* 関数定義の時に生成される closure *)
  | VCont of kont             (* shift により切り取られる continuation *)
  | VInt of int

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

(* eval : expr * (var * v) list * k -> v *)
(* eval : expr * env * kont * kont list -> v *)
let rec eval expr env k kl = match expr with
  | Add(Int n, Int m) -> k (VInt (n + m)) kl
  | Int(n) -> k (VInt n) kl
  | Var(x) -> k (get(x, env)) kl
  | Lam(x, expr) -> k (VLam(x, expr, env)) kl
  | App(expr0, expr1) ->
    eval expr1 env (fun v1 -> fun kl1 ->
        eval expr0 env (fun v0 -> fun kl0 ->
            (match v0 with
             | VLam(x', expr', env') -> eval expr' ((x', v1) :: env') k kl0 (* env に関する cons を用意する *)
             | VCont(Kont k') -> k' v1 (add_klist k kl0)
             | VInt _ -> failwith "VInt not apply function"
            )
          ) kl1) kl
  | S0(sk, expr) ->
    let (k1, kl1) = decompose_klist kl in
    eval expr ((sk, VCont (Kont k)) :: env) (un_kcont k1) kl1
  | R0(expr) -> eval expr env id_cont (add_klist k kl)
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
