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

type exp =
  | Var   of string
  | Lam   of string * exp
  | Lam_  of string * exp
  | Lam__ of string * exp
  | App   of exp * exp
  | If    of bool * exp * exp
  | S0    of string * exp         (* s0 -> k e とする *)
  | R0    of exp
  | T0    of string * exp
  | Code  of exp
  | Int   of int
  | Bool  of bool
  | Eq    of int * int

type v =
  | VLam  of string * exp * env (* 関数定義の時に生成される closure *)
  | VCont of k             (* shift により切り取られる continuation *)
and env = (string * v) list
and k = (v -> v)

(* combinator *)
let cint (n:int) = fun (n:int) -> .<n>. ;;
let cbool (b:bool) = fun (b:bool) -> .<b>. ;;
let capp (cx,cy) = .<cx cy>.;;

exception Not_include_x_in_xs
exception Error

(* get : string * (string * v) list -> v *)
let rec get (x, env) = match env with
  | [] -> raise Not_include_x_in_xs
  | (x',v)::xvs -> if x = x' then v else get (x, xvs)

(* let id = fun a -> a *)
let id a = a

(* eval : exp * (string * v) list * k -> v *)
(* eval : exp * env * k -> v *)
let rec eval (exp, env, k, kl) = match exp with
  | Var(x) -> k (get(x, env))
  | Lam(x, exp) -> k (VLam(x, exp, env))
  | App(exp0, exp1) -> eval (exp1, env, (fun v1 ->
      eval (exp0, env, (fun v0 ->
          (match v0 with
           | VLam(x', exp', env') -> eval (exp', (x', v1) :: env', k)
           | VCont(k') -> k (k' v1))))))
  | S0(sk, exp) -> eval (exp, env(* env + skがk *), (fun v ->
      (* klist のトップがk それ以外 klist *)
      (match v with
       | VLam(x', exp', env') -> eval (exp', (x', VCont(k)) :: env', id)
       | VCont(k') -> k' (VCont(k)))
    ))
  | R0(exp) -> (eval (exp, env, id, k :: kl))
  | _ -> raise Error

(* eval1 : exp -> v *)
let eval1 exp = eval (exp, [], id)

let i = Lam ("x", Var "x")

let k = Lam ("x", Lam ("y", Var "x"))

let s = Lam ("x", (Lam ("y", Lam ("z", (App ((App ((Var "x"), (Var "z"))), (App ((Var "y"), (Var "z")))))))))

let skk = App (App (s,k),k)

(* let example1 = eval1 @@ App (skk, (Var "x")) (\* うまくうごかない．．． *\) *)
