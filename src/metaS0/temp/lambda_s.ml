(* s0/r0 + code 素朴に実験で作ったような評価器のようにデータタイプでやっていく *)

let id = fun x -> x

let add_cps x y k = k @@ x + y
let mul_cps x y k = k @@ x * y
let sub_cps x y k = k @@ x - y

let square n = n * n

(* square_cps n id ~> *)
let square_cps n c = match n with
  | 0 -> c
  | n -> c + n * n

let rec fact n = match n with
  | 0 -> 1
  | n -> n * fact(n-1)

(* fact_cps n 0 ~> *)
let rec fact_cps n k = match n with
  | 0 -> k 1
  | n -> fact_cps (n-1) (fun x -> k (n * x))

(* shift/reset の CPS インタプリタ *)
type t = Var of string
       | Abs of string * t
       | App of t * t
       | Shift of t
       | Reset of t

type v = VAbs of string * t * e
       | VCont of c

and e = (string * v) list

and c = (v -> v);;

let i = Abs ("x", Var "x")

let k = Abs ("x", Abs ("y", Var "x"))

let s = Abs ("x", (Abs ("y", Abs ("z", (App ((App ((Var "x"), (Var "z"))), (App ((Var "y"), (Var "z")))))))))

let skk = App (App (s,k),k)

exception Not_include_x_in_xs

(* get : string * string * v list -> v *)
let rec get (x, e) = match e with
  | [] -> raise Not_include_x_in_xs
  | (x',v)::xvs -> if x = x' then v else get (x, xvs)

(* let id = fun a -> a *)
let id a = a

(* eval : t * string list * v list * c -> v *)
(* eval : t * e * c -> v *)
let rec eval (t, e, c) = match t with
  | Var(x) -> c (get(x, e))
  | Abs(x, t) -> c (VAbs(x, t, e))
  | App(t0, t1) -> eval (t1, e, (fun v1 ->
      eval (t0, e, (fun v0 ->
          (match v0 with
           | VAbs(x', t', e') -> eval (t', (x', v1) :: e', c)
           | VCont(c') -> c (c' v1))))))
  | Shift(t) -> eval (t, e, (fun v ->
      (match v with
       | VAbs(x', t', e') -> eval (t', (x', VCont(c)) :: e', id)
       | VCont(c') -> c' (VCont(c)))
    ))
  | Reset(t) -> c (eval (t, e, id))

(* eval1 : t -> v *)
let eval1 t = eval (t, [], id)
(* let example1 = eval1 @@ App (skk, (Var "x")) *)
