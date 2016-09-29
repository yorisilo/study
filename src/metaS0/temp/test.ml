type exp =
  | IntLit of int
  | BoolLit of bool
  | Plus of exp * exp
  | Times of exp * exp
  | Var of string
  | Fun of string * exp
  | App of exp * exp

type value =
  | IntVal of int
  | BoolVal of bool
  | FunVal  of string * exp * ((string * value) list)

let rec eval1 e =
  match e with
  | IntLit(n)    -> n
  | Plus(e1,e2)  -> (eval1 e1) + (eval1 e2)
  | Times(e1,e2) -> (eval1 e1) * (eval1 e2)
  | _ -> failwith "unknown expression"

let emptyenv () = []

let ext env x v = (x,v) :: env

let rec lookup x env =
  match env with
  | [] -> failwith ("unbound variable: " ^ x)
  | (y,v)::tl -> if x=y then v else lookup x tl


(* eval2 : exp -> value *)
let rec eval2 e =
  match e with
  | IntLit(n)  -> IntVal(n)
  | Plus(e1,e2) ->
    begin
      match (eval2 e1, eval2 e2) with
	    | (IntVal(n1),IntVal(n2)) -> IntVal(n1+n2)
      | _ -> failwith "integer values expected"
    end
  | Times(e1,e2) ->
    begin
      match (eval2 e1, eval2 e2) with
	    | (IntVal(n1),IntVal(n2)) -> IntVal(n1*n2)
      | _ -> failwith "integer values expected"
    end
  | _ -> failwith "unknown expression e"


(* eval2a : exp -> value *)
(* binop : int -> exp -> exp -> value *)
let rec eval2a e =
  match e with
  | IntLit(n)    -> IntVal(n)
  | Plus(e1,e2)  -> binop 1 e1 e2
  | Times(e1,e2) -> binop 2 e1 e2
  | _ -> failwith "unknown expression"
and binop flag e1 e2 =
  match (eval2a e1, eval2a e2) with
  | (IntVal(n1),IntVal(n2)) ->
    if flag = 1 then IntVal(n1 + n2)
    else IntVal(n1 * n2)
  | _ -> failwith "integer values expected"


(* eval2b : exp -> value *)
let rec eval2b e =
  let binop f e1 e2 =
    match (eval2b e1, eval2b e2) with
    | (IntVal(n1),IntVal(n2)) -> IntVal(f n1 n2)
    | _ -> failwith "integer values expected"
  in
  match e with
  | IntLit(n)    -> IntVal(n)
  | Plus(e1,e2)  -> binop (+) e1 e2
  | Times(e1,e2) -> binop ( * ) e1 e2
  | _ -> failwith "unknown expression"


let test1 = eval2 (Plus (IntLit 1, Plus (IntLit 2, IntLit 11)))
let test2 = eval2 (Times (IntLit 1, Plus (IntLit 2, IntLit 11)))

let rec eval3 e env =           (* env を引数に追加 *)
  let binop f e1 e2 env =       (* binop の中でも eval3 を呼ぶので env を追加 *)
    match (eval3 e1 env, eval3 e2 env) with
    | (IntVal(n1),IntVal(n2)) -> IntVal(f n1 n2)
    | _ -> failwith "integer value expected"
  in
  match e with
  | Var(x)       -> lookup x env
  | IntLit(n)    -> IntVal(n)
  | Plus(e1,e2)  -> binop (+) e1 e2 env     (* env を追加 *)
  | Times(e1,e2) -> binop ( * ) e1 e2 env   (* env を追加 *)
  | _ -> failwith "unknown expression"


(* eval4 : env -> (string * value) list -> value *)
(* ラムダ式の導入 *)
let rec eval4 e env =           (* env を引数に追加 *)
  let binop f e1 e2 env =       (* binop の中でも eval3 を呼ぶので env を追加 *)
    match (eval4 e1 env, eval4 e2 env) with
    | (IntVal(n1),IntVal(n2)) -> IntVal(f n1 n2)
    | _ -> failwith "integer value expected"
  in
  match e with
  | Var(x)       -> lookup x env
  | IntLit(n)    -> IntVal(n)
  | Plus(e1,e2)  -> binop (+) e1 e2 env     (* env を追加 *)
  | Times(e1,e2) -> binop ( * ) e1 e2 env   (* env を追加 *)
  | Fun(x,e1) -> FunVal(x, e1, env)
  | App(e1,e2) ->
    begin
      match (eval4 e1 env) with
      | FunVal(x,body,env1) ->
        let arg = (eval4 e2 env)
	      in eval4 body (ext env1 x arg)
      | _ -> failwith "function value expected"
    end
  | _ -> failwith "unknown expression"


(* eval7 : exp -> env -> (value -> 'a) -> 'a *)
(* 継続渡し形式のインタープリタは value を返すのではなく、(value->'a) と
 * いう継続をもらって、'a型の要素を返す。ここで'aは、どんな型でもよい
*)

let rec eval7 e env cont =
  let binop f e1 e2 env cont=       (* binop の中でも eval7 を呼ぶので cont を追加 *)
    match (eval7 e1 env cont, eval7 e2 env cont) with
    | (IntVal(n1),IntVal(n2)) -> IntVal(f n1 n2)
    | _ -> failwith "integer value expected"
  in
  match e with
  | Var(x)       -> cont (lookup x env)
  | IntLit(n)    -> cont (IntVal n)
  | BoolLit(b)   -> cont (BoolVal b)
  | Plus(e1,e2)  -> binop (+) e1 e2 env cont
  | Times(e1,e2) -> binop ( * ) e1 e2 env cont
  | Fun(x,e1) -> cont (FunVal(x, e1, env))
  | App(e1,e2) ->
    eval7 e1 env (fun funpart ->
        eval7 e2 env (fun arg ->
            app funpart arg cont))
and  (* App(e1,e2)のケースは長いので、以下の関数として独立させた *)
  app funpart arg cont =
  match funpart with
	| FunVal(x,body,env1) -> eval7 body (ext env1 x arg) cont
  | _ -> failwith "hoge"

let ee = emptyenv ()
let id = fun a -> a
let eval7top e = eval7 e ee id

type t =
  | IntLit of int
  | BoolLit of bool
  | Plus of t * t
  | Times of t * t
  | Var of string
  | Fun of string * t
  | App of t * t
  | Shift of t
  | Reset of t

type v =
  | IntVal of int
  | BoolVal of bool
  | FunVal  of string * t * ((string * v) list)
  | VAbs of ((v * c) -> v)
  | VCont of c

and c = v -> v

let emptyenv () = []

let ext env x v = (x,v) :: env

let rec lookup x env =
  match env with
  | [] -> failwith ("unbound variable: " ^ x)
  | (y,v)::tl -> if x=y then v else lookup x tl

let ee = emptyenv ()
let id = fun a -> a

let rec eval t env cont =
  let binop f t1 t2 env cont =
    match (eval t1 env cont, eval t2 env cont) with
    | (IntVal(n1), IntVal(n2)) -> IntVal(f n1 n2)
    | _ -> failwith "integer value expected"
  in
  match t with
  | Var(x)       -> cont (lookup x env)
  | IntLit(n)    -> cont (IntVal n)
  | BoolLit(b)   -> cont (BoolVal b)
  | Plus(e1,e2)  -> binop (+) e1 e2 env cont
  | Times(e1,e2) -> binop ( * ) e1 e2 env cont
  | Fun(x,e1) -> cont (FunVal(x, e1, env))
  | App(e1,e2) ->
    eval e1 env (fun funpart ->
        eval e2 env (fun arg ->
            app funpart arg cont))
  | Shift(t) ->
  | Reset(t) -> cont (eval (t, env, id))
and
  app funpart arg cont =
  match funpart with
	| FunVal(x,body,env1) -> eval body (ext env1 x arg) cont
  | _ -> failwith "hoge"

let evaltop e = eval e ee id
