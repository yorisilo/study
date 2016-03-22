(* s-expression S式 *)
type sxp = I of int                    (* Integer *)
         | A of string                 (* Atoms *)
         | S of string                 (* String *)
         | L of sxp list               (* List *)

(*
read_file : string -> string
parse : string -> (sxp * string) list
print : sxp -> string
*)

let rec print s =
  match s with
  | I i -> "I " ^ (string_of_int i)
  | A s -> "A " ^ "\"" ^ s ^ "\""
  | S s -> "S " ^ "\"" ^ s ^ "\""
  | L ls -> "L [" ^ (
      let rec print_list l =
        match l with
        | s::[] -> print s
        | s::ls -> (print s) ^ "; " ^ (print_list ls)
        | [] -> ""
      in print_list ls
    ) ^ "]"

type dom = Bool of bool
         | Int of int
         | Str of string
         | Fun of int * (dom list -> dom)
         | Undefined
         | Void
         | Empty
         | Cons of dom ref * dom ref

exception Error of string

let unFun d =
  match d with
  | Fun (i, f) -> (i, f)
  | _ -> raise (Error "Encountered a non-function value")

let unBool d =
  match d with
  | Bool b -> b
  | _ -> raise (Error "Encountered a non-Bool type")

let unInt d =
  match d with
  | Int i -> i
  | _ -> raise (Error "Encountered a non-Int type")

let env0 x =
  raise (Error ("Variable not found in environment " ^ x))

type var = Val of dom
         | Ref of dom ref

(* env: string -> var *)
let ext env (x:string) (v:var) = fun y -> if x=y then v else env y

let rec lext env xl vl =
  match xl with
  | [] -> env
  | x::xs -> match vl with
             | [] -> raise (Error "Not enough arguments")
             | y::ys ->  lext (ext env x y) xs ys

let rec eval e env =
  try
    (match e with
     | A "true"  -> Bool true
     | A "false" -> Bool false
     | A "empty" -> Empty
     | A x       ->
       (match env x with
        | Val v -> v
        | Ref r -> !r)
     | I i -> Int i
     | S s -> Str s
     | L [A "not"; e1]   -> Bool (not (unBool (eval e1 env)))
     | L [A "+"; e1; e2] -> Int (  (unInt (eval e1 env)
                                    + (unInt (eval e2 env))))
     | L [A "cons"; e1; e2] ->
       Cons (ref (eval e1 env), ref (eval e2 env))
     | L [A "set-car!"; e1; e2] ->
       (match (eval e1 env) with
        | Cons (h,t) -> (h:=(eval e2 env);Void)
        | _ -> raise (Error ("Can’t assign car of " ^(print e1))))
     | L ((A "=") :: e1 :: l) ->
       Bool (let v = unInt (eval e1 env) in
             let l = List.map (fun x -> unInt (eval x env)) l
             in List.for_all (fun y -> y=v) l)
     | L [A "if"; c2; e2; e3] ->
       eval (L [A "cond"; L [c2 ; e2]; L [A "else"; e3]]) env
     | L [A "lambda" ; L [S x] ; e] ->
       Fun (1, fun l -> match l with
           | [v] -> eval e (ext env x (Val v)))
     | L [A "lambda" ; L axs ; e] ->
       let l = List.length axs
       in Fun (l, fun v ->
           eval e (lext env
                     (List.map (function A x -> x) axs)
                     (List.map (fun x -> Val x) v)))
     | L [e1; e2] -> let (1,f) = unFun (eval e1 env) in
       let arg = eval e2 env
       in f [arg]
     | L (e::es) ->
       let (i,f) = unFun (eval e env) in
       let args = List.map (fun e -> eval e env) es in
       let l = List.length args
       in if l=i
       then f args
       else raise (Error ("Function has "^(string_of_int l)^
                          " arguments but called with "^(string_of_int i)))
    )
  with
    Error s -> (print_string ("\n" ^ (print e) ^ "\n");
                raise (Error s))

let rec peval p env =
  match p with
    | [e1] -> eval e1 env
    | (L [A "define"; A x; e1])::p ->
      let r = ref Undefined in
      let env' = ext env x (Ref r) in
      let v = eval e1 env' in
      let _ = (r := v)
      in peval p env'
    | (L [A "define"; L ((A x)::xs); e1])::p ->
      peval (L [A "define"; A x;
                L [A "lambda" ; L xs ; e1]]::p) env
    | _ -> raise (Error "Program form not recognized")


(* let rec fib n = if n < 2 then n else fib (n-1) + fib (n-2) *)

let rec fib_cps n k =
  if n < 2 then k n
  else fib_cps (n-1) (fun r1 ->
       fib_cps (n-2) (fun r2 -> k (r1 + r2)))

let k0 = fun r -> r
let fib n = fib_cps n k0


(* let lefty left right = *)
(*   left in .< 1 + .~(lefty .<2+3>. .<4+5>.). >. *)
