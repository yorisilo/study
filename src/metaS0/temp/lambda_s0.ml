(* without subtyping ver *)

(* value *)
type v = Vlam of string * term
       | VVar of string
       | VInt of int
and
  (* term *)
  term = Var of v
       | App of term * term
       | Reset of term
       | Shift of term
and
  (* context *)
  k = Dot
    | Ke of k * term
    | Kv of v * k
and
  (* trail *)
  tr = Hole
     | KT of k * tr

type tyvar = string

type ty = TAlpha                (* 型 *)
        | TAArrow of anot * ty * ty
        | TVar of tyvar
and
  (* anotation *)
  anot = AIps
       | Atype_ of ty * anot * ty * anot
       | AVar of string

type tyenv = (string * ty) list (* 型環境 *)
type tysubst = (tyvar * ty) list (* 型代入 *)

let ext env x v = (x,v) :: env

let rec lookup x env =
  match env with
  | [] -> failwith ("unbound variable: " ^ x)
  | (y,v)::tl -> if x=y then v else lookup x tl

(* new_typevar : string -> ty *)
let new_typevar s = TVar("'" ^ s)

(* type infer *)
(* tyinf : typenv -> term -> typenv * type_ *)
let rec typeinf typenv term =
  match term with
  | Var(VVar s) ->
    (try
       let t1 = lookup s typenv in
       (typenv, t1)
     with Failure(_) ->          (* 変数s が型環境 typenv に含まれなかった時 *)
       let tvar = new_typevar s in
       let te1 = ext typenv s tvar in
       (te1, tvar)
    )
  | _ -> failwith "unknown term"
;;


(* (\* type checker *\) *)
(* (\* vtycheck : typenv -> v -> typ *\) *)
(* let rec vtycheck typenv v = *)
(*   match v with *)
(*   | VVar s -> lookup s typenv *)
(*   | VInt(_) -> TInt *)
(*   | Vlam(x, term) -> *)
(*     let t1 = lookup x typenv in *)
(*     let t2 = tycheck typenv term in *)
(*     TArrow(t1,t2) *)
(* (\* | _ -> failwith "unknown value" *\) *)
(* and *)
(*   (\* tycheck : typenv -> term -> typ *\) *)
(*   tycheck typenv term = *)
(*   match term with *)
(*   | Var v -> vtycheck typenv v *)
(*   | Plus(t1,t2) -> *)
(*     begin *)
(*       match (tycheck typenv t1, tycheck typenv t2) with *)
(*       | (TInt, TInt) -> TInt *)
(*       | _ -> failwith "type error in Plus" *)
(*     end *)
(*   | App(t1, t2) -> *)
(*     let t1 = tycheck typenv t1 in *)
(*     let t2 = tycheck typenv t2 in *)
(*     begin *)
(*       match t1 with *)
(*       | TArrow(t10, t11) -> if t10 = t2 then t11 else failwith "type error in App" *)
(*       | _ -> failwith "type error in App" *)
(*     end *)
(*   | _ -> failwith "unknown term" *)
