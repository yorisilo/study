(* without subtyping ver *)

(* value *)
type v = Vlam of string * term
       | VVar of string
       | VInt of int
       | VBool of bool
and
  (* term *)
  term = Var of v
       | App of term * term
       | Plus of term * term
       | Reset of term
       | Shift of term
and
  (* context *)
  k = Dot
    | Ke of k * term
    | Kv of v * k

and
  (* trail *)
  tr = Holl
     | KT of k * tr

type typ = TInt
         | TBool
         | TArrow of typ * typ

type typenv = (string * typ) list

let rec lookup x env =
  match env with
  | [] -> failwith ("unbound variable: " ^ x)
  | (y,v)::tl -> if x=y then v else lookup x tl


(* type checker *)
(* vtycheck : tyenv -> v -> typ *)
let rec vtycheck typenv v =
  match v with
  | VVar s -> lookup s typenv
  | VInt(_) -> TInt
  | VBool(_)-> TBool
  | Vlam(x, term) ->
    let t1 = lookup x typenv in
    let t2 = tycheck typenv term in
    TArrow(t1,t2)
(* | _ -> failwith "unknown value" *)
and
  (* tycheck : typenv -> term -> typ *)
  tycheck typenv term =
  match term with
  | Var v -> vtycheck typenv v
  | Plus(t1,t2) ->
    begin
      match (tycheck typenv t1, tycheck typenv t2) with
      | (TInt, TInt) -> TInt
      | _ -> failwith "type error in Plus"
    end
  | App(t1, t2) ->
    let t1 = tycheck typenv t1 in
    let t2 = tycheck typenv t2 in
    begin
      match t1 with
      | TArrow(t10, t11) -> if t10 = t2 then t11 else failwith "type error in App"
      | _ -> failwith "type error in App"
    end
  | _ -> failwith "unknown term"
