open Syntax

let extend (x,v) env = (x,v) :: env

let rec get x env = match env with
  | [] -> failwith ("unbound variable: " ^ x)
  | (x',v)::xvs -> if x = x' then v else get x xvs

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
