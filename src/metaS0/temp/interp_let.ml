open Delimcc;;

(*
  Interpreter for shift/reset with answer type modification
 *)
module type Sym = sig
  type +'t pure
  type (+'t, 'a, 'b) eff
  type (+'s, +'t, +'a, +'b) efun
  type ('s, 't) pfun

  val const : 't -> 't pure

  val lam : ('s pure -> ('t, 'a, 'b) eff) -> ('s, 't, 'a, 'b) efun pure

  val app : (('s, 't, 'a, 'b) efun, 'b, 'c) eff -> ('s, 'c, 'd) eff -> ('t, 'a, 'd) eff
  val appP : ('s, 't) pfun pure -> 's pure -> 't pure

  val shift : (('t, 'a) pfun pure -> 'b pure) -> ('t, 'a, 'b) eff
  val reset : ('s, 's, 't) eff -> 't pure

  val exp : 't pure -> ('t, 'a, 'a) eff
  val run : 't pure -> 't
end

module R = struct
  type 't pure = unit -> 't
  type ('t, 'a, 'b) eff = 'b prompt -> 'a prompt -> 't
  type (+'s, +'t, +'a, +'b) efun = Arr : ('c pure -> ('d, 'e, 'f) eff) -> ('s, 't, 'a, 'b) efun
  type ('s, 't) pfun = 's pure -> 't pure

  let coerce _ = failwith "unreachable"

  let wrap x : 'a pure = fun () -> x
  let unwrap : 'a pure -> 'a = fun x -> x ()

  let const x = wrap x

  let lam (f: 's pure -> ('t, 'a, 'b) eff) : ('s, 't, 'a, 'b) efun pure = wrap (Arr f)

  let unarr (e: ('s, 't, 'a, 'b) efun) : ('s pure -> ('t, 'a, 'b) eff) = match e with Arr f -> Obj.magic f

  let app (e1: (('s, 't, 'a, 'b) efun, 'b, 'c) eff) (e2: ('s, 'c, 'd ) eff) : ('t, 'a, 'd) eff =
    fun p q ->
      let r, s = new_prompt (), new_prompt () in
      let v2 = wrap @@ e2 p r in
      let v1 = e1 r s in
      (unarr v1) v2 s q

  let appP (e1: ('s, 't) pfun pure) e2 : 't pure =
    fun () ->
      let v2 = unwrap e2 in
      let v1 = unwrap e1 in
      v1 (wrap v2) ()

  let shift f : ('t, 'a, 'b) eff =
    fun p q ->
      Delimcc.shift p (fun k' ->
		      unwrap @@ f @@ wrap (fun y ->
					    wrap @@ push_prompt q (fun () -> coerce (k' @@ unwrap y ))))

  let reset e =
    fun () ->
	    let p, q = new_prompt (), new_prompt () in
	    push_prompt p (fun () ->
		      abort q @@ e p q)

  let exp e =
    fun p q -> Delimcc.shift p (fun k -> push_prompt q (fun () -> k @@ unwrap e))

  let run (x: 't pure) : 't = x ()
end

module S = struct
  type 't pure = 't code
  type ('t, 'a, 'b) eff = ('b prompt) code -> ('a prompt) code -> 't code
  type ('s, 't, 'a, 'b) efun = Arr : ('c -> 'd prompt -> 'e prompt -> 'f) -> ('s, 't, 'a, 'b) efun
  type ('s, 't) pfun = ('s -> 't)

  let coerce _ = failwith "unreachable"

  let const x = .<x>.

                let lam f = .<Arr (fun x p q -> .~(f .<x>. .<p>. .<q>.))>.

                            let app e1 e2 =
                              fun p q ->
                                .<let r, s = new_prompt (), new_prompt () in
                                let v2 = .~(e2 p .<r>.) in
                                let Arr f = .~(e1 .<r>. .<s>.) in
                                let v1 = Obj.magic f in
                                v1 v2 s .~q>.

                                let appP e1 e2 =
                                  .<.~e1 .~e2>.

                                  let shift f : ('t, 'a, 'b) eff = fun p q ->
                                    .<Delimcc.shift .~p
                                      (fun k' -> (fun x -> .~(f .<x>.)) (fun y -> push_prompt .~q (fun () -> coerce @@ k' y)))>.

                                    let reset e =
                                      .<let p, q = new_prompt (), new_prompt () in
	                                    push_prompt p (fun () ->
			                                    abort q .~(e .<p>. .<q>.))>.

                                      let exp x = fun p q ->
                                        .<Delimcc.shift .~p (fun k -> push_prompt .~q (fun () -> k .~x))>.

                                        let run x = Runcode.run x
end

module T1 (S: Sym) = struct
  open S
  let res1 = run (const 10)
  let res2' = lam (fun f -> exp @@ lam (fun g -> exp @@ lam (fun x ->
			app (exp f) @@ app (exp g) (exp x))))
  let res2 = run res2'
  let res3' = reset (shift (fun k -> appP k (appP k (const 1))))
  let res3 = run res3'
  let res4 = run @@ reset @@ app (exp @@ lam @@ fun x -> exp @@ x) (exp @@ const 10)
end
let _ = let module M = T1(R) in M.res1
let _ = let module M = T1(S) in M.res1
let _ = let module M = T1(R) in M.res2
let _ = let module M = T1(S) in M.res2


module type SymLet = sig
  include Sym
  type ('t, 'a, 'b) scope
  val new_scope : (('t, 'a, 'b) scope -> ('t, 'a, 'b) eff) -> ('t, 'a, 'b) eff
  val genlet : ('t, 'a, 'b) scope -> 'a pure -> 'a pure
  val genletfun : ('u, 'c, 'd) scope -> ('s pure -> ('t, 'a, 'b) eff) -> ('s, 't, 'a, 'b) efun pure
end

module RLet = struct
  include R
  type ('t, 'a, 'b) scope =  ('t, 'a, 'b) eff prompt

  let new_scope body =
    let p = new_prompt () in
    push_prompt p (fun () -> body p)

  let genlet p e =
    shift0 p (fun k -> let t = e () in k (wrap t))

  let genletfun p e =
    shift0 p (fun k -> let f x = e x in k (wrap @@ Arr f))
end

module SLet = struct
  include SP
  type ('t, 'a, 'b) scope = ('t, 'a, 'b) eff prompt

  let new_scope body =
    let p = new_prompt () in
    push_prompt p (fun () -> body p)

  let genlet p e =
    shift0 p (fun k -> .<let t = .~e in .~(k .<t>.)>.)

  let genletfun p e =
    shift0 p (fun k -> .<let f x p q = .~(e .<x>. .<p>. .<q>.) in .~(k .<Arr f>.)>.)
end

module T2 (S: SymLet) = struct
  open S

  let id = lam @@ fun x -> exp x
  let res = run @@ reset (app (exp id) (lam @@ fun id ->
                                        ignore (app (exp id) (exp @@ const 1));
                                        app (exp id) (exp @@ const false)))

  let res1 = run @@ reset @@
    new_scope (fun p ->
        let f = genletfun p @@ fun x -> (exp x) in
        ignore (app (exp f) (exp @@ const 5));
        app (exp f) (exp @@ const true))
end
let f = let module M = T1(RLet) in RLet.unarr (M.res1)
let _ = let module M = T1(S) in M.res1

module type SymP = sig
  include SymLet

  val p2E : ('t1 -> 't2 -> 't3) -> ('t1, 'a, 'b) eff -> ('t2, 'b, 'c) eff -> ('t3, 'a, 'c) eff
  val pE: ('t -> 'u) -> ('t, 'a, 'b) eff -> ('u, 'a, 'b) eff

  val ifE : (bool, 'b, 'c) eff -> ('t, 'a, 'b) eff -> ('t, 'a, 'b) eff -> ('t, 'a, 'c) eff
  val fixE : ((('s, 't, 'a, 'b) efun) pure -> 's pure -> ('t, 'a, 'b) eff) -> (('s, 't, 'a, 'b) efun) pure
end

module RP = struct
  include RLet

  let p2E f e1 e2 = fun p q ->
    let r = new_prompt () in
    let v2 = e2 p r in
    let v1 = e1 r q in
    f v1 v2

  let pE f x = fun p q -> f (x p q)

  let ifE b e e' = fun p q ->
    let r = new_prompt () in
    if b p r then e r q else e' r q

  let rec fixE (f: ('s, 't, 'a, 'b) efun pure -> 's pure -> (('t, 'a, 'b) eff)) : ('s, 't, 'a, 'b) efun pure =
    lam (fun x -> f (fun x -> fixE f x) x)
end

module SLetE(S:SymP) = struct
  open S

  let (^^) e1 e2 = p2E (^) e1 e2

  let format = new_scope (fun p ->
      let s_int = genletfun p (fun x -> pE string_of_int (exp x)) in
      let s_bool = genletfun p (fun x -> pE string_of_bool (exp x)) in
      let fmt =
        genletfun p (fun to_str -> shift (fun k ->
			      lam (fun x -> exp @@ appP k (reset @@ app (exp to_str) (exp x))))) in
      let lit = genletfun p (fun str -> exp str) in
      (app (exp lit) (exp @@ const "Hello ")) ^^ (app (exp fmt) (exp @@ s_int)) ^^ (app (exp fmt) (exp @@ s_bool)))

  let f = reset format
  let res = run @@ reset @@ app (app (exp f) (exp @@ const true))
      (exp @@ const 10)
end
let _ = let module M = SLetE(RP) in M.res
