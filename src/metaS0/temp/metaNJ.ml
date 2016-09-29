(* Implementation of <NJ> *)

(* The core calculus is entirely the standard lambda-calculus with
   reference cells.
   Therefore, we use the standard OCaml for it
*)

let rec fix f = fun n -> f (fix f) n

(* Code-generating functions and forms *)

module type Code = sig
  type (+'a,+'g) cod

  val cint   : int  -> (int,'g) cod
  val cbool  : bool -> (bool,'g) cod

  val ( +% ) : (int,'g) cod -> (int,'g) cod -> (int,'g) cod
  val ( -% ) : (int,'g) cod -> (int,'g) cod -> (int,'g) cod
  val ( *% ) : (int,'g) cod -> (int,'g) cod -> (int,'g) cod
  val ( /% ) : (int,'g) cod -> (int,'g) cod -> (int,'g) cod
  val ( =% ) : (int,'g) cod -> (int,'g) cod -> (bool,'g) cod
  val ( >% ) : (int,'g) cod -> (int,'g) cod -> (bool,'g) cod

  type ('g1,'g2) ge                     (* g1 >= g2 constraint *)
  val (&) : ('g1,'g2) ge -> ('g2,'g3) ge -> ('g1,'g3) ge  (* composition *)
  val grefl : ('g,'g) ge
  (* coercion *)
  val (lsr) : ('a,'g2) cod -> ('g1,'g2) ge -> ('a,'g1) cod

  type ('c,'g) body =
    {body: 'g1. ('a,'g1) cod -> ('g1,'g) ge -> ('b,'g1) cod}
    constraint 'c = 'a -> 'b

  val lamC   : ('a->'b,'g) body  -> ('a->'b,'g) cod
  (* building applications: normal and inverse *)
  val ($%)   : ('a -> 'b,'g) cod -> ('a,'g) cod  -> ('b,'g) cod (* left-assoc *)
  val (%$)   : ('a,'g) cod -> ('a -> 'b,'g) body -> ('b,'g) cod (* let-like *)

  (* Reference cells: creading, reading, writing *)
  val cref   : ('t,'g) cod -> ('t ref,'g) cod
  val dref   : ('t ref,'g) cod -> ('t,'g) cod
  val cset   : ('t ref,'g) cod -> ('t,'g) cod -> ('t,'g) cod
end

(* One implementation of the signature: pretty-printer *)

module P = struct
  open Format
  (* precedences:
   * http://caml.inria.fr/pub/docs/manual-ocaml/expr.html
   *  high         low
   *  12 <-------> 0
  *)
  type precedence = int
  (* classifier is not used for anything: for type-checking only *)
  type ('a,'g) cod = precedence -> formatter -> unit

  (* observation *)
  type gamma0                           (* local type *)
  let vcount = ref 0
  let gensym () = let x = !vcount in incr vcount; x

  (* Only code with gamma0 classifier can be observed *)
  let observe (x : ('a,gamma0) cod) =
    vcount := 0; x 0 str_formatter; flush_str_formatter ()

  (* Classifiers are really phantom *)
  type ('g1,'g2) ge = ()
  let (&)   : ('g1,'g2) ge -> ('g2,'g3) ge -> ('g1,'g3) ge = fun _ _ -> ()
  let grefl = ()
  let (lsr) : ('a,'g2) cod -> ('g1,'g2) ge -> ('a,'g1) cod = fun x _ -> x

  (* auxiliary functions for printing *)
  let varnames = "xyzuvw"
  let varname : int -> string = function
    | i when i < String.length varnames ->
      String.make 1 @@ varnames.[i]
    | i -> "x" ^ string_of_int i
  let paren (ppf:formatter) : bool -> (formatter -> unit) -> unit = function
    | true -> fun x -> fprintf ppf "(%t)" x
    | _    -> fun x -> x ppf
  let print_infix pth pl pr op = fun e1 e2 ->
    fun (p:precedence) (ppf:formatter) ->
      paren ppf (p > pth) @@
      fun ppf -> fprintf ppf "@[<2>%t@;%s@;%t@]" (e1 pl) op (e2 pr)
  (* application to some standard function *)
  let print_app_std op x = fun (p:precedence) (ppf:formatter) ->
    paren ppf (p > 10) @@
    fun ppf -> fprintf ppf "@[<2>%s@;%t@]" op (x 11)

  (* constant constructors *)
  let cint    n = fun p ppf -> fprintf ppf "%d" n
  let cbool   b = fun p ppf -> fprintf ppf "%b" b

  (* operators *)
  let ( +% )  = print_infix 6 7 7 "+"
  let ( -% )  = print_infix 6 7 7 "-"
  let ( *% )  = print_infix 7 8 8 "*"
  let ( /% )  = print_infix 7 8 8 "/"

  let ( >% )  = print_infix 3 4 4 ">"
  let ( <% )  = print_infix 3 4 4 "<"
  let ( =% )  = print_infix 3 4 4 "="


  let if_ e e1 e2 = fun p ppf ->
    paren ppf (p > 0) @@
    fun ppf -> fprintf ppf "@[<2>if@;%t@;then@;%t@;else@;%t@]"
      (e p) (e1 p) (e2 p)

  type ('c,'g) body =
    {body: 'g1. ('a,'g1) cod -> ('g1,'g) ge -> ('b,'g1) cod}
    constraint 'c = 'a -> 'b

  (* lambda abstraction and applications *)
  let lamC b =
    (* first, eval the body and obtain the code *)
    let vn  = varname (gensym ()) in
    let bv  = b.body (fun _ ppf -> fprintf ppf "%s" vn) () in
    (* and only then print it *)
    fun p ppf ->
      paren ppf (p > 0) @@
      fun ppf ->
      fprintf ppf "@[<2>fun@;%s@;->@;%t@]" vn (bv 0)


  let ($%)  = print_infix 10 10 11 ""
  let (%$)  = fun x f -> lamC f $% x

  let cref x = fun p ppf ->
    paren ppf (p > 10) @@
    fun ppf -> fprintf ppf "@[<2>ref@;%t@]" (x 11)

  let dref x = fun p ppf ->
    paren ppf (p > 10) @@
    fun ppf -> fprintf ppf "@[<2>!@;%t@]" (x 0)

  let cset  = print_infix 1 2 2 ":="
end

(* Examples from the paper *)

module Ex1(S:Code) = struct
  open S
  let ex1 = cint 1
  let ex2 = cint 1 +% cint 2
  let ex3 = lamC {body = fun x _ -> x +% cint 3}

  let power =
    let body = fun f n x -> if n = 0 then cint 1 else x *% f (n - 1) x in
    fun n -> lamC {body = fun x _ -> fix body n x}

  (* With several variables in scope, we need casts *)
  let fn2 = lamC {body = fun x _ ->
      lamC {body = fun y yx ->
          y *% (x lsr yx) +% cint 1}}

  let fn3 = lamC {body = fun x _ ->
      lamC {body = fun y yx ->
          lamC {body = fun z zy ->
              (y lsr zy) *% (x lsr (zy & yx)) +% z}}}


  (* let x = e in e1 in the object language is encoded as
     e |> (fun x -> e1)
  *)
  let refgen =
    cref (cint 2 +% cint 3) %$ {body = fun r _ ->
        cset r (cint 0) %$ {body = fun z ge ->
            dref (r lsr ge)}}
end

let module M = Ex1(P) in
[P.observe M.ex1 P.observe M.ex2;
 P.observe M.ex3;
 P.observe (M.power 3);
 P.observe M.fn2;
 P.observe M.fn3;
 P.observe M.refgen;
]

(* Scope extrusion *)

(* simple extrusion *)
(* It does not type-check! *)

module SE1(S:Code) = struct
  open S
  let res0 =
    let r = ref (cint 0) in
    let _ = lamC {body = fun x _ -> r := cint 1; x} in
    !r
  let res =
    let r = ref (cint 0) in
    let _ = lamC {body = fun x _ -> r := x; x} in
    !r
end

(* Hiding the dangling reference within a function *)

module SE2(S:Code) = struct
  open S
  let res =
    let r = ref (fun () -> ()) in
    let _ = lamC {body = fun x _ -> r := (fun _ -> ignore x); x} in
    !r
end

(* Storing open code in a reference cell and using it correctly.
   This is the artificial example for illustration. For the realistic
   example, see power with reference cells below, or assert insertion.
   This is the example from teh StagedHaskell paper, Sec 2.3.
*)
module SE3(S:Code) = struct
  open S
  let res =
    lamC {body = fun x _ ->
        let r = ref x in
        lamC {body = fun y yx ->
            (!r lsr yx) +% y}}
end

let "fun x -> fun y -> x + y" =
  let module M = SE3(P) in P.observe M.res


(* Attempt to leak: does not type check; see StagedHaskell, Sec 2.3
   Compare with the Haskell error message there.
*)
module SE4(S:Code) = struct
  open S
  let res =
    lamC {body = fun x _ ->
        let r = ref x in
        lamC {body = fun y yx ->
            (let z = !r in r := y; z lsr yx) +% y}}
end
(*
Characters 120-177:
  ...................fun y yx ->
          (let z = !r in r := y; z lsr yx) +% y..
Error: This field value has type
         (int, 'c) S.cod -> ('c, 'c) S.ge -> (int, 'c) S.cod
       which is less general than
         'g1. ('a, 'g1) S.cod -> ('g1, 'g) S.ge -> ('b, 'g1) S.cod
*)

(* Abstracting code *)
module EF1(S:Code) = struct
  open S
    (*
      ef = \z -> <\x -> ~z + x>
      ef1 = ef <1>
      ef2 = <\x y -> ~(ef <x *  y>)>
     *)
  let ef  = fun z -> lamC {body = fun x xz -> (z lsr xz) +% x}
  let ef1 = ef (cint 1)
  let ef2 = lamC {body = fun x _ ->
      lamC {body = fun y yx ->
          ef ((x lsr yx) *% y)}}
end

module ETA(S:Code) = struct
  open S
  (* This one obviously does not type-check
     let eta = fun f -> lamC {body = fun x _ -> f x}
  *)
  (* Needs polymporphism in gamma in the type of f *)
  let eta = lamC
end


(* Power with the reference cells *)

let powerref = fun n x ->
  let r = ref 1 in
  fix (fun f n ->
      if n = 0 then () else
        let _ = r := !r * x in f (n-1)) n;
  !r
;;

let _ = powerref 8 2;;

(* The example indeed stores open code, in r *)

module PREF(S:Code) = struct
  open S
  let pref =
    let body = fun n x ->
      let r = ref (cint 1) in
      fix (fun f n ->
          if n = 0 then () else
            let _ = r := !r *% x in f (n-1)) n;
      !r
    in fun n -> lamC {body = fun x _ -> body n x}
  let p5 = pref 5
end

let module M = PREF(P) in
[P.observe M.p5]

(* Environment polymorphism *)
module POLY(S:Code) = struct
  open S
  let ex1 = fun x ->
    let f  = lamC {body = fun z _  -> cint x +% cint 1 +% z}    in
    let f' = lamC {body = fun z' _ -> (cint x +% cint 1) *% z'} in
    (f $% cint 10) +% (f' $% cint 100)
  let ex2 = fun x ->
    let u  = cint x +% cint 1 in
    let f  = lamC {body = fun z  z0  -> (u lsr z0) +% z}  in
    let f' = lamC {body = fun z' z0 ->  (u lsr z0) *% z'} in
    (f $% cint 10) +% (f' $% cint 100)
  let ex3 = fun x ->
    let u  = fun z -> cint x +% z in
    let f  = lamC {body = fun z  z0  -> (u z)  +% z}  in
    let f' = lamC {body = fun z' z0 ->  (u z') *% z'} in
    (f $% cint 10) +% (f' $% cint 100)
end

let module M = POLY(P) in
[P.observe (M.ex1 5);
 P.observe (M.ex2 5);
 P.observe (M.ex3 5);
]



(* Gibonacci with memoization *)
(* Gibonacci relies on let-insertion; we need either delimited
   control or CPS. And we if get either, we don't actually need
   mutation
*)

(* Gibonacci *)
(* It generates arbitrarily many binders *)


(* First, the regular one *)
let rec gib x y = function
  | 0 -> x
  | 1 -> y
  | n -> gib y (x+y) (n-1)

let 8 = gib 1 1 5

let 1346269 = gib 1 1 30



module GIB(S:Code) = struct
  open S
  (* First, specialize naively *)
  let gib_naive =
    let rec body x y = function
      | 0 -> x
      | 1 -> y
      | n -> body y (x +% y) (n-1)
    in fun n ->
      lamC {body = fun x ox -> lamC {body = fun y yx ->
          body (x lsr yx) y n}}
  let gn5 = gib_naive 5
  (* Code with let-insertion, with lots of new variables *)
  (* Therefore, the code requires polymorphic recursion *)
  let gib =
    let rec body : 'g. (int,'g) cod -> (int,'g) cod -> int -> (int,'g) cod =
      fun x y -> function
        | 0 -> x
        | 1 -> y
        | n -> (x +% y) %$ {body = fun z oz -> body (y lsr oz) z (n-1)}
    in fun n ->
      lamC {body = fun x ox -> lamC {body = fun y yx ->
          body (x lsr yx) y n}}
  let g5 = gib 5
end

let module M = GIB(P) in
[P.observe M.gn5;
 P.observe M.g5]

(* The naive code has a lot of duplicates
   - : string list =
   [("fun x -> fun y -> (y + (x + y)) + ((x + y) + (y + (x + y)))";
   "fun x -> fun y ->
     (fun z ->
          (fun u -> (fun v -> (fun w -> w)  (u + v)) (z + u)) (y + z))
     (x + y)")]

*)



(* Assert-insertion: see TaglessStaged paper, Sec 3.2 *)

(* We extend our language with AssertPos *)
module type CodeAs = sig
  include Code

  (* [assert_pos x m] generates code for [assert (x>0); m] *)
  val assert_pos : (int,'g) cod -> ('a,'g) cod -> ('a,'g) cod
end


module PAs = struct
  include P
  open Format

  let assert_pos x m = fun p ppf ->
    paren ppf (p > 1) @@
    fun ppf -> fprintf ppf "@[<2>assert (%t>0);@;%t@]" (x 3) (m 10)
end

(* Naive version of guarded division *)
module GD1(S:CodeAs) = struct
  open S

  let guarded_div x y = assert_pos y (x /% y)
  (* placeholder for some really complex and long compuation *)
  let complex_exp = cint 100 *% cint 100

  let res = lamC {body = fun y _ -> complex_exp +% guarded_div (cint 10) y}
end

(* We check the divisor right before doing division *)
let "fun x -> 100 * 100 + (assert (x>0); (10 / x))" =
  let module M = GD1(PAs) in P.observe M.res


(* Second version *)
module GD2(S:CodeAs) = struct
  open S

  let assert_locus : (((('a,'g) cod as 'x) -> 'x) ref -> 'x) -> 'x = fun f ->
    let r = ref (fun x -> x) in
    let c = f r in
    let transformer = !r in
    transformer c

  (* Composing the transformers *)
  let add_assert locus transformer =
    locus := let oldtr = !locus in fun x -> oldtr (transformer x)

  let guarded_div locus x y =
    add_assert locus (fun z -> assert_pos y z); (x /% y)

  let complex_exp = cint 100 *% cint 100

  let res = lamC {body = fun y _ ->
      assert_locus @@ fun locus ->
      complex_exp +% guarded_div locus (cint 10) y}

end

let "fun x -> assert (x>0); (100 * 100 + 10 / x)" =
  let module M = GD2(PAs) in P.observe M.res


(* Final version *)
module GuardedDiv(S:CodeAs) = struct
  open S

  let assert_locus : (((('a,'g) cod as 'x) -> 'x) ref -> 'x) -> 'x = fun f ->
    let r = ref (fun x -> x) in
    let c = f r in
    let transformer = !r in
    transformer c

  (* Composing the transformers *)
  let add_assert locus transformer =
    locus := let oldtr = !locus in fun x -> oldtr (transformer x)

  (* Now we allow x and g to have different number of free variables
     (different classifiers).
     The divisor must have a parent classifier
  *)
  let guarded_div locus gexy x y =
    add_assert locus (fun z -> assert_pos y z); (x /% (y lsr gexy))
end

module GD3(S:CodeAs) = struct
  open S
  module M = GuardedDiv(S)
  open M

  let complex_exp = cint 100 *% cint 101

  let res = lamC {body = fun y _ ->
      assert_locus @@ fun locus ->
      lamC {body = fun z zy ->
          complex_exp +% guarded_div locus zy z y}}
end

let "fun x -> assert (x>0); (fun y -> 100 * 101 + y / x)" =
  let module M = GD3(PAs) in P.observe M.res

(* If we by mistake switch y and z, we get an error
   (not very informative though)
*)
module GD4(S:CodeAs) = struct
  open S
  module M = GuardedDiv(S)
  open M

  let complex_exp = cint 100 *% cint 101

  let res = lamC {body = fun y _ ->
      assert_locus @@ fun locus ->
      lamC {body = fun z zy ->
          complex_exp +% guarded_div locus zy y z}}
end

;;



;;
