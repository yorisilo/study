(* type c = I of int *)
(*        | B of bool *)
(*        | CInt of int code *)


(* type v = V of string *)
(*        | Fun of string * e0 *)


(* type e0 = *)

(* type e1 *)

let rec fix f = f (fix f)
(* let rec fix f = fun n -> f (fix f) n *)

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
  val (&)   : ('g1,'g2) ge -> ('g2,'g3) ge -> ('g1,'g3) ge  (* composition *)
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

let test1 =
  let module M = Ex1(P) in
  [P.observe M.ex1;
   P.observe M.ex2;
   P.observe M.ex3;
   (* P.observe (M.power 3); *)
   (* P.observe M.fn2; *)
   (* P.observe M.fn3; *)
   (* P.observe M.refgen *)
  ]
