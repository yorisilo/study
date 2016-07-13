(* 4 *)

(* type 'a sdom = *)
(*     | SBool of ('a, bool) code *)
(*     | SInt of ('a, int) code *)
(*     | SStr of ('a, string) code *)
(*     | SFun of int * ('a sdom list -> 'a sdom) *)
(*     | SUndefined *)
(*     | SVoid *)
(*     | SEmpty *)
(*     | SCons of ('a, dom ref) code * ('a, dom ref) code *)
(*     | SAny of ('a, dom) code *)

type dom =
  | Bool of bool
  | Int of int | Str of string
  | Fun of int * (dom list -> dom)
  | Undefined
  | Void
  | Empty | Cons of dom ref * dom ref

type sdom =
  | SBool of bool code
  | SInt of int code
  | SStr of string code
  | SFun of int * (sdom list -> sdom)
  | SUndefined
  | SVoid
  | SEmpty
  | SCons of (dom ref) code * (dom ref) code
  | SAny of dom code

let unFun d =
  match d with
    | Fun (i,f) -> (i,f)
    | _ -> raise (Error "Encountered a non-funcion value")

let unInt d =
  match d with
    | Int i -> i
    | _ -> raise (Error "Encountered a non-integer value")

let unBool d =
  match d with
    | Bool b -> b
    | _ -> raise (Error "Encountered a non-boolean value")

let rec lift x =
match x with
 | SBool b     -> .<Bool .~b>.
 | SInt  i     -> .<Int  .~i>.
 | SStr  s     -> .<Str  .~s>.
 | SFun (n,f)  -> .<Fun (n,fun v ->
                    .~(keta_list n .<v>. (fun args ->
                    (lift (f (List.map (fun x -> SAny x) args))))))>.
 | SUndefined  -> .<Undefined>.
 | SVoid       -> .<Void>.
 | SEmpty      -> .<Empty>.
 | SCons (h,t) -> .<Cons (.~h, .~t)>.
 | SAny c      -> c

(* New additions to support SAny uniformly *)

let matchBool r k =
   let m = "Expecting boolean value" in
   match r with
   | SBool b -> k b
   | SAny c -> .<match .~c with Bool b -> .~(k .<b>.) | _ -> raise (Error m)>.
   | _ -> k .<raise (Error m)>.

let matchInt r k =
   let m = "Expecting integer value" in
   match r with
   | SInt i -> k i
   | SAny c -> .<match .~c with Int i -> .~(k .<i>.) | _ -> raise (Error m)>.
   | _ -> k .<raise (Error m)>.

let matchStr r k =
   let m = "Expecting string value" in
   match r with
   | SStr s -> k s
   | SAny c -> .<match .~c with Str i -> .~(k .<i>.) | _ -> raise (Error m)>.
   | _ -> k .<raise (Error m)>.

let matchFun r k =
   let m = "Expecting string function" in
   match r with
   | SFun (n,f) -> k (.<n>.,f)
   | SAny c -> .<match .~c with Fun (n,f) ->
                 .~(k (.<n>.,
                       fun v -> SAny .<f .~(lift_list (List.map lift v))>.))
                               | _ -> raise (Error m)>.
   | _ -> k (.<raise (Error m)>., fun x -> SAny .<raise (Error m)>.)

let matchCons r k =
   let m = "Expecting string cons cell value" in
   match r with
   | SCons (h,t) -> k (h,t)
   | SAny c -> .<match .~c with Cons (h,t) -> .~(k (.<h>.,.<t>.))
                               | _ -> raise (Error m)>.
   | _ -> k (.<raise (Error m)>.,.<raise (Error m)>.)

(* This type also changes *)

type 'a svar = Val of 'a sdom | Ref of ('a, dom ref) code

let eta_list l v=
  let rec el_acc l v a =
    if l<=0 then [] else .<List.nth .~v a>. :: (el_acc (l-1) v (a+1))
  in el_acc l v 0

let keta_list l v k =
  let rec el_acc l v a k =
    if l<=0
    then k []
    else
      .<match .~v with
	| x::xs ->
	    .~(el_acc (l-1) .<xs>. (a+1) (fun r ->
	      k (.<x>. :: r)))
	| _ -> raise (Error "")>.
  in el_acc l v 0 k

let rec lift_list l =
  match l with
    | [] -> .<[]>.
    | x::xs -> .< .~x :: .~(lift_list xs)>.      ;;

let rec xeval e env k =
  ((*print_string (print (L [S " {"; e; S "} \n"]));*)
  try
    (match e with
      | A "true"   -> k (SBool .<true>.)
      | A "false"  -> k (SBool .<false>.)
      | A "empty"  -> k SEmpty
      | I i -> k (SInt .<i>.)
      | S s -> k (SStr .<s>.)
      | A x ->
	  (match env x with
	    | Val v -> k v
	    | Ref r -> k (SAny .<(! .~r)>.))
      | L [A "not"; e1] ->
	  xeval e1 env (fun r ->
          matchBool r (fun x ->
          k (SBool .<not .~x>.)))
      | L [A "+"; e1; e2] ->
	  xeval e1 env (fun r1 ->
          xeval e2 env (fun r2 ->
          matchInt r1 (fun x1 ->
          matchInt r2 (fun x2 ->
          k (SInt .<.~x1 + .~x2>.)))))
      | L [A "-"; e1; e2] ->
	  xeval e1 env (fun r1 ->
          xeval e2 env (fun r2 ->
          matchInt r1 (fun x1 ->
          matchInt r2 (fun x2 ->
          k (SInt .<.~x1 - .~x2>.)))))
      | L [A "*"; e1; e2] ->
	  xeval e1 env (fun r1 ->
          xeval e2 env (fun r2 ->
          matchInt r1 (fun x1 ->
          matchInt r2 (fun x2 ->
          k (SInt .<.~x1 * .~x2>.)))))
      | L [A "<"; e1; e2] ->
	  xeval e1 env (fun r1 ->
          xeval e2 env (fun r2 ->
          matchInt r1 (fun x1 ->
          matchInt r2 (fun x2 ->
          k (SBool .<.~x1 < .~x2>.)))))
      | L [A ">"; e1; e2] ->
	  xeval e1 env (fun r1 ->
          xeval e2 env (fun r2 ->
          matchInt r1 (fun x1 ->
          matchInt r2 (fun x2 ->
          k (SBool .<.~x1 > .~x2>.)))))
      | L ((A "=") :: e1 :: l) ->
          xeval e1 env (fun r1 ->
          matchInt r1 (fun v ->
          kmap (fun x k -> xeval x env (fun r -> matchInt r k))
                l
		(fun r ->
          k (SBool (List.fold_left (fun bc nc -> .< .~bc && .~nc = .~v>.)
                                   .<true>. r)))))
      | L ((A "and") :: es) ->
	  let rec all l k =
	    (match l with
	      | [] -> k .<true>.
	      | x::xs ->
		  xeval x env (fun r ->
                  matchBool r (fun x ->
		    .<if .~x
		      then .~(all xs k)
		      else .~(k .<false>.)>.)))
	  in all es (fun r -> k (SBool r))
      | L ((A "or") :: es) ->
	  let rec all l k =
	    (match l with
	      | [] -> k .<false>.
	      | x::xs ->
		  xeval x env (fun r ->
                  matchBool r (fun x ->
		    .<if .~x
		      then .~(k .<true>.)
		      else .~(all xs k)>.)))
	  in all es (fun r -> k (SBool r))
      | L [A "cond"; L [c2 ; e2];
           L [A "else"; e3]] ->
	  xeval c2 env (fun r ->
            matchBool r (fun x ->
            .<if .~x then .~(xeval e2 env k) else .~(xeval e3 env k)>.))
      | L [A "if"; c2; e2; e3] ->
	  xeval (L [A "cond"; L [c2 ; e2];
		      L [A "else"; e3]]) env k
      | L [A "set!"; A x; e2] ->
	  (match env x with
	    | Val v -> raise (Error "Only mutable variables can be set!")
	    | Ref v ->
		xeval e2 env (fun r ->
	          .<let _ = (.~v:= .~(lift r)) in .~(k SVoid)>.))
      | L ((A "begin") :: e :: [])
	-> xeval e env k
      | L ((A "begin") :: e1 :: l) ->
	  xeval e1 env (fun r1 ->
	    xeval (L ((A "begin") :: l)) env (fun r2 ->
	      k r2))
      | L [A "cons"; e1; e2] ->
	  xeval e1 env (fun r1 ->
	    xeval e2 env (fun r2 ->
            k (SCons (.<ref .~(lift r1)>., .<ref .~(lift r2)>.))))
      | L [A "empty?"; e1] ->
	  xeval e1 env (fun r ->
          match r with
            | SEmpty -> k (SBool .<true>.)
            | SAny c -> .<match .~c with
	                  | Empty -> .~(k (SBool .<true>.))
	                  | _     -> .~(k (SBool .<false>.))>.
            | _ -> k (SBool .<false>.))
      | L [A "car"; e1] ->
	  xeval e1 env (fun r ->
          matchCons r (function (h,t) ->
          k (SAny .<! .~h>.)))
      | L [A "cdr"; e1] ->
	  xeval e1 env (fun r ->
          matchCons r (function (h,t) ->
          k (SAny .<! .~t>.)))
      | L [A "set-car!"; e1; e2] ->
	  xeval e1 env (fun r1 ->
	    xeval e2 env (fun r2 ->
            matchCons r1 (function (h,t) ->
            .<(.~h:=.~(lift r2); .~(k SVoid))>.)))
      | L [A "set-cdr!"; e1; e2] ->
	  xeval e1 env (fun r1 ->
	    xeval e2 env (fun r2 ->
            matchCons r1 (function (h,t) ->
            .<(.~t:=.~(lift r2); .~(k SVoid))>.)))
(* We remove keta_list, but add SAny and replace id by lift *)
      | L [A "lambda" ; L axs ; e] ->
	  let l = List.length axs
	  in k (SFun (l, fun r ->
                      SAny (xeval e (lext env
                                     (List.map (function A x -> x) axs)
                                     (List.map (fun x -> Val x) r))
                                     lift)))
(* In the following, we end up adding a lot of lossy operations *)
      | L (e::es) ->
	  xeval e env (fun r1 ->
	    .<let (i,f) = unFun .~(lift r1)
              in .~(kmap (fun e -> xeval e env) es (fun r2 ->
		   let args = (List.map lift r2) in
                   let l = List.length args
		   in .<if l= i
		   then let r = f .~(lift_list args) in .~(k (SAny .<r>.))
		   else raise (Error ("Function has "^(string_of_int l)^
                                      " arguments but called with "^
                                      (string_of_int i)))>.))>.)
      | _ -> raise (Error "Expression form not recognized")
)
  with
      Error s -> (print_string ("\n"^(print e)^"\n"); raise (Error s))
)

let rec xpeval p env k =
  ((*print_string (print (L [I (List.length p); S " "])); *)
  match p with
    | [e1] -> xeval e1 env k
    | (L [A "define"; A x; e1])::p ->
	.<let r = ref Undefined in
	  .~(let env' = ext env x (Ref .<r>.) in
	     xeval e1 env' (fun v ->
	     .<let _ = (r := .~(lift v))
	       in .~(xpeval p env' k)>.))>.
    | (L [A "define"; L ((A x)::xs); e1])::p ->
	xpeval (L [A "define"; A x;
		   L [A "lambda" ; L xs ; e1]]::p) env k
    | _ -> raise (Error "Program form not recognized"))

let readeval a  =
    match parse ("("^a^")") with
      | [(L p,r)] -> (xpeval p env0 lift, r)
      | []      -> raise (Error "Parsing failed")
      | _       -> raise (Error "Recieved more than one parse tree.")

let read_file s =
  let ic = open_in s in
  let rec read_lines acc =
    try read_lines ((input_line ic)::acc)
    with End_of_file -> (close_in ic;acc)
  in String.concat "\n" (List.rev (read_lines []))

let freadeval s =
  let (a,s) = readeval (read_file s) in
    (Runcode.run a, s)

(* let test4 () = *)
(*   let f = "test.aloe" in *)
(*   let _ = Trx.init_times () in *)
(*   let s = Trx.time 10 "read_file" (fun () -> read_file f) in *)
(*   let [(L p,r)] *)
(*         = Trx.time 10 "parse"     (fun () -> parse ("("^s^")")) in *)
(*   let c = Trx.time  1 "xpeval"    (fun () -> xpeval p env0 lift) in *)
(*   let t = Trx.time  1 "compile"   (fun () -> .! .< fun () -> .~c>.) in *)
(*   let a = Trx.time  1 "run"       t in *)
(*   let a = Trx.time  1 "readeval"  (fun () -> freadeval f) in *)
(*   let _ = Trx.print_times () in *)
(*     a *)
(* ;; *)
