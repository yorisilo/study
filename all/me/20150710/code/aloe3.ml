(* 3 *)
exception Error of string

type sxp =
  | I of int          (* Integer *)
  | A of string       (* Atoms  *)
  | S of string       (* String *)
  | L of sxp list     (* List   *)

type dom =
  | Bool of bool
  | Int of int | Str of string
  | Fun of int * (dom list -> dom)
  | Undefined
  | Void
  | Empty | Cons of dom ref * dom ref


type svar = Val of dom code
          | Ref of (dom ref) code
(* type 'a svar = Val of ('a, dom) code | Ref of ('a, dom ref) code *)

(* open M *)

let rec kmap f l k =
  match l with
  | [] -> k []
  | x::xs ->
    kmap f xs (fun r1 ->
        f x (fun r2 ->
            k (r2::r1)))
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

let eta_list l v =
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
	          k (.<x>. :: r)))>.
	    (* | _ -> raise (Error "")>. *)
  in el_acc l v 0 k

let rec lift_list l =
  match l with
  | [] -> .<[]>.
  | x::xs -> .< .~x :: .~(lift_list xs)>.

let rec seval e env k =
  try
    (match e with
     | A "true"   -> k .<Bool true>.
     | A "false"  -> k .<Bool false>.
     | A "empty"  -> k .<Empty>.
     | I i -> k .<Int i>.
     | S s -> k .<Str s>.
     | A x ->
	     (match env x with
	      | Val v -> k v
	      | Ref r -> k .<(Runcode.run .~r)>.)
     | L [A "not"; e1] ->
	     seval e1 env (fun r ->
           k .<Bool (not(unBool .~r))>.)
     | L [A "+"; e1; e2] ->
	     seval e1 env (fun r1 ->
           seval e2 env (fun r2 ->
	             .<match (.~r1,.~r2) with
		           | (Int i1, Int i2) ->
		             .~(k .<Int ((i1 + i2))>.)
		           | _ -> raise (Error "")>.))
     | L [A "-"; e1; e2] ->
	     seval e1 env (fun r1 ->
           seval e2 env (fun r2 ->
	             .<match (.~r1,.~r2) with
		           | (Int i1, Int i2) ->
		             .~(k .<Int ((i1 - i2))>.)
		           | _ -> raise (Error "")>.))
     | L [A "*"; e1; e2] ->
	     seval e1 env (fun r1 ->
           seval e2 env (fun r2 ->
	             .<match (.~r1,.~r2) with
		           | (Int i1, Int i2) ->
		             .~(k .<Int ((i1 * i2))>.)
		           | _ -> raise (Error "")>.))
     | L [A "<"; e1; e2] ->
	     seval e1 env (fun r1 ->
           seval e2 env (fun r2 ->
	             .<match (.~r1,.~r2) with
		           | (Int i1, Int i2) ->
		             .~(k .<Bool ((i1 < i2))>.)
		           | _ -> raise (Error "")>.))
     | L [A ">"; e1; e2] ->
	     seval e1 env (fun r1 ->
           seval e2 env (fun r2 ->
	             .<match (.~r1,.~r2) with
		           | (Int i1, Int i2) ->
		             .~(k .<Bool ((i1 > i2))>.)
		           | _ -> raise (Error "")>.))
     | L ((A "=") :: e1 :: l) ->
       seval e1 env (fun r1 ->
           .<let v = unInt .~r1 in
		       .~(kmap
		            (fun x k -> seval x env (fun r ->
			               k .<unInt .~r>.)) l
		            (fun r ->
			             k .<Bool .~(List.fold_left
					                       (fun bc nc -> .< .~bc && .~nc = v>.)
					                       .<true>. r)>.))>.)
     | L ((A "and") :: es) ->
	     let rec all l k =
	       (match l with
	        | [] -> k .<true>.
	        | x::xs ->
		        seval x env (fun r ->
		            .<if unBool .~r
		            then .~(all xs k)
		            else .~(k .<false>.)>.))
	     in all es (fun r -> k .<Bool .~r>.)
     | L ((A "or") :: es) ->
	     let rec all l k =
	       (match l with
	        | [] -> k .<false>.
	        | x::xs ->
		        seval x env (fun r ->
		            .<if unBool .~r
		            then .~(k .<true>.)
		            else .~(all xs k)>.))
	     in all es (fun r -> k .<Bool .~r>.)
     | L [A "cond"; L [c2 ; e2];
          L [A "else"; e3]] ->
	     seval c2 env (fun r ->
	         .<match .~r with
	         | Bool true  -> .~(seval e2 env k)
	         | Bool false -> .~(seval e3 env k)
	         | _ -> raise (Error "Condition must be boolean")>.)
     | L [A "if"; c2; e2; e3] ->
	     seval (L [A "cond"; L [c2 ; e2];
		             L [A "else"; e3]]) env k
     | L [A "set!"; A x; e2] ->
	     (match env x with
	      | Val v -> raise (Error "Only mutable variables can be set!")
	      | Ref v ->
		      seval e2 env (fun r ->
	            .<let _ = (.~v:= .~r) in .~(k .<Void>.)>.))
     | L ((A "begin") :: e :: [])
	     -> seval e env k
     | L ((A "begin") :: e1 :: l) ->
	     seval e1 env (fun r1 ->
	         seval (L ((A "begin") :: l)) env (fun r2 ->
	             k r2))
     | L [A "cons"; e1; e2] ->
	     seval e1 env (fun r1 ->
	         seval e2 env (fun r2 ->
	             k .<Cons (ref .~r1, ref .~r2)>.))
     | L [A "empty?"; e1] ->
	     seval e1 env (fun r ->
	         .<match .~r with
	         | Empty -> .~(k .<Bool true>.)
	         | _     -> .~(k .<Bool false>.)>.)
     | L [A "car"; e1] ->
	     seval e1 env (fun r ->
	         .<match .~r with
	         | Cons (h,t) -> .~(k .<!h>.)
	         | _ -> raise (Error ("Can't take car of "^(print e1)))>.)
     | L [A "cdr"; e1] ->
	     seval e1 env (fun r ->
	         .<match .~r with
	         | Cons (h,t) -> .~(k .<!t>.)
	         | _ -> raise (Error ("Can't take cdr of "^(print e1)))>.)
     | L [A "set-car!"; e1; e2] ->
	     seval e1 env (fun r1 ->
	         seval e2 env (fun r2 ->
	             .<match .~r1 with
		           | Cons (h,t) -> (h:=.~r2; .~(k .<Void>.))
		           | _ -> raise (Error ("Can't assign car of "^(print e1)))>.))
     | L [A "set-cdr!"; e1; e2] ->
	     seval e1 env (fun r1 ->
	         seval e2 env (fun r2 ->
	             .<match .~r1 with
		           | Cons (h,t) -> (t:=.~r2; .~(k .<Void>.))
		           | _ -> raise (Error ("Can't assign cdr of "^(print e1)))>.))
     | L [A "lambda" ; L axs ; e] ->
	     let l = List.length axs
	     in k .<Fun (l, fun v ->
           .~(keta_list l .<v>. (fun r->
               seval e (lext env
                          (List.map (function A x -> x) axs)
                          (List.map (fun x -> Val x) r))
                 (fun r -> r))))>.
     | L (e::es) ->
	     seval e env (fun r1 ->
	         .<let (i,f) = unFun .~r1
           in .~(kmap (fun e -> seval e env) es (fun r2 ->
		           let args = r2 in
               let l = List.length args
		           in .<if l= i
		           then let r = f .~(lift_list args) in .~(k .<r>.)
		           else raise (Error ("Function has "^(string_of_int l)^
                                  " arguments but called with "^
                                  (string_of_int i)))>.))>.)
     | _ -> raise (Error "Expression form not recognized"))
  with
    Error s -> (print_string ("\n"^(print e)^"\n"); raise (Error s))

let rec speval p env k =
  match p with
  | [e1] -> seval e1 env k
  | (L [A "define"; A x; e1])::p ->
	  .<let r = ref Undefined in
	  .~(let env' = ext env x (Ref .<r>.) in
	     seval e1 env' (fun v ->
	         .<let _ = (r := .~v)
	         in .~(speval p env' k)>.))>.
  | (L [A "define"; L ((A x)::xs); e1])::p ->
	  speval (L [A "define"; A x;
		           L [A "lambda" ; L xs ; e1]]::p) env k
  | _ -> raise (Error "Program form not recognized")

let readeval a  =
  match parse ("("^a^")") with
  | [(L p,r)] -> (speval p env0 (fun x -> x), r)
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

(* let test3 () = *)
(*   let f = "test.aloe" in *)
(*   let _ = Trx.init_times () in *)
(*   let s = Trx.time 10 "read_file" (fun () -> read_file f) in *)
(*   let [(L p,r)] *)
(*     = Trx.time 10 "parse"     (fun () -> parse ("("^s^")")) in *)
(*   let c = Trx.time  1 "speval"    (fun () -> speval p env0 (fun x -> x)) in *)
(*   let t = Trx.time  1 "compile"   (fun () -> Runcode.run .< fun () -> .~c>.) in *)
(*   let a = Trx.time  1 "run"       t in *)
(*   let a = Trx.time  1 "readeval"  (fun () -> freadeval f) in *)
(*   let _ = Trx.print_times () in *)
(*   a *)
