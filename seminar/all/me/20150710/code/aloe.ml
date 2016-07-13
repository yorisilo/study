(* Another Language of Expressions (Aloe)

   Author:  Walid Taha
   Date:    Sat Jun 23 07:49:30 CDT 2007

   Problem: See "A Gentle Introduction to Multi-stage Programming,
                 Part II"
*)

(* ------------------------------------------------------------------
   ##                             PARSING                          ##
   ------------------------------------------------------------------ *)

(* Mon Mar 26 05:20:36 CDT 2007 *)

(*
   ## Parser from Hutton and Meijer (\cite{HuttonMeijer98})
*)

type 'a parser = Parser of (string -> ('a * string) list)

let unParser (Parser f) = f
let item =
  Parser (fun s ->
      let len = String.length s in
      match len with
      | 0 -> []
      | _ -> [(String.get s 0, String.sub s 1 (len-1))])


let return a = Parser (fun s -> [(a,s)])
let bind p f = Parser (fun s ->
    List.flatten (let as_list = unParser p s in
	                List.map (fun (a,s) -> (unParser (f a) s)) as_list))
let zero     = Parser (fun s -> [])
let plus p q = Parser (fun s -> (unParser p s) @ (unParser q s))
let dplus p q= Parser (fun s ->
    match (unParser (plus p q) s) with
      [] -> []
    | x::xs -> [x])
let sat p =
  bind item (fun c ->
      if p c then return c else zero)
let char c = sat (fun x -> c=x)
let rec string s =
  let len = String.length s in
  match len with
  | 0 -> return ""
  | _ -> bind (char (String.get s 0)) (fun c ->
      string (String.sub s 1 (len-1)))
let rec many p = dplus (many1 p) (return [])
and many1 p =
  bind p (fun x ->
      bind (many p) (fun xs ->
          return (x::xs)))
let rec sepby p sep = dplus (sepby1 p sep) (return [])
and sepby1 p sep =
  bind p (fun x ->
      bind (many (bind sep (fun _ -> p))) (fun xs ->
          return (x::xs)))
let rec chain p op a = dplus (chain1 p op) (return a)
and chain1 p op =
  let rec rest a =
    dplus (bind op (fun f ->
        bind p  (fun b ->
            rest (f a b))))
      (return a)
  in bind p (fun a ->
      rest a)
let isSpace c =
  match c with
    ' ' | '\t' | '\n' | '\013' -> true
  | _ -> false
let isDigit c =
  match c with
    '0' |'1' |'2' |'3' |'4' |'5' |'6' |'7' |'8' |'9' -> true
  | _ -> false
let isSymbolChar c =
  match c with
    '(' | ')' | '\"' -> false
  | _ -> not (isSpace c)
let space = many (sat isSpace)
let token p =
  bind p (fun a ->
      bind space (fun _ ->
          return a))
let symb s = token (string s)
let apply p  = unParser (bind space (fun _ -> p))

(*
   ## Example from paper [Arithmetic grammar]
*)

let rec
  expr   s = chain1 (term ())   (addop ())
and term   s = chain1 (factor ()) (mulop ())
and factor s = dplus (digit ()) (bind (symb "(") (fun _ ->
    bind (expr ())  (fun n ->
        bind (symb ")") (fun _ ->
            return n))))
and digit  s = bind (token (sat isDigit)) (fun x ->
    return (Char.code x - Char.code '0'))
and addop  s = dplus
    (bind (symb "+") (fun x ->
         return (+)))
    (bind (symb "-") (fun x ->
         return (-)))
and mulop  s = dplus
    (bind (symb "*") (fun x ->
         return ( * )))
    (bind (symb "/") (fun x ->
         return ( / )))

let a = apply (expr ()) " 1 -2 * 3+4"

(*
   ## New example:  Parsing s-expressions
*)

(* Simple helper functions *)

let rec dl_to_int dl = dl_to_int_acc dl 0
and dl_to_int_acc dl acc =
  match dl with
    [] -> acc
  | (d::ds) -> dl_to_int_acc ds (10*acc + d)

let rec cl_to_str cl =
  match cl with
  | [] -> ""
  | (c::cs) -> (Char.escaped c) ^ (cl_to_str cs)

type sxp =
  | I of int          (* Integer *)
  | A of string       (* Atoms  *)
  | S of string       (* String *)
  | L of sxp list     (* List   *)

exception Error of string

let rec print x =
  match x with
  | I i -> string_of_int i
  | S s -> "\""^s^"\""
  | A s -> s
  | L l -> "("^(lprint l)^")"
and lprint l =
  match l with
  | []    -> ""
  | x::[] -> print x
  | x::xs -> (print x)^" "^(lprint xs)

let rec mk_term () =
  match (Random.int 5) with
  | 0 -> I (Random.int 1000000)
  | 1 -> S ("String"^(string_of_int (Random.int 42)))
  | 2 -> A ("Atom"^(string_of_int (Random.int 42)))
  | 3 -> L []
  | 4 -> L [(mk_term ());(mk_term ());(mk_term ());(mk_term ());(mk_term ())]

let rec
  sxp    s = dplus
    (int ())
	  (dplus
		   (str ())
       (dplus
          (sym ())
		      (bind (symb "(") (fun _ ->
               bind (many (sxp ()))  (fun sxpl ->
                   bind (symb ")") (fun _ ->
                       return (L sxpl)))))))
and digit  s = bind (sat isDigit) (fun x ->
    return (Char.code x - Char.code '0'))
and int    s = bind (token (many1 (digit ()))) (fun ds ->
	  return (I (dl_to_int ds)))
and str    s = (bind (symb "\"") (fun _ ->
    bind (many (sat (fun c -> not (c='\"'))))  (fun cl ->
        bind (symb "\"") (fun _ ->
            return (S (cl_to_str cl))))))
and sym    s = bind (many1 (sat isSymbolChar)) (fun cl ->
    bind space (fun _ ->
        return (A (cl_to_str cl))))

and expr   s = chain1 (term ())   (addop ())
and term   s = chain1 (factor ()) (mulop ())
and factor s = dplus (digit ()) (bind (symb "(") (fun _ ->
    bind (expr ())  (fun n ->
        bind (symb ")") (fun _ ->
            return n))))
and addop  s = dplus
    (bind (symb "+") (fun x ->
         return (+)))
    (bind (symb "-") (fun x ->
         return (-)))
and mulop  s = dplus
    (bind (symb "*") (fun x ->
         return ( * )))
    (bind (symb "/") (fun x ->
         return ( / )))

let parse a = apply (sxp ()) a

let a = parse "(lambda x (x x))"

let rec bug () =
  let a = mk_term () in
  let s = print a in
  let [(p,_)] = parse s in
  if a=p then bug () else a;

  (* ------------------------------------------------------------------
     ##                           INTERPRETER                        ##
     ------------------------------------------------------------------ *)

  (* 1 *)

  (* A simple interpreter *)

type dom =
  | Bool of bool
  | Int of int | Str of string
  | Fun of int * (dom list -> dom)
  | Undefined
  | Void
  | Empty | Cons of dom ref * dom ref

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

let env0 x = raise (Error ("Variable not found in environment "^x))

(* env: string -> var *)
let ext env x v = fun y -> if x=y then v else env y

let rec lext env xl vl =
  match xl with
  | []    -> env
  | x::xs ->
	  match vl with
    | [] -> raise (Error "Not enough arguments")
    | y::ys -> lext (ext env x y) xs ys

type var = Val of dom | Ref of dom ref

let rec eval e env =
  try
    (match e with
     | A "true"   -> Bool true
     | A "false"  -> Bool false
     | A "empty"  -> Empty
     | A x ->
	     (match env x with
	      | Val v -> v
	      | Ref r -> !r)
     | I i -> Int i
     | S s -> Str s
     | L [A "not"; e1] ->
	     Bool (not(unBool (eval e1 env)))
     | L [A "+"; e1; e2] ->
	     Int ((unInt (eval e1 env) + (unInt (eval e2 env))))
     | L [A "-"; e1; e2] ->
	     Int ((unInt (eval e1 env) - (unInt (eval e2 env))))
     | L [A "*"; e1; e2] ->
	     Int ((unInt (eval e1 env) * (unInt (eval e2 env))))
     | L [A "<"; e1; e2] ->
	     Bool ((unInt (eval e1 env) < (unInt (eval e2 env))))
     | L [A ">"; e1; e2] ->
	     Bool ((unInt (eval e1 env) > (unInt (eval e2 env))))
     | L ((A "=") :: e1 :: l) ->
	     Bool (
	       let v = unInt (eval e1 env) in
	       let l = List.map (fun x -> unInt (eval x env)) l in
	       List.for_all (fun y -> y=v) l)
     | L ((A "and") :: es) ->
	     Bool (
	       let rec all l =
		       match l with
		       | [] -> true
		       | x::xs ->
		         if unBool (eval x env)
		         then all xs
		         else false
	       in all es)
     | L ((A "or") :: es) ->
	     Bool (
	       let rec all l =
		       match l with
		       | [] -> false
		       | x::xs ->
		         if unBool (eval x env)
		         then true
		         else all xs
	       in all es)
     | L [A "cond"; L [c2 ; e2];
          L [A "else"; e3]] ->
	     (match (eval c2 env) with
	      | Bool true  -> eval e2 env
	      | Bool false -> eval e3 env
	      | _ -> raise (Error "Condition must be boolean"))
     | L [A "if"; c2; e2; e3] ->
	     eval (L [A "cond"; L [c2 ; e2];
                L [A "else"; e3]]) env
     | L [A "set!"; A x; e2] ->
	     (match env x with
	      | Val v -> raise (Error "Only mutable variables can be set!")
	      | Ref r -> let _ = (r:=(eval e2 env)) in Void)
     | L ((A "begin") :: e :: [])
	     -> eval e env
     | L ((A "begin") :: e1 :: l) ->
	     let _ = eval e1 env in eval (L ((A "begin") :: l)) env
     | L [A "cons"; e1; e2] ->
	     Cons (ref (eval e1 env), ref (eval e2 env))
     | L [A "empty?"; e1] ->
	     (match (eval e1 env) with
        | Empty -> Bool true
	      | _     -> Bool false)
     | L [A "car"; e1] ->
	     (match (eval e1 env) with
	      | Cons (h,t) -> !h
	      | _ -> raise (Error ("Can't take car of "^(print e1))))
     | L [A "cdr"; e1] ->
	     (match (eval e1 env) with
	      | Cons (h,t) -> !t
	      | _ -> raise (Error ("Can't take cdr of "^(print e1))))
     | L [A "set-car!"; e1; e2] ->
	     (match (eval e1 env) with
	      | Cons (h,t) -> (h:=(eval e2 env);Void)
	      | _ -> raise (Error ("Can't assign car of "^(print e1))))
     | L [A "set-cdr!"; e1; e2] ->
	     (match (eval e1 env) with
	      | Cons (h,t) -> (t:=(eval e2 env);Void)
	      | _ -> raise (Error ("Can't assign cdr of "^(print e1))))
     | L [A "lambda" ; L axs ; e] ->
	     let l = List.length axs in
	     Fun (l,
		        fun v ->
		          eval e (lext env
			                  (List.map (function A x -> x) axs)
			                  (List.map (fun x -> Val x) v)))
     (* The following special case is unreachable, dead code, only left as a comment *)
     | L [A "lambda" ; L [S x] ; e] ->
       Fun (1, fun l -> match l with [v] -> eval e (ext env x (Val v)))
     | L (e::es) ->
	     let (i,f) = unFun (eval e env) in
	     let args = List.map (fun e -> eval e env) es in
	     let l = List.length args
	     in if l=i
	     then f args
	     else raise (Error ("Function has "^(string_of_int l)^
				                  " arguments but called with "^(string_of_int i)))
     (* The following special case is unreachable, dead code, only left as a comment *)
     | L [e1; e2] ->
       let (1,f) = unFun (eval e1 env) in
       let arg = eval e2 env in
       f [arg]
     | _ -> raise (Error "Expression form not recognized"))
  with
    Error s -> (print_string ("\n"^(print e)^"\n"); raise (Error s))

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

let readeval a  =
  match parse ("("^a^")") with
  | [(L p,r)] -> (peval p env0, r)
  | []      -> raise (Error "Parsing failed")
  | _       -> raise (Error "Recieved more than one parse tree.")

let read_file s =
  let ic = open_in s in
  let rec read_lines acc =
    try read_lines ((input_line ic)::acc)
    with End_of_file -> (close_in ic;acc)
  in String.concat "\n" (List.rev (read_lines []))

let freadeval s =
  readeval (read_file s)

(* let test1 () = *)
(*   let f = "test.aloe" in *)
(*   let _ = Trx.init_times () in *)
(*   let s = Trx.time 10 "read_file" (fun () -> read_file f) in *)
(*   let [(L p,r)] *)
(*     = Trx.time 10 "parse" (fun () -> parse ("("^s^")")) in *)
(*   let a = Trx.time  1 "peval"     (fun () -> peval p env0) in *)
(*   let a = Trx.time  1 "readeval"  (fun () -> freadeval f) in *)
(*   let _ = Trx.print_times () in *)
(*   a *)

(* 2 *)

(* The interpreter in continuation-passing style CPS *)

let rec kmap f l k =
  match l with
  | [] -> k []
  | x::xs ->
    kmap f xs (fun r1 ->
        f x (fun r2 ->
            k (r2::r1)))

let rec keval e env k =
  try
    (match e with
     | A "true"   -> k (Bool true)
     | A "false"  -> k (Bool false)
     | A "empty"  -> k (Empty)
     | A x ->
	     (match env x with
	      | Val v -> k v
	      | Ref r -> k ((! r)))
     | I i -> k (Int i)
     | S s -> k (Str s)
     | L [A "not"; e1] ->
	     keval e1 env (fun r ->
           k (Bool (not(unBool r))))
     | L [A "+"; e1; e2] ->
	     keval e1 env (fun r1 ->
           keval e2 env (fun r2 ->
	             (match (r1,r2) with
		            | (Int i1, Int i2) ->
		              (k (Int ((i1 + i2))))
		            | _ -> raise (Error ""))))
     (* The following rewrite is unreachable, but is left as a comment *)
     | L [A "+"; e1; e2] -> keval e1 env (fun r1 ->
         keval e2 env (fun r2 ->
             k (Int ((unInt r1) + (unInt r2)))))
     | L [A "-"; e1; e2] ->
	     keval e1 env (fun r1 ->
           keval e2 env (fun r2 ->
	             (match (r1,r2) with
		            | (Int i1, Int i2) ->
		              (k (Int ((i1 - i2))))
		            | _ -> raise (Error ""))))
     | L [A "*"; e1; e2] ->
	     keval e1 env (fun r1 ->
           keval e2 env (fun r2 ->
	             (match (r1,r2) with
		            | (Int i1, Int i2) ->
		              (k (Int ((i1 * i2))))
		            | _ -> raise (Error ""))))
     | L [A "<"; e1; e2] ->
	     keval e1 env (fun r1 ->
           keval e2 env (fun r2 ->
	             (match (r1,r2) with
		            | (Int i1, Int i2) ->
		              (k (Bool ((i1 < i2))))
		            | _ -> raise (Error ""))))
     | L [A ">"; e1; e2] ->
	     keval e1 env (fun r1 ->
           keval e2 env (fun r2 ->
	             (match (r1,r2) with
		            | (Int i1, Int i2) ->
		              (k (Bool ((i1 > i2))))
		            | _ -> raise (Error ""))))
     | L ((A "=") :: e1 :: l) ->
       keval e1 env (fun r1 ->
           let v = unInt r1
           in kmap (fun x k -> keval x env (fun r -> k (unInt r))) l
             (fun r -> k (Bool (List.fold_left
                                  (fun bc nc -> ( bc && nc = v))
                                  true r))))
     | L ((A "and") :: es) ->
	     let rec all l k =
	       (match l with
	        | [] -> k (true)
	        | x::xs ->
		        keval x env (fun r ->
		            (if unBool r
		             then (all xs k)
		             else (k (false)))))
	     in all es (fun r -> k (Bool r))
     | L ((A "or") :: es) ->
	     let rec all l k =
	       (match l with
	        | [] -> k (false)
	        | x::xs ->
		        keval x env (fun r ->
		            (if unBool r
		             then (k (true))
		             else (all xs k))))
	     in all es (fun r -> k (Bool r))
     | L [A "cond"; L [c2 ; e2];
          L [A "else"; e3]] ->
	     keval c2 env (fun r ->
	         (match r with
	          | Bool true  -> (keval e2 env k)
	          | Bool false -> (keval e3 env k)
	          | _ -> raise (Error "Condition must be boolean")))
     | L [A "if"; c2; e2; e3] ->
	     keval (L [A "cond"; L [c2 ; e2];
		             L [A "else"; e3]]) env k
     | L [A "set!"; A x; e2] ->
	     (match env x with
	      | Val v -> raise (Error "Only mutable variables can be set!")
	      | Ref v ->
		      keval e2 env (fun r ->
	            (let _ = (v:= r) in (k (Void)))))
     | L ((A "begin") :: e :: [])
	     -> keval e env k
     | L ((A "begin") :: e1 :: l) ->
	     keval e1 env (fun r1 ->
	         keval (L ((A "begin") :: l)) env (fun r2 ->
	             k r2))
     | L [A "cons"; e1; e2] ->
	     keval e1 env (fun r1 ->
	         keval e2 env (fun r2 ->
	             k (Cons (ref r1, ref r2))))
     | L [A "empty?"; e1] ->
	     keval e1 env (fun r ->
	         (match r with
	          | Empty -> (k (Bool true))
	          | _     -> (k (Bool false))))
     | L [A "car"; e1] ->
	     keval e1 env (fun r ->
	         (match r with
	          | Cons (h,t) -> (k (!h))
	          | _ -> raise (Error ("Can't take car of "^(print e1)))))
     | L [A "cdr"; e1] ->
	     keval e1 env (fun r ->
	         (match r with
	          | Cons (h,t) -> (k (!t))
	          | _ -> raise (Error ("Can't take cdr of "^(print e1)))))
     | L [A "set-car!"; e1; e2] ->
	     keval e1 env (fun r1 ->
	         keval e2 env (fun r2 ->
	             (match r1 with
		            | Cons (h,t) -> (h:=r2; (k (Void)))
		            | _ -> raise (Error ("Can't assign car of "^(print e1))))))
     | L [A "set-cdr!"; e1; e2] ->
	     keval e1 env (fun r1 ->
	         keval e2 env (fun r2 ->
	             (match r1 with
		            | Cons (h,t) -> (t:=r2; (k (Void)))
		            | _ -> raise (Error ("Can't assign cdr of "^(print e1))))))
     | L [A "lambda" ; L axs ; e] ->
	     let l = List.length axs
       in k (Fun (l, fun v ->
           keval e (lext env
                      (List.map (function A x -> x) axs)
                      (List.map (fun x -> Val x) v))
             (fun r -> r)))
     | L (e::es) ->
	     keval e env (fun r1 ->
           let (i,f) = unFun r1
           in kmap (fun e -> keval e env) es (fun r2 ->
               let args = r2 in
               let l = List.length args
               in if l= i
               then let r = f args in k r
               else raise (Error ("Function has "^(string_of_int l)^
                                  " arguments but called with "^(string_of_int i)))))
     | _ -> raise (Error "Expression form not recognized"))
  with
    Error s -> (print_string ("\n"^(print e)^"\n"); raise (Error s))

let rec kpeval p env k =
  match p with
  | [e1] -> keval e1 env k
  | (L [A "define"; A x; e1])::p ->
	  (let r = ref Undefined in
	   (let env' = ext env x (Ref r) in
	    keval e1 env' (fun v ->
	        (let _ = (r := v)
	         in (kpeval p env' k)))))
  | (L [A "define"; L ((A x)::xs); e1])::p ->
	  kpeval (L [A "define"; A x;
		           L [A "lambda" ; L xs ; e1]]::p) env k
  | _ -> raise (Error "Program form not recognized")

let readeval a  =
  match parse ("("^a^")") with
  | [(L p,r)] -> (kpeval p env0 (fun x -> x), r)
  | []      -> raise (Error "Parsing failed")
  | _       -> raise (Error "Recieved more than one parse tree.")

let read_file s =
  let ic = open_in s in
  let rec read_lines acc =
    try read_lines ((input_line ic)::acc)
    with End_of_file -> (close_in ic;acc)
  in String.concat "\n" (List.rev (read_lines []))

let freadeval s =
  readeval (read_file s)

(* let test2 () = *)
(*   let f = "test.aloe" in *)
(*   let _ = Trx.init_times () in *)
(*   let s = Trx.time 10 "read_file" (fun () -> read_file f) in *)
(*   let [(L p,r)] *)
(*     = Trx.time 10 "parse"     (fun () -> parse ("("^s^")")) in *)
(*   let a = Trx.time  1 "kpeval"    (fun () -> kpeval p env0 (fun x -> x)) in *)
(*   let a = Trx.time  1 "readeval"  (fun () -> freadeval f) in *)
(*   let _ = Trx.print_times () in *)
(*   a *)


(* test1 ();; *)
(* test2 ();; *)
(* test3 ();; *)
(* test4 ();; *)
