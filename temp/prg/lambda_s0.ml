open Delimcc;;

(*
   http://stackoverflow.com/questions/14431257/how-to-translate-shift-reset-into-delimcc
   http://d.hatena.ne.jp/keigoi/20100627/1277650709
*)


(* paper:
   reset (fun () -> 3 + shift (fun _ -> 5 * 2) - 1)
*)

(* Delimcc: *)
let test1 = let open Delimcc in
  let np = new_prompt () in
  push_prompt np (fun () -> 3 + (shift np (fun k -> k @@ k @@ 5 * 2)) - 1)

let shift p f = take_subcont p (fun sk () ->
    push_prompt p (fun () -> (f (fun c ->
        push_delim_subcont sk (fun () -> c)))))

let shift0 p f = take_subcont p (fun sk () ->
    f (fun c -> push_delim_subcont sk (fun () -> c)))

type t = Var   of string
       | Abs   of string * t
       | App   of t * t
       | Shift of string * t
       | Reset of t
