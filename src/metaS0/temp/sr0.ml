(* 変数なし OCamlの変数を使って表す *)
(* 型は決まってて，型の解釈は自由に決められる *)
module type SYM =
sig
  type 'a repr
  val lam: ('a repr -> 'b repr) -> ('a -> 'b) repr
  val app: ('a -> 'b) repr -> 'a repr -> 'b repr
end

(* 解釈を自由に決められる *)
module R:SYM =
struct
  type 'a repr = 'a
  (* let lam f = fun x -> f x *)
  let lam f = f                 (* イータ変換 *)
  let app f a = f a
end

module R2: (SYM with type 'a repr = 'a code) =
struct
  type 'a repr = 'a code
  let lam f = .<fun x -> .~(f .<x>.)>.;;
  let app f a = .<.~f .~a>.;;
end

module Ex1 (S:SYM) =
struct
  open S
  let ex1 = lam (fun x -> lam (fun y -> app x y))
end

let test1 =
  let module M = Ex1(R) in
  [M.ex1]
