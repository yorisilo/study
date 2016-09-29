(* λ式を表すデータ型 *)
type exp = Var of string  (* 変数 *) (* 変数名は文字列であらわすことにする *)
         | Abs of string * exp (* λ抽象 *)
         | App of exp * exp (* 関数適用 *)


let i = Abs ("x", Var "x")

let k = Abs ("x", Abs ("y", Var "x"))

let s = Abs ("x", (Abs ("y", Abs ("z", (App ((App ((Var "x"), (Var "z"))), (App ((Var "y"), (Var "z")))))))))

let skk = App (App (s,k),k)

let gensym = (* 新しい変数名を作る補助的な関数 *)
  let counter = ref 0 in (* 整数0を持った参照セルcounterを作る *)
  fun () -> (* ダミーの引数 () を受け取ったら… *)
    incr counter; (* counter の中身を一つ増やす *)
    "g" ^ string_of_int !counter (* g1, g2, g3, ... 等の文字列を返す *)

let rec subst e2 x e1 = (* [e2/x]e1 を求めて返す *)
  match e1 with
  | Var(y) -> if x = y then e2 else Var(y)
  | Abs(y, e) ->
    let y' = gensym () in
    Abs(y', subst e2 x (subst (Var(y')) y e))
  | App(e, e') ->
    App(subst e2 x e, subst e2 x e')

let rec step e = (* e を受け取り、e -> e' となる e' のリストを返す *)
  match e with
  | Var(x) -> []
  | Abs(x, e0) ->
    (* (R-Abs) より *)
    List.map
      (fun e0' -> Abs(x, e0'))
      (step e0)
  | App(e1, e2) ->
    (* (R-Beta) より *)
    (match e1 with
     | Abs(x, e0) -> [subst e2 x e0]
     | _ -> []) @
    (* (R-App1) より *)
    List.map
      (fun e1' -> App(e1', e2))
      (step e1) @
    (* (R-App2) より *)
    List.map
      (fun e2' -> App(e1, e2'))
      (step e2)

let rec repeat e = (* 簡約できなくなるまで step を反復する *)
  match step e with
  | [] -> e
  | e' :: _ -> repeat e'

let example = repeat @@ App (skk, (Var "x"))
(* Var "x" *)
