 shift0 の処理では，その時点での継続を値 VCont(k) としてパッケージ ングしてから Shift0 項の引数 exp (の実行結果の関数)に渡している．reset0 の処理では継続を id にリセットし ており，これにより Shift0 命令で取り出される継続が限定される．


# tagless final での実装
DSLを実装するときに
OCaml自体の型チェックや型推論器などを直接使える．
* Data type でなく，module を使って type を表現する
* 変数は直接インターフェースに出てこない，OCamlのほうの変数を使う

# GADT
* polymorphic な list を GADT で表現する？
(δ:継続のリストを表現するために必要)
