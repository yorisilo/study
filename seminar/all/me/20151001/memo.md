# 研究計画

<!-- ocaml にshift0 reset0 を実装し，そのstepperを実装する． -->
## 一般的なラムダ計算の評価器に対して，shift0/reset0を加えた評価器を実装し，そのstepperを実装する．

現時点で stepper を提供している言語は Racket のみである．
Clements は，Racketの stepper の実装を行っている．
ある時点の実行の状態を取り出す命令をプログラムに挿入するだけで，ステップ実行を行えるということを主張している．


Clementsの実装では，
状態を取り出す命令をbreak point と呼び，それを加えた高レベル言語を ソース言語とする．
break point によるステップ実行は低レベルの ターゲット言語によって実装されている．


ステップ実行を行う時には，まず，Racketのプログラムを ソース言語に変換する関数によって，プログラム中の簡約可能な箇所全てにbreak point を挿入する．
次にそのソース言語をターゲット言語にコンパイルする．

1. まず，単純なラムダ計算の評価器に対する stepper を実装する．
1. 対象言語にshift0/reset0を加えたものに拡張する．
1. その拡張した言語に対するstepperを実装する



## 10/22 CSセミナー発表までにやること
1. まず，単純なラムダ計算の評価器に対する stepper を実装する．
まではやりたい．

# コントロールオペレータの種類

直前に設定されたプロンプトやリセットを保つ

* reset/shift
* prompt/control


直前に設定されたプロンプトやリセットを保たない

* reset0/shift0
  * shift0 はshiftによく似ているオペレータだが，shift0から復帰するたびに対応するresetを削除する．
* prompt0/control0


### keywords

* shift0/reset0
* stepper プログラムの実行を1ステップずつ表示するもの
  * 計算過程を追うことで，プログラムの挙動の理解やデバッグを行いやすくする

# Reference

* http://okmij.org/ftp/continuations/index.html#delimcc-paper
* J. Clements, M. Flatt, and M. Felleisen. Modeling an Algebraic Stepper. Programming Languages and Systems. Springer Berlin Heidelberg, pp. 320-334, 2001. http://link.springer.com/chapter/10.1007%2F3-540-45309-1_21
