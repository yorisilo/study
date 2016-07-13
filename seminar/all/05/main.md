# 全体ゼミ
# Fri May 22 15:27:17 2015

# kobori
## shift/reset
式の途中で元の式の型が変化してしまう
answer type modification (ATM)

    reset (5+ shift k.k)
    ~> rest k where k = \x.rest(5+x)
    k 9 ~> (\x.reset(5+x)) 9
    ~> rest(5+9) ~> reset 14 ~> 14

## ATMをサポートするために

### プロンプト渡し変換
  * 一つのshift/resetを複数のshift/resetで模倣する
  * Effectifl term は2つのプロンプトを受け取る

### effectiful term
  * shiftを含んだ項という意味でなく，そのtermからeffectが染みだしてしまう項のこと
  * 見た目にはpureなtermだが，effectを持つterm?


## OCaml上への実装
* ATMありのshift/reset言語をDSLとして実装
* DSLの解釈に変換を利用

* 終タグレス法 carette et al.2009

## GADT
* 代数的データ型の拡張．コンストラクタごとに独立に型を書けるようになる．

コンストラクタは関数のように書く．

    type _ term =
    | int:int -> int term
    | Add:(int -> int -> int) term
    ...


    let lam:type a b. hoge


# torii
* horn節制約系
* 再帰horn節制約系の解消をするやつの実装の話

## 論文
`PPDP2009 dependent type inference with interpolants`

## 実装
`sorceprogram -> ホーン節制約生成:上記論文3節 -> (HSSCの変換):main -> ホーン節制約解消:今回話すこと．上記論文4節`

* 再帰ホーン節のことを話す
述語変数がひとつしかないもの`P(x):P(y) /\ \emptyset`に対しての解消の話をする


# 修士論文中間発表会
7/16 cs
7/9 知能
7/14 知能
