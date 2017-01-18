# 大石純平 修論メモ
[修論の書類とか](http://private.sie.tsukuba.ac.jp/pub-student/syuron.html)

# タイトル
### 安全なコード移動が可能なコード生成言語の型システムの設計と実装

```
\contentsline {chapter}{\numberline {第1章}はじめに}{1}
\contentsline {chapter}{\numberline {第2章}背景}{3}
\contentsline {section}{\numberline {2.1}コード生成言語}{3}
\contentsline {subsection}{\numberline {2.1.1}コード生成の例}{4}
\contentsline {section}{\numberline {2.2}shift0/reset0}{5}
\contentsline {section}{\numberline {2.3}コード生成とlet挿入}{6}
\contentsline {subsection}{\numberline {2.3.1}コードコンビネータ方式のプログラム例}{6}
\contentsline {subsection}{\numberline {2.3.2}コード生成におけるlet挿入}{7}
\contentsline {section}{\numberline {2.4}Scope extrusion}{10}
\contentsline {chapter}{\numberline {第3章}環境識別子による型システムの構築}{11}
\contentsline {section}{\numberline {3.1}先行研究のアイディア}{11}
\contentsline {section}{\numberline {3.2}本研究: 環境識別子の拡張}{13}
\contentsline {section}{\numberline {3.3}本研究: 型システムの構築}{14}
\contentsline {chapter}{\numberline {第4章}対象言語: 構文と意味論}{16}
\contentsline {section}{\numberline {4.1}構文の定義}{16}
\contentsline {section}{\numberline {4.2}操作的意味論}{17}
\contentsline {chapter}{\numberline {第5章}型システム}{20}
\contentsline {section}{\numberline {5.1}型付け例}{25}
\contentsline {subsection}{\numberline {5.1.1}let挿入の例}{25}
\contentsline {subsection}{\numberline {5.1.2}多段階let挿入の例}{26}
\contentsline {section}{\numberline {5.2}型安全性について}{27}
\contentsline {chapter}{\numberline {第6章}型推論}{28}
\contentsline {section}{\numberline {6.1}型システム$T_2$の導入}{28}
\contentsline {section}{\numberline {6.2}制約生成}{30}
\contentsline {section}{\numberline {6.3}制約の解消}{31}
\contentsline {subsection}{\numberline {6.3.1}typeinf1: 制約の解消アルゴリズム(前半)}{32}
\contentsline {subsection}{\numberline {6.3.2}typeinf2: 制約の解消アルゴリズム(後半)}{34}
\contentsline {chapter}{\numberline {第7章}実装}{37}
\contentsline {section}{\numberline {7.1}評価器}{37}
\contentsline {section}{\numberline {7.2}制約生成器}{38}
\contentsline {chapter}{\numberline {第8章}関連研究}{40}
\contentsline {chapter}{\numberline {第9章}まとめと今後の課題}{41}
\contentsline {chapter}{\hbox to\@lnumwidth {\hfil }謝辞}{42}
\contentsline {chapter}{\hbox to\@lnumwidth {\hfil }参考文献}{43}
\contentsline {chapter}{\numberline {付 録A }シンタックス}{45}
\contentsline {chapter}{\numberline {付 録B }評価器}{47}
\contentsline {chapter}{\numberline {付 録C }制約生成器}{50}
```

##### 型システム
Answer type modificationはなし
(Answer type は変わらないやつに限定している)

# これからやりたいこと
* 評価器の実装 (tagless final + GADT ? or data type を普通に定義してやっていく？)
  (tagless final + GADT においてGADTを使うのは，様々なanswer typeの列を入れるために多相なリストがほしいから)
  * 例を書く

* 型検査器の実装

* 型安全性の証明
  * 型保存定理
  * 進行定理

# やりたかったけどやれなさそうなこと
* 型推論アルゴリズム
* 型推論器の実装

# プラン
## 〆切 2017/1/11 15:30
11/1 - 12/31 あと2ヶ月．．．

### 10/31-11/6
* 評価器の実装
  * 例の充実のため
* `はじめに` のあとに，`背景` を書く
  * コード生成について
  * shift0/reset0 について？
  * で，こういうのが必要なのはこういうモチベーションがあるからって言う

#### やったこと
* `はじめに` を加筆
  * `背景` については `第2章 コード生成とlet挿入` の部分が背景を説明しているので割愛
* `関連研究` を追加

全体で1.5ページくらい増えた．
風邪でダウンしていたので進捗が芳しくない．
次の週で挽回したい．

### 11/7-11/13
* 型検査器の実装の方針を立てる <- 11/16 に先生とミーティング
  * 具体的な項に対して手で計算してみて，どういう風に作ればよいかを考える
* 評価器の実装を詰めていく
  * power関数とか gen_power 関数とか code + s0/r0 の例 を書いていく
  * 動かなかったら，先生に相談したりする
* 論文の図目次がきちんと出るように画像の挿入のtexを書き換える

#### やったこと
* 論文の図目次がきちんと出るように画像の挿入のtexを書き換えた

* 型検査の実装方針の検討
* 評価器 power関数 gen_power関数動かない

### 12/13-
* typeinf を実装 t0=t0 とか t1=t1 の型制約を解くところ型に関する部分(classifier以外) はunification とかは型推論する

sigma part つまり，shift0 のanswer typeの列の subsumption (小さいから大きいやつへ) を考える必要あり．

特に throw rule の k の sigma が合わない問題に対処する方法が必要

#### 解決法
* ```... throw k1 reset0 throw k2 reset0 throw k3 ... ```とするようにして(throw の間にreset0を入れる)，
  * reset0 のtyping rule を変更する(sigma part のところ) <- 今ところこれにしそう
  * あるいは，sigma part のみにたいする 一般の subsumption ルールを作る
  * こっちで行くことにした 20161227  `... throw k1 throw k2 throw k3 ... ` 間に reset0 は入れずに
throw rule を変更する．
throw rule が適用できない問題は k の型につく sigma と， answer type の sigma が合わないから，
使うときの k は answer type と同じというのがきつい制限なので，
それをもう少しゆるめる． 具体的には以下のようにする？
sub typing rule 使えば，`sigma = sigma'` のときも成り立つので良さそう．
しかし，sigma' を変数として型推論しないといけないので，実装がつらそう．
sigma の長さが事前にわかっていればうまくいきそうだけど，
pure でない任意の関数を kに入れられると，長さが不定なので困る．
pureな関数しか k には許さないとすればいけそうだが，，，

```
Γ, g0'>g0, g1'>g1, g2'>g2, k: <t1> = sigma => <t2> |- v : <t1>^g1 ∪ g2 ; sigma'
-------------------------------------------------------------------
Γ, g0'>g0, g1'>g1, g2'>g2, k: <t1> = sigma => <t2> |- throw k v : <t0>^g2 ; sigma'

sigma = <t0>^g0, <t1>^g1, <t2>^g2
sigma' = <t0'>^g0', <t1'>^g1', <t2'>^g2'
```

### 12/27
実装：
* 制約生成を出すところまで
  * デバッグのためにもプリティプリンタを作ったほうが良さそう

論文：
* 型システムの変更(throwのところ) とバグ潰し
* ３章のはじめくらいになぜ型システムを作るかの話をする
* 5章のところで，型システムのsubject reductionが成り立っていると，scope extrusion が起きないということの説明を書く． 証明は将来課題とする
  * 型保存に関して
    * subject reduction 予想これが示せると，なんでscope extrusionが起きないというと，．．．っていうのを書く． 証明はしない？
    * progress はやる？ progress の意味はなんだろう -> まあやるだけだからやろうか


#### 修士論文 self containedにする
* 一般的なところも書く

* 実装の章を入れる
  * 動いているコード例がほしい
  * こういう環境で動かした
  * 動いている例を載せる
  * 実装したコード自体は付録に載せる

* 証明のところについてはどうするか未定...
  * 5章のところで，scope extrusion が起きないということは書いていない．
  証明したらどう嬉しいのかを書く
  あるいは，
  8月のやつの型安全性を示すとか

* なぜ型システムを作るか 3章の最初くらい
  * 動的につけたいわけじゃなく，静的につけたい
  * 大石 型システムで型がつかないやつを例にあげる

* 型保存に関して
  * subject reduction 予想これが示せると，なんでscope extrusionが起きないというと，．．．っていうのを書く． 証明はしない？

  progress はやる？ progress の意味はなんだろう -> まあやるだけだからやろうか

reset0 の直前直後に sigma part の subsumption を付ける？

### 優先度付きTODO: 修士論文
1. 1/8(日)までに 6章 型推論アルゴリズム のところを論文にする
   * 制約生成，制約解消 をアルゴリズムの形としてスッキリ見やすくさせる．
1. 型推論アルゴリズムのところを整理する．ちゃんと動く形のアルゴリズムにする
1. 型システムの健全性の証明 (subject reductionが成り立てば，scope extrusionが起きない)
1. 制約生成アルゴリズムの実装(型推論アルゴリズム)
1. 制約解消アルゴリズムの実装(型推論アルゴリズム)
1. sigma part subsumption ルールについて色々バリエーションがある
   * reset0 の直前に sigma part の subsumptionルールを付けるのはやめて，throw の直後に sigma part の subsumptionをつけることにした (now: 2017/1/17)
     throw の kのsigma と 全体の型のsigma とが一致してないと型付けできなかったのを，sigma の条件をゆるめることにした．本来なら，throw 以外でも sigmaの条件を緩めるほうが良いが，(実装が猥雑になりそうなので)とりあえず，throwだけ変えてる．(多段階let挿入の例はちゃんと型付けされるので)
     throwルールはこんなふうにしてる
    ```
    Γ, k: <t'> = <t2>^g2, sigma => <t2> |- e : <t'>^g1 ∪ g2 ; <t1>^g2, sigma       Γ |= g1 > g2
    -------------------------------------------------------------------------------------------------
    Γ, k: <t'> = <t2>^g2, sigma => <t2> |- throw k e : t ; <t1>^g1, sigma
    ```
    reset0ルールを変更するのなら，以下のようにする
    ```
    Γ |- e : <t1>^g1 ; <t1>^g2, sigma       Γ |= g1 > g2
    -------------------------------------------------------------------------------------------------
    Γ |- reset0 e : <t1>^g1; sigma
    ```
   or
   * sigma part のsubsumption ルール本体を 型システムに導入 (型推論アルゴリズムが難しくなりそう) or
   * sigma part の先頭要素のみだけでなく，sigma part 全体の subsumptionルールの導入 or
   * などなど

### 2017/1/10 これからのスケジュール
* 1/14くらいに 水谷先生にメールする．
  * 今実装を直していて，それに合わせて，修論も少し変更が必要なので，1/18,1/19,1/20 の間に修論を渡したいと考えている．1/18-20で水谷先生の都合の良い日はいつか聞く．
  * 1/18-1/20 副査(水谷先生)にfixした修論を送る．(これが最終のfix)
  * この時に 水谷先生，海野先生，亀山先生 に渡すようの紙での修論(製本したやつ)を作る．亀山先生にわたすやつは，背表紙とか全部整えたやつを渡す(1/11に出したのと同じ体裁にする)
* 1/27 発表

#### スライド作成
ソフトウェア学会並の詳しさで大丈夫？
* 型推論のところを主に説明

* この修論で達成したこと
* 問題点
* どう解決したか
  * アイデア
  * 実装とかの例とか出せれば良い

##### 構成 25分-23分
* 概要
* 問題
* 解決方法
* やったこと，できること
* まとめ

#### 修論
* 型システム
  * ✔ 型システムの各規則がダラッと並んでるので，それを区切りを入れて見やすく．
  * ✔ 型システムのところで， sigma を sigma-part と呼ぶことにすることわりを書いておく．
  * ✔ で，型推論アルゴリズムで sigma-part の変数を sigma変数と呼んで sigma_x と書くって書く．

* 型推論アルゴリズム
  * lambda_ で，sigma変数が使われるので，sigma-part の制約も生成される．それの解消アルゴリズムが必要．

* 実装の章を増やす(復活させる) プログラム実装はそのままいれるか
  * 制約生成のところまでは終わらせる．
    * 制約生成の実行例を書く．
  * 制約解消については，今後行う．って書く．
  * 下から上に型付けをしていき，制約を生成していく
  対応する型付け規則がなければそこでとまる．型とclassifier，sigma-partに関する制約が出てくる
  ここでは多段階let挿入が制約生成がきちんとできることを確認した(制約が出た例を見せる)
  制約解消は今進行中である

#### 実装
* 制約生成のところまで．
  * 多段階let 挿入の実行例は動かしたい．
* 今回1/27 では，制約生成ができましたよってところまで．
  * 制約解消については実装できてないので，今後の課題とする．

### 修論について
* `|-^ γ` の型判断 の `sigma` は `.` とするみたいな断り書きを入れて，全体の型システムをそのように変更する必要あり
* 型システム T2 throw規則 変更の一考必要あり，reset0 のほうに sigma-part のsub sumption を導入すべき？
* 制約解消のところ，unify1 のアルゴリズム sigmaのところ変更すべし sigma > sigma はなくなったので，その場合については消すべし
* 制約解消については，最後に 固有変数条件をみたすかどうかのチェックが必要．具体的には 型文脈Γ において，d1 を含む不等式の制約が成り立つかどうかをチェックする

T1 code規則 を
```
Γ |-^γ e : t^1 ; .
-------------------------------------------------------------------------------------------------
Γ |- <e> : <t^1>^g1; sigma
```
このようにする
