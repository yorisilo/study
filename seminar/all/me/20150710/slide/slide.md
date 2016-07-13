class: center, middle

<!-- ruby -run -ehttpd . -p8000 -->

# 全体ゼミ

20150710

大石純平

---


# 論文紹介します

* A Gentle Introduction to Multi-stage Programming, Part II

* Walid Taha

---

# 1 Introduction
A Gentle Introduction to Multi-stage Programming のpart I では，

1. インタプリタを書いて，その正当性をチェック
2. ステージングの annotation を加えることにより ステージインタプリタへ
3. ステージングの実装のパフォーマンスのチェック

の3つのステップからなるアプローチを紹介した．
満足するステージングに到達するために，CPS変換が必要である．

part 1 では，Lint と呼ばれるシンプルな言語に焦点を当てていた．
* Lintは， intergerという1つの型のみを持ち，integerからintegerへの関数のみを持つような言語

part 2 では， Aloe と呼ばれる Scheme 言語のサブセット言語に焦点を当てる．
型のタグを付けたり，外したりということが Over head となる．

動的型付け言語を実装することができるというように，ステージングの専門知識のレパートリーを拡大することを目的とする．


---

# 2 Parsing

---

# 3 An Interpreter fo Aloe

---

# 4 Converting into Continuation-Passing Style (CPS)

---

# 5 Staging the CPS-Converted Interpreter

---

# 6 The Interpretation of a Program as Partially Static Data Structures

---

# 7 Conclusions
