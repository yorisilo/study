# Memo


## 1 Intro
"A Gentle Introduction to Multi-stage Programming"のpart 1では，

1. インタプリタを書いて，その正当性をチェック
2. ステージングの annotation を加えることにより ステージインタプリタへ
3. ステージングの実装のパフォーマンスのチェック

の3つのステップからなるアプローチを紹介した．
3つめのステップに到達した時，満足するステージングに到達するために，CPSへの変換が必要であると予期すべきである．

part 1 では，Lint と呼ばれるシンプルな言語に焦点を当てていた．
* Lint: intergerという1つの型のみを持ち，integerからintegerへの関数のみを持つような言語

part 2 では， Aloe と呼ばれる Scheme 言語のサブセット言語に焦点を当てる．
動的型付け言語を実装することができるというように，ステージングの専門知識のレパートリーを拡大することを目的とする．


## 2 Parse

* S式の定義
```
s-expression ::= integer | symbol | string | (s-expression*)
```
上記のs-expression のシンタックスの式に対して，パースが成功すると，
以下の様なocamlの型の値が返ってくる．

```OCaml
type sxp =
| I of int (* Integer *) | A of string (* Atoms (symbols) *)
| S of string (* String *) | L of sxp list (* List *)
```

* 例

S式のリスト (1 2 3 4) は

```OCaml
L [I 1; I 2; I 3; I 4]
```

((1 2) (3 4)) は

```OCaml
L [L [I 1; I 2]; L [I 3; I 4]]
```

(lambda (x) (repeat x \"ping \")) は

```OCaml
L [A "lambda"; L [A "x"]; L [A "repeat"; A "x"; S "ping "]]
```

というようなOCamlの型の値となる．

## 3 An Interpreter for Aloe
## Aloe用のDSLをocamlで書く
Aloeとは，
bool, integer, string, mutable variable, mutable list, higher-order function を含む
scheme のサブセット言語である．

型なしの言語のインタプリタを書くときに考慮すべき最初のことは，言語がサポートする値の種類を決定することである．
Aloeに対して，以下の値の種類に興味がある．


```OCaml
type dom = Bool of bool
         | Int of int
         | Str of string
         | Fun of int * (dom list -> dom)
         | Undefined
         | Void
         | Empty
         | Cons of dom ref * dom ref
```

#### 3 base types
* booleans
* integers
* strings

#### function
* 各関数の値は，それが期待する引数の個数を表す整数でタグ付けされる．

#### Undefined と Void
* Undefined は初期化されていない場所に対して使用される．
* Void は 副作用のある計算から結果が存在しないことを示すものである．

### 3.2 Exceptions and Untagging
Aloe プログラムの計算中にエラーが出る可能性のために OCamlの例外を導入する

```OCaml
exception Error of string
```

タグ付けされた(FunとかBoolとかIntとか...)値に対して，そのタグを取り除く関数を定義するときに上記の例外を使用する．

```OCaml
let unFun d =
  match d with
    | Fun (i,f) -> (i,f)
    | _ -> raise (Error "Encountered a non-function value")
```

### 3.3 Environments and Assignable Variables

```OCaml
let env0 x =
  raise (Error ("Variable not found in environment "^x))
```
* env0 : 空の環境を表す関数

```OCaml
let ext env x v = fun y -> if x=y then v else env y

```

* ext : 環境の中の一つの変数に対して新しいbindingを与える関数


```OCaml
let rec lext env xl vl =
  match xl with
  | []    -> env
  | x::xs -> match vl with
             | [] -> raise (Error "Not enough arguments")
             | y::ys -> lext (ext env x y) xs ys
```

* lext: 一気に，環境の中の複数の変数に対して，bindingを与える関数

重要なこととして，Aloe言語はSchemeのサブセット言語であるので，
OCamlで実装するときにいくつかの変数は割り当てることができるが，全ての変数は割り当てることができないということである．
例えば， Aloeの関数の引数は不変である．（関数の部分適用とかできない）
この違いを反映するために，全ての環境には，型の値に名前をマップする必要がある．

```OCaml
type var = Val of dom | Ref of dom ref
```

##### footnote
環境をfirst-orderなcollection 型でなく関数として表現するのに驚くかもしれない．
プログラム言語のセマンティクス，特にdenotational あるいは translational なセマンティクスを研究するときには，環境を単に関数として考えるのが一般的である．



### 3.4 Concrete Syntax
前述したように，Aloe言語のための抽象構文を表現するために，S式のOCamlのデータ型を使用する．
それにもかかわらず，まだ，我々が興味を持っている言語の具体的な構文を述べることが有用である．

As noted earlier, we use the OCaml data type for s-expressions to represent the abstract syntax for our programs. Nevertheless, it is still useful to state the concrete syntax for the language that we are interested in.

```
I is the set of integers
S is the set of strings
A is the set of symbols ("A" for "Atomic")

U ::= not|empty?|car|cdr
B ::= + | - | * | < | > | = | cons | set-car! | set-cdr!
E ::= true | false | empty | I | "S" | A | (U E) | (B E E)
      | (cond(E E)(elseE))|(set!AE)|(andE E*)|(orE E*)
      | (begin E E*) | (lambda (A*) E) | (E E*)

P ::= E | (define A E)P | (define (A A*) E)P
```

* I : integer 負の記号の後に数字のシークエンスとして定義されている．
* S : string 文字のシークエンス
* A : symbol (atom) スペースの存在しない文字のシークエンス

* U : unary operator (単項演算子)
* B : binary operator (二項演算子)
* E : expression  bool値，空のリストを表す empty が含まれていて，integer, string, symbol を埋め込む．で，ここで，注意することとしては，symbolに関しては曖昧性があることである．

例えば， true っていう expression は E の定義の true ってやつと A っていうやつのいずれかに一致する．このような理由から，文字列の導出は常に，E の定義の一番左のやつから検討していく．

The set of expressions E contains terminals to denote booleans and the empty list, and it also embeds integers, strings, and symbols.
When we get to symbols, the user should note that there is a possibility for ambiguity here.

The expression true, for example, can match either the first or the sixth (symbol) production. For this reason we consider our productions order dependent, and the derivation of a string always uses the production that appears left-most in the definition. This does not change the set of strings defined, but it makes the derivation of each string unique. The significance of the order of production is also important for ensuring the proper behavior from the main case analysis performed in the interpreter.

* P : program  プログラムは，式，または，変数や関数定義のネストされた配列

##### Note 1 (Practical Consideration: Validating the Reference Interpreter)
Note 1 (Practical Consideration: Validating the Reference Interpreter). We caution the reader that even though Aloe is a small language, we spent considerable time removing seemingly trivial bugs from the first version of the interpreter. Staging provides no help with this problem, and in fact any problems present in the original interpreter and that go unnoticed are also present in the staged interpreter. Thus, we strongly recommend developing an extensive acceptance test that illustrates the correct functionality of each of the language constructs while developing the original interpreter. Such tests will also be useful later when developing the staged interpreter and when assessing the performance impact of staging.
A helpful by-product of using both the syntax and the semantics of Dr. Scheme for Aloe was that it was easy to validate the correct behavior of our test examples using the standard Dr. Scheme implementation. Because the correctness of language implementations is of such great importance, the benefits of devising a new syntax for your language should be weighed carefully against the benefits of having such a direct method of validating the implementation. This is not just relevant in cases when we are evaluating new implementation technology such as staged interpreters. Consider how the development of ML implementations could have been different if it used Scheme syntax, or XML if it used s-expression syntax. Change in syntax can often impede reuse and obfuscate new ideas.

### 3.5 The Interpreter for Expressions
Aloe のインタプリタは，主に2つの関数で構成されている．

* eval : 式(expression)に対するインタプリタ（まあインタプリタというよりは評価器）
* peval : プログラムに対するインタプリタ

である．
シンタックスが提示する順序に従うために，まずeval関数が式に対しての評価を行い，式と環境を引数に取り，値を返す．

It is structured primarily as a match statement over the input expression. The match statement is surrounded by a try statement, so that exceptions are caught immediately, some informative debugging information is printed, and the exception is raised again. Thus, the overall structure of the interpreter is as follows:

```OCaml
let rec eval e env =
  try (match e with
      ...)
  with
      Error s -> (print_string ("\n"^(print e)^"\n");
                  raise (Error s))
```

...はeval関数のbodyである．

The reader should note that we choose to have the interpreter traverse the syntax represented by s-expressions to save space. This choice makes the different branches of the match statement order sensitive. Thus, this tutorial does trade good interpreter design for presentation space. The reader interested in better interpreter design is encourage to consult a standard reference [3].

##### Note 2(Practical Consideration: Reporting Runtime Errors)

Our Aloe interpreter provides minimal contextual information to the user when reporting runtime error. More comprehensive reporting about errors as well as debugging support would not only be useful to the users of the language but would also help the implementor of the language as well. Thus, these issues should be given careful consideration when implementing any language of size comparable to or larger than the Aloe.


#### Atomic Expressions, Integers, and Strings
Aloe の中で，原子式 (atomic expressions) の semantics は非常に簡単である．

```ocaml
| A "true" -> Bool true
| A "false" -> Bool false
| A "empty" -> Empty
| A x -> (match env x with
         |Val v -> v
         |Ref r -> !r)
| I i -> Int i
| S s -> Str s
```

true, false, empty は そのまま解釈される．
で，それら true, false, empty に一致しなかったsymbolのケースに対して，
環境内の名前をlook up することによって解釈されるように変数は定義されている．
環境へのlook upは失敗する可能性がある．なので，文字列である x にenv を適用すると例外が発生することがある．

If we do get a value back, the interpreter checks to see whether it is assignable or not. If it is a simple value, we return it directly. If it is an assignable value, then we de-reference the assignable value and return the value to which it is pointing.

#### Unary and Binary Operators
単項演算子と二項演算子に関しては多少複雑になる．しかし大部分はまだ直接的である．

```ocaml
| L [A "not"; e1]   -> Bool (not (unBool (eval e1 env)))
| L [A "+"; e1; e2] -> Int (  (unInt (eval e1 env)
                            + (unInt (eval e2 env))))
```
Aloe の論理否定は 引数を評価し，ブールタグを除去した値に対して，OCamlの論理否定を適用し，その得られた値にBoolタグを付ければ良い．

The pattern of untagging and re-tagging repeats in our interpreter, which is a necessity when being explicit about the semantics of a dynamically typed language. Because OCaml is statically typed, this forces us to make the tag manipulation explicit. While this may seem verbose at first, we see in later discussion that being explicit about tags may be convenient for discussing different strategies for implementing the same dynamically typed computation.

cons演算子について，

```ocaml
| L [A "cons"; e1; e2] ->
  Cons (ref (eval e1 env), ref (eval e2 env))
```

このlistのconsの実装は，e2 がリストであることを確認していない．

次にset-car! について，

```ocaml
 | L [A "set-car!"; e1; e2] ->
   (match (eval e1 env) with
    | Cons (h,t) -> (h:=(eval e2 env);Void)
    | _ -> raise (Error ("Can’t assign car of " ^ (print e1))))
```
最初の引数 e1 を評価し，それが，空でないリストであれば，第二引数 e2 を評価し，リストの先頭に，その評価結果を代入する．

#### Variable Arity Constructs
* Arity 引数の個数

プログラミング言語によっては，可変な引数を許可するのは珍しくない．
1つ以上の引数をとり，そらら全てが等しい整数である場合にのみ trueを返す．

```ocaml
| L ((A "=") :: e1 :: l) -> Bool (let v = unInt (eval e1 env) in
                              let l = List.map (fun x -> unInt (eval x env)) l
                                in List.for_all (fun y -> y=v) l)

```

まず，最初に引数 e1 が評価されて，Intタグが除去される．これは，"="という演算子が整数に対してのみ動作するように意図されているという事実を反映している．
その後，引数 l (リスト) の要素に同一の操作を行うmappingを行う．
最後に，そのリストのすべての要素が最初の要素 e1 と等しいかどうかを確認する．
論理積と論理和も似た方法で実装されている．


#### Conditionals and Syntactic Sugar

条件式を定義するのは簡単である．
しかし，私達は条件式の引数の個数を2つの引数に制限し，...
However, we limit them to having two arguments and leave the generalization as an exercise to the reader in applying the variable arity technique presented above.

シンタックスシュガーに対処する方法を説明するために条件文を使用する．
特に，de-sugard な式にインタプリタを適用することが再帰呼び出しによって可能ならば．

```ocaml
| L [A "if"; c2; e2; e3] -> eval (L [A "cond"; L [c2 ; e2]; L [A "else"; e3]]) env

```

The key issue that requires attention using this technique to support syntactic sugar is that the we should make sure that it does not introduce non-termination. While this may seem inconsequential in a setting in which the language being interpreted can itself express diverging computation, the distinction between divergence in the interpretation and divergence in the result of the interpretation will become evident when we stage such interpreters.


#### Lambda Abstraction
ラムダ抽象の引数が1つのみであるなら，ラムダ抽象の解釈は1行で表現できる．

```ocaml
| L [A "lambda" ; L [S x] ; e] ->
   Fun (1, fun l -> match l with
                    [v] -> eval e (ext env x (Val v)))
```

1つのみの引数に対してのパターンマッチングとして必要なのは，その引数がstringであることと，そのstringの値がxへのboundとなっていることである．
そのパターンはきっかり1つの式であることが必要である．
その解釈はFunタグが付いた値を返す．そのFunタグが付いた値は 1つ目はそれが期待する引数の個数を表し（この場合は1）．2つ目はOCamlのラムダ抽象であり，それは，1つの要素のみからなるリストを引数と取る．
そのOCamlのラムダ抽象の結果は，Aloeのラムダ抽象のbodyである式 e を評価した結果である．
この式の評価は，環境 env のもとで，name x から値 Val v へのマッピングによって生じる．
ラムダ抽象の引数を1つに固定させるという事実を反映するために，vにタグ Val を付ける．

Aloeでは，ラムダ抽象は複数の引数を扱うことができるという事実を処理するために，
以下の様な事を行う．多少複雑になるが，引数が1つの時とやってることは本質的には変わらない．

```ocaml
| L [A "lambda" ; L axs ; e] ->
    let l = List.length axs
    in Fun (l, fun v ->
                 eval e (lext env
                         (List.map (function A x -> x) axs)
                         (List.map (fun x -> Val x) v)))
```

Here, we are simply allowing the argument to be a list of names and handling this extra degree of generality by mapping over lists and using the function for extending the environment with a list of mappings (introduced earlier).

#### Function Application
まず，single-argument function の場合を考慮すれば，ラムダ抽象の場合と同様に理解しやすい．

```ocaml
| L [e1; e2] -> let (1,f) = unFun (eval e1 env) in
                let arg = eval e2 env
                in f [arg]
```
パターンマッチでは，e1 は1つの引数を持つ関数であることを前提としている．
まず最初の let statement では，式e1を評価し，Fun タグを除去する．
第一成分が1であり，第二成分がfである．
次のlet statement では，e1の引数であるe2 を評価し argとしている．
最後に 1引数関数であるfにシングルトンリスト[arg]を渡す．


一般的な関数適用は次のとおりである．

```ocaml
| L (e::es) ->
   let (i,f) = unFun (eval e env) in
   let args = List.map (fun e -> eval e env) es in
   let l = List.length args
   in if l=i
     then f args
     else raise (Error ("Function has "^(string_of_int l)^
                        " arguments but called with "^(string_of_int i)))
```

まず，e を評価し，
それから es の要素全てに対して評価を行っていき，その結果を args(dom list) とする．
それからargsの個数と e の期待する引数の個数とが一致していれば，関数適用を行い，
それ以外の場合は，エラーが発生する．

### 3.6 The Interpreter for Programs
peval(Aloeプログラムのインタプリタ．まあ評価器)という関数は，
プログラムと環境を引数にし，値を返す．
式と比較して，Aloe プログラムは比較的単純である．

```ocaml
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
```
* 最初のケースは，プログラムが1つの式でできている場合である．
その場合は，1つの式を要素に持つシングルトンリストなので，単にその式に対してevalを適用する．

* 2つ目のケースでは，ステートメントをdefineしている．
まず，rを特別な値として，reference cell として Undefinedという値に初期化する．
次に，この r に定義しようとしている変数をマッピングする現在の環境の拡張を作成する．
次に，参照の本体を評価する．
最後に r をアップデートし，拡張された環境でのプログラムの残りの部分の評価を行う．

The second case is a define statement.
We wish to interpret all define statements as recursive, and there are many ways in which this can be achieved.
In this interpreter, we employ a useful trick that can provide an efficient implementation in the presence of side effects in the interpretation,
we create a reference cell initialized to the special value Undefined.
Then, we create an extension of the current environment mapping the variable that we are about to define to this reference.
Next, we evaluate the body of the reference.
Finally, we update the reference with the result of the evaluation of the body and continue the evaluation of the rest of the program in the extended environment.

Clearly, this technique only produces a useful value if the definition of the variable that we are about to define is not strict in its use of that variable.

* 3つ目のケースは，上記の特別な場合として，ラムダ抽象あるいは関数値を生成する場合のケースである．(遅延ストリームを表現するためによく使用される．)
  * 遅延ストリーム : 必要となった時に新しいデータを生成すること．

This is generally the case, for example, if the definition is a lambda abstraction or an operation that produces a function value (which are often used, for example, to represent lazy streams).

* 最後のケースは，それ以外の構文となった場合を表し，エラーが発生する．

The last case of the interpreter produces an error if any other syntactic form is encountered at the top level of a program.
With this, we have completed our overview of the key features of the reference interpreter for the Aloe language.


## 4 Converting into Continuation-Passing Style (CPS)
Consel と Danvy は部分的に評価する前に，CPS変換プログラムの有用性を示した．
同じことがステージングの前のプログラムに対しても言える．

直感的に言うと，静的に条件を知ることさえなく，CPS変換のプログラムは特別な機会を全ての条件のステートメントのブランチで持っている．

Consel and Danvy [1] recognized the utility of CPS converting programs before they are partially evaluated. The same is observed for CPS converting programs before they are staged [9,7]. Intuitively, having a program in CPS makes it possible to explore specialization opportunities in all branches of a conditional statement even when the condition is not statically known.
We begin this section with a brief review of CPS conversion, and then proceed to discussing the CPS conversion of the interpreter that we developed above.

### 4.1 CPS Conversion

Consider the Fibonacci function, which can be implemented in OCaml as follows:

```ocaml
let rec fib n = if n<2 then n else fib (n-1) + fib (n-2)

```

This function has type int -> int. Converting this function into CPS yields the following:

```ocaml
let rec fib_cps n k = if n<2 then k n else fib_cps (n-1)
                                             (fun r1 -> fib_cps (n-2)
                                                          (fun r2 -> k (r1 + r2)))

let k0 = fun r -> r
let fib n = fib_cps n k0
```

Where fib_cps is a function of type int -> (int -> ’a) -> ’a. This new code is derived as follows.

#### Functions Get an Extra Parameter

We add the extra parameter k to the function that we are converting. This parameter is called the continuation, and its job is to process whatever value was being simply returned in the original function. So, because the original function returns a value of type int, the con- tinuation has type int -> ’a. This type confirms that the continuation is a function that expects an integer value. It also says that the continuation can return a value of any type: CPS conversion does not restrict what we do with the value after it is “returned” by applying the continuation to it. Note, how- ever, that the final return value of the new function (fib_cps) is also ’a. In other words, whatever value the continuation returns, it is also the value that is returned by the converted function.


#### ...


### 4.2 Effect of CPS Conversion on the Type of the Interpreter
part 1で述べたように，ステージングする前に，プログラムをCPS変換することは一般的に有用である．
As noted in Part I, it is generally useful to convert a program into CPS before staging it. To convert our interpreter for the expressions

```ocaml
eval : sxp -> (string -> var) -> dom
```
CPSは体系的にコードを書き換える必要があり，
1. 全ての関数呼び出しに余分な継続という引数を取り，
2. 単に元のコードに返される全ての値にこの継続を適用する．


これは，以下の様な新しい関数をもたらす

```ocaml
keval : sxp -> (string -> var) -> (dom -> dom) -> dom
```

### 4.3 CPS Converting the Interpreter
We now turn to CPS converting the code of an interpreter similar to the one for Aloe. We conclude the section by reporting the results of running our timing experiments on the CPS-converted interpreter.

### 4.4 Taking in the Continuation
eval関数の最も外側の構造に対して，僅かな変更が必要である．

```ocaml
let rec keval e env k =
  try
    (match e with
     ...)
  with Error s -> (print_string ("\n"^(print e)^"\n");
                   raise (Error s))

```
継続をあわらす k という引数を加えた．
k は もとのeval関数に戻された全ての値にeval関数の残りの部分に適用する関数である．

In the first line, we have added an extra parameter k, through which we pass the continuation function. This is the function that we apply in the rest of the interpreter to every value that we simply returned in the original interpreter.
A natural question to ask when we consider the next line is: why not simply add an application of k around the try statement, and be done with the con- version to CPS? While this would be valid from the point of view of external behavior, to achieve our goal of effective staging, it is important that we push the applications of the continuation k as far down as possible to the leaves of our program. In particular, this means that we push the applications down over try statements and match statements.
A useful observation to make at this point is that pushing this single ap- plication of the continuation from around a match statement duplicates this application around all the branches. While this duplication is inconsequential in normal evaluation of a match statement, it is significant when evaluating the staged version of a match statement.

### 4.5 Match Statements and Primitive Computation

次に match 文の各枝について見ていく，

単に値を返すという簡単なケースでは，
単純に この値に継続 k を適用する．

```ocaml
| A "true"   -> k (Bool true)
| A "false"  -> k (Bool false)
| A "empty"  -> k (Empty)
```

### 4.6 Match Statements and Primitive Computation

変数の場合は，2つのポイントがある．

1.


### 4.7 Simple, Non-Primitive Function Calls
関数呼び出しは，新しい関数を呼び出して，もとの関数の呼び出しに書き換える事によって変換される．



### 4.8 Extending Continuations and Naming Intermediate Results
一般的に言えば，しかしながら，直接再帰呼び出しを同じ（異なる引数の）関数が再帰関数の1つのケースがもつのは例外であり，ルールではない．

再帰呼び出しのための継続が現在の継続 k でない時，どのような継続を渡せばよいのだろうか．

基本的なルールとしては，変換をしようとしているもとの式の中の再帰呼び出しを囲む計算を見ることである．

もとの結果で起こることは何でも，再帰呼び出しに渡す継続は現在の継続が適用される前に実行する必要がある．

例として論理否定をみてみよう．

```ocaml
| L [A "not"; e1] -> keval e1 env (fun r ->
                                   k (Bool (not (unBool r))))

```

```ocaml
| L [A "not"; e1]   -> Bool (not (unBool (eval e1 env)))
```

と比較して，CPS変換したコードのほうは，inside-out 式 となっている．
* inside-out 式 : 一番内側の再帰呼び出しを一番外側にしている．
