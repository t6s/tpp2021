<link rel="stylesheet" href="{{site.github.url}}/css/tpp2020.css" charset="utf-8">

# The 17th Theorem Proving and Provers meeting (TPP 2021)

TPP (Theorem Proving and Provers) ミーティングは，
2005年から年に1回開催され，
定理証明系を作っている人から使う側の人まで幅広い人たちが集まり，
様々な側面からの話をしてアイディアの交換をしてきたものです．

ミーティング期間中の討論を大切にしたいと考えていますので，
出来上がった仕事の講演だけでなく，
進行中の仕事，未完成の仕事についての講演も歓迎します．
参加者には可能な限りご講演いただくことを期待しています．

TPP is a series of annual meetings for developers
as well as users of theorem provers.
Discussions from various aspects and exchanges
of ideas have taken place in the past meetings since 2005.

We regard the discussions during the meeting to be most important.
As such, not only the talks about completed work, but those about ongoing 
work and half-baked work are also welcome.
We hope all participants would consider giving a talk.


## 開催日程（暫定）/ Date (tentative)
2021年9月6日(月), 7日(火) / Mon. 6th to Tue. 7th, September.

## 会場 / Venue
北見工業大学 A106講義室 / Kitami Institute of Technology, Room A106

コロナウイルス感染症 (COVID-19)の感染拡大状況に応じ,
今年度もオンライン(Zoom)で開催する可能性があります. 

開催日が近付きましたら決定してメーリングリストにてお知らせします. 

According to the spread of coronavirus infection (COVID-19), 
we may switch to an online meeting (Zoom).

We will decide later whether we go online, and announce on the mailing list.

## 住所 / Address

〒090-8507 北海道北見市公園町165番地 / 165 Koen-cho, Kitami, Hokkaido 090-8507
[アクセス](https://www.kitami-it.ac.jp/about/access/) / [Access](https://www.kitami-it.ac.jp/about/access/)


## 懇親会 / Dinner Party
未定
<!--
- 日時: 11/16 18:30～ / Time: 16th Mon. 18:30～
- 会場 / Place: オンライン(Zoom)
-->

## 幹事 / Organizer

才川隆文 (名古屋大学) /
Takafumi Saikawa (Nagoya University)

Email: tscompor&lt;at&gt;gmail.com

松田一徳 (北見工業大学) /
Kazunori Matsuda (Kitami Institute of Technology)
Email: kaz-matsuda&lt;at&gt;kitami-it.ac.jp

<!--
## 参加申し込み / Registration
9/1(水)までに / Please register by 1st September from

<span style="font-size:150%">
[こちらから / here](tps://docs.google.com/forms/d/e/1FAIpQLSceNfw0KZRPFjw9FMe2m5NJ3RGDCnJOtYbJgxktdOl4RxWQdA/viewform)
</span>

-->

## プログラム / Technical Program
### Sep. 6

<!--
* 15:10 **Opening; On TPP Mark 2020** (30min) ([slides](tpp2020-nakasho.pdf)) <br/>
  中正 和久 @ 山口大学

* 15:40 **可換代数の形式化** (20min) ([slides](tpp2020-watase.pdf)) <br/>
  渡瀬 泰成<br/>

* Break (10min)

* 16:10 **MIZAR数学ライブラリの依存関係に関する研究** (20 min) ([slides](tpp2020-shigenaka.pdf)) <br/>
  重中 晟吾 @ 山口大学大学院<br/>
  Mizarのライブラリ(Mizar Mathematical Library：MML)には依存関係を
一覧することができないという課題があり，ライブラリメンテナンスの障害となっていた．
本研究では，Mizarライブラリの依存関係をグラフ化することによって可視化した．
グラフの描画には，階層グラフ描画及び力学モデルを用いたグラフ描画を用いた．
さらに，視認性の向上を図るために，任意のノード周辺の依存関係を強調表示する機能，
任意のノード(article)を検索する機能，任意のノードを動かすことのできる機能を実装した．

* 16:30 **Rings, categories and schemes in Coq/SSReflect** (20 min) ([slides](tpp2020-qi.pdf))<br/>
  QI, Xuanrui @ 名古屋大学多元数理科学研究科<br/>
  We report on our ongoing efforts of formalizing algebraic geometry in
Coq/SSReflect/MathComp, starting with the notion of a scheme.
Modern algebraic geometry is the result of synthesizing of many areas
in mathematics, and defining the notion of a scheme requires concepts
and results in multiple areas of mathematics, particularly commutative
algebra and category theory. We use packed classes to define a hierarchy
of rings and categorical structures, and use this hierarchy to formalize
the notion of an affine scheme. This talk presents unfinished work,
and the author welcomes all kinds of feedback.

* Break (20min)

* 17:10 **Mizar数学ライブラリをホスティングするWebプラットフォームの研究** (20 min) ([slides](tpp2020-yamamichi.pdf)) <br/>
  山道 大地 @ 山口大学大学院<br/>
  近年、Mizarライブラリの増加により，ライブラリを読解する時間が増加していることが問題となっている．
従来研究されてきた対策はいくつかあるが，可読性が低く，形式言語の更新に追従できなかった．
このような問題を解決するために，私の研究では，形式言語にTeX 形式の解説を併記すると共に，
解説をライブラリの更新に追従させることができるプラットフォームを作成している．

* 17:30 **定理証明支援系Mizarによる記述を補助するエディタ拡張機能の研究** (20 min) ([slides](tpp2020-taniguchi.pdf))<br/>
  谷口 広途 @ 山口大学大学院<br/>
  本研究では，数学の書式に近く，可読性が高い定理証明支援系 Mizar を支援するための
エディタ拡張機能「Mizar Extension」を開発している．
本講演では，Mizar Extensionの現状と今後について発表する．

* 17:50 **Mersenne-Twisterの形式化** (20 min) ([slides](tpp2020-saikawa1.pdf)) ([preprint](tpp2020-saikawa2.pdf))<br/>
  才川 隆文 @ 名古屋大学<br/>
  乱数生成器Mersenne-Twisterの、Coq + Mathcompでの形式化について、進行中の仕事を紹介する。
アルゴリズムの形式化とCプログラムの抽出、長周期性の証明に必要ないくつかの代数的性質が証明が、
これまでにできている。多項式の既約性判定がまだできていない。

* Break (20min)

* 18:30 **Dinner Party**
-->

## TPPmark 
後日出題します.

<!--

<span style="color: red">modified at 20:30, Sep. 28th, 2020</span>

SAT/SMTソルバで解を探索するような問題にしてみました．それぞれ手証明も可能です．回答は nakasho <at> yamaguchi-u.ac.jp まで送付をお願いします．

I made problems to find the solutions using SAT/SMT solvers. You can also prove them without solvers. Please send your answer to nakasho <at> yamaguchi-u.ac.jp.

### 問1.
124本のベクトルからなる集合 X = {(x,y,z) | x,y,z ∈ {0,±1,±√2}} \ {(0,0,0)} の各要素を白または黒に塗り分けることを考えます．
このとき，次の2条件 a), b) を満たすようにベクトルを白または黒に塗り分けることはできないことを証明してください． 
- a) 2つの直交するベクトルのうち，少なくとも1本は黒色である． 
- b) 互いに直交し合う3つのベクトルのうち，少なくとも1本は白色である． 

Consider painting each element of the set X = {(x,y,z) | x,y,z ∈ {0,±1,±√2}} \ {(0,0,0)} of 124 vectors white or black.
Prove that the vectors cannot be painted white or black in such a way that the following two conditions a) and b) are met. 
- a) Whenever two of the vectors are orthogonal, at least one is black. 
- b) Whenever three of the vectors are mutually orthogonal, at least one is white. 

### 問2. 
条件 c) を満たしつつ，条件 a) と b) の少なくとも一方は成り立たないように，ベクトルの集合 X からできるだけ多くの要素を減らしてください． （ヒント: 33本までは減らせることが知られています．）
- c) 集合内に互いに直交し合う3つのベクトルの集合が少なくとも1つは存在する．

Reduce as many elements as possible from the set of vectors X such that at least one of the conditions a) and b) does not hold while condition c) is satisfied. (Hint: It is known that you can reduce the number to 33.)
- c) There is at least one set of three mutually orthogonal vectors in the set. 

### 問3.
より一般的に n 次元 (n > 3) の場合に拡張してください．
このとき問題は，条件 c') を満たしつつ，条件 a) と b') の少なくとも一方は成り立たないように， n 次元ベクトルの集合を見つけることとなります．
- a) 2つの直交するベクトルのうち，少なくとも1本は黒色である． 
- b') 互いに直交し合うn本のベクトルのうち，少なくとも1本は白色である． 
- c') 集合内に互いに直交し合う n 本のベクトルの集合が少なくとも1つは存在する．

一般の場合はとても難しいです．特定の n (> 3) に対して，このようなベクトルの集合を構成する回答も歓迎します．

More generally, extend it to the case of n dimensions (n > 3). 
The problem is to find a set of n-dimensional vectors such that at least one of the conditions a) and b') does not hold while condition c') is satisfied.
- a) Whenever two of the vectors are orthogonal, at least one is black.
- b') Whenever n vectors are mutually orthogonal, at least one is white.
- c') There exists at least one set of n vectors in the set that are mutually orthogonal to each other.

The general case is very difficult. The constitution of such a set of vectors for a particular n (> 3) is also welcome.
-->

<!--
### 解答 / Solutions
- Jacques Garrigue [Coq](https://github.com/aabaa/tpp2020/blob/gh-pages/tppmark2020-garrigue.v)
- Masahiro Sakai [QBF solver](https://github.com/msakai/tppmark2020)
-->

## これまでのTPP / Past TPPs
[TPP2020](https://aabaa.github.io/tpp2020/) /
[TPP2019](https://akihisayamada.github.io/tpp2019/) /
[TPP2018](https://ksk.github.io/tpp2018/) /
[TPP2017](https://aigarashi.github.io/TPP2017/) /
[TPP2016](http://pllab.is.ocha.ac.jp/~asai/tpp2016/) /
[TPP2015](https://sites.google.com/a/progsci.info.kanagawa-u.ac.jp/tpp2015/) /
[TPP2014](https://imi.kyushu-u.ac.jp/lasm/tpp2014/) /
[TPP2013](https://www.cs.shinshu-u.ac.jp/~okazaki/TPP2013/index.html) /
[TPP2012](https://www.math.s.chiba-u.ac.jp/tpp2012/) /
[TPP2011](https://staff.aist.go.jp/reynald.affeldt/tpp2011/) /
[TPP2010](https://www.math.nagoya-u.ac.jp/~garrigue/tpp10/) /
[TPP2009](https://ist.ksc.kwansei.ac.jp/~ktaka/TPP09/TPP09.html) /
[TPP2008](http://www.score.cs.tsukuba.ac.jp/~minamide/tpp/) /
[TPP2007](http://www.score.cs.tsukuba.ac.jp/~minamide/tpp/tpp07/index.html) /
[TPP2006](https://www.jaist.ac.jp/joint-workshop/TPSmeeting/2006_11/program.html) /
[TPP2005](https://www.jaist.ac.jp/joint-workshop/TPSmeeting/2005_11/program.html)
