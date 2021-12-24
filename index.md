---
layout: default
title: The 17th Theorem Proving and Provers meeting (TPP 2021)
---

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


## 開催日程 / Date
2021年11月21日(日), 22日(月) / Sun. 21st to Mon. 22nd, November 2021.

## 会場 / Venue

**<a style="font-size: 32px; color:red" href="map/map.html">Route to the rooms</a>**

北見工業大学 / Kitami Institute of Technology

<table>
<tr>
    <td>11/21</td>
    <td>2号館 1階 C121講義室, Building 2, 1st Floor, Room C121</td>
</tr>
<tr>
    <td>11/22</td>
    <td>14号館 1階 E131講義室 , Building 14, 1st Floor, Room E131</td>
</tr>
</table>

発表・質疑応答等はZoomを利用してオンラインでも参加可能にする予定です.

The talks and discussions will be available online using Zoom.

## 住所 / Address

〒090-8507 北海道北見市公園町165番地 / 165 Koen-cho, Kitami, Hokkaido 090-8507

[アクセス](https://www.kitami-it.ac.jp/access/) / [Access](https://www.kitami-it.ac.jp/access/)


## 懇親会 / Dinner Party
新型コロナウイルス感染症 (COVID-19)感染拡大防止のため,
対面での懇親会は開催しない予定です. 

In order to avoid the risk of COVID-19,
we are not going to hold a dinner party this year.


## 幹事 / Organizer

才川隆文 (名古屋大学) /
Takafumi Saikawa (Nagoya University), 

Email: tscompor&lt;at&gt;gmail.com

松田一徳 (北見工業大学) /
Kazunori Matsuda (Kitami Institute of Technology), 

Email: kaz-matsuda&lt;at&gt;kitami-it.ac.jp

## 参加申し込み / Registration
~~11/16(火)までに / Please register by 16th November from~~<br/>
(ご講演なしの)参加登録は当日まで受け付けています / You can still register for the participation (without a talk) from

<span style="font-size:150%">
[こちらから/here](https://docs.google.com/forms/d/e/1FAIpQLScbaL-rlDBnLCKPJFnQLoluu9KdRvL_AoLKtSDFSyvuAytmfw/viewform)
</span>

## プログラム / Technical Program

Each talk slot includes the time for discussion and break.

### Nov.21
* 13:00 - 13:10 **Opening** (10min) <br/>
  才川 隆文 @ 名古屋大学

* 13:10 - 13:55 **Formalizing quantum circuits with MathComp/Ssreflect** (30 + 15 min) ([slides](<slides/saikawa.pdf>))<br/>
   才川 隆文 @ 名古屋大学 <br/>
   We formalized a basic tensor algebra used in quantum circuits.
   Compared to the previous work, in which compositions of quantum gates
   are expressed by large matrices padded by identity,
   our formalization takes the gates as parametric linear functions
   and deals with their compositions by polymorphism.

* 13:55 - 14:40 **生命保険数学の形式化 / Formalizing Actuarial Mathematics** (30 + 15 min) ([slides](<slides/ito.pdf>))<br/>
   伊藤 洋介 / Yosuke Ito @ SOMPOひまわり生命保険株式会社 / Sompo Himawari Life Insurance Inc. <br/>
   生命保険数学とは、主に生命保険における保険料や負債の計算に関する理論であり、
   アクチュアリー試験の試験科目にも含まれている。
   今回、定理証明支援系Coqを用いて生命保険数学の基本的な定義や公式を形式化したので、
   その概要を報告する。併せて、本研究の実務への応用可能性や課題についても触れる。<br/>
   Actuarial Mathematics is a theory mainly about the calculation of premiums
   reserves of life insurance. In this talk, I will present the current work
   of formalizing the basic concept of Actuarial Mathematics. In addition,
   I will mention the possibility for industrial application and
   some obstacles to overcome.

* 14:40 - 15:25 **Toward an interpretation of Intutionistic Fixed Point Logic in Coq** (30 + 15 min) ([slides](<slides/thies.pdf>))<br/>
   Holger Thies @ Kyoto University<br/>
   IFP  (Intuitionistic Fixed Point Logic) is a proof system developed
   mainly by U. Berger and collaborators
   (M. Seisenberger, O. Petrovska, H. Tsuiki).<br/>
   IFP extends intuitionistic first-order logic by strictly positive
   inductive and coinductive definitions and it is particularly well-suited
   for proofs over abstract mathematical structures such as  real numbers.
   IFP further allows  program extraction based on a uniform realizability
   interpretation which can e.g. be used to extract certified programs for
   exact real computation.<br/>
   In this talk we present some recent work on progress on implementing
   IFP style proofs on top of Coq's dependent type theory and investigate
   the possibility of program extraction from such proofs.<br/>
   (The talk is based on j.w.w. Sewon Park and Hideki Tsuiki)

* 15:25 - 16:10 **Formal proofs related to incremental Merkle trees** (30 + 15 min) ([slides](<slides/ogawa.pdf>))<br/>
   小川瑞史 @ 北陸先端科学技術大学院大学<br/>
   本発表では、国際会議CADE2005にて発表したincremental Merkle treeの性質の
   MONAによる形式証明について再考し、Isabelle における Sledgehammer を用いる形式証明の
   可能性と問題点を提示する。Incremental Merkle tree はブロックチェーンの
   基本データ構造であり、近年、その性質の形式証明が試みられており、再度、その可能性を検証する。

* 16:10 - 16:35 **可換環論のMizarによる形式化** (15 + 10 min) ([slides](<slides/watase.pdf>))<br/>
   Yasushige WATASE @ 立正大学<br/>
   昨年に引き続き筆者のMizarによる形式化を紹介。
   根基イデアルの形式化やAffine空間上の代数的集合の形式化等

* 16:35 - 17:00 **Rings, categories and schemes in Coq II: the functor of points** (15 + 10 min) ([slides](<slides/qi.pdf>))<br/>
   Xuanrui Qi @ 名古屋大学<br/>
   Last year at TPP 2020, I gave a talk on a nascent project about defining
   schemes in Coq/SSReflect. This talk reports further progress on the project:
   specifically, I abandoned the idea to define textbook-style schemes,
   but instead defining schemes via a "functor of points", a technique
   well known since Grothendieck's time. Thereby, we may avoid Coq's
   shortcomings and come up with a more versatile definition of schemes in Coq,
   using MathComp libraries.

* 17:00 - 17:25 **ゲーム研究とCoq〜大富豪の場合〜** (15 + 10 min) ([slides](<slides/ohto.pdf>))<br/>
   大渡　勝己 <br/>
   組合せゲーム理論の研究にCoqの証明が役立った事例として、
   大富豪ゲームの性質と証明について紹介します。

* 17:25 - 18:00 **TPPMark and closing of day 1** (25 min) <br/>


### Nov.22
* 09:00 - 09:45 **Proving the correctness of OCaml typing by translation into Coq** (30 + 15 min) ([slides](<slides/garrigue.pdf>))<br/>
   Jacques Garrigue @ 名古屋大学<br/>
   Proving the correctness of a type checker for a full-fledged programming
   language is a difficult task. As an alternative approach, we consider
   translating the result of type checking to Coq. The expressiveness of
   Gallina's type system allows a type preserving translation,
   and its strong soundness properties ensures the safety of typed terms.<br/>
   We developed a new backend for a subset of OCaml that generates a Coq
   version, such that one can verify that the result of their evaluation is
   the intended one. We plan to extend it to cover a large part of the language.

* 09:45 - 10:30 **範疇文法のIsabelleによる形式化** (30 + 15 min) ([slides](<slides/taniguchi.pdf>))<br/>
   TANIGUCHI Masaya @ 北陸先端科学技術大学院大学<br/>
   範疇文法において型の繰り上げ規則などを導入することで，より広い言語クラスの文法を
   表現することがSteedmanやMoortgatらによって提案されてきた．
   我々は範疇文法を定理証明支援系Isabelleによって形式化し，
   型の繰り上げ規則などが体系から定理として自然に導出できることを示す．

* 10:30 - 11:15 **定理証明支援系Coqでのモナドを用いたクイックソートの形式化とMonaeの拡張** (30 + 15 min) ([slides](<slides/saito.pdf>))<br/>
   斉藤歩夢 @ 東京工業大学　数理・計算科学系<br/>
   Functional programming languages are suitable for equational reasoning
   because of their referential transparency.  However, many practical programs
   have side effects which can be dealt with using monads.
   Therefore, there is a lot of interest in formal verification with monadic
   effects. In order to improve the proving experience using monadic effects,
   we enrich an existing formalization of monads using a formalization of
   quicksort. For that purpose, we built on a result by Mu and Chiang who
   derived two implementations of quicksort using monads: a pure one and
   another one using the array monad. They also provide an Agda formalization
   with axiomatized facts that highlight technical difficulties about
   nondeterministic permutations and the termination of monadic functions.
   We address these difficulties by providing lacking lemmas about
   nondeterministic permutations and by proving the termination of all
   monadic functions. In particular, we explain how to deal with termination
   in a systematic way.

* 11:15 - 12:00 **Progress Report on the Formalization of the Lebesgue Integral in MathComp-Analysis** (30 + 15 min) ([slides](<slides/affeldt.pdf>))<br/>
   Reynald Affeldt @ 産業技術総合研究所<br/>
   This presentation is a progress report on an original formalization of
   measure and integration theory in the Coq proof assistant. It
   leverages on existing techniques from the Mathematics Components
   project such as iterated operators and extends MathComp-Analysis with
   extended real numbers, infinite sums, mathematical structures for
   measure theory, and the Lebesgue measure and integral.  We provide an
   introduction to the resulting framework by showcasing in particular
   the formal proof of the monotone convergence theorem.

* 12:00 - 12:10 **Closing** (10min) <br/>
  才川 隆文 @ 名古屋大学


<!---
* <time (??:??)> **<title of the talk>** (<duration (?? min)>)([slides](<filename>))([preprint](<filename>))<br/>
   <name> @ <affiliation><br/>
   <abstsract>

* Break (20min)

* <time> **Dinner Party**
-->


## TPPmark

解答 / Solutions

- Jacques Garrigue <a href="tppmark/tpp2021-garrigue-1.zip"> Coq </a>
- 井上健太 <a href="tppmark/tppmark2021-inoue.v"> Coq </a>


解答は才川宛(tscompor&lt;at&gt;gmail.com)にお送り下さい. / Please send your answer to Saikawa (tscompor&lt;at&gt;gmail.com).

以下の盤面を状態とした状態遷移系を考えます.

六角形の盤面は三角形6つに区切られていて,
盤面の外周の各辺は白黒2色に塗り分けられています.
この塗り分けをポートと呼びます. 

この盤面の各三角形にパネルをはめてゆきます. 
各パネルは小三角形4つからなり,
頂点を含む小三角形1つと, その他の3つは色が違います. 

- 初期状態：空盤面
- 状態遷移：盤面の空三角形のどれか1つに,  任意のパネルをはめる
- 終了判定：
    -  一つのポートから, そのポートが乗っている盤面外周辺と
       **隣り合っていない** 他の外周辺の同色のポートへ,
       「道」ができたら終了
    - 空三角形が無ければ終了

Consider the following state transition on a game board.

The board is a hexagon comprising six triangles.
Each of the outer edges of the hexagon is divided into black and white segments,
which we call "ports".

We are going to place triangular tiles onto the board.
Each tile consists of four smaller triangles, among which
one at some vertex of the tile is differently colored than the other three.

- Initial state: Empty board
- Transition: Placement of an arbitrary tile onto some empty triangle on the board.
- Termination conditions:
    - There is a "path" which connects one port to some same-colored port
      on a **non-adjacent** edge of the board.
    - There is no remaining empty triangle on the board.

<img src="board.png" alt="Board" />

<img src="black_path.png" alt="Black path" width="250"/> <img src="both_paths.png" alt="Both paths" width="250"/> <img src="no_path.png" alt="No path" width="250"/>

<img src="adj.png" alt="Adjacent ports" width="250"/>

### 問1
この状態遷移系を形式化して下さい

Formalize this system.

### 問2
可能な終了状態の盤面数を以下の三つに分類して計算し, それが正しいことを証明して下さい. 

1. 道ができていない盤面数
2. 白ポートから白ポートへの道のみ,
   あるいは黒ポートから黒ポートへの道のみができている盤面数
3. 白から白, 黒から黒, 両方の道ができている盤面数

Classify the final states of the board into the following three,
and count the number of each. Also verify the correctness of the counting.

1. Those with no path
2. Those with either only black paths or only white paths
3. Those with both black and white paths

### 問3
この状態遷移系を白黒ふたりのプレイヤーによるゲームとみなすことにします.
各プレイヤーは交互にパネルを置いてゆき,
白の道のみができたら白の勝ち, 黒の道のみができたら黒の勝ち,
それ以外は引き分けです. 

このゲームに必勝法は存在するでしょうか？

Regard this system as a game played by black and white,
each player taking turns placing tiles.
When a final state is reached with paths of only one color,
the corresponding player wins.
Otherwise the game ends in a draw.

Prove or disprove the existence of a winning strategy in this game.

### 謝辞 / Acknowledgements
このゲーム(TRIROAD)はもともと北見工業大学の中村文彦さんが考案されたもので,
今回簡略化してTPPMarkの題材とさせて頂くにあたり, いろいろとご協力頂きました.
御礼申し上げます.

The above game (TRIROAD) was originally invented by Fumihiko Nakamura of
Kitami Institute of Technology.
We are very grateful for his help in
simplifying and using the game as a TPPMark problem.

[TRIROAD](https://famulitelab.github.io/games/triroad/)


<!---
### 解答 / Solutions
- <author> [<software>](<url>
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
