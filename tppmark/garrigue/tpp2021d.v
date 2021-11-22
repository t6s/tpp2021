From mathcomp Require Import all_ssreflect.

Section data.
Inductive corner := Center | Left | Right.
Definition corners := [:: Center; Left; Right].

Definition eq_corner (c1 c2 : corner) :=
  match c1, c2 with
  | Center, Center | Left, Left | Right, Right => true
  | _, _ => false
  end.

Lemma eq_cornerP : Equality.axiom eq_corner.
Proof. move=> x y; apply/(iffP idP) => [|<-]; by case: x; case: y. Qed.

Definition eq_corner_mixin := EqMixin eq_cornerP.
Canonical corner_eqType := Eval hnf in EqType _ eq_corner_mixin.

Definition nat_of_corner c :=
  match c with
  | Center => 0
  | Left => 1
  | Right => 2
  end.
Definition corner_of_nat := nth Center corners.
Lemma corner_of_natK : cancel nat_of_corner corner_of_nat.
Proof. by case. Qed.
Lemma corner_enumP : Finite.axiom corners.
Proof. by case. Qed.

Definition corner_choiceMixin := CanChoiceMixin corner_of_natK.
Canonical corner_choiceType := Eval hnf in ChoiceType corner corner_choiceMixin.
Definition corner_countMixin := CanCountMixin corner_of_natK.
Canonical corner_countType := Eval hnf in CountType corner corner_countMixin.
Definition corner_finMixin := FinMixin corner_enumP.
Canonical corner_finType := Eval hnf in FinType corner corner_finMixin.

Definition color := bool.
Definition Black := false.
Definition White := true.
Record triangle := mkT {main: color; other: corner}.

Definition triangles := allpairs mkT [:: Black; White] corners.

Definition eq_triangle (t1 t2 : triangle) :=
  (main t1 == main t2) && (other t1 == other t2).
Lemma eq_triangleP : Equality.axiom eq_triangle.
Proof.
rewrite /eq_triangle => -[m1 o1] [m2 o2] /=.
apply/(iffP andP).
- by case => /eqP <- /eqP <-.
- by case=> -> ->; rewrite !eqxx.
Qed.
Definition eq_triangle_mixin := EqMixin eq_triangleP.
Canonical triangle_eqType := Eval hnf in EqType _ eq_triangle_mixin.

Lemma triangleK : cancel (fun tr => (main tr, other tr)) (fun p => mkT p.1 p.2).
Proof. by case. Qed.
Lemma triangle_finite : Finite.axiom triangles.
Proof. by case => -[] []. Qed.

Definition triangle_choiceMixin := CanChoiceMixin triangleK.
Canonical triangle_choiceType :=
  Eval hnf in ChoiceType triangle triangle_choiceMixin.
Definition triangle_countMixin := CanCountMixin triangleK.
Canonical triangle_countType :=
  Eval hnf in CountType triangle triangle_countMixin.
Definition triangle_finMixin := FinMixin triangle_finite.
Canonical triangle_finType :=
  Eval hnf in FinType triangle triangle_finMixin.
End data.

Section set_tnth.
Context {T : Type} {n : nat}.
Lemma size_set_nth_in x0 (s : seq T) (i : nat) (y : T) :
  i < size s -> size (set_nth x0 s i y) = size s.
Proof. move=> Hi. by rewrite size_set_nth (maxn_idPr Hi). Qed.

Lemma size_set_tnth_in x0 (s : n.-tuple T) (i : 'I_n) (y : T) :
  size (set_nth x0 s i y) == n.
Proof. by rewrite size_set_nth_in // size_tuple. Qed.

Definition set_tnth (arr : n.-tuple T) i a :=
  Tuple (size_set_tnth_in (tnth_default arr i) arr i a).

Lemma tnth_set_tnth (arr : n.-tuple T) i j a :
  tnth (set_tnth arr i a) j = if (j : nat) == i then a else tnth arr j.
Proof.
rewrite /tnth /set_tnth /= (set_nth_default (tnth_default arr i)).
  rewrite nth_set_nth /= (set_nth_default (tnth_default arr j)) //.
  by rewrite size_tuple.
by rewrite (eqP (size_set_tnth_in _ _ _ _)).
Qed.

Lemma set_tnth_same (arr : n.-tuple T) i :
  set_tnth arr i (tnth arr i) = arr.
Proof.
apply eq_from_tnth => j; rewrite tnth_set_tnth.
by case: ifPn => // /eqP /val_inj ->.
Qed.

Lemma set_tnth_again (arr : n.-tuple T) i a b :
  set_tnth (set_tnth arr i a) i b = set_tnth arr i b.
Proof.
apply eq_from_tnth => j; rewrite !tnth_set_tnth.
by case: ifP => // ->.
Qed.
End set_tnth.

Section board.
Variable max_slices : nat.
Hypothesis Hmax_slices : max_slices > 0.

(* Specification of board and path *)

Definition board := max_slices.-tuple (option triangle).
Definition all_pos := enum 'I_max_slices.
Definition vertex : Type := 'I_max_slices * corner.
Definition empty_board : board := [tuple of nseq max_slices None].

(* Z/max_slicesZ *)
Definition nextn m := if m.+1 < max_slices then m.+1 else 0.
Definition prevn m := if m is n.+1 then n else max_slices.-1.

Definition next (m : 'I_max_slices) : 'I_max_slices.
apply (@Ordinal _ (nextn m)).
abstract (rewrite /nextn; by case: ifP).
Defined.

Definition prev (m : 'I_max_slices) : 'I_max_slices.
apply (@Ordinal _ (prevn m)).
abstract (case: m => -[|m] i /=; by rewrite (ltn_predL,ltnW)).
Defined.

Lemma nextK m : prev (next m) = m.
Proof.
apply val_inj; rewrite /= /next /nextn.
case: ifP => // /negbT.
rewrite -leqNgt => Hm'.
apply/eqP.
by rewrite eqn_leq -ltnS -(ltnS m) (prednK Hmax_slices) Hm' ltn_ord.
Qed.

Lemma prevK m : next (prev m) = m.
Proof.
apply val_inj; rewrite /= /next /nextn.
case: m => /= -[_ | n -> //].
by rewrite prednK // ltnn.
Qed.

Section all_paths.
Variable coloring : board.

(* The color of a vertex (if there is a tile) *)
Definition vcolor (v : vertex) : option color :=
  match tnth coloring v.1 with
  | None => None
  | Some (mkT col o) =>
    if v.2 == o then Some (negb col) else Some col
  end.

(* Adjacency relation for corners *)
Definition next_corner (v1 v2 : vertex) :=
  let (n1,c1) := v1 in let (n2,c2) := v2 in
  (next n1 == n2) &&
  ((c1 == Right) && (c2 == Left) || (c1 == Center) && (c2 == Center)).

(* Adjacency relation *)
Definition adj : rel vertex :=
  fun v1 v2 =>
    ((fst v1 == fst v2) || next_corner v1 v2 || next_corner v2 v1) &&
    isSome (vcolor v1) && (vcolor v1 == vcolor v2).

Lemma adjC : symmetric adj.
Proof.
move=> v1 v2.
rewrite /adj eq_sym -orbA (orbC (next_corner _ _)) orbA.
case: (vcolor v1); case: (vcolor v2); rewrite /= !(andbT,andbF) // => c.
  move=> c'; by rewrite -(eq_sym (Some c)).
case/boolP: (Some c == None) => //.
by rewrite andbF.
Qed.

(* Adjacency relation for borders *)
Definition valid_port (v : vertex) :=
  match snd v with
  | Center => false
  | Left => vcolor v == Some White
  | Right => vcolor v == Some Black
  end.

Definition diff n1 n2 :=
  let d := n1 - n2 in
  if d is 0 then n2 - n1 else d.

(* Specification of a valid path (connected, same color, non-adjacent) *)
Definition valid_path (v : vertex) p :=
  path adj v p && valid_port v && valid_port (last v p) &&
  let d := diff v.1 (last v p).1 in (d > 1) && (d.+1 < max_slices).  

Definition has_path := exists v, exists p, valid_path v p.

(* Algorithm to find all valid paths *)
Definition next_vertices n :=
  allpairs pair [:: prev n; n; next n] [:: Center; Left; Right].

Fixpoint find_path h (v : vertex) p :=
  if h is h.+1 then
    if v \in p then [::] else
      (if valid_path v p then [:: v :: p] else [::]) ++
      let nexts := next_vertices v.1 in
      flatten [seq find_path h v' (v :: p) | v' <- nexts & adj v v']
  else [::].

Definition all_ports := allpairs pair all_pos [:: Left; Right].

Definition all_paths :=
  flatten
    [seq find_path (3 * max_slices) v [::] | v <- all_ports & valid_port v].

Lemma valid_path_adj v p h :
  valid_path v p -> h < size p ->
  adj (nth v (v :: p) h) (nth v (v :: p) h.+1).
Proof.
rewrite /valid_path => /andP[] /andP[] /andP[] Hv _ _ _.
elim: h v p Hv => [|h IH] v [] // v' p /= /andP[Hv Hv'] // Hsz.
by rewrite !(set_nth_default v' v) ?IH //= ltnW.
Qed.

Lemma adj_next_vertices v v' : adj v v' -> v' \in next_vertices v.1.
Proof.
rewrite /adj /next_vertices /next_corner.
case: v v' => n1 c1 [n2 c2].
rewrite ![_.1]/= -orbA.
case/andP => /andP[] /orP[/eqP <- _ _ |].
  by case: c2; rewrite /= !inE eqxx !orbT.
case/orP => /andP[] /eqP <- /orP[] /andP[/eqP -> /eqP ->] Hc /eqP Hc';
by rewrite !inE ?nextK ?eqxx ?orbT.
Qed.

Opaque next_vertices.
Lemma find_path_valid h v p v' p' :
  v' :: p' \in find_path h v p ->
  uniq p -> valid_path v' p' && uniq (v' :: p').
Proof.
elim: h v p => [|h IH] v p //= H' Hu.
case: ifP H' => // Hcy.
rewrite mem_cat => /orP[].
  case: ifP => Hv //.
  rewrite inE => /eqP[] -> ->.
  by rewrite Hv Hcy.
case/flatten_mapP => /= v'' Hv'' /IH -> //=.
by rewrite Hcy.
Qed.

Lemma find_path_post h v p p1 :
  p1 \in find_path h v p -> exists p2, p1 = p2 ++ v :: p.
Proof.
elim: h v p => [|h IH] //= v p.
case: ifP => // _.
rewrite mem_cat => /orP[].
  case: ifP => // _.
  rewrite inE => /eqP ->.
  by exists [::].
case/flatten_mapP => /= v' Hv' /IH [p2 ->].
exists (p2 ++ [:: v']).
by rewrite -catA.
Qed.

Lemma find_valid_path_rec h v p :
  valid_path v p -> uniq (v :: p) -> 0 < h <= size p + 1 ->
  v :: p \in find_path (3 * max_slices - size p - 1 + h)
                       (nth v (v :: p) h.-1) (drop h (v :: p)).
Proof.
move=> Hv Hu.
elim: h => [|h IH] // Hh.
rewrite -[in drop _ _]add1n -drop_drop addnS /=.
case: ifP.
  rewrite -[X in nth _ _ X]addn0 -nth_drop.
  move/(drop_uniq h): Hu.
  case: (drop h _) => [| a p'] //=.
  rewrite drop0 => Ha Ha'.
  by rewrite Ha' in Ha.
move=> _.
rewrite mem_cat; apply/orP.
destruct h; [left | right].
  by rewrite /= drop0 Hv inE.
apply/flatten_mapP.
have Hsz: h < size p by case/andP/proj2: Hh; rewrite addn1 ltnS.
exists (nth v (v :: p) h).
  have Hadj := valid_path_adj _ _ _ Hv Hsz.
  by rewrite mem_filter adj_next_vertices adjC Hadj.
rewrite drop_drop -drop_nth // IH //.
by case/andP: Hh => _ /ltnW ->.
Qed.

Lemma find_valid_path v p :
  valid_path v p -> uniq (v :: p) ->
  v :: p \in find_path (3 * max_slices) (last v p) nil.
Proof.
move => Hp Hu.
have := find_valid_path_rec (size p + 1) v p Hp Hu.
rewrite -subnDA subnK.
  rewrite addn1 succnK /= drop_oversize // (last_nth v); by apply.
have := allpairs_tupleP pair [tuple of all_pos] [tuple of corners].
rewrite [X in X * 3]card_ord mulnC => /eqP <-.
have -> : size p + 1 = size (v :: p) by rewrite addn1.
apply/uniq_leq_size => // x Hx.
apply/allpairsPdep.
exists x.1; exists x.2.
rewrite mem_enum /=.
by case: x {Hx} => n [].
Qed.

(* For any valid path, there is an acyclic one starting from the same port *)
Lemma valid_path_uniq v p :
  valid_path v p -> exists p', valid_path v p' && uniq (v :: p').
Proof.
do! case/andP. case/shortenP => p' Hp' Hu _ Hv Hv' Hd.
exists p'; by rewrite /valid_path Hp' Hv Hv' Hu andbT.
Qed.

Lemma all_pathsP v p :
  reflect (valid_path v p && uniq (v :: p)) (v :: p \in all_paths).
Proof.
apply/(iffP flatten_mapP).
- case => u.
  rewrite mem_filter => /andP[Hp Hu] /find_path_valid; by apply.
- case/andP => Hp Hu.
  move/find_valid_path/(_ Hu): (Hp) => Hv.
  exists (last v p) => //.
  rewrite mem_filter.
  case/andP: Hp => /andP[_ Hp] _.
  rewrite Hp; apply/allpairsPdep.
  move: Hp; case: (last v p) => n c; exists n; exists c.
  rewrite mem_enum. by case: c Hp.
Qed.

Lemma all_paths_cons :
  ~~ nilp all_paths -> exists v, exists p, v :: p \in all_paths.
Proof.
case Hcol: all_paths => [| p] // _.
have {Hcol}Hp : p \in all_paths by rewrite Hcol inE eqxx.
case/flatten_mapP: Hp (Hp) => v Hv /find_path_post [p2] ->.
case: p2 => [|a p2]; esplit; esplit; rewrite inE; apply/orP; left; exact/eqP.
Qed.

Lemma all_paths_nilP : reflect has_path (~~ nilp all_paths).
Proof.
case/boolP: (nilp _) => Hnil; constructor.
- case=> v [p] /valid_path_uniq [p'] /all_pathsP.
  by move/nilP: Hnil => ->.
- move/all_paths_cons: Hnil => [v] [p] /all_pathsP /andP[] Hvp Hu.
  by exists v; exists p.
Qed.
End all_paths.

(* Specification of a game *)
Inductive Reachable : board -> Prop :=
  | Reach_empty : Reachable empty_board
  | Reach_add coloring n tr : Reachable coloring ->
                              ~ has_path coloring ->
                              tnth coloring n = None ->
                              Reachable (set_tnth coloring n (Some tr)).

Definition final (coloring :  board) :=
  all isSome coloring \/ has_path coloring.

(* Computable specification *)
Definition pre_boards (coloring : board) :=
  [seq set_tnth coloring i None | i <- all_pos & isSome (tnth coloring i)].

Definition final_board (coloring : board) :=
  all isSome coloring && nilp (all_paths coloring) ||
  ~~ nilp (all_paths coloring) &&
  has (fun col => nilp (all_paths col)) (pre_boards coloring).

(* Equivalence to be proved as final_boardP *)
Definition final_board_correct := forall coloring,
  reflect (Reachable coloring /\ final coloring) (final_board coloring).

(* All possible outcomes *)
Definition all_final := [seq x <- enum [finType of board] | final_board x].

Definition has_color (c : color) (coloring : board) (p : seq vertex) :=
  if p is v :: _ then vcolor coloring v == Some c else false.

Definition classify (coloring : board) :=
  let paths := all_paths coloring in
  match has (has_color White coloring) paths,
        has (has_color Black coloring) paths with
  | true, true => inl true
  | false, false => inl false
  | true, false => inr White
  | false, true => inr Black
  end.

Record results :=
    {total : nat ; no_path : nat; both_colors : nat ;
     only_white : nat; only_black : nat}.

(* Classify and count *)
Definition all_results :=
  let kinds := map classify all_final in
  {| total := size kinds; no_path := count_mem (inl false) kinds;
     both_colors := count_mem (inl true) kinds;
     only_white := count_mem (inr White) kinds;
     only_black := count_mem (inr Black) kinds |}.

(* Proof of final_board_correct *)

Section le_board.
Variables col1 col2 : board.
(* Refinement order on boards *)
Definition le_board :=
  forall i, tnth col1 i = None \/ tnth col1 i = tnth col2 i.
Hypothesis Hle : le_board.

Lemma vcolor_mono v : vcolor col1 v -> vcolor col2 v = vcolor col1 v.
Proof.
case: v => n c.
move: (Hle n).
rewrite /vcolor /=.
by case: (tnth col1 n) => // tr [] // <-.
Qed.

Lemma adj_mono v1 v2 : adj col1 v1 v2 -> adj col2 v1 v2.
Proof.
rewrite /adj; do! case/andP. move => -> /= Hv1 /eqP Hv2.
by rewrite (vcolor_mono _ Hv1) Hv1 (vcolor_mono v2) -Hv2 /=.
Qed.

Lemma path_mono v p : path (adj col1) v p -> path (adj col2) v p.
Proof. by elim: p v => //= v' p IH v /andP[] /adj_mono -> /IH ->. Qed.

Lemma valid_port_mono v : valid_port col1 v -> valid_port col2 v.
Proof.
rewrite /valid_port. 
case: v.2 => // /eqP Hcol1; move: (vcolor_mono v); by rewrite Hcol1 => ->.
Qed.

Lemma valid_path_mono v p : valid_path col1 v p -> valid_path col2 v p.
Proof.
do! case/andP. rewrite /valid_path => /path_mono -> Hv0 Hv'0 /andP[] -> ->.
by rewrite !valid_port_mono.
Qed.

Lemma has_path_mono : has_path col1 -> has_path col2.
Proof. case=> v [p] Hv; exists v; exists p; exact: valid_path_mono. Qed.
End le_board.

Definition partial (coloring : board) n :=
  [tuple if i < n then tnth coloring i else None | i < max_slices].

Lemma set_tnth_partial coloring (n : 'I_max_slices) :
  set_tnth (partial coloring n) n (tnth coloring n) = partial coloring n.+1.
Proof.
apply eq_from_tnth => i.
rewrite !tnth_set_tnth !tnth_mktuple ltnS (leq_eqVlt i).
case/boolP: (_ == _) => // /eqP ni; by rewrite -(val_inj ni) ni ltnn.
Qed.

Lemma tnth_partial coloring (n : 'I_max_slices) :
  tnth (partial coloring n) n = None.
Proof. by rewrite tnth_mktuple ltnn. Qed.

Lemma partial_max coloring : partial coloring max_slices = coloring.
Proof. apply eq_from_tnth => i; by rewrite tnth_mktuple ltn_ord. Qed.

Lemma partial_0 coloring : partial coloring 0 = empty_board.
Proof. apply eq_from_tnth => i; by rewrite tnth_mktuple tnth_nseq. Qed.

Lemma le_board_partial coloring n : le_board (partial coloring n) coloring.
Proof. move=> i; rewrite tnth_mktuple /=; case: ifP; by [left | right]. Qed.

Lemma ReachableP (coloring : board) :
  ~ has_path coloring -> Reachable coloring.
Proof.
move=> Hap; rewrite -(partial_max coloring).
set n := max_slices.
have: n <= max_slices by [].
elim: n => [|n IH] Hn; first by rewrite partial_0; constructor.
move/(_ (ltnW Hn)): IH.
rewrite -(set_tnth_partial coloring (Ordinal Hn)).
case Htr : (tnth _ _) => [tr|]; last first.
  by rewrite -(tnth_partial coloring (Ordinal Hn)) set_tnth_same.
constructor => //.
  move=> Hpc; elim Hap; apply/has_path_mono/le_board_partial: Hpc.
exact/tnth_partial.
Qed.

Lemma all_paths_empty : nilp (all_paths empty_board).
Proof.
apply/all_paths_nilP => -[[n []]] [p];
by rewrite /valid_path /valid_port /vcolor !(andbF,tnth_nseq).
Qed.

Lemma final_boardP : final_board_correct.
Proof.
move=> coloring.
apply/(iffP idP).
- case/orP.
    rewrite /final => /andP[] -> /=.
    split; by [apply/ReachableP/all_paths_nilP | left].
  case/andP => Hnil /hasP /= [col Hin] /all_paths_nilP Hncol.
  move/ReachableP: (Hncol) => Hcol.
  move/mapP: Hin => [i].
  rewrite mem_filter => /andP[Hnth] _ Ecol.
  split; last by right; apply/all_paths_nilP.
  have <- : set_tnth col i (tnth coloring i) = coloring.
    by rewrite Ecol set_tnth_again set_tnth_same.
  case Htr: (tnth coloring i) Hnth => [tr|] // _.
  apply Reach_add => //.
  by rewrite Ecol tnth_set_tnth /= eqxx.
- case=> -[].
    case => [/allP/(_ None) | /all_paths_nilP].
      by rewrite mem_nseq Hmax_slices eqxx => /(_ isT).
    by rewrite all_paths_empty.
  rewrite /final_board => col n tr Hreach /all_paths_nilP Hnil Hnone.
  case/boolP: (nilp _) => [/all_paths_nilP Hnil' [->|] // | _].
  rewrite andbF /= => Hfin.
  apply/hasP; exists col => //.
  apply/mapP; exists n.
    by rewrite mem_filter mem_enum tnth_set_tnth eqxx.
  by rewrite set_tnth_again -Hnone set_tnth_same.
Qed.
End board.

Require Extraction.
Extraction "tpp2021.ml" all_results.

(* Eval native_compute in all_results. *)
(* Terminates in 8mn with only a partially evaluated (unusable) term *)
