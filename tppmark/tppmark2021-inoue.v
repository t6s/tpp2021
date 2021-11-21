From mathcomp
     Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ********************* *)
Section tppmark.
  Definition color := bool.
  Definition white : color := true.
  Definition black : color := false.
  Definition inv : color -> color := negb.
  Definition vertc : Type := option color.
  Definition panel : Type := vertc * color.

  Definition edgeColor (p:panel) : color * color :=
    match p with
    | (None,s) => (inv s,inv s)
    | (Some d,s) => if d == white then (s,inv s) else (inv s,s)
    end.

  Definition leftColor (p:panel) : color * color :=
    match p with
    | (None,s) => (inv s,s)
    | (Some d,s) => if d == white then (s,inv s) else (inv s,inv s)
    end.

  Definition rightColor (p:panel) : color * color :=
    match p with
    | (None,s) => (inv s,s)
    | (Some d,s) => if d == white then (inv s,inv s) else (s, inv s)
    end.

  Definition isPort (p:panel) : pred color :=
    match p with
    | (None,s) => eqb (inv s)
    | (Some d,s) => fun _ => d == s
    end.

  Lemma isPort_Valid (p:panel) (c:color) :
    reflect (if c == white then (edgeColor p).1 = c else (edgeColor p).2 = c)
            (isPort p c).
  Proof. case : p c =>[][[]|][][]; exact : eqP. Qed.

  Definition leftPort (p:panel) (c:color) : (bool * bool) :=
    let lc := leftColor p in (lc.1 == c,lc.2 == c).

  Definition rightPort (p:panel) (c:color) : (bool * bool) :=
    let rc := rightColor p in (rc.1 == c,rc.2 == c).

  Definition connected : rel (bool * bool) :=
    fun x y => x.1 && y.1 || x.2 && y.2.

  Fixpoint portDistances (s:seq panel) (c:color) : bool * bool * seq nat :=
    match s with
    | [::] => (false,false,[::])
    | p :: s' =>
      let (lPort,sd) := portDistances s' c in
      let nextSd := map S sd in
      if connected (rightPort p c) lPort
      then (leftPort p c, if isPort p c then 0 :: nextSd else nextSd)
      else (false,false,[::])
    end.

  Definition allPathFrom (p:panel) (s:seq panel) (c:color) : seq nat :=
    if isPort p c
    then let (lPort,sd) := (portDistances s c) in
         if connected (rightPort p c) lPort then sd
         else [::]
    else [::].

  Definition hasPathFrom (s:seq panel) (c:color) : bool :=
    match s with
    | [::] => false
    | p :: s' => allPathFrom p s' c != [::]
    end.

  Fixpoint headseq (T:Type) (s:seq (option T)) : seq T :=
    match s with
    | [::] => [::]
    | None :: s' => [::]
    | Some a :: s' => a :: headseq s'
    end.

  Fixpoint allrots (T:Type) (s:seq T) : seq (seq T) :=
    map (rot^~ s) (iota 0 (size s)).

  Definition existsPath (s:seq (option panel)) (c:color) : bool :=
    has (hasPathFrom^~ c \o @headseq _) (allrots s).

  (* Q1 *)
  (* the case of n-gon *)
  Inductive stateTransition (n:nat) : seq (option panel) -> Prop :=
  | InitState : stateTransition n (mkseq (fun _ => None) n)
  | PutPanel (m:nat) (s s':seq (option panel)) (p:panel) of
             stateTransition n s & ~ existsPath s white
    & ~ existsPath s black & m < n & None :: s' = rot m s
    : stateTransition n (Some p :: s').

End tppmark.
