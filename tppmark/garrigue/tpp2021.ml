
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h

(** val pred : nat -> nat **)

let pred n = match n with
| O -> n
| S u -> u

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

type reflect =
| ReflectT
| ReflectF

(** val ssr_have : 'a1 -> ('a1 -> 'a2) -> 'a2 **)

let ssr_have step rest =
  rest step

module Option =
 struct
  (** val apply : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

  let apply f x = function
  | Some y -> f y
  | None -> x

  (** val bind : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option **)

  let bind f =
    apply f None

  (** val map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

  let map f =
    bind (fun x -> Some (f x))
 end

type ('aT, 'rT) simpl_fun =
  'aT -> 'rT
  (* singleton inductive, whose constructor was SimplFun *)

(** val fun_of_simpl : ('a1, 'a2) simpl_fun -> 'a1 -> 'a2 **)

let fun_of_simpl f =
  f

(** val comp : ('a2 -> 'a1) -> ('a3 -> 'a2) -> 'a3 -> 'a1 **)

let comp f g x =
  f (g x)

(** val pcomp :
    ('a2 -> 'a1 option) -> ('a3 -> 'a2 option) -> 'a3 -> 'a1 option **)

let pcomp f g x =
  Option.bind f (g x)

(** val tag : ('a1, 'a2) sigT -> 'a1 **)

let tag =
  projT1

(** val tagged : ('a1, 'a2) sigT -> 'a2 **)

let tagged =
  projT2

(** val tagged0 : 'a1 -> 'a2 -> ('a1, 'a2) sigT **)

let tagged0 i x =
  ExistT (i, x)

(** val addb : bool -> bool -> bool **)

let addb = function
| True -> negb
| False -> (fun x -> x)

(** val isSome : 'a1 option -> bool **)

let isSome = function
| Some _ -> True
| None -> False

(** val iffP : bool -> reflect -> reflect **)

let iffP _ pb =
  let _evar_0_ = fun _ _ _ -> ReflectT in
  let _evar_0_0 = fun _ _ _ -> ReflectF in
  (match pb with
   | ReflectT -> _evar_0_ __ __ __
   | ReflectF -> _evar_0_0 __ __ __)

(** val idP : bool -> reflect **)

let idP = function
| True -> ReflectT
| False -> ReflectF

(** val andP : bool -> bool -> reflect **)

let andP b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> ReflectT
             | False -> ReflectF)
  | False -> ReflectF

type 't pred0 = 't -> bool

type 't predType =
  __ -> 't pred0
  (* singleton inductive, whose constructor was PredType *)

type 't pred_sort = __

(** val predPredType : 'a1 predType **)

let predPredType x =
  Obj.magic x

type 't simpl_pred = ('t, bool) simpl_fun

(** val simplPred : 'a1 pred0 -> 'a1 simpl_pred **)

let simplPred p =
  p

(** val predT : 'a1 simpl_pred **)

let predT =
  (fun _ -> True)

module PredOfSimpl =
 struct
  (** val coerce : 'a1 simpl_pred -> 'a1 pred0 **)

  let coerce =
    fun_of_simpl
 end

(** val pred_of_argType : 'a1 simpl_pred **)

let pred_of_argType =
  predT

type 't rel = 't -> 't pred0

type 't mem_pred =
  't pred0
  (* singleton inductive, whose constructor was Mem *)

(** val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort **)

let pred_of_mem mp =
  Obj.magic mp

(** val in_mem : 'a1 -> 'a1 mem_pred -> bool **)

let in_mem x mp =
  Obj.magic pred_of_mem mp x

(** val simpl_of_mem : 'a1 mem_pred -> 'a1 simpl_pred **)

let simpl_of_mem mp =
  simplPred (fun x -> in_mem x mp)

(** val mem : 'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred **)

let mem pT =
  pT

(** val predType0 : ('a2 -> 'a1 pred0) -> 'a1 predType **)

let predType0 x =
  Obj.magic x

module Equality =
 struct
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  (** val op : 'a1 mixin_of -> 'a1 rel **)

  let op m =
    m.op

  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort mixin_of **)

  let coq_class cT =
    cT
 end

(** val eq_op : Equality.coq_type -> Equality.sort rel **)

let eq_op t =
  (Equality.coq_class t).Equality.op

(** val eqP : Equality.coq_type -> Equality.sort Equality.axiom **)

let eqP t =
  let _evar_0_ = fun _ a -> a in
  let { Equality.op = x; Equality.mixin_of__1 = x0 } = t in _evar_0_ x x0

(** val eqb : bool -> bool -> bool **)

let eqb b =
  addb (negb b)

(** val eqbP : bool Equality.axiom **)

let eqbP __top_assumption_ =
  let _evar_0_ = fun __top_assumption_0 ->
    let _evar_0_ = ReflectT in
    let _evar_0_0 = ReflectF in
    (match __top_assumption_0 with
     | True -> _evar_0_
     | False -> _evar_0_0)
  in
  let _evar_0_0 = fun __top_assumption_0 ->
    let _evar_0_0 = ReflectF in
    let _evar_0_1 = ReflectT in
    (match __top_assumption_0 with
     | True -> _evar_0_0
     | False -> _evar_0_1)
  in
  (match __top_assumption_ with
   | True -> _evar_0_
   | False -> _evar_0_0)

(** val bool_eqMixin : bool Equality.mixin_of **)

let bool_eqMixin =
  { Equality.op = eqb; Equality.mixin_of__1 = eqbP }

(** val bool_eqType : Equality.coq_type **)

let bool_eqType =
  Obj.magic bool_eqMixin

(** val pred1 :
    Equality.coq_type -> Equality.sort -> Equality.sort simpl_pred **)

let pred1 t a1 =
  simplPred (fun x -> eq_op t x a1)

type 't subType = { val0 : (__ -> 't); sub0 : ('t -> __ -> __);
                    subType__2 : (__ -> ('t -> __ -> __) -> __ -> __) }

type 't sub_sort = __

(** val sub0 : 'a1 pred0 -> 'a1 subType -> 'a1 -> 'a1 sub_sort **)

let sub0 _ s x =
  s.sub0 x __

(** val insub : 'a1 pred0 -> 'a1 subType -> 'a1 -> 'a1 sub_sort option **)

let insub p sT x =
  match idP (p x) with
  | ReflectT -> Some (sub0 p sT x)
  | ReflectF -> None

(** val inj_eqAxiom :
    Equality.coq_type -> ('a1 -> Equality.sort) -> 'a1 Equality.axiom **)

let inj_eqAxiom eT f x y =
  iffP (eq_op eT (f x) (f y)) (eqP eT (f x) (f y))

(** val val_eqP :
    Equality.coq_type -> Equality.sort pred0 -> Equality.sort subType ->
    Equality.sort sub_sort Equality.axiom **)

let val_eqP t _ sT =
  inj_eqAxiom t sT.val0

(** val pair_eq :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort, Equality.sort)
    prod rel **)

let pair_eq t1 t2 u v =
  match eq_op t1 (fst u) (fst v) with
  | True -> eq_op t2 (snd u) (snd v)
  | False -> False

(** val pair_eqP :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort, Equality.sort)
    prod Equality.axiom **)

let pair_eqP t1 t2 __top_assumption_ =
  let _evar_0_ = fun x1 x2 __top_assumption_0 ->
    let _evar_0_ = fun y1 y2 ->
      iffP
        (match eq_op t1 (fst (Pair (x1, x2))) (fst (Pair (y1, y2))) with
         | True -> eq_op t2 (snd (Pair (x1, x2))) (snd (Pair (y1, y2)))
         | False -> False)
        (andP (eq_op t1 (fst (Pair (x1, x2))) (fst (Pair (y1, y2))))
          (eq_op t2 (snd (Pair (x1, x2))) (snd (Pair (y1, y2)))))
    in
    let Pair (x, x0) = __top_assumption_0 in _evar_0_ x x0
  in
  let Pair (x, x0) = __top_assumption_ in _evar_0_ x x0

(** val prod_eqMixin :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort, Equality.sort)
    prod Equality.mixin_of **)

let prod_eqMixin t1 t2 =
  { Equality.op = (pair_eq t1 t2); Equality.mixin_of__1 = (pair_eqP t1 t2) }

(** val prod_eqType :
    Equality.coq_type -> Equality.coq_type -> Equality.coq_type **)

let prod_eqType t1 t2 =
  Obj.magic prod_eqMixin t1 t2

(** val opt_eq :
    Equality.coq_type -> Equality.sort option -> Equality.sort option -> bool **)

let opt_eq t u v =
  Option.apply (fun x -> Option.apply (eq_op t x) False v) (negb (isSome v)) u

(** val opt_eqP : Equality.coq_type -> Equality.sort option Equality.axiom **)

let opt_eqP t _top_assumption_ =
  let _evar_0_ = fun x __top_assumption_ ->
    let _evar_0_ = fun y -> iffP (eq_op t x y) (eqP t x y) in
    let _evar_0_0 = ReflectF in
    (match __top_assumption_ with
     | Some x0 -> _evar_0_ x0
     | None -> _evar_0_0)
  in
  let _evar_0_0 = fun __top_assumption_ ->
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = ReflectT in
    (match __top_assumption_ with
     | Some x -> _evar_0_0 x
     | None -> _evar_0_1)
  in
  (match _top_assumption_ with
   | Some x -> _evar_0_ x
   | None -> _evar_0_0)

(** val option_eqMixin :
    Equality.coq_type -> Equality.sort option Equality.mixin_of **)

let option_eqMixin t =
  { Equality.op = (opt_eq t); Equality.mixin_of__1 = (opt_eqP t) }

(** val option_eqType : Equality.coq_type -> Equality.coq_type **)

let option_eqType t =
  Obj.magic option_eqMixin t

(** val tagged_as :
    Equality.coq_type -> (Equality.sort, 'a1) sigT -> (Equality.sort, 'a1)
    sigT -> 'a1 **)

let tagged_as i u v =
  match eqP i (tag u) (tag v) with
  | ReflectT -> tagged v
  | ReflectF -> tagged u

(** val tag_eq :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) ->
    (Equality.sort, Equality.sort) sigT -> (Equality.sort, Equality.sort)
    sigT -> bool **)

let tag_eq i t_ u v =
  match eq_op i (tag u) (tag v) with
  | True -> eq_op (t_ (tag u)) (tagged u) (tagged_as i u v)
  | False -> False

(** val tag_eqP :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) ->
    (Equality.sort, Equality.sort) sigT Equality.axiom **)

let tag_eqP i t_ __top_assumption_ =
  let _evar_0_ = fun i0 x __top_assumption_0 ->
    let _evar_0_ = fun j ->
      let _evar_0_ = fun y ->
        iffP
          (eq_op (t_ i0) x (tagged_as i (ExistT (i0, x)) (ExistT (i0, y))))
          (eqP (t_ i0) x (tagged_as i (ExistT (i0, x)) (ExistT (i0, y))))
      in
      let _evar_0_0 = fun _ -> ReflectF in
      (match eqP i i0 j with
       | ReflectT -> _evar_0_
       | ReflectF -> _evar_0_0)
    in
    let ExistT (x0, x1) = __top_assumption_0 in _evar_0_ x0 x1
  in
  let ExistT (x, x0) = __top_assumption_ in _evar_0_ x x0

(** val tag_eqMixin :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) ->
    (Equality.sort, Equality.sort) sigT Equality.mixin_of **)

let tag_eqMixin i t_ =
  { Equality.op = (tag_eq i t_); Equality.mixin_of__1 = (tag_eqP i t_) }

(** val tag_eqType :
    Equality.coq_type -> (Equality.sort -> Equality.coq_type) ->
    Equality.coq_type **)

let tag_eqType i t_ =
  Obj.magic tag_eqMixin i t_

(** val sum_eq :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort, Equality.sort)
    sum -> (Equality.sort, Equality.sort) sum -> bool **)

let sum_eq t1 t2 u v =
  match u with
  | Inl x -> (match v with
              | Inl y -> eq_op t1 x y
              | Inr _ -> False)
  | Inr x -> (match v with
              | Inl _ -> False
              | Inr y -> eq_op t2 x y)

(** val sum_eqP :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort, Equality.sort)
    sum Equality.axiom **)

let sum_eqP t1 t2 _top_assumption_ =
  let _evar_0_ = fun x __top_assumption_ ->
    let _evar_0_ = fun y -> iffP (eq_op t1 x y) (eqP t1 x y) in
    let _evar_0_0 = fun _ -> ReflectF in
    (match __top_assumption_ with
     | Inl x0 -> _evar_0_ x0
     | Inr x0 -> _evar_0_0 x0)
  in
  let _evar_0_0 = fun x __top_assumption_ ->
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = fun y -> iffP (eq_op t2 x y) (eqP t2 x y) in
    (match __top_assumption_ with
     | Inl x0 -> _evar_0_0 x0
     | Inr x0 -> _evar_0_1 x0)
  in
  (match _top_assumption_ with
   | Inl x -> _evar_0_ x
   | Inr x -> _evar_0_0 x)

(** val sum_eqMixin :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort, Equality.sort)
    sum Equality.mixin_of **)

let sum_eqMixin t1 t2 =
  { Equality.op = (sum_eq t1 t2); Equality.mixin_of__1 = (sum_eqP t1 t2) }

(** val sum_eqType :
    Equality.coq_type -> Equality.coq_type -> Equality.coq_type **)

let sum_eqType t1 t2 =
  Obj.magic sum_eqMixin t1 t2

(** val eqn : nat -> nat -> bool **)

let rec eqn m n =
  match m with
  | O -> (match n with
          | O -> True
          | S _ -> False)
  | S m' -> (match n with
             | O -> False
             | S n' -> eqn m' n')

(** val eqnP : nat Equality.axiom **)

let eqnP n m =
  iffP (eqn n m) (idP (eqn n m))

(** val nat_eqMixin : nat Equality.mixin_of **)

let nat_eqMixin =
  { Equality.op = eqn; Equality.mixin_of__1 = eqnP }

(** val nat_eqType : Equality.coq_type **)

let nat_eqType =
  Obj.magic nat_eqMixin

(** val addn_rec : nat -> nat -> nat **)

let addn_rec =
  add

(** val addn : nat -> nat -> nat **)

let addn =
  addn_rec

(** val subn_rec : nat -> nat -> nat **)

let subn_rec =
  sub

(** val subn : nat -> nat -> nat **)

let subn =
  subn_rec

(** val leq : nat -> nat -> bool **)

let leq m n =
  eq_op nat_eqType (Obj.magic subn m n) (Obj.magic O)

(** val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter n f x =
  match n with
  | O -> x
  | S i -> f (iter i f x)

(** val iteri : nat -> (nat -> 'a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iteri n f x =
  match n with
  | O -> x
  | S i -> f i (iteri i f x)

(** val iterop : nat -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

let iterop n op0 x =
  let f = fun i y -> match i with
                     | O -> x
                     | S _ -> op0 x y in iteri n f

(** val muln_rec : nat -> nat -> nat **)

let muln_rec =
  mul

(** val muln : nat -> nat -> nat **)

let muln =
  muln_rec

(** val expn_rec : nat -> nat -> nat **)

let expn_rec m n =
  iterop n muln m (S O)

(** val expn : nat -> nat -> nat **)

let expn =
  expn_rec

(** val nat_of_bool : bool -> nat **)

let nat_of_bool = function
| True -> S O
| False -> O

(** val odd : nat -> bool **)

let rec odd = function
| O -> False
| S n' -> negb (odd n')

(** val double_rec : nat -> nat **)

let rec double_rec = function
| O -> O
| S n' -> S (S (double_rec n'))

(** val double : nat -> nat **)

let double =
  double_rec

(** val size : 'a1 list -> nat **)

let rec size = function
| Nil -> O
| Cons (_, s') -> S (size s')

(** val nilp : 'a1 list -> bool **)

let nilp s =
  eq_op nat_eqType (Obj.magic size s) (Obj.magic O)

(** val ohead : 'a1 list -> 'a1 option **)

let ohead = function
| Nil -> None
| Cons (x, _) -> Some x

(** val ncons : nat -> 'a1 -> 'a1 list -> 'a1 list **)

let ncons n x =
  iter n (fun x0 -> Cons (x, x0))

(** val nseq : nat -> 'a1 -> 'a1 list **)

let nseq n x =
  ncons n x Nil

(** val cat : 'a1 list -> 'a1 list -> 'a1 list **)

let rec cat s1 s2 =
  match s1 with
  | Nil -> s2
  | Cons (x, s1') -> Cons (x, (cat s1' s2))

(** val last : 'a1 -> 'a1 list -> 'a1 **)

let rec last x = function
| Nil -> x
| Cons (x', s') -> last x' s'

(** val nth : 'a1 -> 'a1 list -> nat -> 'a1 **)

let rec nth x0 s n =
  match s with
  | Nil -> x0
  | Cons (x, s') -> (match n with
                     | O -> x
                     | S n' -> nth x0 s' n')

(** val set_nth : 'a1 -> 'a1 list -> nat -> 'a1 -> 'a1 list **)

let rec set_nth x0 s n y =
  match s with
  | Nil -> ncons n x0 (Cons (y, Nil))
  | Cons (x, s') ->
    (match n with
     | O -> Cons (y, s')
     | S n' -> Cons (x, (set_nth x0 s' n' y)))

(** val filter : 'a1 pred0 -> 'a1 list -> 'a1 list **)

let rec filter a = function
| Nil -> Nil
| Cons (x, s') ->
  (match a x with
   | True -> Cons (x, (filter a s'))
   | False -> filter a s')

(** val count : 'a1 pred0 -> 'a1 list -> nat **)

let rec count a = function
| Nil -> O
| Cons (x, s') -> addn (nat_of_bool (a x)) (count a s')

(** val has : 'a1 pred0 -> 'a1 list -> bool **)

let rec has a = function
| Nil -> False
| Cons (x, s') -> (match a x with
                   | True -> True
                   | False -> has a s')

(** val all : 'a1 pred0 -> 'a1 list -> bool **)

let rec all a = function
| Nil -> True
| Cons (x, s') -> (match a x with
                   | True -> all a s'
                   | False -> False)

(** val eqseq :
    Equality.coq_type -> Equality.sort list -> Equality.sort list -> bool **)

let rec eqseq t s1 s2 =
  match s1 with
  | Nil -> (match s2 with
            | Nil -> True
            | Cons (_, _) -> False)
  | Cons (x1, s1') ->
    (match s2 with
     | Nil -> False
     | Cons (x2, s2') ->
       (match eq_op t x1 x2 with
        | True -> eqseq t s1' s2'
        | False -> False))

(** val eqseqP : Equality.coq_type -> Equality.sort list Equality.axiom **)

let eqseqP t _top_assumption_ =
  let _evar_0_ = fun __top_assumption_ ->
    let _evar_0_ = ReflectT in
    let _evar_0_0 = fun _ _ -> ReflectF in
    (match __top_assumption_ with
     | Nil -> _evar_0_
     | Cons (x, x0) -> _evar_0_0 x x0)
  in
  let _evar_0_0 = fun x1 s1 iHs __top_assumption_ ->
    let _evar_0_0 = ReflectF in
    let _evar_0_1 = fun x2 s2 ->
      ssr_have (eqP t x1 x2) (fun __top_assumption_0 ->
        let _evar_0_1 = fun _ -> iffP (eqseq t s1 s2) (iHs s2) in
        let _evar_0_2 = fun _ -> ReflectF in
        (match __top_assumption_0 with
         | ReflectT -> _evar_0_1 __
         | ReflectF -> _evar_0_2 __))
    in
    (match __top_assumption_ with
     | Nil -> _evar_0_0
     | Cons (x, x0) -> _evar_0_1 x x0)
  in
  let rec f = function
  | Nil -> _evar_0_
  | Cons (y, l0) -> _evar_0_0 y l0 (f l0)
  in f _top_assumption_

(** val seq_eqMixin :
    Equality.coq_type -> Equality.sort list Equality.mixin_of **)

let seq_eqMixin t =
  { Equality.op = (eqseq t); Equality.mixin_of__1 = (eqseqP t) }

(** val seq_eqType : Equality.coq_type -> Equality.coq_type **)

let seq_eqType t =
  Obj.magic seq_eqMixin t

(** val mem_seq :
    Equality.coq_type -> Equality.sort list -> Equality.sort -> bool **)

let rec mem_seq t = function
| Nil -> (fun _ -> False)
| Cons (y, s') ->
  let p = mem_seq t s' in
  (fun x -> match eq_op t x y with
            | True -> True
            | False -> p x)

type seq_eqclass = Equality.sort list

(** val pred_of_seq :
    Equality.coq_type -> seq_eqclass -> Equality.sort pred_sort **)

let pred_of_seq t s =
  Obj.magic mem_seq t s

(** val seq_predType : Equality.coq_type -> Equality.sort predType **)

let seq_predType t =
  predType0 (Obj.magic pred_of_seq t)

(** val map0 : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map0 f = function
| Nil -> Nil
| Cons (x, s') -> Cons ((f x), (map0 f s'))

(** val pmap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list **)

let rec pmap f = function
| Nil -> Nil
| Cons (x, s') ->
  let r = pmap f s' in Option.apply (fun x0 -> Cons (x0, r)) r (f x)

(** val iota : nat -> nat -> nat list **)

let rec iota m = function
| O -> Nil
| S n' -> Cons (m, (iota (S m) n'))

(** val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldr f z0 = function
| Nil -> z0
| Cons (x, s') -> f x (foldr f z0 s')

(** val flatten : 'a1 list list -> 'a1 list **)

let flatten s =
  foldr cat Nil s

(** val allpairs : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let allpairs f s t =
  flatten (map0 (fun x -> map0 (fun y -> f x y) t) s)

module CodeSeq =
 struct
  (** val code : nat list -> nat **)

  let code =
    foldr (fun n m -> muln (expn (S (S O)) n) (S (double m))) O

  (** val decode_rec : nat -> nat -> nat -> nat list **)

  let rec decode_rec v q r =
    match q with
    | O -> Cons (v, Nil)
    | S q' ->
      (match r with
       | O -> Cons (v, (decode_rec O q' q'))
       | S n ->
         (match n with
          | O -> decode_rec (S v) q' q'
          | S r' -> decode_rec v q' r'))

  (** val decode : nat -> nat list **)

  let decode n = match n with
  | O -> Nil
  | S _ -> decode_rec O (pred n) (pred n)
 end

(** val seq_of_opt : 'a1 option -> 'a1 list **)

let seq_of_opt u =
  Option.apply (nseq (S O)) Nil u

(** val tag_of_pair : ('a1, 'a2) prod -> ('a1, 'a2) sigT **)

let tag_of_pair p =
  tagged0 (fst p) (snd p)

(** val pair_of_tag : ('a1, 'a2) sigT -> ('a1, 'a2) prod **)

let pair_of_tag u =
  Pair ((tag u), (tagged u))

module Choice =
 struct
  type 't mixin_of =
    't pred0 -> nat -> 't option
    (* singleton inductive, whose constructor was Mixin *)

  (** val find : 'a1 mixin_of -> 'a1 pred0 -> nat -> 'a1 option **)

  let find m =
    m

  type 't class_of = { base : 't Equality.mixin_of; mixin : 't mixin_of }

  (** val base : 'a1 class_of -> 'a1 Equality.mixin_of **)

  let base c =
    c.base

  (** val mixin : 'a1 class_of -> 'a1 mixin_of **)

  let mixin c =
    c.mixin

  type coq_type =
    __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort class_of **)

  let coq_class cT =
    cT

  (** val eqType : coq_type -> Equality.coq_type **)

  let eqType cT =
    (coq_class cT).base

  module InternalTheory =
   struct
    (** val find : coq_type -> sort pred0 -> nat -> sort option **)

    let find t =
      find (coq_class t).mixin
   end
 end

(** val pcanChoiceMixin :
    Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1 option) ->
    'a1 Choice.mixin_of **)

let pcanChoiceMixin t _ f' =
  let liftP = fun sP -> simplPred (fun x -> Option.apply sP False (f' x)) in
  let sf = fun sP n ->
    Option.bind f'
      (Choice.InternalTheory.find t (PredOfSimpl.coerce (liftP sP)) n)
  in
  (fun sP -> fun_of_simpl (sf sP))

(** val canChoiceMixin :
    Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1) -> 'a1
    Choice.mixin_of **)

let canChoiceMixin t f f' =
  pcanChoiceMixin t f (fun y -> Some (f' y))

(** val sub_choiceMixin :
    Choice.coq_type -> Choice.sort pred0 -> Choice.sort subType ->
    Choice.sort sub_sort Choice.mixin_of **)

let sub_choiceMixin t p sT =
  pcanChoiceMixin t sT.val0 (insub p sT)

(** val seq_choiceMixin :
    Choice.coq_type -> Choice.sort list Choice.mixin_of **)

let seq_choiceMixin t =
  let r = fun f xs x -> f (Cons (x, xs)) in
  let f =
    let rec f sP ns xs =
      match ns with
      | Nil -> (match sP xs with
                | True -> Some xs
                | False -> None)
      | Cons (n, ns1) ->
        let fr = fun_of_simpl (r (f sP ns1)) xs in
        Option.bind fr
          (Choice.InternalTheory.find t (fun x -> isSome (fr x)) n)
    in f
  in
  (fun sP nn -> f sP (CodeSeq.decode nn) Nil)

(** val seq_choiceType : Choice.coq_type -> Choice.coq_type **)

let seq_choiceType t =
  { Choice.base = (Equality.coq_class (seq_eqType (Choice.eqType t)));
    Choice.mixin = (Obj.magic seq_choiceMixin t) }

(** val tagged_choiceMixin :
    Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> (Choice.sort,
    Choice.sort) sigT Choice.mixin_of **)

let tagged_choiceMixin i t_ =
  let ft = fun tP n i0 ->
    Option.map (tagged0 i0)
      (Choice.InternalTheory.find (t_ i0) (comp tP (tagged0 i0)) n)
  in
  let fi = fun tP ni nt ->
    Option.bind (ft tP nt)
      (Choice.InternalTheory.find i (fun i0 -> isSome (ft tP nt i0)) ni)
  in
  (fun tP n ->
  match CodeSeq.decode n with
  | Nil -> None
  | Cons (ni, l) ->
    (match l with
     | Nil -> None
     | Cons (nt, l0) ->
       (match l0 with
        | Nil -> fi tP ni nt
        | Cons (_, _) -> None)))

(** val tagged_choiceType :
    Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> Choice.coq_type **)

let tagged_choiceType i t_ =
  { Choice.base =
    (Equality.coq_class
      (tag_eqType (Choice.eqType i) (fun i0 -> Choice.eqType (t_ i0))));
    Choice.mixin = (Obj.magic tagged_choiceMixin i t_) }

(** val nat_choiceMixin : nat Choice.mixin_of **)

let nat_choiceMixin =
  let f = fun p n -> match p n with
                     | True -> Some n
                     | False -> None in
  (fun p -> fun_of_simpl (f p))

(** val nat_choiceType : Choice.coq_type **)

let nat_choiceType =
  { Choice.base = (Equality.coq_class nat_eqType); Choice.mixin =
    (Obj.magic nat_choiceMixin) }

(** val bool_choiceMixin : bool Choice.mixin_of **)

let bool_choiceMixin =
  canChoiceMixin nat_choiceType (Obj.magic nat_of_bool) (Obj.magic odd)

(** val bool_choiceType : Choice.coq_type **)

let bool_choiceType =
  { Choice.base = (Equality.coq_class bool_eqType); Choice.mixin =
    (Obj.magic bool_choiceMixin) }

(** val option_choiceMixin :
    Choice.coq_type -> Choice.sort option Choice.mixin_of **)

let option_choiceMixin t =
  canChoiceMixin (seq_choiceType t) (Obj.magic seq_of_opt) (Obj.magic ohead)

(** val option_choiceType : Choice.coq_type -> Choice.coq_type **)

let option_choiceType t =
  { Choice.base = (Equality.coq_class (option_eqType (Choice.eqType t)));
    Choice.mixin = (Obj.magic option_choiceMixin t) }

(** val prod_choiceMixin :
    Choice.coq_type -> Choice.coq_type -> (Choice.sort, Choice.sort) prod
    Choice.mixin_of **)

let prod_choiceMixin t1 t2 =
  canChoiceMixin (tagged_choiceType t1 (fun _ -> t2)) (Obj.magic tag_of_pair)
    (Obj.magic pair_of_tag)

(** val prod_choiceType :
    Choice.coq_type -> Choice.coq_type -> Choice.coq_type **)

let prod_choiceType t1 t2 =
  { Choice.base =
    (Equality.coq_class (prod_eqType (Choice.eqType t1) (Choice.eqType t2)));
    Choice.mixin = (Obj.magic prod_choiceMixin t1 t2) }

module Countable =
 struct
  type 't mixin_of = { pickle : ('t -> nat); unpickle : (nat -> 't option) }

  (** val pickle : 'a1 mixin_of -> 'a1 -> nat **)

  let pickle m =
    m.pickle

  (** val unpickle : 'a1 mixin_of -> nat -> 'a1 option **)

  let unpickle m =
    m.unpickle

  type 't class_of = { base : 't Choice.class_of; mixin : 't mixin_of }

  (** val base : 'a1 class_of -> 'a1 Choice.class_of **)

  let base c =
    c.base

  (** val mixin : 'a1 class_of -> 'a1 mixin_of **)

  let mixin c =
    c.mixin

  type coq_type =
    __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort class_of **)

  let coq_class cT =
    cT

  (** val choiceType : coq_type -> Choice.coq_type **)

  let choiceType cT =
    (coq_class cT).base
 end

(** val unpickle0 : Countable.coq_type -> nat -> Countable.sort option **)

let unpickle0 t =
  (Countable.coq_class t).Countable.mixin.Countable.unpickle

(** val pickle0 : Countable.coq_type -> Countable.sort -> nat **)

let pickle0 t =
  (Countable.coq_class t).Countable.mixin.Countable.pickle

(** val pcanCountMixin :
    Countable.coq_type -> ('a1 -> Countable.sort) -> (Countable.sort -> 'a1
    option) -> 'a1 Countable.mixin_of **)

let pcanCountMixin t f f' =
  { Countable.pickle = (comp (pickle0 t) f); Countable.unpickle =
    (pcomp f' (unpickle0 t)) }

(** val canCountMixin :
    Countable.coq_type -> ('a1 -> Countable.sort) -> (Countable.sort -> 'a1)
    -> 'a1 Countable.mixin_of **)

let canCountMixin t f f' =
  pcanCountMixin t f (fun y -> Some (f' y))

(** val sub_countMixin :
    Countable.coq_type -> Countable.sort pred0 -> Countable.sort subType ->
    Countable.sort sub_sort Countable.mixin_of **)

let sub_countMixin t p sT =
  pcanCountMixin t sT.val0 (insub p sT)

(** val pickle_seq : Countable.coq_type -> Countable.sort list -> nat **)

let pickle_seq t s =
  CodeSeq.code (map0 (pickle0 t) s)

(** val unpickle_seq :
    Countable.coq_type -> nat -> Countable.sort list option **)

let unpickle_seq t n =
  Some (pmap (unpickle0 t) (CodeSeq.decode n))

(** val seq_countMixin :
    Countable.coq_type -> Countable.sort list Countable.mixin_of **)

let seq_countMixin t =
  { Countable.pickle = (pickle_seq t); Countable.unpickle = (unpickle_seq t) }

(** val seq_countType : Countable.coq_type -> Countable.coq_type **)

let seq_countType t =
  { Countable.base =
    (Choice.coq_class (seq_choiceType (Countable.choiceType t)));
    Countable.mixin = (Obj.magic seq_countMixin t) }

(** val pickle_tagged :
    Countable.coq_type -> (Countable.sort -> Countable.coq_type) ->
    (Countable.sort, Countable.sort) sigT -> nat **)

let pickle_tagged i t_ u =
  CodeSeq.code (Cons ((pickle0 i (tag u)), (Cons
    ((pickle0 (t_ (tag u)) (tagged u)), Nil))))

(** val unpickle_tagged :
    Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> nat ->
    (Countable.sort, Countable.sort) sigT option **)

let unpickle_tagged i t_ s =
  match CodeSeq.decode s with
  | Nil -> None
  | Cons (ni, l) ->
    (match l with
     | Nil -> None
     | Cons (nx, l0) ->
       (match l0 with
        | Nil ->
          Option.bind (fun i0 ->
            Option.map (tagged0 i0) (unpickle0 (t_ i0) nx)) (unpickle0 i ni)
        | Cons (_, _) -> None))

(** val tag_countMixin :
    Countable.coq_type -> (Countable.sort -> Countable.coq_type) ->
    (Countable.sort, Countable.sort) sigT Countable.mixin_of **)

let tag_countMixin i t_ =
  { Countable.pickle = (pickle_tagged i t_); Countable.unpickle =
    (unpickle_tagged i t_) }

(** val tag_countType :
    Countable.coq_type -> (Countable.sort -> Countable.coq_type) ->
    Countable.coq_type **)

let tag_countType i t_ =
  { Countable.base =
    (Choice.coq_class
      (tagged_choiceType (Countable.choiceType i) (fun i0 ->
        Countable.choiceType (t_ i0)))); Countable.mixin =
    (Obj.magic tag_countMixin i t_) }

(** val nat_countMixin : nat Countable.mixin_of **)

let nat_countMixin =
  { Countable.pickle = (fun x -> x); Countable.unpickle = (fun x -> Some x) }

(** val nat_countType : Countable.coq_type **)

let nat_countType =
  { Countable.base = (Choice.coq_class nat_choiceType); Countable.mixin =
    (Obj.magic nat_countMixin) }

(** val bool_countMixin : bool Countable.mixin_of **)

let bool_countMixin =
  canCountMixin nat_countType (Obj.magic nat_of_bool) (Obj.magic odd)

(** val bool_countType : Countable.coq_type **)

let bool_countType =
  { Countable.base = (Choice.coq_class bool_choiceType); Countable.mixin =
    (Obj.magic bool_countMixin) }

(** val option_countMixin :
    Countable.coq_type -> Countable.sort option Countable.mixin_of **)

let option_countMixin t =
  canCountMixin (seq_countType t) (Obj.magic seq_of_opt) (Obj.magic ohead)

(** val prod_countMixin :
    Countable.coq_type -> Countable.coq_type -> (Countable.sort,
    Countable.sort) prod Countable.mixin_of **)

let prod_countMixin t1 t2 =
  canCountMixin (tag_countType t1 (fun _ -> t2)) (Obj.magic tag_of_pair)
    (Obj.magic pair_of_tag)

(** val prod_countType :
    Countable.coq_type -> Countable.coq_type -> Countable.coq_type **)

let prod_countType t1 t2 =
  { Countable.base =
    (Choice.coq_class
      (prod_choiceType (Countable.choiceType t1) (Countable.choiceType t2)));
    Countable.mixin = (Obj.magic prod_countMixin t1 t2) }

(** val path : 'a1 rel -> 'a1 -> 'a1 list -> bool **)

let rec path e x = function
| Nil -> True
| Cons (y, p') -> (match e x y with
                   | True -> path e y p'
                   | False -> False)

module Finite =
 struct
  type mixin_of = { mixin_base : Equality.sort Countable.mixin_of;
                    mixin_enum : Equality.sort list }

  (** val mixin_base :
      Equality.coq_type -> mixin_of -> Equality.sort Countable.mixin_of **)

  let mixin_base _ m =
    m.mixin_base

  (** val mixin_enum : Equality.coq_type -> mixin_of -> Equality.sort list **)

  let mixin_enum _ m =
    m.mixin_enum

  (** val coq_EnumMixin :
      Countable.coq_type -> Countable.sort list -> mixin_of **)

  let coq_EnumMixin t e =
    let m = t.Countable.mixin in { mixin_base = m; mixin_enum = e }

  type 't class_of = { base : 't Choice.class_of; mixin : mixin_of }

  (** val base : 'a1 class_of -> 'a1 Choice.class_of **)

  let base c =
    c.base

  (** val mixin : 'a1 class_of -> mixin_of **)

  let mixin c =
    c.mixin

  (** val base2 : 'a1 class_of -> 'a1 Countable.class_of **)

  let base2 c =
    { Countable.base = c.base; Countable.mixin =
      (Obj.magic c.mixin.mixin_base) }

  type coq_type =
    __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort class_of **)

  let coq_class cT =
    cT

  (** val clone : coq_type -> 'a1 class_of -> coq_type **)

  let clone _ c =
    Obj.magic c

  (** val choiceType : coq_type -> Choice.coq_type **)

  let choiceType cT =
    (coq_class cT).base

  (** val countType : coq_type -> Countable.coq_type **)

  let countType cT =
    base2 (coq_class cT)

  module type EnumSig =
   sig
    val enum : coq_type -> sort list
   end

  module EnumDef =
   struct
    (** val enum : coq_type -> Equality.sort list **)

    let enum cT =
      (coq_class cT).mixin.mixin_enum

    (** val enumDef : __ **)

    let enumDef =
      __
   end
 end

(** val enum_mem :
    Finite.coq_type -> Finite.sort mem_pred -> Finite.sort list **)

let enum_mem t mA =
  filter (PredOfSimpl.coerce (simpl_of_mem mA)) (Finite.EnumDef.enum t)

(** val image_mem :
    Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort mem_pred -> 'a1
    list **)

let image_mem t f mA =
  map0 f (enum_mem t mA)

(** val codom : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 list **)

let codom t f =
  image_mem t f
    (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))

(** val option_enum : Finite.coq_type -> Finite.sort option list **)

let option_enum t =
  Cons (None, (map0 (fun x -> Some x) (Finite.EnumDef.enum t)))

(** val option_finMixin : Finite.coq_type -> Finite.mixin_of **)

let option_finMixin t =
  { Finite.mixin_base = (Obj.magic option_countMixin (Finite.countType t));
    Finite.mixin_enum = (Obj.magic option_enum t) }

(** val option_finType : Finite.coq_type -> Finite.coq_type **)

let option_finType t =
  { Finite.base =
    (Choice.coq_class (option_choiceType (Finite.choiceType t)));
    Finite.mixin = (option_finMixin t) }

type ordinal = nat
  (* singleton inductive, whose constructor was Ordinal *)

(** val nat_of_ord : nat -> ordinal -> nat **)

let nat_of_ord _ i =
  i

(** val ordinal_subType : nat -> nat subType **)

let ordinal_subType n =
  { val0 = (Obj.magic nat_of_ord n); sub0 = (Obj.magic (fun x _ -> x));
    subType__2 = (fun _ k_S u -> k_S (Obj.magic u) __) }

(** val ordinal_eqMixin : nat -> ordinal Equality.mixin_of **)

let ordinal_eqMixin n =
  { Equality.op = (fun x y ->
    eq_op nat_eqType (Obj.magic nat_of_ord n x) (Obj.magic nat_of_ord n y));
    Equality.mixin_of__1 =
    (Obj.magic val_eqP nat_eqType (fun x -> leq (S (Obj.magic x)) n)
      (ordinal_subType n)) }

(** val ordinal_eqType : nat -> Equality.coq_type **)

let ordinal_eqType n =
  Obj.magic ordinal_eqMixin n

(** val ordinal_choiceMixin : nat -> ordinal Choice.mixin_of **)

let ordinal_choiceMixin n =
  Obj.magic sub_choiceMixin nat_choiceType (fun x -> leq (S (Obj.magic x)) n)
    (ordinal_subType n)

(** val ordinal_choiceType : nat -> Choice.coq_type **)

let ordinal_choiceType n =
  { Choice.base = (Equality.coq_class (ordinal_eqType n)); Choice.mixin =
    (Obj.magic ordinal_choiceMixin n) }

(** val ordinal_countMixin : nat -> ordinal Countable.mixin_of **)

let ordinal_countMixin n =
  Obj.magic sub_countMixin nat_countType (fun x -> leq (S (Obj.magic x)) n)
    (ordinal_subType n)

(** val ord_enum : nat -> ordinal list **)

let ord_enum n =
  pmap (Obj.magic insub (fun x -> leq (S x) n) (ordinal_subType n)) (iota O n)

(** val ordinal_finMixin : nat -> Finite.mixin_of **)

let ordinal_finMixin n =
  { Finite.mixin_base = (Obj.magic ordinal_countMixin n); Finite.mixin_enum =
    (Obj.magic ord_enum n) }

(** val ordinal_finType : nat -> Finite.coq_type **)

let ordinal_finType n =
  { Finite.base = (Choice.coq_class (ordinal_choiceType n)); Finite.mixin =
    (ordinal_finMixin n) }

type 't tuple_of =
  't list
  (* singleton inductive, whose constructor was Tuple *)

(** val tval : nat -> 'a1 tuple_of -> 'a1 list **)

let tval _ t =
  t

(** val tuple_subType : nat -> 'a1 list subType **)

let tuple_subType n =
  { val0 = (Obj.magic tval n); sub0 = (Obj.magic (fun x _ -> x));
    subType__2 = (fun _ k_S u -> k_S (Obj.magic u) __) }

(** val tnth_default : nat -> 'a1 tuple_of -> ordinal -> 'a1 **)

let tnth_default n t =
  let _evar_0_ = fun _ -> assert false (* absurd case *) in
  let _evar_0_0 = fun a _ _ -> a in
  (match tval n t with
   | Nil -> _evar_0_
   | Cons (x, x0) -> _evar_0_0 x x0)

(** val tnth : nat -> 'a1 tuple_of -> ordinal -> 'a1 **)

let tnth n t i =
  nth (tnth_default n t i) (tval n t) (nat_of_ord n i)

(** val tuple_eqMixin :
    nat -> Equality.coq_type -> Equality.sort tuple_of Equality.mixin_of **)

let tuple_eqMixin n t =
  { Equality.op = (fun x y ->
    eq_op (seq_eqType t) (Obj.magic tval n x) (Obj.magic tval n y));
    Equality.mixin_of__1 =
    (Obj.magic val_eqP (seq_eqType t) (fun x ->
      eq_op nat_eqType (Obj.magic size x) (Obj.magic n)) (tuple_subType n)) }

(** val tuple_eqType : nat -> Equality.coq_type -> Equality.coq_type **)

let tuple_eqType n t =
  Obj.magic tuple_eqMixin n t

(** val tuple_choiceMixin :
    nat -> Choice.coq_type -> Choice.sort tuple_of Choice.mixin_of **)

let tuple_choiceMixin n t =
  Obj.magic sub_choiceMixin (seq_choiceType t) (fun x ->
    eq_op nat_eqType (Obj.magic size x) (Obj.magic n)) (tuple_subType n)

(** val tuple_choiceType : nat -> Choice.coq_type -> Choice.coq_type **)

let tuple_choiceType n t =
  { Choice.base = (Equality.coq_class (tuple_eqType n (Choice.eqType t)));
    Choice.mixin = (Obj.magic tuple_choiceMixin n t) }

(** val tuple_countMixin :
    nat -> Countable.coq_type -> Countable.sort tuple_of Countable.mixin_of **)

let tuple_countMixin n t =
  Obj.magic sub_countMixin (seq_countType t) (fun x ->
    eq_op nat_eqType (Obj.magic size x) (Obj.magic n)) (tuple_subType n)

module type FinTupleSig =
 sig
  val enum : nat -> Finite.coq_type -> Finite.sort tuple_of list
 end

module FinTuple =
 struct
  (** val enum : nat -> Finite.coq_type -> Finite.sort tuple_of list **)

  let enum n t =
    let extend = fun e ->
      flatten (codom t (fun x -> map0 (fun x0 -> Cons (x, x0)) e))
    in
    pmap
      (Obj.magic insub (fun x ->
        eq_op nat_eqType (Obj.magic size x) (Obj.magic n)) (tuple_subType n))
      (iter n extend (Cons (Nil, Nil)))

  (** val enumP : __ **)

  let enumP =
    __

  (** val size_enum : __ **)

  let size_enum =
    __
 end

(** val tuple_finMixin : nat -> Finite.coq_type -> Finite.mixin_of **)

let tuple_finMixin n t =
  { Finite.mixin_base = (Obj.magic tuple_countMixin n (Finite.countType t));
    Finite.mixin_enum = (Obj.magic FinTuple.enum n t) }

(** val tuple_finType : nat -> Finite.coq_type -> Finite.coq_type **)

let tuple_finType n t =
  { Finite.base =
    (Choice.coq_class (tuple_choiceType n (Finite.choiceType t)));
    Finite.mixin = (tuple_finMixin n t) }

type corner =
| Center
| Left
| Right

(** val corners : corner list **)

let corners =
  Cons (Center, (Cons (Left, (Cons (Right, Nil)))))

(** val eq_corner : corner -> corner -> bool **)

let eq_corner c1 c2 =
  match c1 with
  | Center -> (match c2 with
               | Center -> True
               | _ -> False)
  | Left -> (match c2 with
             | Left -> True
             | _ -> False)
  | Right -> (match c2 with
              | Right -> True
              | _ -> False)

(** val eq_cornerP : corner Equality.axiom **)

let eq_cornerP x y =
  iffP (eq_corner x y) (idP (eq_corner x y))

(** val eq_corner_mixin : corner Equality.mixin_of **)

let eq_corner_mixin =
  { Equality.op = eq_corner; Equality.mixin_of__1 = eq_cornerP }

(** val corner_eqType : Equality.coq_type **)

let corner_eqType =
  Obj.magic eq_corner_mixin

(** val nat_of_corner : corner -> nat **)

let nat_of_corner = function
| Center -> O
| Left -> S O
| Right -> S (S O)

(** val corner_of_nat : nat -> corner **)

let corner_of_nat =
  nth Center corners

(** val corner_choiceMixin : corner Choice.mixin_of **)

let corner_choiceMixin =
  canChoiceMixin nat_choiceType (Obj.magic nat_of_corner)
    (Obj.magic corner_of_nat)

(** val corner_choiceType : Choice.coq_type **)

let corner_choiceType =
  { Choice.base = (Equality.coq_class corner_eqType); Choice.mixin =
    (Obj.magic corner_choiceMixin) }

(** val corner_countMixin : corner Countable.mixin_of **)

let corner_countMixin =
  canCountMixin nat_countType (Obj.magic nat_of_corner)
    (Obj.magic corner_of_nat)

(** val corner_countType : Countable.coq_type **)

let corner_countType =
  { Countable.base = (Choice.coq_class corner_choiceType); Countable.mixin =
    (Obj.magic corner_countMixin) }

type color = bool

(** val black : bool **)

let black =
  False

(** val white : bool **)

let white =
  True

type triangle = { main : color; other : corner }

(** val triangles : triangle list **)

let triangles =
  allpairs (fun x x0 -> { main = x; other = x0 }) (Cons (black, (Cons (white,
    Nil)))) corners

(** val eq_triangle : triangle -> triangle -> bool **)

let eq_triangle t1 t2 =
  match eq_op bool_eqType (Obj.magic t1.main) (Obj.magic t2.main) with
  | True -> eq_op corner_eqType (Obj.magic t1.other) (Obj.magic t2.other)
  | False -> False

(** val eq_triangleP : triangle Equality.axiom **)

let eq_triangleP __top_assumption_ =
  let _evar_0_ = fun m1 o1 __top_assumption_0 ->
    let _evar_0_ = fun m2 o2 ->
      iffP
        (match eq_op bool_eqType m1 m2 with
         | True -> eq_op corner_eqType o1 o2
         | False -> False)
        (andP (eq_op bool_eqType m1 m2) (eq_op corner_eqType o1 o2))
    in
    let { main = x; other = x0 } = __top_assumption_0 in
    Obj.magic _evar_0_ x x0
  in
  let { main = x; other = x0 } = __top_assumption_ in Obj.magic _evar_0_ x x0

(** val eq_triangle_mixin : triangle Equality.mixin_of **)

let eq_triangle_mixin =
  { Equality.op = eq_triangle; Equality.mixin_of__1 = eq_triangleP }

(** val triangle_eqType : Equality.coq_type **)

let triangle_eqType =
  Obj.magic eq_triangle_mixin

(** val triangle_choiceMixin : triangle Choice.mixin_of **)

let triangle_choiceMixin =
  canChoiceMixin (prod_choiceType bool_choiceType corner_choiceType)
    (fun tr -> Obj.magic (Pair (tr.main, tr.other))) (fun p -> { main =
    (fst (Obj.magic p)); other = (snd (Obj.magic p)) })

(** val triangle_choiceType : Choice.coq_type **)

let triangle_choiceType =
  { Choice.base = (Equality.coq_class triangle_eqType); Choice.mixin =
    (Obj.magic triangle_choiceMixin) }

(** val triangle_countMixin : triangle Countable.mixin_of **)

let triangle_countMixin =
  canCountMixin (prod_countType bool_countType corner_countType) (fun tr ->
    Obj.magic (Pair (tr.main, tr.other))) (fun p -> { main =
    (fst (Obj.magic p)); other = (snd (Obj.magic p)) })

(** val triangle_countType : Countable.coq_type **)

let triangle_countType =
  { Countable.base = (Choice.coq_class triangle_choiceType);
    Countable.mixin = (Obj.magic triangle_countMixin) }

(** val triangle_finMixin : Finite.mixin_of **)

let triangle_finMixin =
  Finite.coq_EnumMixin triangle_countType (Obj.magic triangles)

(** val triangle_finType : Finite.coq_type **)

let triangle_finType =
  { Finite.base = (Choice.coq_class triangle_choiceType); Finite.mixin =
    triangle_finMixin }

(** val set_tnth : nat -> 'a1 tuple_of -> ordinal -> 'a1 -> 'a1 tuple_of **)

let set_tnth n arr i a =
  set_nth (tnth_default n arr i) (tval n arr) (nat_of_ord n i) a

type board = triangle option tuple_of

(** val all_pos : nat -> Finite.sort list **)

let all_pos max_slices =
  enum_mem (ordinal_finType max_slices)
    (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType))

type vertex = (ordinal, corner) prod

(** val nextn : nat -> nat -> nat **)

let nextn max_slices m =
  match leq (S (S m)) max_slices with
  | True -> S m
  | False -> O

(** val prevn : nat -> nat -> nat **)

let prevn max_slices = function
| O -> pred max_slices
| S n -> n

(** val next : nat -> ordinal -> ordinal **)

let next max_slices m =
  nextn max_slices (nat_of_ord max_slices m)

(** val prev : nat -> ordinal -> ordinal **)

let prev max_slices m =
  prevn max_slices (nat_of_ord max_slices m)

(** val vcolor : nat -> board -> vertex -> color option **)

let vcolor max_slices coloring v =
  match tnth max_slices coloring (fst v) with
  | Some t ->
    let { main = col; other = o } = t in
    (match eq_op corner_eqType (snd (Obj.magic v)) (Obj.magic o) with
     | True -> Some (negb col)
     | False -> Some col)
  | None -> None

(** val next_corner : nat -> vertex -> vertex -> bool **)

let next_corner max_slices v1 v2 =
  let Pair (n1, c1) = v1 in
  let Pair (n2, c2) = v2 in
  (match eq_op (ordinal_eqType max_slices) (Obj.magic next max_slices n1)
           (Obj.magic n2) with
   | True ->
     (match match eq_op corner_eqType (Obj.magic c1) (Obj.magic Right) with
            | True -> eq_op corner_eqType (Obj.magic c2) (Obj.magic Left)
            | False -> False with
      | True -> True
      | False ->
        (match eq_op corner_eqType (Obj.magic c1) (Obj.magic Center) with
         | True -> eq_op corner_eqType (Obj.magic c2) (Obj.magic Center)
         | False -> False))
   | False -> False)

(** val adj : nat -> board -> vertex rel **)

let adj max_slices coloring v1 v2 =
  match match match match eq_op (ordinal_eqType max_slices)
                            (fst (Obj.magic v1)) (fst (Obj.magic v2)) with
                    | True -> True
                    | False -> next_corner max_slices v1 v2 with
              | True -> True
              | False -> next_corner max_slices v2 v1 with
        | True -> isSome (vcolor max_slices coloring v1)
        | False -> False with
  | True ->
    eq_op (option_eqType bool_eqType)
      (Obj.magic vcolor max_slices coloring v1)
      (Obj.magic vcolor max_slices coloring v2)
  | False -> False

(** val valid_port : nat -> board -> vertex -> bool **)

let valid_port max_slices coloring v =
  match snd v with
  | Center -> False
  | Left ->
    eq_op (option_eqType bool_eqType)
      (Obj.magic vcolor max_slices coloring v) (Obj.magic (Some white))
  | Right ->
    eq_op (option_eqType bool_eqType)
      (Obj.magic vcolor max_slices coloring v) (Obj.magic (Some black))

(** val diff : nat -> nat -> nat **)

let diff n1 n2 =
  let d = subn n1 n2 in (match d with
                         | O -> subn n2 n1
                         | S _ -> d)

(** val valid_path : nat -> board -> vertex -> vertex list -> bool **)

let valid_path max_slices coloring v p =
  match match match path (adj max_slices coloring) v p with
              | True -> valid_port max_slices coloring v
              | False -> False with
        | True -> valid_port max_slices coloring (last v p)
        | False -> False with
  | True ->
    let d =
      diff (nat_of_ord max_slices (fst v))
        (nat_of_ord max_slices (fst (last v p)))
    in
    (match leq (S (S O)) d with
     | True -> leq (S (S d)) max_slices
     | False -> False)
  | False -> False

(** val next_vertices : nat -> ordinal -> (ordinal, corner) prod list **)

let next_vertices max_slices n =
  allpairs (fun x x0 -> Pair (x, x0)) (Cons ((prev max_slices n), (Cons (n,
    (Cons ((next max_slices n), Nil)))))) (Cons (Center, (Cons (Left, (Cons
    (Right, Nil))))))

(** val find_path :
    nat -> board -> nat -> vertex -> vertex pred_sort -> vertex list list **)

let rec find_path max_slices coloring h v p =
  match h with
  | O -> Nil
  | S h0 ->
    (match in_mem (Obj.magic v)
             (mem
               (seq_predType
                 (prod_eqType (ordinal_eqType max_slices) corner_eqType)) p) with
     | True -> Nil
     | False ->
       cat
         (match valid_path max_slices coloring v (Obj.magic p) with
          | True -> Cons ((Cons (v, (Obj.magic p))), Nil)
          | False -> Nil)
         (let nexts = next_vertices max_slices (fst v) in
          flatten
            (map0 (fun v' ->
              Obj.magic find_path max_slices coloring h0 v' (Cons (v,
                (Obj.magic p))))
              (filter (fun v' -> adj max_slices coloring v v') nexts))))

(** val all_ports : nat -> (Finite.sort, corner) prod list **)

let all_ports max_slices =
  allpairs (fun x x0 -> Pair (x, x0)) (all_pos max_slices) (Cons (Left, (Cons
    (Right, Nil))))

(** val all_paths : nat -> board -> vertex list list **)

let all_paths max_slices coloring =
  flatten
    (map0 (fun v ->
      find_path max_slices coloring (muln (S (S (S O))) max_slices)
        (Obj.magic v) (Obj.magic Nil))
      (filter (fun v -> valid_port max_slices coloring (Obj.magic v))
        (all_ports max_slices)))

(** val pre_boards : nat -> board -> triangle option tuple_of list **)

let pre_boards max_slices coloring =
  map0 (fun i -> set_tnth max_slices coloring (Obj.magic i) None)
    (filter (fun i -> isSome (tnth max_slices coloring (Obj.magic i)))
      (all_pos max_slices))

(** val final_board : nat -> board -> bool **)

let final_board max_slices coloring =
  match match all isSome (tval max_slices coloring) with
        | True -> nilp (all_paths max_slices coloring)
        | False -> False with
  | True -> True
  | False ->
    (match negb (nilp (all_paths max_slices coloring)) with
     | True ->
       has (fun col -> nilp (all_paths max_slices col))
         (pre_boards max_slices coloring)
     | False -> False)

(** val all_final : nat -> board list **)

let all_final max_slices =
  filter (fun x -> final_board max_slices x)
    (Obj.magic enum_mem
      (Finite.clone
        (tuple_finType max_slices (option_finType triangle_finType))
        (Finite.coq_class
          (tuple_finType max_slices (option_finType triangle_finType))))
      (mem predPredType (Obj.magic PredOfSimpl.coerce pred_of_argType)))

(** val has_color : nat -> color -> board -> vertex list -> bool **)

let has_color max_slices c coloring = function
| Nil -> False
| Cons (v, _) ->
  eq_op (option_eqType bool_eqType) (Obj.magic vcolor max_slices coloring v)
    (Obj.magic (Some c))

(** val classify : nat -> board -> (bool, bool) sum **)

let classify max_slices coloring =
  let paths = all_paths max_slices coloring in
  (match has (has_color max_slices white coloring) paths with
   | True ->
     (match has (has_color max_slices black coloring) paths with
      | True -> Inl True
      | False -> Inr white)
   | False ->
     (match has (has_color max_slices black coloring) paths with
      | True -> Inr black
      | False -> Inl False))

type results = { total : nat; no_path : nat; both_colors : nat;
                 only_white : nat; only_black : nat }

(** val all_results : nat -> results **)

let all_results max_slices =
  let kinds = map0 (classify max_slices) (all_final max_slices) in
  { total = (size kinds); no_path =
  (count
    (PredOfSimpl.coerce
      (Obj.magic pred1 (sum_eqType bool_eqType bool_eqType) (Inl False)))
    kinds); both_colors =
  (count
    (PredOfSimpl.coerce
      (Obj.magic pred1 (sum_eqType bool_eqType bool_eqType) (Inl True)))
    kinds); only_white =
  (count
    (PredOfSimpl.coerce
      (Obj.magic pred1 (sum_eqType bool_eqType bool_eqType) (Inr white)))
    kinds); only_black =
  (count
    (PredOfSimpl.coerce
      (Obj.magic pred1 (sum_eqType bool_eqType bool_eqType) (Inr black)))
    kinds) }
