
type __ = Obj.t

type bool =
| True
| False

val negb : bool -> bool

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

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2

val pred : nat -> nat

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

type reflect =
| ReflectT
| ReflectF

val ssr_have : 'a1 -> ('a1 -> 'a2) -> 'a2

module Option :
 sig
  val apply : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

  val bind : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option

  val map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option
 end

type ('aT, 'rT) simpl_fun =
  'aT -> 'rT
  (* singleton inductive, whose constructor was SimplFun *)

val fun_of_simpl : ('a1, 'a2) simpl_fun -> 'a1 -> 'a2

val comp : ('a2 -> 'a1) -> ('a3 -> 'a2) -> 'a3 -> 'a1

val pcomp : ('a2 -> 'a1 option) -> ('a3 -> 'a2 option) -> 'a3 -> 'a1 option

val tag : ('a1, 'a2) sigT -> 'a1

val tagged : ('a1, 'a2) sigT -> 'a2

val tagged0 : 'a1 -> 'a2 -> ('a1, 'a2) sigT

val addb : bool -> bool -> bool

val isSome : 'a1 option -> bool

val iffP : bool -> reflect -> reflect

val idP : bool -> reflect

val andP : bool -> bool -> reflect

type 't pred0 = 't -> bool

type 't predType =
  __ -> 't pred0
  (* singleton inductive, whose constructor was PredType *)

type 't pred_sort = __

val predPredType : 'a1 predType

type 't simpl_pred = ('t, bool) simpl_fun

val simplPred : 'a1 pred0 -> 'a1 simpl_pred

val predT : 'a1 simpl_pred

module PredOfSimpl :
 sig
  val coerce : 'a1 simpl_pred -> 'a1 pred0
 end

val pred_of_argType : 'a1 simpl_pred

type 't rel = 't -> 't pred0

type 't mem_pred =
  't pred0
  (* singleton inductive, whose constructor was Mem *)

val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort

val in_mem : 'a1 -> 'a1 mem_pred -> bool

val simpl_of_mem : 'a1 mem_pred -> 'a1 simpl_pred

val mem : 'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred

val predType0 : ('a2 -> 'a1 pred0) -> 'a1 predType

module Equality :
 sig
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  val op : 'a1 mixin_of -> 'a1 rel

  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort mixin_of
 end

val eq_op : Equality.coq_type -> Equality.sort rel

val eqP : Equality.coq_type -> Equality.sort Equality.axiom

val eqb : bool -> bool -> bool

val eqbP : bool Equality.axiom

val bool_eqMixin : bool Equality.mixin_of

val bool_eqType : Equality.coq_type

val pred1 : Equality.coq_type -> Equality.sort -> Equality.sort simpl_pred

type 't subType = { val0 : (__ -> 't); sub0 : ('t -> __ -> __);
                    subType__2 : (__ -> ('t -> __ -> __) -> __ -> __) }

type 't sub_sort = __

val sub0 : 'a1 pred0 -> 'a1 subType -> 'a1 -> 'a1 sub_sort

val insub : 'a1 pred0 -> 'a1 subType -> 'a1 -> 'a1 sub_sort option

val inj_eqAxiom :
  Equality.coq_type -> ('a1 -> Equality.sort) -> 'a1 Equality.axiom

val val_eqP :
  Equality.coq_type -> Equality.sort pred0 -> Equality.sort subType ->
  Equality.sort sub_sort Equality.axiom

val pair_eq :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort, Equality.sort)
  prod rel

val pair_eqP :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort, Equality.sort)
  prod Equality.axiom

val prod_eqMixin :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort, Equality.sort)
  prod Equality.mixin_of

val prod_eqType : Equality.coq_type -> Equality.coq_type -> Equality.coq_type

val opt_eq :
  Equality.coq_type -> Equality.sort option -> Equality.sort option -> bool

val opt_eqP : Equality.coq_type -> Equality.sort option Equality.axiom

val option_eqMixin :
  Equality.coq_type -> Equality.sort option Equality.mixin_of

val option_eqType : Equality.coq_type -> Equality.coq_type

val tagged_as :
  Equality.coq_type -> (Equality.sort, 'a1) sigT -> (Equality.sort, 'a1) sigT
  -> 'a1

val tag_eq :
  Equality.coq_type -> (Equality.sort -> Equality.coq_type) ->
  (Equality.sort, Equality.sort) sigT -> (Equality.sort, Equality.sort) sigT
  -> bool

val tag_eqP :
  Equality.coq_type -> (Equality.sort -> Equality.coq_type) ->
  (Equality.sort, Equality.sort) sigT Equality.axiom

val tag_eqMixin :
  Equality.coq_type -> (Equality.sort -> Equality.coq_type) ->
  (Equality.sort, Equality.sort) sigT Equality.mixin_of

val tag_eqType :
  Equality.coq_type -> (Equality.sort -> Equality.coq_type) ->
  Equality.coq_type

val sum_eq :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort, Equality.sort)
  sum -> (Equality.sort, Equality.sort) sum -> bool

val sum_eqP :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort, Equality.sort)
  sum Equality.axiom

val sum_eqMixin :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort, Equality.sort)
  sum Equality.mixin_of

val sum_eqType : Equality.coq_type -> Equality.coq_type -> Equality.coq_type

val eqn : nat -> nat -> bool

val eqnP : nat Equality.axiom

val nat_eqMixin : nat Equality.mixin_of

val nat_eqType : Equality.coq_type

val addn_rec : nat -> nat -> nat

val addn : nat -> nat -> nat

val subn_rec : nat -> nat -> nat

val subn : nat -> nat -> nat

val leq : nat -> nat -> bool

val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

val iteri : nat -> (nat -> 'a1 -> 'a1) -> 'a1 -> 'a1

val iterop : nat -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

val muln_rec : nat -> nat -> nat

val muln : nat -> nat -> nat

val expn_rec : nat -> nat -> nat

val expn : nat -> nat -> nat

val nat_of_bool : bool -> nat

val odd : nat -> bool

val double_rec : nat -> nat

val double : nat -> nat

val size : 'a1 list -> nat

val nilp : 'a1 list -> bool

val ohead : 'a1 list -> 'a1 option

val ncons : nat -> 'a1 -> 'a1 list -> 'a1 list

val nseq : nat -> 'a1 -> 'a1 list

val cat : 'a1 list -> 'a1 list -> 'a1 list

val last : 'a1 -> 'a1 list -> 'a1

val nth : 'a1 -> 'a1 list -> nat -> 'a1

val set_nth : 'a1 -> 'a1 list -> nat -> 'a1 -> 'a1 list

val filter : 'a1 pred0 -> 'a1 list -> 'a1 list

val count : 'a1 pred0 -> 'a1 list -> nat

val has : 'a1 pred0 -> 'a1 list -> bool

val all : 'a1 pred0 -> 'a1 list -> bool

val eqseq :
  Equality.coq_type -> Equality.sort list -> Equality.sort list -> bool

val eqseqP : Equality.coq_type -> Equality.sort list Equality.axiom

val seq_eqMixin : Equality.coq_type -> Equality.sort list Equality.mixin_of

val seq_eqType : Equality.coq_type -> Equality.coq_type

val mem_seq : Equality.coq_type -> Equality.sort list -> Equality.sort -> bool

type seq_eqclass = Equality.sort list

val pred_of_seq : Equality.coq_type -> seq_eqclass -> Equality.sort pred_sort

val seq_predType : Equality.coq_type -> Equality.sort predType

val map0 : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val pmap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list

val iota : nat -> nat -> nat list

val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val flatten : 'a1 list list -> 'a1 list

val allpairs : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

module CodeSeq :
 sig
  val code : nat list -> nat

  val decode_rec : nat -> nat -> nat -> nat list

  val decode : nat -> nat list
 end

val seq_of_opt : 'a1 option -> 'a1 list

val tag_of_pair : ('a1, 'a2) prod -> ('a1, 'a2) sigT

val pair_of_tag : ('a1, 'a2) sigT -> ('a1, 'a2) prod

module Choice :
 sig
  type 't mixin_of =
    't pred0 -> nat -> 't option
    (* singleton inductive, whose constructor was Mixin *)

  val find : 'a1 mixin_of -> 'a1 pred0 -> nat -> 'a1 option

  type 't class_of = { base : 't Equality.mixin_of; mixin : 't mixin_of }

  val base : 'a1 class_of -> 'a1 Equality.mixin_of

  val mixin : 'a1 class_of -> 'a1 mixin_of

  type coq_type =
    __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort class_of

  val eqType : coq_type -> Equality.coq_type

  module InternalTheory :
   sig
    val find : coq_type -> sort pred0 -> nat -> sort option
   end
 end

val pcanChoiceMixin :
  Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1 option) ->
  'a1 Choice.mixin_of

val canChoiceMixin :
  Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort -> 'a1) -> 'a1
  Choice.mixin_of

val sub_choiceMixin :
  Choice.coq_type -> Choice.sort pred0 -> Choice.sort subType -> Choice.sort
  sub_sort Choice.mixin_of

val seq_choiceMixin : Choice.coq_type -> Choice.sort list Choice.mixin_of

val seq_choiceType : Choice.coq_type -> Choice.coq_type

val tagged_choiceMixin :
  Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> (Choice.sort,
  Choice.sort) sigT Choice.mixin_of

val tagged_choiceType :
  Choice.coq_type -> (Choice.sort -> Choice.coq_type) -> Choice.coq_type

val nat_choiceMixin : nat Choice.mixin_of

val nat_choiceType : Choice.coq_type

val bool_choiceMixin : bool Choice.mixin_of

val bool_choiceType : Choice.coq_type

val option_choiceMixin : Choice.coq_type -> Choice.sort option Choice.mixin_of

val option_choiceType : Choice.coq_type -> Choice.coq_type

val prod_choiceMixin :
  Choice.coq_type -> Choice.coq_type -> (Choice.sort, Choice.sort) prod
  Choice.mixin_of

val prod_choiceType : Choice.coq_type -> Choice.coq_type -> Choice.coq_type

module Countable :
 sig
  type 't mixin_of = { pickle : ('t -> nat); unpickle : (nat -> 't option) }

  val pickle : 'a1 mixin_of -> 'a1 -> nat

  val unpickle : 'a1 mixin_of -> nat -> 'a1 option

  type 't class_of = { base : 't Choice.class_of; mixin : 't mixin_of }

  val base : 'a1 class_of -> 'a1 Choice.class_of

  val mixin : 'a1 class_of -> 'a1 mixin_of

  type coq_type =
    __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort class_of

  val choiceType : coq_type -> Choice.coq_type
 end

val unpickle0 : Countable.coq_type -> nat -> Countable.sort option

val pickle0 : Countable.coq_type -> Countable.sort -> nat

val pcanCountMixin :
  Countable.coq_type -> ('a1 -> Countable.sort) -> (Countable.sort -> 'a1
  option) -> 'a1 Countable.mixin_of

val canCountMixin :
  Countable.coq_type -> ('a1 -> Countable.sort) -> (Countable.sort -> 'a1) ->
  'a1 Countable.mixin_of

val sub_countMixin :
  Countable.coq_type -> Countable.sort pred0 -> Countable.sort subType ->
  Countable.sort sub_sort Countable.mixin_of

val pickle_seq : Countable.coq_type -> Countable.sort list -> nat

val unpickle_seq : Countable.coq_type -> nat -> Countable.sort list option

val seq_countMixin :
  Countable.coq_type -> Countable.sort list Countable.mixin_of

val seq_countType : Countable.coq_type -> Countable.coq_type

val pickle_tagged :
  Countable.coq_type -> (Countable.sort -> Countable.coq_type) ->
  (Countable.sort, Countable.sort) sigT -> nat

val unpickle_tagged :
  Countable.coq_type -> (Countable.sort -> Countable.coq_type) -> nat ->
  (Countable.sort, Countable.sort) sigT option

val tag_countMixin :
  Countable.coq_type -> (Countable.sort -> Countable.coq_type) ->
  (Countable.sort, Countable.sort) sigT Countable.mixin_of

val tag_countType :
  Countable.coq_type -> (Countable.sort -> Countable.coq_type) ->
  Countable.coq_type

val nat_countMixin : nat Countable.mixin_of

val nat_countType : Countable.coq_type

val bool_countMixin : bool Countable.mixin_of

val bool_countType : Countable.coq_type

val option_countMixin :
  Countable.coq_type -> Countable.sort option Countable.mixin_of

val prod_countMixin :
  Countable.coq_type -> Countable.coq_type -> (Countable.sort,
  Countable.sort) prod Countable.mixin_of

val prod_countType :
  Countable.coq_type -> Countable.coq_type -> Countable.coq_type

val path : 'a1 rel -> 'a1 -> 'a1 list -> bool

module Finite :
 sig
  type mixin_of = { mixin_base : Equality.sort Countable.mixin_of;
                    mixin_enum : Equality.sort list }

  val mixin_base :
    Equality.coq_type -> mixin_of -> Equality.sort Countable.mixin_of

  val mixin_enum : Equality.coq_type -> mixin_of -> Equality.sort list

  val coq_EnumMixin : Countable.coq_type -> Countable.sort list -> mixin_of

  type 't class_of = { base : 't Choice.class_of; mixin : mixin_of }

  val base : 'a1 class_of -> 'a1 Choice.class_of

  val mixin : 'a1 class_of -> mixin_of

  val base2 : 'a1 class_of -> 'a1 Countable.class_of

  type coq_type =
    __ class_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort class_of

  val clone : coq_type -> 'a1 class_of -> coq_type

  val choiceType : coq_type -> Choice.coq_type

  val countType : coq_type -> Countable.coq_type

  module type EnumSig =
   sig
    val enum : coq_type -> sort list
   end

  module EnumDef :
   EnumSig
 end

val enum_mem : Finite.coq_type -> Finite.sort mem_pred -> Finite.sort list

val image_mem :
  Finite.coq_type -> (Finite.sort -> 'a1) -> Finite.sort mem_pred -> 'a1 list

val codom : Finite.coq_type -> (Finite.sort -> 'a1) -> 'a1 list

val option_enum : Finite.coq_type -> Finite.sort option list

val option_finMixin : Finite.coq_type -> Finite.mixin_of

val option_finType : Finite.coq_type -> Finite.coq_type

type ordinal = nat
  (* singleton inductive, whose constructor was Ordinal *)

val nat_of_ord : nat -> ordinal -> nat

val ordinal_subType : nat -> nat subType

val ordinal_eqMixin : nat -> ordinal Equality.mixin_of

val ordinal_eqType : nat -> Equality.coq_type

val ordinal_choiceMixin : nat -> ordinal Choice.mixin_of

val ordinal_choiceType : nat -> Choice.coq_type

val ordinal_countMixin : nat -> ordinal Countable.mixin_of

val ord_enum : nat -> ordinal list

val ordinal_finMixin : nat -> Finite.mixin_of

val ordinal_finType : nat -> Finite.coq_type

type 't tuple_of =
  't list
  (* singleton inductive, whose constructor was Tuple *)

val tval : nat -> 'a1 tuple_of -> 'a1 list

val tuple_subType : nat -> 'a1 list subType

val tnth_default : nat -> 'a1 tuple_of -> ordinal -> 'a1

val tnth : nat -> 'a1 tuple_of -> ordinal -> 'a1

val tuple_eqMixin :
  nat -> Equality.coq_type -> Equality.sort tuple_of Equality.mixin_of

val tuple_eqType : nat -> Equality.coq_type -> Equality.coq_type

val tuple_choiceMixin :
  nat -> Choice.coq_type -> Choice.sort tuple_of Choice.mixin_of

val tuple_choiceType : nat -> Choice.coq_type -> Choice.coq_type

val tuple_countMixin :
  nat -> Countable.coq_type -> Countable.sort tuple_of Countable.mixin_of

module type FinTupleSig =
 sig
  val enum : nat -> Finite.coq_type -> Finite.sort tuple_of list
 end

module FinTuple :
 FinTupleSig

val tuple_finMixin : nat -> Finite.coq_type -> Finite.mixin_of

val tuple_finType : nat -> Finite.coq_type -> Finite.coq_type

type corner =
| Center
| Left
| Right

val corners : corner list

val eq_corner : corner -> corner -> bool

val eq_cornerP : corner Equality.axiom

val eq_corner_mixin : corner Equality.mixin_of

val corner_eqType : Equality.coq_type

val nat_of_corner : corner -> nat

val corner_of_nat : nat -> corner

val corner_choiceMixin : corner Choice.mixin_of

val corner_choiceType : Choice.coq_type

val corner_countMixin : corner Countable.mixin_of

val corner_countType : Countable.coq_type

type color = bool

val black : bool

val white : bool

type triangle = { main : color; other : corner }

val triangles : triangle list

val eq_triangle : triangle -> triangle -> bool

val eq_triangleP : triangle Equality.axiom

val eq_triangle_mixin : triangle Equality.mixin_of

val triangle_eqType : Equality.coq_type

val triangle_choiceMixin : triangle Choice.mixin_of

val triangle_choiceType : Choice.coq_type

val triangle_countMixin : triangle Countable.mixin_of

val triangle_countType : Countable.coq_type

val triangle_finMixin : Finite.mixin_of

val triangle_finType : Finite.coq_type

val set_tnth : nat -> 'a1 tuple_of -> ordinal -> 'a1 -> 'a1 tuple_of

type board = triangle option tuple_of

val all_pos : nat -> Finite.sort list

type vertex = (ordinal, corner) prod

val nextn : nat -> nat -> nat

val prevn : nat -> nat -> nat

val next : nat -> ordinal -> ordinal

val prev : nat -> ordinal -> ordinal

val vcolor : nat -> board -> vertex -> color option

val next_corner : nat -> vertex -> vertex -> bool

val adj : nat -> board -> vertex rel

val valid_port : nat -> board -> vertex -> bool

val diff : nat -> nat -> nat

val valid_path : nat -> board -> vertex -> vertex list -> bool

val next_vertices : nat -> ordinal -> (ordinal, corner) prod list

val find_path :
  nat -> board -> nat -> vertex -> vertex pred_sort -> vertex list list

val all_ports : nat -> (Finite.sort, corner) prod list

val all_paths : nat -> board -> vertex list list

val pre_boards : nat -> board -> triangle option tuple_of list

val final_board : nat -> board -> bool

val all_final : nat -> board list

val has_color : nat -> color -> board -> vertex list -> bool

val classify : nat -> board -> (bool, bool) sum

type results = { total : nat; no_path : nat; both_colors : nat;
                 only_white : nat; only_black : nat }

val all_results : nat -> results
