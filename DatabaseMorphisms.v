Require Import List Setoid Classes.RelationClasses Arith FunctionalExtensionality.
Require Export Database.
Require Import Common.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

(** * Morphisms between database schemas *)
Section RowTypeMorphisms.
  (** A [RowTypeMorphism r1 r2] is a way of assigning columns of [r1]
      to columns of [r2].  We require that the types of the columns be
      the same. *)

  Inductive RowTypeMorphism : RowType -> RowType -> Type :=
  | RTMNil : forall toTs, RowTypeMorphism nil toTs
  | RTMCons : forall T fromTs toTs,
                Column T toTs
                -> RowTypeMorphism fromTs toTs
                -> RowTypeMorphism (T :: fromTs) toTs.
  Print ColumnList.

  Fixpoint ColumnListOfRowTypeMorphism r1 r2 (m : RowTypeMorphism r1 r2) : ColumnList r2 r1
    := match m with
           | RTMNil ts => CNil ts
           | RTMCons T fromTs toTs c m' => @CCons T toTs fromTs c (ColumnListOfRowTypeMorphism m')
         end.

  Fixpoint RowTypeMorphismOfColumnList r1 r2 (m : ColumnList r1 r2) : RowTypeMorphism r2 r1
    := match m with
         | CNil ts => RTMNil ts
         | CCons T fromTs toTs c m' => @RTMCons T toTs fromTs c (RowTypeMorphismOfColumnList m')
       end.

  Global Coercion ColumnListOfRowTypeMorphism : RowTypeMorphism >-> ColumnList.
  Global Coercion RowTypeMorphismOfColumnList : ColumnList >-> RowTypeMorphism.

  Lemma RowTypeMorphism_ColumnList_iso r1 r2 (m : RowTypeMorphism r1 r2)
  : ((m : ColumnList _ _) : RowTypeMorphism _ _) = m.
    induction m; simpl; try rewrite IHm; reflexivity.
  Qed.

  Lemma ColumnList_RowTypeMorphism_iso r1 r2 (m : ColumnList r1 r2)
  : ((m : RowTypeMorphism _ _) : ColumnList _ _) = m.
    induction m; simpl; try rewrite IHm; reflexivity.
  Qed.
End RowTypeMorphisms.
