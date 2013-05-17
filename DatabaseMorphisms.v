Require Import List Setoid Classes.RelationClasses Arith FunctionalExtensionality ProofIrrelevance.
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

Section ListIndex.
  Variable T : Type.

  Inductive ListIndex : list T -> Type :=
  | ListFirst : forall x l, ListIndex (x :: l)
  | ListNext : forall x l, ListIndex l -> ListIndex (x :: l).

  Fixpoint NatOfListIndex l (i : ListIndex l) : { n : nat | n < length l }
    := match i in (ListIndex l0) return {n : nat | n < length l0} with
         | ListFirst _ _
           => exist _ 0 (lt_0_Sn _)
         | ListNext x l0 i0
           => exist (fun n : nat => n < length (x :: l0))
                    (S (proj1_sig (@NatOfListIndex l0 i0)))
                    (lt_n_S _ _ (proj2_sig (@NatOfListIndex l0 i0)))
       end.

   Fixpoint ListIndexOfNat l n (H : n < length l) {struct n} : ListIndex l
     := match l as l return (n < length l -> ListIndex l) with
          | nil => fun H0 => match lt_n_0 n H0 with end
          | t :: l0
            => match
              n as n return (n < length (t :: l0) -> ListIndex (t :: l0))
            with
              | 0 => fun _ => ListFirst t l0
              | S n0 =>
                fun H1 =>
                  ListNext t
                           (@ListIndexOfNat l0 n0 (lt_S_n _ _ H1))
            end
        end H.

   Global Arguments ListIndexOfNat : clear implicits.

   Local Hint Extern 0 (@eq ?T _ _) => match type of T with Prop => apply proof_irrelevance end.
   Local Hint Extern 2 => apply f_equal.
   Local Hint Extern 1 => exfalso; eapply lt_n_0.

   Local Ltac t :=
     repeat match goal with
               | _ => intro
               | _ => progress simpl in *
               | _ => progress trivial
               | _ => progress destruct_to_empty_set_in_match
               | _ => progress eauto
               | [ |- appcontext[@ListIndexOfNat _ _ (?f ?x)] ] => generalize (f x); intro
               | [ H : _ |- _ ] => erewrite <- H; solve [ eauto ]
               | _ => apply f_equal
             end.

  Lemma ListIndex_iso_1 l
  : forall i H, @ListIndexOfNat l (proj1_sig (NatOfListIndex i)) H = i.
    induction i; t.
  Qed.

  Lemma ListIndex_iso_2 l
  : forall n H, proj1_sig (NatOfListIndex (@ListIndexOfNat l n H)) = n.
    intros n.
    revert l.
    induction n; t;
    destruct l; t.
  Qed.
End ListIndex.

Section SyntacticalListMap.
  Variables T1 T2 : Type.
  Inductive SyntacticalListMap : list T1 -> list T2 -> Type :=
  | SLMNil : forall l2, SyntacticalListMap nil l2
  | SLMCons : forall t1 l1 l2,
                ListIndex l2
                -> SyntacticalListMap l1 l2
                -> SyntacticalListMap (t1 :: l1) l2.

  Fixpoint SyntacticalListMapOfSemanticalListMap l1 l2 {struct l1}
  : ({ n : nat | n < length l1 } -> { n : nat | n < length l2 })
    -> SyntacticalListMap l1 l2
    := match
        l1 as l1
        return
        (({n : nat | n < length l1} -> {n : nat | n < length l2}) -> SyntacticalListMap l1 l2)
      with
        | nil => fun _ => SLMNil l2
        | t :: l3 =>
          fun f =>
            SLMCons
              t
              (ListIndexOfNat l2 _ (proj2_sig (f (exist _ 0 (lt_0_Sn (length l3))))))
              (@SyntacticalListMapOfSemanticalListMap
                 l3
                 l2
                 (fun nH =>
                    f (exist _ (S (proj1_sig nH)) (lt_n_S _ _ (proj2_sig nH)))))
      end.

  Fixpoint SemanticalListMapOfSyntacticalListMap l1 l2 (m : SyntacticalListMap l1 l2)
  : { n : nat | n < length l1 } -> { n : nat | n < length l2 }
    := match
        m in (SyntacticalListMap l1 l2)
        return ({n : nat | n < length l1} -> {n : nat | n < length l2})
      with
        | SLMNil _ => fun nH0 => match lt_n_0 _ (proj2_sig nH0) with end
        | SLMCons t1 l1' l2' l m0 =>
          fun nH =>
            match nH with
              | exist 0 _ => NatOfListIndex l
              | exist (S n') H =>
                @SemanticalListMapOfSyntacticalListMap l1' l2' m0
                                                       (exist _ n' (lt_S_n _ _ H))
            end
      end.

   Local Hint Extern 0 (@eq ?T _ _) => match type of T with Prop => apply proof_irrelevance end.
   Local Hint Extern 2 => apply f_equal.
   Local Hint Extern 1 => exfalso; eapply lt_n_0.
   Local Hint Extern 0 => apply ListIndex_iso_1.

   Local Ltac t :=
     repeat match goal with
               | _ => intro
               | _ => progress simpl in *
               | _ => progress trivial
               | _ => progress destruct_to_empty_set_in_match
               | _ => progress eauto
               | [ |- appcontext[@ListIndexOfNat _ _ (?f ?x)] ] => generalize (f x); intro
               | [ H : _ |- _ ] => erewrite <- H; solve [ eauto ]
               | [ |- appcontext[match ?E with _ => _ end] ] => progress destruct E
               | _ => apply f_equal
               | _ => progress (etransitivity; try eassumption; [])
               | _ => apply functional_extensionality_dep
               | _ => solve [ simpl_eq; trivial ]
               | _ => simpl_eq; rewrite ListIndex_iso_2
               | _ => apply f_equal2
             end.

  Lemma SemanticalListMapOfSyntacticalListMapOfSemanticalListMap_id l1 l2 m
  : @SyntacticalListMapOfSemanticalListMap l1 l2 (SemanticalListMapOfSyntacticalListMap m) = m.
    induction m; t.
  Qed.

  Lemma SyntacticalListMapOfSemanticalListMapOfSyntacticalListMap_id l1 l2 f
  : SemanticalListMapOfSyntacticalListMap (@SyntacticalListMapOfSemanticalListMap l1 l2 f) = f.
    revert l2 f.
    induction l1; t.
    rewrite IHl1.
    t.
  Qed.
End SyntacticalListMap.

Section TableMorphisms.
  (** A [TableMorphism m t1 t2] is, given a way [m] of assigning
      columns of [t1] to columns of [t2], a way of assigning each row
      in [t1] to a row in [t2].  We require that the types of the
      columns be the same. *)
  Definition TableMorphism rt1 rt2 (m : RowTypeMorphism rt1 rt2)
  : Table rt1 -> Table rt2 -> Type
    := @SyntacticalListMap _ _.
End TableMorphisms.

Section RowMorphisms.
  (** We can perform a pull-back along a RowTypeMorphism. *)

End RowMorphisms.
