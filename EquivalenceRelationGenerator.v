Require Import Setoid.
Require Import Common.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Gen.
  Variable A : Type.
  Variable equiv : relation A.

  Inductive EquivalenceOf : A -> A -> Prop :=
  | gen_underlying : forall a b, equiv a b -> EquivalenceOf a b
  | gen_refl : forall a, EquivalenceOf a a
  | gen_sym : forall a b, EquivalenceOf a b -> EquivalenceOf b a
  | gen_trans : forall a b c, EquivalenceOf a b -> EquivalenceOf b c -> EquivalenceOf a c.

  Hint Constructors EquivalenceOf.

  Lemma EquivalenceOf_Equivalence : Equivalence EquivalenceOf.
    constructor; eauto.
  Defined.

  Definition generateEquivalence : { equiv' : A -> A -> Prop | Equivalence equiv' & forall a b, equiv a b -> equiv' a b }.
    exists EquivalenceOf.
    exact EquivalenceOf_Equivalence.
    eauto.
  Defined.
End Gen.

Add Parametric Relation A equiv : _ (@EquivalenceOf A equiv)
  reflexivity proved by (@gen_refl _ _)
  symmetry proved by (@gen_sym _ _)
  transitivity proved by (@gen_trans _ _)
    as EquivalenceOf_rel.
