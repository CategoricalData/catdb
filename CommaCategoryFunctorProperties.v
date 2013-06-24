Require Import JMeq.
Require Export CommaCategoryFunctors.
Require Import Common Notations FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Local Ltac slice_t :=
  apply Functor_eq; repeat intro;
  simpl in * |- ;
  destruct_head prod;
  destruct_head CommaCategory_Morphism;
  destruct_head CommaCategory_Object;
  try apply CommaCategory_Morphism_JMeq;
  try apply CommaCategory_Object_eq;
  simpl;
  autorewrite with morphism;
  trivial.

Section FCompositionOf.
  Variable A : Category.
  Variable B : Category.
  Variable C : Category.

  Lemma CommaCategoryInducedFunctor_FCompositionOf s d d'
        (m1 : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d)
        (m2 : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) d d') :
    CommaCategoryInducedFunctor (Compose m2 m1)
    = ComposeFunctors (CommaCategoryInducedFunctor m2) (CommaCategoryInducedFunctor m1).
  Proof.
    abstract slice_t. (* 6.824 s *)
  Qed.

  Lemma CommaCategoryInducedFunctor_FIdentityOf (x : Object ((OppositeCategory (C ^ A)) * (C ^ B))) :
    CommaCategoryInducedFunctor (Identity x)
    = IdentityFunctor _.
    abstract slice_t. (* 1.748 s *)
  Qed.
End FCompositionOf.
