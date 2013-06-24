Require Export SigTCategory Functor.
Require Import Common FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section T2.
  (* use dummy variables so we don't have to specify the types of
     all these hypotheses *)
  Context `(dummy0 : @Category_sigT A Pobj0 Pmor0 Pidentity0 Pcompose0 P_Associativity0 P_LeftIdentity0 P_RightIdentity0).
  Context `(dummy1 : @Category_sigT A Pobj1 Pmor1 Pidentity1 Pcompose1 P_Associativity1 P_LeftIdentity1 P_RightIdentity1).

  Let sigT_cat0 := @Category_sigT A Pobj0 Pmor0 Pidentity0 Pcompose0 P_Associativity0 P_LeftIdentity0 P_RightIdentity0.
  Let sigT_cat1 := @Category_sigT A Pobj1 Pmor1 Pidentity1 Pcompose1 P_Associativity1 P_LeftIdentity1 P_RightIdentity1.

  Variable P_ObjectOf : forall x, Pobj0 x -> Pobj1 x.

  Let InducedT2Functor_sigT_ObjectOf (x : sigT Pobj0) : sigT Pobj1
    := existT _ (projT1 x) (P_ObjectOf (projT2 x)).

  Variable P_MorphismOf : forall (s d : sigT Pobj0) (m : sigT (Pmor0 s d)),
    Pmor1
    (existT Pobj1 (projT1 s) (P_ObjectOf (projT2 s)))
    (existT Pobj1 (projT1 d) (P_ObjectOf (projT2 d)))
    (projT1 m).

  Let InducedT2Functor_sigT_MorphismOf (s d : sigT Pobj0) (m : sigT (Pmor0 s d)) : sigT (Pmor1 (InducedT2Functor_sigT_ObjectOf s) (InducedT2Functor_sigT_ObjectOf d))
    := existT _ (projT1 m) (@P_MorphismOf s d m).

  Hypothesis P_CompositionOf : forall s d d' (m1 : sigT (Pmor0 s d)) (m2 : sigT (Pmor0 d d')),
    P_MorphismOf (existT (Pmor0 s d') (Compose (projT1 m2) (projT1 m1)) (Pcompose0 (projT2 m2) (projT2 m1))) =
    Pcompose1 (P_MorphismOf m2) (P_MorphismOf m1).

  Hypothesis P_IdentityOf : forall o,
    P_MorphismOf (existT (Pmor0 o o) (Identity (projT1 o)) (Pidentity0 o)) =
    Pidentity1 (InducedT2Functor_sigT_ObjectOf o).

  Definition InducedT2Functor_sigT : Functor sigT_cat0 sigT_cat1.
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor C D
          InducedT2Functor_sigT_ObjectOf
          InducedT2Functor_sigT_MorphismOf
          _
          _
        )
    end;
    subst_body;
    abstract (
      simpl in *; intros; unfold Morphism; simpl_eq; try reflexivity; JMeq_eq;
        apply @P_CompositionOf || apply @P_IdentityOf
    ).
  Defined.
End T2.
