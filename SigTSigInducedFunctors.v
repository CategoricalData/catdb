Require Import ProofIrrelevance.
Require Export SigTInducedFunctors SigTSigCategory.
Require Import Common FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section T2.
  (* use dummy variables so we don't have to specify the types of
     all these hypotheses *)
  Context `(dummy0 : @Category_sigT_sig A Pobj0 Pmor0 Pidentity0 Pcompose0).
  Context `(dummy1 : @Category_sigT_sig A Pobj1 Pmor1 Pidentity1 Pcompose1).

  Let sigT_sig_cat0 := @Category_sigT_sig A Pobj0 Pmor0 Pidentity0 Pcompose0.
  Let sigT_sig_cat1 := @Category_sigT_sig A Pobj1 Pmor1 Pidentity1 Pcompose1.

  Variable P_ObjectOf : forall x, Pobj0 x -> Pobj1 x.

  Let InducedT2Functor_sigT_sig_ObjectOf (x : sigT Pobj0) : sigT Pobj1
    := existT _ (projT1 x) (P_ObjectOf (projT2 x)).

  Hypothesis P_MorphismOf : forall (s d : sigT Pobj0) (m : sig (Pmor0 s d)),
    Pmor1
    (existT Pobj1 (projT1 s) (P_ObjectOf (projT2 s)))
    (existT Pobj1 (projT1 d) (P_ObjectOf (projT2 d)))
    (proj1_sig m).

  Let InducedT2Functor_sigT_sig_MorphismOf (s d : sigT Pobj0) (m : sig (Pmor0 s d)) :
    sig (Pmor1 (InducedT2Functor_sigT_sig_ObjectOf s) (InducedT2Functor_sigT_sig_ObjectOf d))
    := exist _ (proj1_sig m) (@P_MorphismOf s d m).

  Let sig_of_sigT' (A : Type) (P : A -> Prop) (X : sigT P) := exist P (projT1 X) (projT2 X).
  Let sigT_of_sig' (A : Type) (P : A -> Prop) (X : sig P) := existT P (proj1_sig X) (proj2_sig X).

  Definition InducedT2Functor_sigT_sig : Functor sigT_sig_cat0 sigT_sig_cat1.
    eapply (ComposeFunctors (sigT_functor_sigT_sig _ _ _ _) (ComposeFunctors _ (sigT_sig_functor_sigT _ _ _ _))).
    Grab Existential Variables.
    eapply (@InducedT2Functor_sigT A Pobj0 Pmor0 Pidentity0 Pcompose0 _ _ _ Pobj1 Pmor1 Pidentity1 Pcompose1 _ _ _
      P_ObjectOf (fun s d m => @P_MorphismOf s d (sig_of_sigT' m)));
    subst_body;
    abstract (simpl; intros; apply proof_irrelevance).
  Defined.
End T2.
