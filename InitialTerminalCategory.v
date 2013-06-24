Require Export Category Functor.
Require Import Common Notations NatCategory.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section InitialTerminal.
   Definition InitialCategory : Category := 0.
   Definition TerminalCategory : Category := 1.
End InitialTerminal.

Section Functors.
  Variable C : Category.

  Definition FunctorTo1 : Functor C 1
    := Build_Functor C 1 (fun _ => tt) (fun _ _ _ => eq_refl) (fun _ _ _ _ _ => eq_refl) (fun _ => eq_refl).
  Definition FunctorToTerminal : Functor C TerminalCategory := FunctorTo1.

  Definition FunctorFrom1 (c : C) : Functor 1 C
    := Build_Functor 1 C (fun _ => c) (fun _ _ _ => Identity c) (fun _ _ _ _ _ => eq_sym (@RightIdentity _ _ _ _)) (fun _ => eq_refl).
  Definition FunctorFromTerminal (c : C) : Functor TerminalCategory C := FunctorFrom1 c.

  Definition FunctorFrom0 : Functor 0 C
    := Build_Functor 0 C (fun x => match x with end) (fun x _ _ => match x with end) (fun x _ _ _ _ => match x with end) (fun x => match x with end).
  Definition FunctorFromInitial : Functor InitialCategory C := FunctorFrom0.
End Functors.

Section FunctorsUnique.
  Variable C : Category.

  Lemma InitialCategoryFunctorUnique
  : forall F F' : Functor InitialCategory C,
      F = F'.
  Proof.
    functor_eq; destruct_head_hnf @Empty_set.
  Qed.

  Lemma InitialCategoryFunctor'Unique
  : forall F F' : Functor C InitialCategory,
      F = F'.
  Proof.
    intros F F'.
    functor_eq; auto.
    match goal with
      | [ x : _ |- _ ] => solve [ let H := fresh in assert (H := F x); destruct H ]
    end.
  Qed.

  Lemma InitialCategoryInitial
  : forall F, F = FunctorFromInitial C.
  Proof.
    intros; apply InitialCategoryFunctorUnique.
  Qed.

  Lemma TerminalCategoryFunctorUnique
  : forall F F' : Functor C TerminalCategory,
      F = F'.
  Proof.
    functor_eq; auto.
  Qed.

  Lemma TerminalCategoryTerminal
  : forall F, F = FunctorToTerminal C.
  Proof.
    intros; apply TerminalCategoryFunctorUnique.
  Qed.
End FunctorsUnique.
