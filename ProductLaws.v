Require Export NatCategory ProductCategory.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Section swap.
  Definition SwapFunctor (C : Category) `(D : Category)
  : Functor (C * D) (D * C)
    := Build_Functor (C * D) (D * C)
                                (fun cd => (snd cd, fst cd))
                                (fun _ _ m => (snd m, fst m))
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Lemma ProductLawSwap (C : Category) `(D : Category)
  : ComposeFunctors (SwapFunctor C D) (SwapFunctor D C) = IdentityFunctor _.
    functor_eq; intuition.
  Qed.
End swap.

Section Law0.
  Variable C : Category.

  Definition ProductLaw0Functor : Functor (C * 0) 0.
    refine (Build_Functor (C * 0) 0
                                     (@snd _ _)
                                     (fun _ _ => @snd _ _)
                                     _
                                     _);
    abstract (
        intros;
        destruct_head_hnf @prod;
        destruct_head Empty_set
      ).
  Defined.

  Definition ProductLaw0Functor_Inverse : Functor 0 (C * 0).
    repeat esplit;
    intros; destruct_head_hnf Empty_set.
    Grab Existential Variables.
    intros; destruct_head_hnf Empty_set.
    intros; destruct_head_hnf Empty_set.
  Defined.

  Lemma ProductLaw0 : ComposeFunctors ProductLaw0Functor ProductLaw0Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ProductLaw0Functor_Inverse ProductLaw0Functor = IdentityFunctor _.
  Proof.
    split; functor_eq;
    destruct_head_hnf @prod;
    destruct_head_hnf Empty_set.
  Qed.
End Law0.

Section Law0'.
  Variable C : Category.

  Let ProductLaw0'Functor' : Functor (0 * C) 0.
    functor_simpl_abstract_trailing_props (ComposeFunctors (ProductLaw0Functor C) (SwapFunctor _ _)).
  Defined.
  Definition ProductLaw0'Functor : Functor (0 * C) 0 := Eval hnf in ProductLaw0'Functor'.

  Let ProductLaw0'Functor_Inverse' : Functor 0 (0 * C).
    functor_simpl_abstract_trailing_props (ComposeFunctors (SwapFunctor _ _) (ProductLaw0Functor_Inverse C)).
  Defined.
  Definition ProductLaw0'Functor_Inverse : Functor 0 (0 * C) := Eval hnf in ProductLaw0'Functor_Inverse'.

  Lemma ProductLaw0' : ComposeFunctors ProductLaw0'Functor ProductLaw0'Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ProductLaw0'Functor_Inverse ProductLaw0'Functor = IdentityFunctor _.
  Proof.
    split; functor_eq;
    destruct_head_hnf @prod;
    destruct_head_hnf Empty_set.
  Qed.
End Law0'.

Section Law1.
  Variable C : Category.

  Let ProductLaw1Functor' : Functor (C * 1) C.
    functor_simpl_abstract_trailing_props (fst_Functor (C := C) (D := 1)).
  Defined.
  Definition ProductLaw1Functor : Functor (C * 1) C
    := Eval hnf in ProductLaw1Functor'.

  Definition ProductLaw1Functor_Inverse : Functor C (C * 1).
    refine (Build_Functor C (C * 1)
                                     (fun c => (c, tt))
                                     (fun s d m => (m, eq_refl))
                                     _
                                     _);
    abstract (
        intros; simpl in *; simpl_eq; reflexivity
      ).
  Defined.

  Lemma ProductLaw1 : ComposeFunctors ProductLaw1Functor ProductLaw1Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ProductLaw1Functor_Inverse ProductLaw1Functor = IdentityFunctor _.
  Proof.
    split; functor_eq;
    destruct_head_hnf @prod;
    destruct_head_hnf @eq;
    destruct_head_hnf unit;
    reflexivity.
  Qed.
End Law1.

Section Law1'.
  Variable C : Category.

  Definition ProductLaw1'Functor' : Functor (1 * C) C.
    functor_simpl_abstract_trailing_props (ComposeFunctors (ProductLaw1Functor C) (SwapFunctor _ _)).
  Defined.
  Definition ProductLaw1'Functor : Functor (1 * C) C := Eval hnf in ProductLaw1'Functor'.

  Let ProductLaw1'Functor_Inverse' : Functor C (1 * C).
    functor_simpl_abstract_trailing_props (ComposeFunctors (SwapFunctor _ _) (ProductLaw1Functor_Inverse C)).
  Defined.
  Definition ProductLaw1'Functor_Inverse : Functor C (1 * C) := Eval hnf in ProductLaw1'Functor_Inverse'.

  Lemma ProductLaw1' : ComposeFunctors ProductLaw1'Functor ProductLaw1'Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ProductLaw1'Functor_Inverse ProductLaw1'Functor = IdentityFunctor _.
  Proof.
    split; functor_eq;
    destruct_head_hnf @prod;
    destruct_head_hnf @eq;
    destruct_head_hnf unit;
    reflexivity.
  Qed.
End Law1'.
