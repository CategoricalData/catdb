Require Export NatCategory ProductCategory.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope category_scope.

Section swap.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Definition SwapFunctor : SpecializedFunctor (C * D) (D * C).
    refine (Build_SpecializedFunctor (C * D) (D * C)
                                     (fun cd => (snd cd, fst cd))
                                     (fun _ _ m => (snd m, fst m))
                                     _
                                     _);
    abstract (
        intros; simpl; present_spcategory; simpl_eq; reflexivity
      ).
  Defined.
End swap.

Section Law0.
  Context `(C : @SpecializedCategory objC).

  Definition ProductLaw0Functor : SpecializedFunctor (C * 0) 0.
    refine (Build_SpecializedFunctor (C * 0) 0
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

  Definition ProductLaw0Functor_Inverse : SpecializedFunctor 0 (C * 0).
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
  Context `(C : @SpecializedCategory objC).

  Definition ProductLaw0'Functor : SpecializedFunctor (0 * C) 0
    := ComposeFunctors (ProductLaw0Functor C) (SwapFunctor _ _).

  Definition ProductLaw0'Functor_Inverse : SpecializedFunctor 0 (0 * C)
    := ComposeFunctors (SwapFunctor _ _) (ProductLaw0Functor_Inverse C).

  Lemma ProductLaw0' : ComposeFunctors ProductLaw0'Functor ProductLaw0'Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ProductLaw0'Functor_Inverse ProductLaw0'Functor = IdentityFunctor _.
  Proof.
    split; functor_eq;
    destruct_head_hnf @prod;
    destruct_head_hnf Empty_set.
  Qed.
End Law0'.

Section Law1.
  Context `(C : @SpecializedCategory objC).

  Definition ProductLaw1Functor : SpecializedFunctor (C * 1) C
    := fst_Functor.

  Definition ProductLaw1Functor_Inverse : SpecializedFunctor C (C * 1).
    refine (Build_SpecializedFunctor C (C * 1)
                                     (fun c => (c, tt))
                                     (fun s d m => (m, eq_refl))
                                     _
                                     _);
    abstract (
        intros; simpl in *; present_spcategory; simpl_eq; reflexivity
      ).
  Defined.

  Lemma ProductLaw1 : ComposeFunctors ProductLaw1Functor ProductLaw1Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ProductLaw1Functor_Inverse ProductLaw1Functor = IdentityFunctor _.
  Proof.
    split; functor_eq;
    destruct_head_hnf @prod;
    destruct_head_hnf unit;
    destruct_head_hnf @eq;
    reflexivity.
  Qed.
End Law1.

Section Law1'.
  Context `(C : @SpecializedCategory objC).

  Definition ProductLaw1'Functor : SpecializedFunctor (1 * C) C
    := ComposeFunctors (ProductLaw1Functor C) (SwapFunctor _ _).

  Definition ProductLaw1'Functor_Inverse : SpecializedFunctor C (1 * C)
    := ComposeFunctors (SwapFunctor _ _) (ProductLaw1Functor_Inverse C).

  Lemma ProductLaw1' : ComposeFunctors ProductLaw1'Functor ProductLaw1'Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ProductLaw1'Functor_Inverse ProductLaw1'Functor = IdentityFunctor _.
  Proof.
    split; functor_eq;
    destruct_head_hnf @prod;
    destruct_head_hnf unit;
    destruct_head_hnf @eq;
    reflexivity.
  Qed.
End Law1'.
