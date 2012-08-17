Require Export ProductCategory.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Section ProductInducedFunctors.
  Context `(C : @SpecializedCategory objC morC).
  Context `(D : @SpecializedCategory objD morD).
  Context `(E : @SpecializedCategory objE morE).

  Variable F : SpecializedFunctor (C * D) E.

  Local Ltac t :=
    simpl; intros; present_spfunctor;
      rewrite <- FCompositionOf || rewrite <- FIdentityOf;
        f_equal; simpl_eq;
        autorewrite with core;
          reflexivity.

  Definition InducedProductFstFunctor (d : D) : SpecializedFunctor C E.
    refine {| ObjectOf' := (fun c => F (c, d));
      MorphismOf' := (fun _ _ m => MorphismOf F (s := (_, d)) (d := (_, d)) (m, Identity d))
    |};
    abstract t.
  Defined.

  Definition InducedProductSndFunctor (c : C) : SpecializedFunctor D E.
    refine {| ObjectOf' := (fun d => F (c, d));
      MorphismOf' := (fun _ _ m => MorphismOf F (s := (c, _)) (d := (c, _)) (Identity c, m))
    |};
    abstract t.
  Defined.
End ProductInducedFunctors.

Notation "F ( c , - )" := (InducedProductSndFunctor F c) : functor_scope.
Notation "F ( - , d )" := (InducedProductFstFunctor F d) : functor_scope.
