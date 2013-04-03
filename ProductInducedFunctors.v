Require Export ProductCategory Functor NaturalTransformation.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Local Ltac t :=
  intros; simpl; repeat (rewrite <- FCompositionOf || rewrite <- FIdentityOf);
  apply f_equal; expand; autorewrite with morphism;
  reflexivity.

Section ProductInducedFunctors.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).

  Variable F : SpecializedFunctor (C * D) E.

  Definition InducedProductFstFunctor (d : D) : SpecializedFunctor C E.
    refine (Build_SpecializedFunctor
              C E
              (fun c => F (c, d))
              (fun _ _ m => MorphismOf F (s := (_, d)) (d := (_, d)) (m, Identity d))
              _
              _);
    abstract t.
  Defined.

  Definition InducedProductSndFunctor (c : C) : SpecializedFunctor D E.
    refine (Build_SpecializedFunctor
              D E
              (fun d => F (c, d))
              (fun _ _ m => MorphismOf F (s := (c, _)) (d := (c, _)) (Identity c, m))
              _
              _);
    abstract t.
  Defined.
End ProductInducedFunctors.

Notation "F ⟨ c , - ⟩" := (InducedProductSndFunctor F c) : functor_scope.
Notation "F ⟨ - , d ⟩" := (InducedProductFstFunctor F d) : functor_scope.

Section ProductInducedNaturalTransformations.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).

  Variable F : SpecializedFunctor (C * D) E.

  Definition InducedProductFstNaturalTransformation {s d} (m : Morphism C s d) : SpecializedNaturalTransformation (F ⟨ s, - ⟩) (F ⟨ d, - ⟩).
    match goal with
      | [ |- SpecializedNaturalTransformation ?F0 ?G0 ] =>
        refine (Build_SpecializedNaturalTransformation F0 G0
          (fun d => MorphismOf F (s := (_, d)) (d := (_, d)) (m, Identity (C := D) d))
          _
        )
    end;
    abstract t.
  Defined.

  Definition InducedProductSndNaturalTransformation {s d} (m : Morphism D s d) : SpecializedNaturalTransformation (F ⟨ -, s ⟩) (F ⟨ - , d ⟩).
    match goal with
      | [ |- SpecializedNaturalTransformation ?F0 ?G0 ] =>
        refine (Build_SpecializedNaturalTransformation F0 G0
          (fun c => MorphismOf F (s := (c, _)) (d := (c, _)) (Identity (C := C) c, m))
          _
        )
    end;
    abstract t.
  Defined.
End ProductInducedNaturalTransformations.

Notation "F ⟨ f , - ⟩" := (InducedProductSndNaturalTransformation F f) : natural_transformation_scope.
Notation "F ⟨ - , f ⟩" := (InducedProductFstNaturalTransformation F f) : natural_transformation_scope.
