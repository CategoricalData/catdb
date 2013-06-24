Require Export ProductCategory Functor NaturalTransformation.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Ltac t :=
  intros; simpl; repeat (rewrite <- FCompositionOf || rewrite <- FIdentityOf);
  apply f_equal; expand; autorewrite with morphism;
  reflexivity.

Section ProductInducedFunctors.
  Variable C : Category.
  Variable D : Category.
  Variable E : Category.

  Variable F : Functor (C * D) E.

  Definition InducedProductFstFunctor (d : D) : Functor C E.
    refine {| ObjectOf := (fun c => F (c, d));
      MorphismOf := (fun _ _ m => MorphismOf F (s := (_, d)) (d := (_, d)) (m, Identity d))
    |};
    abstract t.
  Defined.

  Definition InducedProductSndFunctor (c : C) : Functor D E.
    refine {| ObjectOf := (fun d => F (c, d));
      MorphismOf := (fun _ _ m => MorphismOf F (s := (c, _)) (d := (c, _)) (Identity c, m))
    |};
    abstract t.
  Defined.
End ProductInducedFunctors.

Notation "F ⟨ c , - ⟩" := (InducedProductSndFunctor F c) : functor_scope.
Notation "F ⟨ - , d ⟩" := (InducedProductFstFunctor F d) : functor_scope.

Section ProductInducedNaturalTransformations.
  Variable C : Category.
  Variable D : Category.
  Variable E : Category.

  Variable F : Functor (C * D) E.

  Definition InducedProductFstNaturalTransformation {s d} (m : Morphism C s d) : NaturalTransformation (F ⟨ s, - ⟩) (F ⟨ d, - ⟩).
    match goal with
      | [ |- NaturalTransformation ?F0 ?G0 ] =>
        refine (Build_NaturalTransformation F0 G0
          (fun d => MorphismOf F (s := (_, d)) (d := (_, d)) (m, Identity (C := D) d))
          _
        )
    end;
    abstract t.
  Defined.

  Definition InducedProductSndNaturalTransformation {s d} (m : Morphism D s d) : NaturalTransformation (F ⟨ -, s ⟩) (F ⟨ - , d ⟩).
    match goal with
      | [ |- NaturalTransformation ?F0 ?G0 ] =>
        refine (Build_NaturalTransformation F0 G0
          (fun c => MorphismOf F (s := (c, _)) (d := (c, _)) (Identity (C := C) c, m))
          _
        )
    end;
    abstract t.
  Defined.
End ProductInducedNaturalTransformations.

Notation "F ⟨ f , - ⟩" := (InducedProductSndNaturalTransformation F f) : natural_transformation_scope.
Notation "F ⟨ - , f ⟩" := (InducedProductFstNaturalTransformation F f) : natural_transformation_scope.
