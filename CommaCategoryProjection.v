Require Export CommaCategory ProductCategory.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope functor_scope.
Local Open Scope category_scope.

Section CommaCategory.
  Variable A : Category.
  Variable B : Category.
  Variable C : Category.
  Variable S : Functor A C.
  Variable T : Functor B C.

  Definition CommaCategoryProjection : Functor (S ↓ T) (A * B)
    := Build_Functor (S ↓ T) (A * B)
                                (@projT1 _ _)
                                (fun _ _ m => proj1_sig m)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).
End CommaCategory.

Section SliceCategory.
  Variable A : Category.

  Local Arguments ComposeFunctors / .
  Local Arguments ComposeFunctors_FCompositionOf / .
  Local Arguments ComposeFunctors_FIdentityOf / .
  Local Transparent ComposeFunctors_FCompositionOf.
  Local Transparent ComposeFunctors_FIdentityOf.

  Definition ArrowCategoryProjection : Functor (ArrowCategory A) A
    := Eval simpl in fst_Functor ∘ CommaCategoryProjection _ (IdentityFunctor A).

  Definition SliceCategoryOverProjection (a : A) : Functor (A / a) A
    := Eval simpl in fst_Functor ∘ CommaCategoryProjection (IdentityFunctor A) _.

  Definition CosliceCategoryOverProjection (a : A) : Functor (a \ A) A
    := Eval simpl in snd_Functor ∘ CommaCategoryProjection _ (IdentityFunctor A).

  Section Slice_Coslice.
    Variable C : Category.
    Variable a : C.
    Variable S : Functor A C.

    Definition SliceCategoryProjection : Functor (S ↓ a) A
      := Eval simpl in fst_Functor ∘ CommaCategoryProjection S (FunctorFromTerminal C a).

    Definition CosliceCategoryProjection : Functor (a ↓ S) A
      := Eval simpl in snd_Functor ∘ CommaCategoryProjection (FunctorFromTerminal C a) S.
  End Slice_Coslice.
End SliceCategory.
