Require Export SpecializedCommaCategory ProductCategory.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Section CommaCategory.
  Context `(A : @SpecializedCategory objA).
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).
  Variable S : SpecializedFunctor A C.
  Variable T : SpecializedFunctor B C.

  Definition CommaCategoryProjection : SpecializedFunctor (S ↓ T) (A * B)
    := Build_SpecializedFunctor (S ↓ T) (A * B)
                                (@projT1 _ _)
                                (fun _ _ m => proj1_sig m)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).
End CommaCategory.

Section SliceCategory.
  Context `(A : @SpecializedCategory objA).

  Local Arguments ComposeFunctors' / .

  Definition ArrowCategoryProjection : SpecializedFunctor (ArrowSpecializedCategory A) A
    := Eval simpl in ComposeFunctors' fst_Functor (CommaCategoryProjection _ (IdentityFunctor A)).

  Definition SliceCategoryOverProjection (a : A) : SpecializedFunctor (A / a) A
    := Eval simpl in ComposeFunctors' fst_Functor (CommaCategoryProjection (IdentityFunctor A) _).

  Definition CosliceCategoryOverProjection (a : A) : SpecializedFunctor (a \ A) A
    := ComposeFunctors' snd_Functor (CommaCategoryProjection _ (IdentityFunctor A)).

  Section Slice_Coslice.
    Context `(C : @SpecializedCategory objC).
    Variable a : C.
    Variable S : SpecializedFunctor A C.

    Section Slice.
      Definition SliceCategoryProjection : SpecializedFunctor (S ↓ a) A
        := Eval simpl in ComposeFunctors' fst_Functor (CommaCategoryProjection S (FunctorFromTerminal C a)).
    End Slice.

    Section Coslice.
      Definition CosliceCategoryProjection : SpecializedFunctor (a ↓ S) A
        := Eval simpl in ComposeFunctors' snd_Functor (CommaCategoryProjection (FunctorFromTerminal C a) S).
      Check CosliceCategoryProjection.
      Eval simpl in SpecializedFunctor (a ↓ S) A.
    End Coslice.
  End Slice_Coslice.
End SliceCategory.
