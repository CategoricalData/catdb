Require Import ProofIrrelevance.
Require Export CommaCategory.
Require Import Common DiscreteCategory.

Set Implicit Arguments.

Local Open Scope category_scope.

Section CommaCategory.
  (* [Definition]s are not sort-polymorphic, and it's too slow to not use
     [Definition]s, so we might as well use [Category]s rather than [SpecializedCategory]s. *)
  Variable A B C : Category.
  Variable S : Functor A C.
  Variable T : Functor B C.

  Local Notation "S ↓ T" := (CommaCategory S T) (at level 70, no associativity).

  Hint Resolve FCompositionOf FIdentityOf.

  Definition CommaCategoryProjection : Functor (S ↓ T) (A * B).
    refine (Build_SpecializedFunctor (S ↓ T) (A * B)
      (@projT1 _ _)
      (fun _ _ m => (proj1_sig m))
      _
      _
    ); abstract trivial.
  Defined.
End CommaCategory.

Section SliceCategory.
  Variables A C : Category.
  Variable a : C.
  Variable S : Functor A C.

  Definition SliceCategoryProjection : Functor (SliceCategory a S) A
    := ComposeFunctors fst_Functor (CommaCategoryProjection S (SliceCategory_Functor C a)).

  Definition CosliceCategoryProjection : Functor (CosliceCategory a S) A
    := ComposeFunctors snd_Functor (CommaCategoryProjection (SliceCategory_Functor C a) S).
End SliceCategory.
