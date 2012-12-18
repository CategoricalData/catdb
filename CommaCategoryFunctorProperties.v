Require Import JMeq.
Require Export CommaCategoryFunctors.
Require Import Common Notations FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope category_scope.

Local Ltac slice_t :=
  repeat match goal with
           | [ |- @JMeq (sig _) _ (sig _) _ ] => apply sig_JMeq
           | [ |- (_ -> _) = (_ -> _) ] => apply f_type_equal
           | _ => progress (intros; simpl in *; trivial; subst_body)
           | _ => progress simpl_eq
           | _ => progress (repeat rewrite Associativity; repeat rewrite LeftIdentity; repeat rewrite RightIdentity)
           | _ => progress JMeq_eq
           | _ => apply f_equal
           | [ |- JMeq (?f ?x) (?f ?y) ] =>
             apply (@f_equal1_JMeq _ _ x y f)
           | [ |- JMeq (?f ?x) (?g ?y) ] =>
             apply (@f_equal_JMeq _ _ _ _ x y f g)
           | _ =>
             progress (
               destruct_type @CommaSpecializedCategory_Object;
               destruct_type @CommaSpecializedCategory_Morphism;
               destruct_sig;
               present_spcategory
             )
           | [ |- @eq (SpecializedFunctor _ _) _ _ ] => functor_eq
         end.

Section FCompositionOf.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.

  Section Slice.
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F).
    Local Notation "C / c" := (@SliceSpecializedCategoryOver _ _ C c).

    Lemma SliceCategoryInducedFunctor_FCompositionOf s d d' (m1 : Morphism D s d) (m2 : Morphism D d d')
    : SliceCategoryInducedFunctor F s d' (Compose m2 m1)
      = ComposeFunctors (SliceCategoryInducedFunctor F d d' m2) (SliceCategoryInducedFunctor F s d m1).
      slice_t.
    Qed.

    Lemma SliceCategoryInducedFunctor_FIdentityOf x
    : SliceCategoryInducedFunctor F x x (Identity x) = IdentityFunctor _.
      slice_t.
    Qed.
  End Slice.

  Section Coslice.
    Local Notation "A ↓ F" := (CosliceSpecializedCategory A F).
    Local Notation "C / c" := (@SliceSpecializedCategoryOver _ _ C c).

    Let DOp := OppositeCategory D.

    Lemma CosliceCategoryInducedFunctor_FCompositionOf s d d' (m1 : Morphism D d s) (m2 : Morphism D d' d)
    : CosliceCategoryInducedFunctor F s d' (Compose m1 m2)
      = ComposeFunctors (CosliceCategoryInducedFunctor F d d' m2) (CosliceCategoryInducedFunctor F s d m1).
      slice_t.
    Qed.

    Lemma CosliceCategoryInducedFunctor_FIdentityOf x
    : CosliceCategoryInducedFunctor F x x (Identity x) = IdentityFunctor _.
      slice_t.
    Qed.
  End Coslice.
End FCompositionOf.
