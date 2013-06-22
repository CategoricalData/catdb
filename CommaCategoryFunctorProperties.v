Require Import JMeq.
Require Export CommaCategoryFunctors.
Require Import Common Notations FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Local Ltac slice_t :=
  repeat match goal with
           | [ |- @eq (SpecializedFunctor _ _) _ _ ] => apply Functor_eq; intros
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
               destruct_sig
             )
         end.

Section FCompositionOf.
  Context `(A : SpecializedCategory).
  Context `(B : SpecializedCategory).
  Context `(C : SpecializedCategory).

  Lemma CommaCategoryInducedFunctor_FCompositionOf s d d'
        (m1 : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d)
        (m2 : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) d d') :
    CommaCategoryInducedFunctor (Compose m2 m1)
    = ComposeFunctors (CommaCategoryInducedFunctor m2) (CommaCategoryInducedFunctor m1).
    Time slice_t. (* 44 s *)
  Qed.

  Lemma CommaCategoryInducedFunctor_FIdentityOf (x : Object ((OppositeCategory (C ^ A)) * (C ^ B))) :
    CommaCategoryInducedFunctor (Identity x)
    = IdentityFunctor _.
    Time slice_t. (* 11 s *)
  Qed.
End FCompositionOf.
