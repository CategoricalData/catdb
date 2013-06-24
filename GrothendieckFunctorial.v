Require Import JMeq.
Require Export Grothendieck FunctorCategory SetCategory.
Require Import Common Notations Cat CommaCategory NatCategory FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section GrothendieckNondependentFunctorial.
  Local Open Scope category_scope.
  Local Notation "Cat / C" := (SliceCategoryOver Cat C).

  Context `(C : @Category).

  Let Cat := Cat.

  Section functorial.
    Section object_of.
      Definition CategoryOfElementsFunctorial_ObjectOf
                 (x : TypeCat ^ C)
      : Cat / C.
        hnf.
        match goal with
          | [ |- CommaCategory_Object ?F ?G ] => refine (_ : CommaCategory_ObjectT F G)
        end.
        hnf; simpl.
        exists (((CategoryOfElements x
                  : Category)
                 : Category),
               tt).
        exact (GrothendieckFunctor _).
      Defined.
    End object_of.

    Section morphism_of.
      Variables F G : Functor C TypeCat.
      Variable T : NaturalTransformation F G.

      Definition CategoryOfElementsFunctorial'_MorphismOf_ObjectOf
      : CategoryOfElements F -> CategoryOfElements G
        := fun x => Build_GrothendieckPair _
                                           _
                                           (T (GrothendieckC x) (GrothendieckX x)).

      Definition CategoryOfElementsFunctorial'_MorphismOf_MorphismOf
                 s d (m : Morphism (CategoryOfElements F) s d)
      : Morphism (CategoryOfElements G)
                 (CategoryOfElementsFunctorial'_MorphismOf_ObjectOf s)
                 (CategoryOfElementsFunctorial'_MorphismOf_ObjectOf d).
        exists (proj1_sig m).
        abstract (
            destruct m;
            let H := fresh in
            pose proof (Commutes T) as H;
            simpl in *;
              fg_equal;
            repeat rewrite_rev_hyp;
            reflexivity
          ).
      Defined.

      Definition CategoryOfElementsFunctorial'_MorphismOf
      : Functor (CategoryOfElements F) (CategoryOfElements G).
        refine (Build_Functor (CategoryOfElements F) (CategoryOfElements G)
                                         CategoryOfElementsFunctorial'_MorphismOf_ObjectOf
                                         CategoryOfElementsFunctorial'_MorphismOf_MorphismOf
                                         _
                                         _);
        abstract (simpl; simpl_eq; reflexivity).
      Defined.

      Definition CategoryOfElementsFunctorial_MorphismOf
      : Morphism (Cat / C)
                 (CategoryOfElementsFunctorial_ObjectOf F)
                 (CategoryOfElementsFunctorial_ObjectOf G).
        hnf.
        match goal with
          | [ |- CommaCategory_Morphism ?F ?G ]
            => refine (_ : CommaCategory_MorphismT F G)
        end.
        hnf; simpl.
        exists (CategoryOfElementsFunctorial'_MorphismOf, eq_refl).
        abstract (simpl; functor_eq).
      Defined.
    End morphism_of.

    Local Ltac t :=
      repeat match goal with
               | _ => intro
               | _ => reflexivity
               | _ => apply CommaCategory_Morphism_eq
               | _ => progress simpl
               | _ => progress simpl_eq
               | _ => progress destruct_head_hnf @GrothendieckPair
               | _ => progress apply f_equal
               | _ => progress apply Functor_eq
               | _ => progress JMeq_eq
               | _ => progress expand
             end.

    Definition CategoryOfElementsFunctorial'
    : Functor (TypeCat ^ C) Cat.
      refine (Build_Functor (TypeCat ^ C) Cat
                                       (fun x => CategoryOfElements x : Category)
                                       CategoryOfElementsFunctorial'_MorphismOf
                                       _
                                       _);
      abstract t.
    Defined.

    Definition CategoryOfElementsFunctorial
    : Functor (TypeCat ^ C) (Cat / C).
      refine (Build_Functor (TypeCat ^ C) (Cat / C)
                                       CategoryOfElementsFunctorial_ObjectOf
                                       CategoryOfElementsFunctorial_MorphismOf
                                       _
                                       _);
      abstract t.
    Defined.
  End functorial.
End GrothendieckNondependentFunctorial.
