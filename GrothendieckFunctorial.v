Require Import JMeq.
Require Export Grothendieck FunctorCategory SetCategory.
Require Import Common Notations SmallCat SpecializedCommaCategory NatCategory FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Section GrothendieckNondependentFunctorial.
  Local Open Scope category_scope.
  Local Notation "Cat / C" := (SliceSpecializedCategoryOver Cat C).

  Context `(C : @LocallySmallSpecializedCategory objC).

  Let Cat := LocallySmallCat.

  Section functorial.
    Section object_of.
      Definition CategoryOfElementsFunctorial_ObjectOf
                 (x : TypeCat ^ C)
      : Cat / C.
        hnf.
        match goal with
          | [ |- CommaSpecializedCategory_Object ?F ?G ] => refine (_ : CommaSpecializedCategory_ObjectT F G)
        end.
        hnf; simpl.
        exists (((CategoryOfElements x
                  : LocallySmallSpecializedCategory _)
                 : LocallySmallCategory),
               tt).
        exact (GrothendieckFunctor _).
      Defined.
    End object_of.

    Section morphism_of.
      Variables F G : SpecializedFunctor C TypeCat.
      Variable T : SpecializedNaturalTransformation F G.

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
        refine (Build_SpecializedFunctor (CategoryOfElements F) (CategoryOfElements G)
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
          | [ |- CommaSpecializedCategory_Morphism ?F ?G ]
            => refine (_ : CommaSpecializedCategory_MorphismT F G)
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
               | _ => progress simpl_eq
               | _ => progress destruct_head_hnf @GrothendieckPair
               | _ => progress apply f_equal
               | _ => progress apply Functor_eq
               | _ => progress JMeq_eq
               | _ => progress expand
             end.

    Definition CategoryOfElementsFunctorial'
    : SpecializedFunctor (TypeCat ^ C) Cat.
      refine (Build_SpecializedFunctor (TypeCat ^ C) Cat
                                       (fun x => CategoryOfElements x : LocallySmallSpecializedCategory _)
                                       CategoryOfElementsFunctorial'_MorphismOf
                                       _
                                       _);
      abstract t.
    Defined.

    Definition CategoryOfElementsFunctorial
    : SpecializedFunctor (TypeCat ^ C) (Cat / C).
      refine (Build_SpecializedFunctor (TypeCat ^ C) (Cat / C)
                                       CategoryOfElementsFunctorial_ObjectOf
                                       CategoryOfElementsFunctorial_MorphismOf
                                       _
                                       _);
      abstract t.
    Defined.
  End functorial.
End GrothendieckNondependentFunctorial.
