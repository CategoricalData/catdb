Require Export Grothendieck FunctorCategory SetCategory.
Require Import Common Notations SmallCat.

Set Implicit Arguments.

Generalizable All Variables.

Section GrothendieckNondependentFunctorial.
  Context `(C : @SpecializedCategory objC).

  Section functorial.
    Variables F G : SpecializedFunctor C TypeCat.
    Variable T : SpecializedNaturalTransformation F G.

    Definition CategoryOfElementsFunctorial_ObjectOf
    : CategoryOfElements F -> CategoryOfElements G
      := fun x => Build_GrothendieckPair _
                                         _
                                         (T (GrothendieckC x) (GrothendieckX x)).

    Definition CategoryOfElementsFunctorial_MorphismOf
               s d (m : Morphism (CategoryOfElements F) s d)
    : Morphism (CategoryOfElements G)
               (CategoryOfElementsFunctorial_ObjectOf s)
               (CategoryOfElementsFunctorial_ObjectOf d).
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

    Definition CategoryOfElementsFunctorial
    : Functor (CategoryOfElements F) (CategoryOfElements G).
      refine (Build_SpecializedFunctor (CategoryOfElements F) (CategoryOfElements G)
                                       CategoryOfElementsFunctorial_ObjectOf
                                       CategoryOfElementsFunctorial_MorphismOf
                                       _
                                       _);
      abstract (simpl; simpl_eq; reflexivity).
    Defined.
  End functorial.
End GrothendieckNondependentFunctorial.
