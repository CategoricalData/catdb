Require Export SimplicialSets.
Require Import Notations Subcategory SetCategory FunctorCategoryFunctorial.

Generalizable Variables objC.

Set Implicit Arguments.

Local Notation "'Δ'" := SimplexCategory : category_scope.

Section SemiSimplicialSets.
  (* Quoting David Spivak:

     Consider the subcategory of Δ with the same objects (wide) but
     only injective morphisms.  If we call that Γ (which is
     nonstandard), then semi-simplicial sets (also a non-standard
     term) are Fun(Γᵒᵖ,Set). Define the obvious inclusion Γ -> Δ,
     which we will use to make simplicial sets without having to worry
     about "degneracies". *)

  Definition SemiSimplexCategory : SpecializedCategory nat.
    eapply (WideSubcategory Δ (@IsMonomorphism _ _));
    abstract eauto with morphism.
  Defined.

  Local Notation "'Γ'" := SemiSimplexCategory : category_scope.

  Definition SemiSimplexCategoryInclusionFunctor : SpecializedFunctor Γ Δ
    := WideSubcategoryInclusionFunctor _ _ _ _.

  Definition SemiSimplicialCategory `(C : SpecializedCategory objC) := (C ^ (OppositeCategory Γ))%category.

  Definition SemiSimplicialSet := SemiSimplicialCategory SetCat.
  Definition SemiSimplicialType := SemiSimplicialCategory TypeCat.
  Definition SemiSimplicialProp := SemiSimplicialCategory PropCat.
End SemiSimplicialSets.

Notation "'SemiSimplicialOf' obj" := (let C := CatOf obj in SemiSimplicialCategory C) (at level 0).
