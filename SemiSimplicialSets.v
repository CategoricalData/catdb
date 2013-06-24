Require Export SimplicialSets.
Require Import Notations Subcategory SetCategory FunctorCategoryFunctorial.

Generalizable Variables objC.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Notation Δ := SimplexCategory.

Section SemiSimplicialSets.
  (* Quoting David Spivak:

     Consider the subcategory of Δ with the same objects (wide) but
     only injective morphisms.  If we call that Γ (which is
     nonstandard), then semi-simplicial sets (also a non-standard
     term) are Fun(Γᵒᵖ,Set). Define the obvious inclusion Γ -> Δ,
     which we will use to make simplicial sets without having to worry
     about "degneracies". *)

  Definition SemiSimplexCategory : Category.
    eapply (WideSubcategory Δ (@IsMonomorphism _));
    abstract eauto with morphism.
  Defined.

  Local Notation Γ := SemiSimplexCategory.

  Definition SemiSimplexCategoryInclusionFunctor : Functor Γ Δ
    := WideSubcategoryInclusionFunctor _ _ _ _.

  Definition SemiSimplicialCategory (C : Category) := (C ^ (OppositeCategory Γ))%category.

  Definition SemiSimplicialSet := SemiSimplicialCategory SetCat.
  Definition SemiSimplicialType := SemiSimplicialCategory TypeCat.
  Definition SemiSimplicialProp := SemiSimplicialCategory PropCat.
End SemiSimplicialSets.

Notation SemiSimplicialOf obj := (let C := CatOf obj in SemiSimplicialCategory C).
