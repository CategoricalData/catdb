Require Import Setoid.
Require Import Common EquivalenceRelation Category Functor NaturalTransformation.

Section FunctorCategory.
  Variable C D : Category.

  (*
     There is a category Fun(C, D) of functors from [C] to [D].

     I'm a bit worried about the difference between equivalent functors and
     equal functors.
     *)
  Definition FunctorCategory : Category.
    refine {| Object := Functor C D;
      Morphism := @NaturalTransformation C D;
      MorphismsEquivalent' := @NaturalTransformationsEquivalent C D;
      Compose := @NTComposeT C D;
      Identity := @IdentityNaturalTransformation C D
      |}; abstract (t; try simpl_transitivity;
        unfold NTComposeT; unfold NaturalTransformationsEquivalent in *; t).
  Defined.
End FunctorCategory.
