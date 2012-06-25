Require Export Category.
Require Import Common Functor NaturalTransformation.

Set Implicit Arguments.

Section FunctorCategory.
  Variable C D : Category.

  Hint Resolve Associativity LeftIdentity RightIdentity.

  (*
     There is a category Fun(C, D) of functors from [C] to [D].
     *)
  Definition FunctorCategory : Category.
    refine {| Object := Functor C D;
      Morphism := @NaturalTransformation C D;
      Compose := @NTComposeT C D;
      Identity := @IdentityNaturalTransformation C D
      |}; abstract (nt_eq; auto).
  Defined.
End FunctorCategory.
