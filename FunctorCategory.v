Require Export Category SmallCategory Functor SmallNaturalTransformation NaturalTransformation.
Require Import Common.

Set Implicit Arguments.

Section FunctorCategory.
  Variable C : SmallCategory.
  Variable D : Category.

  Hint Resolve Associativity LeftIdentity RightIdentity.

  (*
     There is a category Fun(C, D) of functors from [C] to [D].
     *)
  Definition FunctorCategory : Category.
    refine {| Object := Functor C D;
      Morphism := @SmallNaturalTransformation C D;
      Compose := @SNTComposeT C D;
      Identity := @IdentitySmallNaturalTransformation C D
      |}; abstract (snt_eq; auto).
  Defined.
End FunctorCategory.
