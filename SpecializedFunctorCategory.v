Require Export SpecializedCategory SpecializedFunctor SpecializedNaturalTransformation.
Require Import Common.

Set Implicit Arguments.

Section FunctorCategory.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.

  Hint Resolve Associativity LeftIdentity RightIdentity.

  (*
     There is a category Fun(C, D) of functors from [C] to [D].
     *)
  Definition SpecializedFunctorCategory : @SpecializedCategory (SpecializedFunctor C D) (@SpecializedNaturalTransformation _ _ _ _ C D).
    refine {| Compose' := @SPNTComposeT _ _ _ _ C D;
      Identity' := @IdentitySpecializedNaturalTransformation _ _ _ _ C D
      |}; abstract (spnt_eq; auto).
  Defined.
End FunctorCategory.
