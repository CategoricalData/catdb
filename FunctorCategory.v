Require Export SpecializedCategory Functor NaturalTransformation.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Section FunctorCategory.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  (*
     There is a category Fun(C, D) of functors from [C] to [D].
     *)
  Definition FunctorCategory : @SpecializedCategory (SpecializedFunctor C D).
    refine {|
      Morphism' := SpecializedNaturalTransformation (C := C) (D := D);
      Compose' := NTComposeT (C := C) (D := D);
      Identity' := IdentityNaturalTransformation (C := C) (D := D)
    |}; abstract (nt_eq; auto with morphism).
  Defined.
End FunctorCategory.

Notation "C ^ D" := (FunctorCategory D C) : category_scope.
Notation "C ^ D" := (FunctorCategory D C) : functor_scope.
