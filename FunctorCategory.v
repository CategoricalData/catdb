Require Export SpecializedCategory Functor NaturalTransformation.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Section FunctorCategory.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  (*
     There is a category Fun(C, D) of functors from [C] to [D].
   *)
  Definition FunctorCategory : @SpecializedCategory (SpecializedFunctor C D).
    refine (@Build_SpecializedCategory _
                                       (SpecializedNaturalTransformation (C := C) (D := D))
                                       (IdentityNaturalTransformation (C := C) (D := D))
                                       (NTComposeT (C := C) (D := D))
                                       _
                                       _
                                       _);
    abstract (nt_eq; auto with morphism).
  Defined.
End FunctorCategory.

Notation "C ^ D" := (FunctorCategory D C) : category_scope.
