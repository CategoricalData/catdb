Require Export SpecializedCategory Functor NaturalTransformation.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section FunctorCategory.
  Context `(C : SpecializedCategory).
  Context `(D : SpecializedCategory).

  (*
     There is a category Fun(C, D) of functors from [C] to [D].
   *)
  Definition FunctorCategory : SpecializedCategory.
    refine (@Build_SpecializedCategory (SpecializedFunctor C D)
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
