Require Export Category Functor NaturalTransformation.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section FunctorCategory.
  Variable C : Category.
  Variable D : Category.

  (*
     There is a category Fun(C, D) of functors from [C] to [D].
   *)
  Definition FunctorCategory : Category.
    refine (@Build_Category (Functor C D)
                                       (NaturalTransformation (C := C) (D := D))
                                       (IdentityNaturalTransformation (C := C) (D := D))
                                       (NTComposeT (C := C) (D := D))
                                       _
                                       _
                                       _);
    abstract (nt_eq; auto with morphism).
  Defined.
End FunctorCategory.

Notation "C ^ D" := (FunctorCategory D C) : category_scope.
