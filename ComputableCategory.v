Require Export SpecializedCategory Functor.
Require Import Common.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section ComputableCategory.
  Variable I : Type.
  Variable Index2Cat : I -> SpecializedCategory.

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Definition ComputableCategory : SpecializedCategory.
    refine (@Build_SpecializedCategory I
                                       (fun C D : I => SpecializedFunctor C D)
                                       (fun o : I => IdentityFunctor o)
                                       (fun C D E : I => ComposeFunctors (C := C) (D := D) (E := E))
                                       _
                                       _
                                       _);
    abstract functor_eq.
  Defined.
End ComputableCategory.
