Require Export Category Functor.
Require Import Common.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section ComputableCategory.
  Variable I : Type.
  Variable Index2Cat : I -> Category.

  Local Coercion Index2Cat : I >-> Category.

  Definition ComputableCategory : Category.
    refine (@Build_Category I
                                       (fun C D : I => Functor C D)
                                       (fun o : I => IdentityFunctor o)
                                       (fun C D E : I => ComposeFunctors (C := C) (D := D) (E := E))
                                       _
                                       _
                                       _);
    abstract functor_eq.
  Defined.
End ComputableCategory.
