Require Export SpecializedCategory Functor.
Require Import Common.

Set Implicit Arguments.

Set Asymmetric Patterns.

Section ComputableCategory.
  Variable I : Type.
  Variable Index2Object : I -> Type.
  Variable Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i).

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Definition ComputableCategory : @SpecializedCategory I.
    refine (@Build_SpecializedCategory _
                                       (fun C D : I => SpecializedFunctor C D)
                                       (fun o : I => IdentityFunctor o)
                                       (fun C D E : I => ComposeFunctors (C := C) (D := D) (E := E))
                                       _
                                       _
                                       _);
    abstract functor_eq.
  Defined.
End ComputableCategory.
