Require Export SpecializedCategory Functor.
Require Import Common.

Set Implicit Arguments.

Section ComputableCategory.
  Variable I : Type.
  Variable Index2Object : I -> Type.
  Variable Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i).

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Definition ComputableCategory : @SpecializedCategory I.
    refine {|
      Morphism' := (fun C D : I => SpecializedFunctor C D);
      Identity' := (fun o : I => IdentityFunctor o);
      Compose' := (fun C D E : I => ComposeFunctors (C := C) (D := D) (E := E))
      |}; abstract functor_eq.
  Defined.
End ComputableCategory.
