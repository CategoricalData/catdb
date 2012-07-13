Require Export SpecializedCategory Functor.
Require Import Common.

Set Implicit Arguments.

Section ComputableCategory.
  Variable I : Type.
  Variable Index2Object : I -> Type.
  Variable Index2Morphism : forall i : I, Index2Object i -> Index2Object i -> Type.
  Variable Index2Cat : forall i : I, SpecializedCategory (@Index2Morphism i).

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Definition ComputableCategory : @SpecializedCategory I (fun C D : I => SpecializedFunctor C D).
    refine {|
      Identity' := (fun o : I => @IdentityFunctor _ _ o);
      Compose' := (fun C D E : I => @ComposeFunctors _ _ C _ _ D _ _ E)
      |}; abstract functor_eq.
  Defined.
End ComputableCategory.
