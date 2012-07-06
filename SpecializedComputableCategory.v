Require Export SpecializedCategory SpecializedFunctor.
Require Import Common.

Set Implicit Arguments.

Section ComputableSpecializedCategory.
  Variable I : Type.
  Variable Index2Object : I -> Type.
  Variable Index2Morphism : forall i : I, Index2Object i -> Index2Object i -> Type.
  Variable Index2Cat : forall i : I, SpecializedCategory (@Index2Morphism i).

  Coercion Index2Cat : I >-> SpecializedCategory.

  Definition ComputableSpecializedCategory : @SpecializedCategory I (fun C D : I => SpecializedFunctor C D).
    refine {|
      Identity' := (fun o : I => @IdentitySpecializedFunctor _ _ o);
      Compose' := (fun C D E : I => @ComposeSpecializedFunctors _ _ _ _ _ _ C D E)
      |}; abstract spfunctor_eq.
  Defined.
End ComputableSpecializedCategory.
