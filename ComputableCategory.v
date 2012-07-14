Require Export Category SmallCategory SmallFunctor.
Require Import Common.

Set Implicit Arguments.

Section ComputableCategory.
  Variable I : Type.
  Variable Index2Cat : I -> SmallCategory.

  Coercion Index2Cat : I >-> SmallCategory.

  Definition ComputableCategory : Category.
    refine {| Object := I;
      Morphism := SmallFunctor;
      Compose := @ComposeSmallFunctors;
      Identity := @IdentitySmallFunctor
      |}; abstract sfunctor_eq.
  Defined.
End ComputableCategory.
