Require Import Setoid.
Require Export Category SmallCategory SmallFunctor.
Require Import Common.

Set Implicit Arguments.

Section ComputableCategory.
  Variable O : Type.
  Variable Object2Cat : O -> SmallCategory.

  Coercion Object2Cat : O >-> SmallCategory.

  Definition ComputableCategory : Category.
    refine {| Object := O;
      Morphism := SmallFunctor;
      Compose := @ComposeSmallFunctors;
      Identity := @IdentitySmallFunctor
      |}; abstract sfunctor_eq.
  Defined.
End ComputableCategory.
