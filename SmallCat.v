Require Export Category SmallCategory.
Require Import Common SmallFunctor.

Set Implicit Arguments.

Section SmallCat.
  Hint Resolve ComposeSmallFunctorsAssociativity LeftIdentitySmallFunctor RightIdentitySmallFunctor.

  Definition SmallCat : Category.
    refine {| Object := SmallCategory;
      Morphism := @SmallFunctor;
      Identity := @IdentitySmallFunctor;
      Compose := @ComposeSmallFunctors
      |}; auto.
  Defined.
End SmallCat.
