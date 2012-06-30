Require Import Setoid.
Require Export Category SmallCategory.
Require Import Common SmallFunctor.

Set Implicit Arguments.

Section ComputableCategory.
  Variable O : Type.
  Variable Object2Cat : O -> SmallCategory.

  Coercion Object2Cat : O >-> SmallCategory.

  Hint Resolve LeftIdentitySmallFunctor RightIdentitySmallFunctor f_equal2 ComposeSmallFunctorsAssociativity.

  Definition ComputableCategory : Category.
    refine {| Object := O;
      Morphism := SmallFunctor;
      Compose := @ComposeSmallFunctors;
      Identity := @IdentitySmallFunctor
      |}; abstract (t; simpl_transitivity).
  Defined.
End ComputableCategory.
