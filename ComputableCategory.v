Require Import Setoid.
Require Export Category.
Require Import Common Functor.

Set Implicit Arguments.

Section ComputableCategory.
  Variable O : Type.
  Variable Object2Cat : O -> Category.

  Coercion Object2Cat : O >-> Category.

  Hint Resolve LeftIdentityFunctor RightIdentityFunctor f_equal2 ComposeFunctorsAssociativity.

  Definition ComputableCategory : Category.
    refine {| Object := O;
      Morphism := Functor;
      Compose := (fun _ _ _ F G => ComposeFunctors F G);
      Identity := (fun o => IdentityFunctor o)
      |}; abstract (t; simpl_transitivity).
  Defined.
End ComputableCategory.
