Require Import Setoid.
Require Export Category.
Require Import Common EquivalenceRelation Functor.

Set Implicit Arguments.

Section ComputableCategory.
  Variable O : Type.
  Variable Object2Cat : O -> Category.

  Coercion Object2Cat : O >-> Category.

  Hint Resolve LeftIdentityFunctor RightIdentityFunctor PreComposeFunctors PostComposeFunctors ComposeFunctorsAssociativity.

  Definition ComputableCategory : Category.
    refine {| Object := O;
      Morphism := Functor;
      MorphismsEquivalent' := (fun _ _ F G => FunctorsEquivalent F G);
      Compose := (fun _ _ _ F G => ComposeFunctors F G);
      Identity := (fun o => IdentityFunctor o)
      |}; abstract (t; simpl_transitivity).
  Defined.
End ComputableCategory.
