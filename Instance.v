Require Import Bool Omega Setoid.
Require Export Schema.
Require Import Common EquivalenceRelation.

Set Implicit Arguments.

Section Schema.
  Variable S : Schema.

  Record Instance := {
    TypeOf :> S -> Type;
    FunctionOf : forall s d (E : S.(Edge) s d), TypeOf s -> TypeOf d;
    EquivalenceOf : forall s d (p1 p2 : path S s d), S.(PathsEquivalent) _ _ p1 p2
      -> forall x, compose TypeOf FunctionOf p1 x = compose TypeOf FunctionOf p2 x
  }.

  Record ProgressiveUpdate (I J : Instance) := {
    PUComponentsOf :> forall c, I c -> J c;
    PUCommutes : forall s d (p : path S s d),
      forall x, PUComponentsOf d (compose I I.(FunctionOf) p x)
        = compose J J.(FunctionOf) p (PUComponentsOf s x)
  }.
End Schema.
