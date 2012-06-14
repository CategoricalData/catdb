Require Import Bool Omega Setoid.
Require Import Common EquivalenceRelation.
Require Export Schema.

Set Implicit Arguments.

Section Schema.
  Variable S : Schema.

  Record Instance := {
    TypeOf :> S -> Type;
    FunctionOf : forall s d (E : S.(Edge) s d), TypeOf s -> TypeOf d;
    EquivalenceOf : forall s d (p1 p2 : path S s d), S.(PathsEquivalent) _ _ p1 p2
      -> forall x, compose TypeOf FunctionOf p1 x = compose TypeOf FunctionOf p2 x
  }.

  (* XXX We need a better name for this *)
  Record SNaturalTransformation (I J : Instance) := {
    SComponentsOf :> forall c, I c -> J c;
    SCommutes : forall s d (p : path S s d),
      forall x, SComponentsOf d (compose I I.(FunctionOf) p x)
        = compose J J.(FunctionOf) p (SComponentsOf s x)
  }.
End Schema.
