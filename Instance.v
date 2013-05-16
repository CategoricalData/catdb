Require Import FunctionalExtensionality Setoid.
Require Export Schema.
Require Import Common Translation SetSchema.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Schema.
  Variable S : Schema.

  Record Instance := {
    TypeOf :> S -> Type;
    FunctionOf : forall s d (E : S.(Edge) s d), TypeOf s -> TypeOf d;
    EquivalenceOf : forall s d (p1 p2 : path S s d), S.(PathsEquivalent) p1 p2
      -> forall x, compose TypeOf FunctionOf p1 x = compose TypeOf FunctionOf p2 x
  }.

  Record ProgressiveUpdate (I J : Instance) := {
    PUComponentsOf :> forall c, I c -> J c;
    PUCommutes : forall s d (p : path S s d),
      forall x, PUComponentsOf d (compose I I.(FunctionOf) p x)
        = compose J J.(FunctionOf) p (PUComponentsOf s x)
  }.

  Variable I : Instance.

  Lemma compose_transferPath : forall s d (p : path S s d) x,
    compose I.(TypeOf) I.(FunctionOf) p x
    = compose (fun x => x) (fun _ _ e => e) (transferPath (I.(TypeOf) : S -> TypeSch)
      (fun _ _ e => AddEdge NoEdges (I.(FunctionOf) _ _ e)) p) x.
    induction p; simpl; intuition; f_equal; auto.
  Qed.

  Definition translationOf : Translation S TypeSch.
    refine (@Build_Translation S TypeSch
      I.(TypeOf)
      (fun _ _ e => AddEdge NoEdges (I.(FunctionOf) _ _ e))
      _);
    abstract (intros; hnf; extensionality x;
      do 2 rewrite <- compose_transferPath; apply EquivalenceOf; assumption).
  Defined.

End Schema.

Coercion translationOf : Instance >-> Translation.
