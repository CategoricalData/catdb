Require Import Program.
Require Import Common Schema Category Instance Translation.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Translation_Instance.
  Variables C D : Schema.
  Variable F : Translation C D.
  Variable I : Instance D.

  Lemma compose_prepend : forall s d (p : path D s d) s' (E : D.(Edge) s' s) x,
    compose I (FunctionOf I) (prepend p E) x
    = compose I (FunctionOf I) p (I.(FunctionOf) _ _ E x).
    induction p; t.
  Qed.

  Lemma compose_append : forall s d (p : path D s d) d' (E : D.(Edge) d d') x,
    compose I (FunctionOf I) (AddEdge p E) x
    = I.(FunctionOf) _ _ E (compose I (FunctionOf I) p x).
    induction p; t.
  Qed.

  Hint Rewrite compose_prepend.
  Hint Rewrite compose_append.
  Hint Rewrite concatenate_noedges_p.
  Hint Rewrite concatenate_p_noedges.

  Lemma compose_concatenate : forall s d (p : path D s d) d' (p' : path D d d') x,
    compose I (FunctionOf I) (concatenate p p') x
    = compose I (FunctionOf I) p' (compose I (FunctionOf I) p x).
    induction p'; t.
  Qed.

  Hint Rewrite compose_concatenate.

  Lemma compose_PathOf : forall s d (p : path C s d) x,
    compose I (FunctionOf I) (TransferPath F p) x
    = compose (fun x0 : C => I (F x0))
    (fun s0 d0 (E : Edge C s0 d0) =>
      compose I (FunctionOf I) (PathOf F _ _ E)) p x.
    induction p; t.
  Qed.

  Hint Rewrite <- compose_transferPath compose_PathOf.

  Hint Resolve EquivalenceOf TEquivalenceOf.

  Definition Translation_Instance : Instance C.
    refine {| TypeOf := (fun x => I (F x));
      FunctionOf := (fun _ _ E => compose _ (I.(FunctionOf)) (F.(PathOf) _ _ E)) |};
    abstract (t_with t'; auto).
  Defined.
End Translation_Instance.

Section Categories.
  Variable C : Category.

  Hint Resolve LeftIdentity RightIdentity.
  Hint Extern 1 => symmetry.

  Theorem identity_unique : forall a (id' : C.(Morphism) a a),
    (forall f : C.(Morphism) a a, Compose id' f = f) ->
      id' = Identity a.
    intros; transitivity (Compose id' (Identity a)); eauto.
  Qed.
End Categories.
