Require Import Common.

Set Implicit Arguments.

Section path.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Polymorphic Inductive path (s : V) : V -> Type :=
  | NoEdges : path s s
  | AddEdge : forall d d', path s d -> E d d' -> path s d'.

  Polymorphic Fixpoint prepend s d (p : path s d) : forall s', E s' s -> path s' d :=
    match p with
      | NoEdges => fun _ E' => AddEdge (NoEdges _) E'
      | AddEdge _ _ p' E => fun _ E' => AddEdge (prepend p' E') E
    end.

  Polymorphic Fixpoint concatenate s d d' (p : path s d) (p' : path d d') : path s d' :=
    match p' with
      | NoEdges => p
      | AddEdge _ _ p' E => AddEdge (concatenate p p') E
    end.

  Polymorphic Fixpoint concatenate' s d (p : path s d) : forall d', path d d' -> path s d' :=
    match p with
      | NoEdges => fun _ p' => p'
      | AddEdge _ _ p E => fun _ p' => concatenate' p (prepend p' E)
    end.

  Variable typeOf : V -> Type.
  Variable functionOf : forall s d, E s d -> typeOf s -> typeOf d.

  Polymorphic Fixpoint compose_path s d (p : path s d) : typeOf s -> typeOf d :=
    match p with
      | NoEdges => fun x => x
      | AddEdge _ _ p' E => fun x => functionOf E (compose_path p' x)
    end.
End path.

Arguments NoEdges [V E s].
Arguments AddEdge [V E s d d'] _ _.
Arguments prepend [V E s d] p [s'] p'.

Section path_Theorems.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Polymorphic Lemma concatenate_noedges_p : forall s d (p : path E s d), concatenate NoEdges p = p.
  Proof.
    induction p; t.
  Qed.

  Polymorphic Lemma concatenate_p_noedges : forall s d (p : path E s d), concatenate p NoEdges = p.
  Proof.
    t.
  Qed.

  Polymorphic Lemma concatenate'_p_addedge : forall s d d' d'' (p : path E s d) (p' : path E d d') (e : E d' d''),
    concatenate' p (AddEdge p' e) = AddEdge (concatenate' p p') e.
  Proof.
    induction p; t.
  Qed.

  Polymorphic Hint Rewrite concatenate'_p_addedge.

  Polymorphic Lemma concatenate'_p_noedges : forall s d (p : path E s d), concatenate' p NoEdges = p.
  Proof.
    induction p; t.
  Qed.

  Polymorphic Lemma concatenate'_noedges_p : forall s d (p : path E s d), concatenate' NoEdges p = p.
  Proof.
    t.
  Qed.

  Polymorphic Hint Rewrite concatenate'_p_noedges.

  Polymorphic Lemma concatenate_addedge_concatenate'_prepend : forall s d d'0 d' (p : path E s d) (e : E d d'0) (p' : path E d'0 d'),
    concatenate (AddEdge p e) p' = concatenate' p (prepend p' e).
  Proof.
    induction p'; t.
  Qed.

  Polymorphic Hint Resolve concatenate_noedges_p concatenate_addedge_concatenate'_prepend.

  Polymorphic Lemma concatenate_concatenate'_equivalent : forall s d d' (p : path E s d) (p' : path E d d'), concatenate p p' = concatenate' p p'.
  Proof.
    induction p; t.
  Qed.

  Polymorphic Hint Rewrite concatenate_noedges_p concatenate_addedge_concatenate'_prepend.
  Polymorphic Hint Rewrite <- concatenate_concatenate'_equivalent.

  Polymorphic Lemma concatenate_p_addedge : forall s d d' d'' (p : path E s d) (p' : path E d d') (e : E d' d''),
    concatenate p (AddEdge p' e) = AddEdge (concatenate p p') e.
  Proof.
    induction p; t.
  Qed.

  Polymorphic Lemma concatenate_prepend_p : forall s s' d d' (p1 : path E s' d) (p2 : path E d d') (e : E s s'),
    (prepend (concatenate p1 p2) e) = (concatenate (prepend p1 e) p2).
  Proof.
    induction p1; t.
  Qed.

  Polymorphic Hint Rewrite concatenate_prepend_p.

  Polymorphic Lemma concatenate_associative o1 o2 o3 o4 : forall (p1 : path E o1 o2) (p2 : path E o2 o3) (p3 : path E o3 o4),
    (concatenate (concatenate p1 p2) p3) = (concatenate p1 (concatenate p2 p3)).
  Proof.
    induction p1; t.
  Qed.

  Polymorphic Lemma compose_path_addedge s d d' (p : path E s d) (e : E _ d') typeOf functionOf : forall x, compose_path typeOf functionOf (AddEdge p e) x = functionOf _ _ e (compose_path typeOf functionOf p x).
  Proof.
    induction p; t_with t'.
  Qed.

  Polymorphic Lemma compose_path_prepend s' s d (p : path E s d) (e : E s' _) typeOf functionOf : forall x, compose_path typeOf functionOf (prepend p e) x = (compose_path typeOf functionOf p (functionOf _ _ e x)).
  Proof.
    induction p; t_with t'.
  Qed.
End path_Theorems.

Polymorphic Hint Rewrite compose_path_prepend compose_path_addedge.
Polymorphic Hint Rewrite concatenate_p_noedges concatenate_noedges_p.
Polymorphic Hint Resolve concatenate_p_noedges concatenate_noedges_p.
