Require Import Bool Omega Setoid.
Require Import Common EquivalenceRelation.

Set Implicit Arguments.

Section path'.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Inductive path' (s : V) : V -> Type :=
  | NoEdges : path' s s
  | AddEdge : forall d d', path' s d -> E d d' -> path' s d'.

  Fixpoint prepend s d (p : path' s d) : forall s', E s' s -> path' s' d :=
    match p with
      | NoEdges => fun _ E' => AddEdge (NoEdges _) E'
      | AddEdge _ _ p' E => fun _ E' => AddEdge (prepend p' E') E
    end.

  Fixpoint concatenate s d d' (p : path' s d) (p' : path' d d') : path' s d' :=
    match p' with
      | NoEdges => p
      | AddEdge _ _ p' E => AddEdge (concatenate p p') E
    end.

  Fixpoint concatenate' s d (p : path' s d) : forall d', path' d d' -> path' s d' :=
    match p with
      | NoEdges => fun _ p' => p'
      | AddEdge _ _ p E => fun _ p' => concatenate' p (prepend p' E)
    end.

  Variable typeOf : V -> Type.
  Variable functionOf : forall s d, E s d -> typeOf s -> typeOf d.

  Fixpoint compose s d (p : path' s d) : typeOf s -> typeOf d :=
    match p with
      | NoEdges => fun x => x
      | AddEdge _ _ p' E => fun x => functionOf E (compose p' x)
    end.
End path'.

Implicit Arguments NoEdges [V E s].
Implicit Arguments AddEdge [V E s d d'].
Implicit Arguments prepend [V E s d s'].

Section path'_Theorems.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Lemma concatenate_noedges_p : forall s d (p : path' E s d), concatenate NoEdges p = p.
    induction p; t.
  Qed.

  Lemma concatenate_p_noedges : forall s d (p : path' E s d), concatenate p NoEdges = p.
    t.
  Qed.

  Lemma concatenate'_addedge : forall s d d' d'' (p : path' E s d) (p' : path' E d d') (e : E d' d''),
    concatenate' p (AddEdge p' e) = AddEdge (concatenate' p p') e.
    induction p; t.
  Qed.

  Hint Rewrite concatenate'_addedge.

  Lemma concatenate'_p_noedges : forall s d (p : path' E s d), concatenate' p NoEdges = p.
    induction p; t.
  Qed.

  Lemma concatenate'_noedges_p : forall s d (p : path' E s d), concatenate' NoEdges p = p.
    t.
  Qed.

  Hint Rewrite concatenate'_p_noedges.

  Lemma concatenate_addedge : forall s d d'0 d' (p : path' E s d) (e : E d d'0) (p' : path' E d'0 d'),
    concatenate (AddEdge p e) p' = concatenate' p (prepend p' e).
    induction p'; t.
  Qed.

  Hint Resolve concatenate_noedges_p concatenate_addedge.

  Lemma concatenate_prepend_equivalent : forall s d d' (p : path' E s d) (p' : path' E d d'), concatenate p p' = concatenate' p p'.
    induction p; t.
  Qed.

  Hint Rewrite concatenate_noedges_p concatenate_addedge.
  Hint Rewrite <- concatenate_prepend_equivalent.

  Lemma concatenate_prepend : forall s s' d d' (p1 : path' E s' d) (p2 : path' E d d') (e : E s s'),
    (prepend (concatenate p1 p2) e) = (concatenate (prepend p1 e) p2).
    induction p1; t.
  Qed.

  Hint Rewrite concatenate_prepend.

  Lemma concatenate_associative o1 o2 o3 o4 : forall (p1 : path' E o1 o2) (p2 : path' E o2 o3) (p3 : path' E o3 o4),
    (concatenate (concatenate p1 p2) p3) = (concatenate p1 (concatenate p2 p3)).
    induction p1; t.
  Qed.
End path'_Theorems.

Record Schema := {
  Vertex :> Type;
  Edge : Vertex -> Vertex -> Type;

  PathsEquivalent' : forall s d, (path' Edge s d) -> (path' Edge s d) -> Prop;
  PathsEquivalent : EquivalenceRelation PathsEquivalent';

  PreCompose : forall s d (E : Edge s d) d' (p1 p2 : path' _ d d'),
    PathsEquivalent' p1 p2 -> PathsEquivalent' (prepend p1 E) (prepend p2 E);
  PostCompose : forall s d (p1 p2 : path' _ s d) d' (E : Edge d d'),
    PathsEquivalent' p1 p2 -> PathsEquivalent' (AddEdge p1 E) (AddEdge p2 E)
}.

Hint Resolve PreCompose PostCompose.

Theorem PreCompose' : forall S s d (E : S.(Edge) s d) d' (p1 p2 : path' _ d d'),
  PathsEquivalent _ _ _ p1 p2 -> PathsEquivalent _ _ _ (prepend p1 E) (prepend p2 E).
  intros; auto.
Qed.

Theorem PostCompose' : forall S s d (p1 p2 : path' _ s d) d' (E : S.(Edge) d d'),
  PathsEquivalent _ _ _ p1 p2
  -> PathsEquivalent _ _ _ (AddEdge p1 E) (AddEdge p2 E).
  intros; auto.
Qed.

Hint Resolve PreCompose' PostCompose'.

Add Parametric Relation S s d : _ (PathsEquivalent S s d)
  reflexivity proved by (Reflexive _ _ _)
  symmetry proved by (Symmetric _ _ _)
  transitivity proved by (Transitive _ _ _)
    as paths_eq.

Lemma paths_equivalence_equivalent S : relations_equivalence_equivalent S.(PathsEquivalent).
  hnf; trivial.
Qed.

Hint Rewrite paths_equivalence_equivalent.

(* It's not true that [(p1 = p2 -> p3 = p4) -> (PathsEquivalent p1 p2 -> PathsEquivalent p3 p4)]
   Consider a case where p1 = NoEdges and p2 is a path containing an edge and its inverse,
   and p3 and p4 are not equivalent paths.

   So, let's do the relevant theorems again... *)
Section path'_Equivalence_Theorems.
  Variable S : Schema.

  Lemma addedge_equivalent : forall s d d' (p p' : path' _ s d), PathsEquivalent S _ _ p p'
    -> forall e : Edge _ d d', PathsEquivalent S _ _ (AddEdge p e) (AddEdge p' e).
    t.
  Qed.

  Lemma prepend_equivalent : forall s' s d (p p' : path' _ s d), PathsEquivalent S _ _ p p'
    -> forall e : Edge _ s' s, PathsEquivalent S _ _ (prepend p e) (prepend p' e).
    t.
  Qed.

  Hint Rewrite concatenate_noedges_p concatenate_addedge.
  Hint Rewrite <- concatenate_prepend_equivalent.
  Hint Resolve prepend_equivalent addedge_equivalent.

  Lemma pre_concatenate_equivalent : forall s' s d (p1 : path' _ s' s) (p p' : path' _ s d),
    PathsEquivalent S _ _ p p' -> PathsEquivalent S _ _ (concatenate p1 p) (concatenate p1 p').
    induction p1; t.
  Qed.

  Lemma post_concatenate_equivalent : forall s d d' (p p' : path' _ s d) (p2 : path' _ d d'),
    PathsEquivalent S _ _ p p' -> PathsEquivalent S _ _ (concatenate p p2) (concatenate p' p2).
    induction p2; t.
  Qed.

  Hint Resolve pre_concatenate_equivalent post_concatenate_equivalent.

  Add Parametric Morphism s d d' p:
    (@concatenate _ S.(Edge) s d d' p)
    with signature (PathsEquivalent S _ _) ==> (PathsEquivalent S _ _) as concatenate_pre_mor.
    t.
  Qed.

  Add Parametric Morphism s d d' p:
    (fun p' => (@concatenate _ S.(Edge) s d d' p' p))
    with signature (PathsEquivalent S _ _) ==> (PathsEquivalent S _ _) as concatenate_post_mor.
    t.
  Qed.

  Hint Resolve Transitive.

  Lemma concatenate_equivalent : forall s d d' (p1 p1' : path' _ s d) (p2 p2' : path' _ d d'),
    PathsEquivalent S _ _ p1 p1' -> PathsEquivalent S _ _ p2 p2' -> PathsEquivalent S _ _ (concatenate p1 p2) (concatenate p1' p2').
    t; eauto.
  Qed.
End path'_Equivalence_Theorems.

Hint Resolve concatenate_equivalent.

Add Parametric Morphism S s d d' :
  (@concatenate _ S.(Edge) s d d')
  with signature (PathsEquivalent S _ _) ==> (PathsEquivalent S _ _) ==> (PathsEquivalent S _ _) as concatenate_mor.
  t.
Qed.

Add Parametric Morphism S s d d' :
  (@AddEdge S _ s d d')
  with signature (PathsEquivalent S _ _) ==> (@eq _) ==> (PathsEquivalent S _ _) as AddEdge_mor.
  t.
Qed.

Add Parametric Morphism S s d d' :
  (fun p => @concatenate' S _ s d p d')
  with signature (PathsEquivalent S _ _) ==> (PathsEquivalent S _ _) ==> (PathsEquivalent S _ _) as concatenate'_mor.
  intros; repeat rewrite <- concatenate_prepend_equivalent; t.
Qed.

Add Parametric Morphism S s' s d :
  (fun p => @prepend S _ s d p s')
  with signature (PathsEquivalent S _ _) ==> (@eq _) ==> (PathsEquivalent S _ _) as prepend_mor.
  t.
Qed.

Definition path S := path' S.(Edge).
