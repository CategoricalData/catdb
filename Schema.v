Require Import Bool Omega Setoid.
Require Import EquivalenceRelation.

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

Ltac t' := simpl; intuition.

Ltac t := t';
  repeat (match goal with
            | [ H : context[@eq] |- _ ] => rewrite H
            | _ => progress autorewrite with core in *
          end; t').

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

  Lemma addedge_equal : forall s d d' (p p' : path' E s d), p = p' -> forall e : E d d', AddEdge p e = AddEdge p' e.
    t.
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

Theorem PreCompose' : forall S s d (E : S.(Edge) s d) d' (p1 p2 : path' _ d d'),
  PathsEquivalent _ _ _ p1 p2 -> PathsEquivalent _ _ _ (prepend p1 E) (prepend p2 E).
  intros; apply PreCompose; auto.
Qed.

Theorem PostCompose' : forall S s d (p1 p2 : path' _ s d) d' (E : S.(Edge) d d'),
  PathsEquivalent _ _ _ p1 p2
  -> PathsEquivalent _ _ _ (AddEdge p1 E) (AddEdge p2 E).
  intros; apply PostCompose; auto.
Qed.

Add Parametric Relation S s d : _ (PathsEquivalent S s d)
  reflexivity proved by (Reflexive _ _ _)
  symmetry proved by (Symmetric _ _ _)
  transitivity proved by (Transitive _ _ _)
    as paths_eq.

Lemma paths_equivalence_equivalent S : relations_equivalence_equivalent S.(PathsEquivalent).
  unfold relations_equivalence_equivalent; trivial.
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
    t. apply PostCompose. assumption.
  Qed.
  
  Lemma prepend_equivalent : forall s' s d (p p' : path' _ s d), PathsEquivalent S _ _ p p'
    -> forall e : Edge _ s' s, PathsEquivalent S _ _ (prepend p e) (prepend p' e).
    t. apply PreCompose. assumption.
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

  Add Parametric Morphism s d d' p:
    (@concatenate _ S.(Edge) s d d' p)
    with signature (PathsEquivalent S _ _) ==> (PathsEquivalent S _ _) as concatenate_pre_mor.
    t; apply pre_concatenate_equivalent; assumption.
  Qed.

  Add Parametric Morphism s d d' p:
    (fun p' => (@concatenate _ S.(Edge) s d d' p' p))
    with signature (PathsEquivalent S _ _) ==> (PathsEquivalent S _ _) as concatenate_post_mor.
    t; apply post_concatenate_equivalent; assumption.
  Qed.

  Hint Rewrite concatenate_prepend_equivalent.
  Hint Resolve post_concatenate_equivalent pre_concatenate_equivalent.

  Lemma concatenate_equivalent : forall s d d' (p1 p1' : path' _ s d) (p2 p2' : path' _ d d'),
    PathsEquivalent S _ _ p1 p1' -> PathsEquivalent S _ _ p2 p2' -> PathsEquivalent S _ _ (concatenate p1 p2) (concatenate p1' p2').
    intros; transitivity (concatenate p1 p2'); t.
  Qed.
End path'_Equivalence_Theorems.

Add Parametric Morphism S s d d' :
  (@concatenate _ S.(Edge) s d d')
  with signature (PathsEquivalent S _ _) ==> (PathsEquivalent S _ _) ==> (PathsEquivalent S _ _) as concatenate_mor.
  t; apply concatenate_equivalent; assumption.
Qed.

Section Schema.
  Variable S : Schema.

  Definition path := path' S.(Edge).

  Record Instance := {
    TypeOf :> S -> Type;
    FunctionOf : forall s d (E : S.(Edge) s d), TypeOf s -> TypeOf d;
    EquivalenceOf : forall s d (p1 p2 : path s d), S.(PathsEquivalent) _ _ p1 p2
      -> forall x, compose TypeOf FunctionOf p1 x = compose TypeOf FunctionOf p2 x
  }.

  (* XXX We need a better name for this *)
  Record SNaturalTransformation (I J : Instance) := {
    SComponentsOf :> forall c, I c -> J c;
    SCommutes : forall s d (p : path s d),
      forall x, SComponentsOf d (compose I I.(FunctionOf) p x)
        = compose J J.(FunctionOf) p (SComponentsOf s x)
  }.
End Schema.

Section Schemas.
  Variables C D : Schema.

  Section transferPath.
    Variable vertexOf : C -> D.
    Variable pathOf : forall s d, C.(Edge) s d -> path D (vertexOf s) (vertexOf d).

    Fixpoint transferPath s d (p : path C s d) : path D (vertexOf s) (vertexOf d) :=
      match p with
        | NoEdges => NoEdges
        | AddEdge _ _ p' E => concatenate (transferPath p') (pathOf _ _ E)
      end.
  End transferPath.

  Record Translation := {
    VertexOf :> C -> D;
    PathOf : forall s d, C.(Edge) s d -> path D (VertexOf s) (VertexOf d);
    TEquivalenceOf : forall s d (p1 p2 : path C s d),
      PathsEquivalent C _ _ p1 p2
      -> PathsEquivalent D _ _ (transferPath VertexOf PathOf p1) (transferPath VertexOf PathOf p2)
  }.
End Schemas.
