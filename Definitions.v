Require Import Bool Omega.

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

  Fixpoint concatenate s d (p : path' s d) : forall d', path' d d' -> path' s d' :=
    match p with
      | NoEdges => fun _ p' => p'
      | AddEdge _ _ p E => fun _ p' => concatenate p (prepend p' E)
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

Record Category := {
  Vertex :> Type;
  Edge : Vertex -> Vertex -> Type;

  PathsEquivalent : forall s d, path' Edge s d -> path' Edge s d -> Prop;
  Reflexive : forall s d (p : path' _ s d),
    PathsEquivalent p p;
  Symmetric : forall s d (p1 p2 : path' _ s d),
    PathsEquivalent p1 p2 -> PathsEquivalent p2 p1;
  Transitive : forall s d (p1 p2 p3 : path' _ s d),
    PathsEquivalent p1 p2 -> PathsEquivalent p2 p3 -> PathsEquivalent p1 p3;

  PreCompose : forall s d (E : Edge s d) d' (p1 p2 : path' _ d d'),
    PathsEquivalent p1 p2 -> PathsEquivalent (prepend p1 E) (prepend p2 E);
  PostCompose : forall s d (p1 p2 : path' _ s d) d' (E : Edge d d'),
    PathsEquivalent p1 p2 -> PathsEquivalent (AddEdge p1 E) (AddEdge p2 E)
}.

Section Category.
  Variable C : Category.

  Definition path := path' C.(Edge).

  Record Instance := {
    TypeOf :> C.(Vertex) -> Type;
    FunctionOf : forall s d (E : C.(Edge) s d), TypeOf s -> TypeOf d;
    EquivalenceOf : forall s d (p1 p2 : path s d), C.(PathsEquivalent) p1 p2
      -> forall x, compose TypeOf FunctionOf p1 x = compose TypeOf FunctionOf p2 x
  }.
(*
  Record NaturalTransformation I J : Instance C := {
    FunctionOf :> c: C.(Vertex) -> I.(TypeOf) c -> J.(TypeOf) c
    EquivalenceOf : forall s d (p : path s d) 
      -> C.(PathsEquivalent) compose( FunctionOf(t), I(p) ) compose ( J(p), FunctionOf(s))
}
*)

End Category.

Section Categories.
  Variables C D : Category.

  Section transferPath.
    Variable vertexOf : C.(Vertex) -> D.(Vertex).
    Variable pathOf : forall s d, C.(Edge) s d -> path D (vertexOf s) (vertexOf d).

    Fixpoint transferPath s d (p : path C s d) : path D (vertexOf s) (vertexOf d) :=
      match p with
        | NoEdges => NoEdges
        | AddEdge _ _ p' E => concatenate (transferPath p') (pathOf _ _ E)
      end.
  End transferPath.

  Record Functor := {
    VertexOf :> C.(Vertex) -> D.(Vertex);
    PathOf : forall s d, C.(Edge) s d -> path D (VertexOf s) (VertexOf d);
    FEquivalenceOf : forall s d (p1 p2 : path C s d),
      PathsEquivalent C p1 p2
      -> PathsEquivalent D (transferPath VertexOf PathOf p1) (transferPath VertexOf PathOf p2)
  }.
End Categories.
