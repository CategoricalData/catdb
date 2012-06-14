Require Import Bool Omega Setoid.
Require Import Common EquivalenceRelation.
Require Export Schema.

Set Implicit Arguments.

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
