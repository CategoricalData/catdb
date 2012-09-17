Require Import Notations.

Set Implicit Arguments.

Generalizable All Variables.

Section SpecializedGraph.
  Record SpecializedGraph (v : Type) := {
    Vertex :> _ := v;
    Edge' : v -> v -> Type
  }.
End SpecializedGraph.

Bind Scope graph_scope with SpecializedGraph.
Bind Scope vertex_scope with Vertex.
Bind Scope edge_scope with Edge'.

Arguments Vertex {v%type} G%graph : rename.

Section SpecializedGraphInterface.
  Context `(G : @SpecializedGraph v).

  Definition Edge : forall s d : G, _ := Eval cbv beta delta [Edge'] in G.(Edge').
End SpecializedGraphInterface.

Bind Scope edge_scope with Edge.

Arguments Vertex {v%type} G : rename, simpl never.
Arguments Edge {v%type} G s d : rename, simpl nomatch.

Record Graph := {
  GVertex : Type;

  UnderlyingSpecializedGraph :> @SpecializedGraph GVertex
}.

Definition GeneralizeGraph `(G : @SpecializedGraph v) : Graph.
  refine {| GVertex := G.(Vertex) |}; auto.
Defined.

Coercion GeneralizeGraph : SpecializedGraph >-> Graph.

Bind Scope graph_scope with Graph.
