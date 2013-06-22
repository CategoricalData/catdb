Require Import Notations.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Graph.
  Record Graph (v : Type) := {
    Vertex :> _ := v;
    Edge' : v -> v -> Type
  }.
End Graph.

Bind Scope graph_scope with Graph.
Bind Scope vertex_scope with Vertex.
Bind Scope edge_scope with Edge'.

Arguments Vertex {v%type} G%graph : rename.

Section GraphInterface.
  Context `(G : @Graph v).

  Definition Edge : forall s d : G, _ := Eval cbv beta delta [Edge'] in G.(Edge').
End GraphInterface.

Bind Scope edge_scope with Edge.

Arguments Vertex {v%type} G : rename, simpl never.
Arguments Edge {v%type} G s d : rename, simpl nomatch.
