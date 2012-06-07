Require Import Bool Omega Setoid.
Require Export Schema Category.
Require Import Common EquivalenceRelation EquivalenceClass.

Set Implicit Arguments.

Section Schema_Category_Equivalence.
  Variable C : Category.
  Variable S : Schema.

  Hint Rewrite concatenate_noedges_p concatenate_p_noedges concatenate_addedge.
  Hint Rewrite <- concatenate_prepend_equivalent.
  Hint Rewrite concatenate_associative.

  Hint Extern 1 (@RelationsEquivalent _ _ _ (PathsEquivalent _) _ _ _ _) => apply addedge_equivalent.
  Hint Extern 1 (@RelationsEquivalent _ _ _ (PathsEquivalent _) _ _ _ _) => apply PreCompose.

  Check EquivalenceClassOf.
Print path.

  Definition path2path' s d (p : path S s d) : path' (Edge S) s d := p.
(*
  Definition saturate : Category.
    refine {| Object := S;
      Morphism := forall s d, @EquivalenceClassOf (path S s d) (@PathsEquivalent S s d);
      (* foo := 1; *) (* uncommenting this line gives "Anomaly: uncaught exception Not_found. Please report."  Maybe I should report this?  But I haven't figured out a minimal test case. *)
      Identity := (fun _ => NoEdges);
      Compose := (fun _ _ _ m1 m2 => concatenate m2 m1)
      |}; abstract (intros; solve [ t | match goal with
                                          | [ p : path _ _ _ |- _ ] => solve [ induction p; t ]
                                        end ]).
  Defined.
*)
  Fixpoint compose_morphism_path s d (p : path' C.(Morphism) s d) : Morphism _ s d :=
    match p with
      | NoEdges => Identity s
      | AddEdge _ _ p' E => Compose E (compose_morphism_path p')
    end.

  Hint Rewrite Associativity.

  Lemma compose_morphism_path_alt : forall s d d' (E : Morphism C s d) (p : path' _ d d'),
    compose_morphism_path (prepend p E) = Compose (compose_morphism_path p) E.
    induction p; t; eauto.
  Qed.

  Hint Rewrite compose_morphism_path_alt.

  Definition unsaturate : Schema.
    refine {| Vertex := C;
      Edge := C.(Morphism);
      PathsEquivalent' := (fun s d (p p' : _ s d) => compose_morphism_path p = compose_morphism_path p')
    |}; abstract (t; etransitivity; eauto).
  Defined.
End Schema_Category_Equivalence.
