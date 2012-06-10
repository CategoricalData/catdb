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

  Definition path2path' s d (p : path S s d) : path' (Edge S) s d := p.

  Hint Rewrite concatenate_p_noedges concatenate_noedges_p concatenate_associative.

  Ltac replace_noedges :=
        repeat match goal with
             | [ H : ?rel NoEdges ?x |- _ ] => repeat rewrite <- H in *; clear H
           end; rewrite concatenate_p_noedges in * || rewrite concatenate_noedges_p in *.

  (* TODO: Speed this up, automate this better. *)
  Definition saturate : Category.
    refine {| Object := S;
      Morphism := fun s d => EquivalenceClass (@PathsEquivalent S s d) (Reflexive _ s d) (Symmetric _ s d) (Transitive _ s d);
      (* foo := 1; *) (* uncommenting this line gives "Anomaly: uncaught exception Not_found. Please report."  Maybe I should report this?  But I haven't figured out a minimal test case. *)
      Identity := (fun _ => classOf NoEdges);
      Compose := (fun s d d' m1 m2 => apply2_to_class (@concatenate S S.(Edge) s d d') (@concatenate_mor S s d d') m2 m1)
    |}; intros; apply forall_equiv__eq;
    repeat (simpl; intros; destruct_type or; destruct_hypotheses; repeat split);
      repeat (replace_noedges; replace_inClass; intros); simpl;
        repeat (replace_inClass; eexists; eauto); clear_inClass; try assumption || reflexivity; try replace_noedges;
          repeat match goal with
                   | [ H : context[PathsEquivalent] |- _ ] => rewrite H in *; clear H
                 end; repeat rewrite concatenate_associative; try reflexivity.
(* abstract (intros; solve [ t | match goal with
                                          | [ p : path _ _ _ |- _ ] => solve [ induction p; t ]
                                        end ]).*)
  Defined.

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
