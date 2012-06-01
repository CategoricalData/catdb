Require Import Bool Omega Setoid.
Require Import Common EquivalenceRelation Schema Category.

Set Implicit Arguments.

Section Schema_Category_Equivalence.
  Variable C : Category.
  Variable S : Schema.

  Hint Rewrite concatenate_noedges_p concatenate_p_noedges concatenate_addedge.
  Hint Rewrite <- concatenate_prepend_equivalent.
  Hint Rewrite concatenate_associative.

  Hint Extern 1 (@RelationsEquivalent _ _ _ (PathsEquivalent _) _ _ _ _) => apply addedge_equivalent.
  Hint Extern 1 (@RelationsEquivalent _ _ _ (PathsEquivalent _) _ _ _ _) => apply PreCompose.

  Definition saturate : Category.
    refine {| Object := S;
      Morphism := path S;
      (* foo := 1; *) (* uncommenting this line gives "Anomaly: uncaught exception Not_found. Please report."  Maybe I should report this?  But I haven't figured out a minimal test case. *)
      MorphismsEquivalent := S.(PathsEquivalent);
      Identity := (fun _ => NoEdges);
      Compose := (fun _ _ _ m1 m2 => concatenate m2 m1)
      |}; abstract (intros; solve [ t | match goal with
                                          | [ p : path _ _ _ |- _ ] => solve [ induction p; t ]
                                        end ]).
  Defined.

  Fixpoint compose_morphism_path s d (p : path' C.(Morphism) s d) : Morphism _ s d :=
    match p with
      | NoEdges => Identity s
      | AddEdge _ _ p' E => Compose E (compose_morphism_path p')
    end.

  Lemma MorphismsEquivalent_symm : forall s o1 o2 x y,
    MorphismsEquivalent _ _ _ y x
    -> MorphismsEquivalent s o1 o2 x y.
    intros; symmetry; eassumption.
  Qed.

  Lemma MorphismsEquivalent_trans : forall s o1 o2 x y z,
    MorphismsEquivalent _ _ _ x z
    -> MorphismsEquivalent _ _ _ z y
    -> MorphismsEquivalent s o1 o2 x y.
    intros; transitivity z; eassumption.
  Qed.

  Hint Resolve MorphismsEquivalent_symm MorphismsEquivalent_trans.
  Hint Resolve Associativity' LeftIdentity' RightIdentity' PreComposeMorphisms' PostComposeMorphisms'.

  Hint Rewrite Associativity.

  Lemma compose_morphism_path_alt : forall s d d' (E : Morphism C s d) (p : path' _ d d'),
    MorphismsEquivalent _ _ _ (compose_morphism_path (prepend p E)) (Compose (compose_morphism_path p) E).
    induction p; t; eauto.
  Qed.

  Hint Rewrite compose_morphism_path_alt.

  Definition unsaturate : Schema.
    refine {| Vertex := C;
      Edge := C.(Morphism);
      PathsEquivalent' := (fun s d (p p' : _ s d) => MorphismsEquivalent _ _ _ (compose_morphism_path p) (compose_morphism_path p'))
    |}; abstract (t; eauto).
  Defined.
End Schema_Category_Equivalence.
