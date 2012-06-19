Require Import Bool Omega Setoid FunctionalExtensionality ProofIrrelevance JMeq.
Require Import Common EquivalenceRelation FEqualDep.
Require Export Schema.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

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

    Hint Rewrite concatenate_noedges_p concatenate_p_noedges.
    Hint Rewrite <- concatenate_associative.

    Lemma concatenate_transferPath s d d' (p : path C s d) (p' : path C d d') :
      transferPath (concatenate p p') = concatenate (transferPath p) (transferPath p').
      induction p'; t_with t'.
    Qed.
  End transferPath.

  Record Translation := {
    VertexOf :> C -> D;
    PathOf : forall s d, C.(Edge) s d -> path D (VertexOf s) (VertexOf d);
    TransferPath := (fun s d (p : path C s d) => transferPath VertexOf PathOf p);
    TEquivalenceOf : forall s d (p1 p2 : path C s d),
      PathsEquivalent C _ _ p1 p2
      -> PathsEquivalent D _ _ (TransferPath _ _ p1) (TransferPath _ _ p2)
  }.

  Global Add Parametric Morphism s d T :
    (@TransferPath T s d)
    with signature (@PathsEquivalent C _ _) ==> (@PathsEquivalent D _ _)
      as TransferPath_mor.
    exact (@TEquivalenceOf T s d).
  Qed.

  Lemma concatenate_TransferPath s d d' (p : path C s d) (p' : path C d d') T :
      TransferPath T (concatenate p p') = concatenate (TransferPath T p) (TransferPath T p').
    unfold TransferPath; simpl.
    apply concatenate_transferPath.
  Qed.

  Lemma TransferPath_NoEdges o T :
    TransferPath T (@NoEdges _ _ o) = NoEdges.
    reflexivity.
  Qed.
End Schemas.

Hint Rewrite concatenate_transferPath concatenate_TransferPath.

Section Translations_Equal.
  Lemma translations_equal : forall C D (F G : Translation C D),
    VertexOf F = VertexOf G
    -> (VertexOf F = VertexOf G -> PathOf F == PathOf G)
    -> F = G.
    destruct F as [ vo po tp eo ], G as [ vo' po' tp' eo' ];
      simpl; intros; firstorder; subst tp tp'; repeat subst;
        f_equal; apply proof_irrelevance.
  Qed.
End Translations_Equal.

Ltac translation_eq_step_with tac := intros; simpl;
  match goal with
    | _ => reflexivity
    | [ |- @eq (Translation _ _) _ _ ] => apply translations_equal
    | [ |- (fun _ : ?A => _) = _ ] => apply functional_extensionality_dep; intro
    | [ |- (fun _ : ?A => _) == _ ] => apply (@functional_extensionality_dep_JMeq A); intro
    | [ |- (forall _ : ?A, _) = _ ] => apply (@forall_extensionality_dep A); intro
    | _ => tac
  end; repeat simpl; JMeq_eq.

Ltac translation_eq_with tac := repeat translation_eq_step_with tac.

Ltac translation_eq_step := translation_eq_step_with idtac.
Ltac translation_eq := translation_eq_with idtac.

Section TranslationComposition.
  Variable B C D E : Schema.

  Hint Resolve concatenate_transferPath.

  Lemma compose_transferPath (vertexOf : C -> D) pathOf (vertexOf' : D -> E) pathOf' : forall s d (p : path C s d),
    (transferPath (fun c : C => vertexOf' (vertexOf c))
      (fun (s0 d0 : C) (e : Edge C s0 d0) =>
        transferPath vertexOf' pathOf' (pathOf s0 d0 e)) p) =
    transferPath vertexOf' pathOf' (transferPath vertexOf pathOf p).
  Proof.
    induction p; reflexivity || symmetry; t_with t'.
  Qed.

  Hint Rewrite compose_transferPath.
  Hint Resolve TEquivalenceOf.

  Definition ComposeTranslations (G : Translation D E) (F : Translation C D) : Translation C E.
    refine {| VertexOf := (fun c => G (F c));
      PathOf := (fun _ _ e => G.(TransferPath) (F.(PathOf) _ _ e))
    |}; abstract (unfold TransferPath; t_with t'; repeat apply TEquivalenceOf; assumption).
  Defined.
End TranslationComposition.

Implicit Arguments ComposeTranslations [C D E].

Section Schema.
  Variable C D : Schema.

  (* There is an identity translation.  It does the obvious thing. *)
  Definition IdentityTranslation : Translation C C.
    refine {| VertexOf := (fun x => x);
      PathOf := (fun _ _ x => AddEdge NoEdges x)
    |}; abstract (
      intros ? ? p1 p2 ?;
        transitivity p1;
          try solve [ induction p1; try apply AddEdge_mor; try apply (IHp1 p1); reflexivity ];
            transitivity p2;
              try solve [ induction p2; try apply AddEdge_mor; try apply (IHp2 p2); reflexivity ];
                assumption
    ).
  Defined.

  Hint Unfold ComposeTranslations IdentityTranslation VertexOf PathOf.

  Lemma LeftIdentityTranslation (F : Translation D C) : ComposeTranslations IdentityTranslation F = F.
    translation_eq.
    match goal with
      | [ |- ?a = ?b ] => induction b; t_with t'
    end.
  Qed.

  Lemma RightIdentityTranslation (F : Translation C D) : ComposeTranslations F IdentityTranslation = F.
    translation_eq; t_with t'.
  Qed.
End Schema.

Section TranslationCompositionLemmas.
  Variable B C D E : Schema.

  Lemma ComposeTranslationsAssociativity (F : Translation B C) (G : Translation C D) (H : Translation D E) :
    ComposeTranslations (ComposeTranslations H G) F = ComposeTranslations H (ComposeTranslations G F).
    unfold ComposeTranslations; translation_eq.
    match goal with
      | [ |- TransferPath _ ?p = _ ] => induction p; t_with t'
    end.
  Qed.
End TranslationCompositionLemmas.
