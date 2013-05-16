Require Import Setoid FunctionalExtensionality ProofIrrelevance JMeq.
Require Import Common Notations FEqualDep.
Require Export Schema.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

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
      PathsEquivalent C p1 p2
      -> PathsEquivalent D (TransferPath _ _ p1) (TransferPath _ _ p2)
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

  Lemma translations_equal_parts : forall C D (F G : Translation C D),
    F = G -> VertexOf F = VertexOf G /\ PathOf F == PathOf G.
    intros; repeat subst; split; trivial.
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

Section TranslationsEquivalent.
  Variables C D : Schema.
  Variables F G : Translation C D.

  Definition TranslationsEquivalent :=
    exists vo po po' eo eo',
      F = {| VertexOf := vo; PathOf := po; TEquivalenceOf := eo |} /\
      G = {| VertexOf := vo; PathOf := po'; TEquivalenceOf := eo' |} /\
      forall s d (e : C.(Edge) s d), PathsEquivalent _ (po _ _ e) (po' _ _ e).

  Lemma translations_equivalent :
    VertexOf F = VertexOf G
    -> (VertexOf F = VertexOf G ->
        forall s d (e : C.(Edge) s d), GeneralizedPathsEquivalent (PathOf F _ _ e) (PathOf G _ _ e))
    -> TranslationsEquivalent.
    unfold TranslationsEquivalent;
      destruct F as [ vo po tp eo ], G as [ vo' po' tp' eo' ];
        simpl; intros; subst tp tp'; intuition; repeat subst;
          repeat esplit; f_equal; intros.
    match goal with
      | [ s : _, d : _, e : _, H : _ |- _ ] => specialize (H s d e); simpl_GeneralizedPathsEquivalent; assumption
    end.
  Qed.
End TranslationsEquivalent.

Ltac translation_eqv_step_with tac := intros; simpl;
  match goal with
    | _ => reflexivity
    | [ |- TranslationsEquivalent _ _ ] => apply translations_equivalent
    | [ |- (fun _ : ?A => _) = _ ] => apply functional_extensionality_dep; intro
    | [ |- (fun _ : ?A => _) == _ ] => apply (@functional_extensionality_dep_JMeq A); intro
    | [ |- (forall _ : ?A, _) = _ ] => apply (@forall_extensionality_dep A); intro
    | [ H := _ |- _ ] => subst H
    | _ => simpl in *; repeat subst; try simpl_GeneralizedPathsEquivalent; tac
  end; repeat simpl in *; JMeq_eq.

Ltac translation_eqv_with tac := repeat translation_eqv_step_with tac.

Ltac translation_eqv_step := translation_eqv_step_with idtac.
Ltac translation_eqv := translation_eqv_with idtac.

Section TranslationsEquivalent_Relation.
  Variables C D E : Schema.

  Lemma TranslationsEquivalent_refl (T : Translation C D) : TranslationsEquivalent T T.
    translation_eqv.
  Qed.

  Lemma TranslationsEquivalent_sym (T U : Translation C D) :
    TranslationsEquivalent T U -> TranslationsEquivalent U T.
    intro H; destruct H; destruct_hypotheses.
    translation_eqv; symmetry; intuition.
  Qed.

  Lemma TranslationsEquivalent_trans (T U V : Translation C D) :
    TranslationsEquivalent T U -> TranslationsEquivalent U V -> TranslationsEquivalent T V.
    intros H0 H1; destruct H0, H1; destruct_hypotheses.
    translation_eqv;
    match goal with
      | [ H : _ |- _ ] => apply translations_equal_parts in H; unfold PathOf, VertexOf in H; destruct H; repeat subst
    end; try reflexivity.
    etransitivity; eauto.
  Qed.

  Hint Resolve TEquivalenceOf.

  Lemma PreComposeTranslationsEquivalent (T T' : Translation C D) (U : Translation D E) :
    TranslationsEquivalent T T' -> TranslationsEquivalent (ComposeTranslations U T) (ComposeTranslations U T').
    intro H; destruct H; translation_eqv_with ltac:(destruct_hypotheses; eauto).
  Qed.

  Hint Resolve concatenate_mor.

  Lemma PostComposeTranslationsEquivalent (T : Translation C D) (U U' : Translation D E) :
    TranslationsEquivalent U U' -> TranslationsEquivalent (ComposeTranslations U T) (ComposeTranslations U' T).
    intro H; destruct H; translation_eqv_with ltac:(destruct_hypotheses; eauto).
    destruct T; unfold TransferPath; translation_eqv.
    match goal with
      | [ |- ?Rel (transferPath _ _ ?p) (transferPath _ _ ?p) ] => induction p; simpl; try reflexivity
    end; eauto.
  Qed.
End TranslationsEquivalent_Relation.

Add Parametric Relation C D : _ (@TranslationsEquivalent C D)
  reflexivity proved by (@TranslationsEquivalent_refl _ _)
  symmetry proved by (@TranslationsEquivalent_sym _ _)
  transitivity proved by (@TranslationsEquivalent_trans _ _)
    as TranslationsEquivalent_rel.

Add Parametric Morphism C D E : (@ComposeTranslations C D E)
  with signature (@TranslationsEquivalent _ _) ==> (@TranslationsEquivalent _ _) ==> (@TranslationsEquivalent _ _)
    as ComposeTranslations_mor.
  intros ? ? H0 ? ? H1.
  etransitivity; try apply PostComposeTranslationsEquivalent; eauto;
    apply PreComposeTranslationsEquivalent; eauto.
Qed.
