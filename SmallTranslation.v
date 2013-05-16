Require Import Setoid FunctionalExtensionality ProofIrrelevance JMeq.
Require Export SmallSchema Translation.
Require Import Common Notations FEqualDep.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Section SmallSchemas.
  Variables C D : SmallSchema.

  Record SmallTranslation := {
    SVertexOf :> C -> D;
    SPathOf : forall s d, C.(SEdge) s d -> spath D (SVertexOf s) (SVertexOf d);
    STransferPath := (fun s d (p : spath C s d) => (@transferPath C D) SVertexOf SPathOf _ _ p);
    STEquivalenceOf : forall s d (p1 p2 : spath C s d),
      SPathsEquivalent C p1 p2
      -> SPathsEquivalent D (STransferPath _ _ p1) (STransferPath _ _ p2)
  }.

  Global Add Parametric Morphism s d T :
    (@STransferPath T s d)
    with signature (@SPathsEquivalent C _ _) ==> (@SPathsEquivalent D _ _)
      as STransferPath_mor.
    exact (@STEquivalenceOf T s d).
  Qed.

  Lemma concatenate_STransferPath s d d' (p : spath C s d) (p' : spath C d d') T :
      STransferPath T (concatenate p p') = concatenate (STransferPath T p) (STransferPath T p').
    unfold STransferPath; simpl.
    apply concatenate_transferPath.
  Qed.

  Lemma STransferPath_SNoEdges o T :
    STransferPath T (@NoEdges _ _ o) = NoEdges.
    reflexivity.
  Qed.
End SmallSchemas.

Hint Rewrite concatenate_STransferPath.

Section SmallTranslations_Equal.
  Lemma stranslations_equal : forall C D (F G : SmallTranslation C D),
    SVertexOf F = SVertexOf G
    -> (SVertexOf F = SVertexOf G -> SPathOf F == SPathOf G)
    -> F = G.
    destruct F as [ vo po tp eo ], G as [ vo' po' tp' eo' ];
      simpl; intros; firstorder; subst tp tp'; repeat subst;
        f_equal; apply proof_irrelevance.
  Qed.

  Lemma stranslations_equal_parts : forall C D (F G : SmallTranslation C D),
    F = G -> SVertexOf F = SVertexOf G /\ SPathOf F == SPathOf G.
    intros; repeat subst; split; trivial.
  Qed.
End SmallTranslations_Equal.

Ltac stranslation_eq_step_with tac := intros; simpl;
  match goal with
    | _ => reflexivity
    | [ |- @eq (SmallTranslation _ _) _ _ ] => apply stranslations_equal
    | [ |- (fun _ : ?A => _) = _ ] => apply functional_extensionality_dep; intro
    | [ |- (fun _ : ?A => _) == _ ] => apply (@functional_extensionality_dep_JMeq A); intro
    | [ |- (forall _ : ?A, _) = _ ] => apply (@forall_extensionality_dep A); intro
    | _ => tac
  end; repeat simpl; JMeq_eq.

Ltac stranslation_eq_with tac := repeat stranslation_eq_step_with tac.

Ltac stranslation_eq_step := stranslation_eq_step_with idtac.
Ltac stranslation_eq := stranslation_eq_with idtac.

Section SmallTranslationComposition.
  Variable B C D E : SmallSchema.

  Hint Resolve concatenate_transferPath.

  Hint Rewrite compose_transferPath.
  Hint Resolve STEquivalenceOf.

  Definition ComposeSmallTranslations (G : SmallTranslation D E) (F : SmallTranslation C D) : SmallTranslation C E.
    refine {| SVertexOf := (fun c => G (F c));
      SPathOf := (fun _ _ e => G.(STransferPath) (F.(SPathOf) _ _ e))
    |}; abstract (unfold STransferPath; t_with t'; repeat apply STEquivalenceOf; assumption).
  Defined.
End SmallTranslationComposition.

Implicit Arguments ComposeSmallTranslations [C D E].

Section SmallSchema.
  Variable C D : SmallSchema.

  (* There is an identity stranslation.  It does the obvious thing. *)
  Definition IdentitySmallTranslation : SmallTranslation C C.
    refine {| SVertexOf := (fun x => x);
      SPathOf := (fun _ _ x => AddEdge NoEdges x)
    |}; abstract (
      intros ? ? p1 p2 ?;
        transitivity p1;
          try solve [ induction p1; try apply SAddEdge_mor; try apply (IHp1 p1); reflexivity ];
            transitivity p2;
              try solve [ induction p2; try apply SAddEdge_mor; try apply (IHp2 p2); reflexivity ];
                assumption
    ).
  Defined.

  Hint Unfold ComposeSmallTranslations IdentitySmallTranslation SVertexOf SPathOf.

  Lemma LeftIdentitySmallTranslation (F : SmallTranslation D C) : ComposeSmallTranslations IdentitySmallTranslation F = F.
    stranslation_eq.
    match goal with
      | [ |- ?a = ?b ] => induction b; t_with t'
    end.
  Qed.

  Lemma RightIdentitySmallTranslation (F : SmallTranslation C D) : ComposeSmallTranslations F IdentitySmallTranslation = F.
    stranslation_eq; t_with t'.
  Qed.
End SmallSchema.

Section SmallTranslationCompositionLemmas.
  Variable B C D E : SmallSchema.

  Lemma ComposeSmallTranslationsAssociativity (F : SmallTranslation B C) (G : SmallTranslation C D) (H : SmallTranslation D E) :
    ComposeSmallTranslations (ComposeSmallTranslations H G) F = ComposeSmallTranslations H (ComposeSmallTranslations G F).
    unfold ComposeSmallTranslations; stranslation_eq.
    match goal with
      | [ |- STransferPath _ ?p = _ ] => induction p; t_with t'
    end.
  Qed.
End SmallTranslationCompositionLemmas.

Section SmallTranslationsEquivalent.
  Variables C D : SmallSchema.
  Variables F G : SmallTranslation C D.

  Definition SmallTranslationsEquivalent :=
    exists vo po po' eo eo',
      F = {| SVertexOf := vo; SPathOf := po; STEquivalenceOf := eo |} /\
      G = {| SVertexOf := vo; SPathOf := po'; STEquivalenceOf := eo' |} /\
      forall s d (e : C.(SEdge) s d), SPathsEquivalent _ (po _ _ e) (po' _ _ e).

  Lemma stranslations_equivalent :
    SVertexOf F = SVertexOf G
    -> (SVertexOf F = SVertexOf G ->
        forall s d (e : C.(SEdge) s d), GeneralizedSPathsEquivalent (SPathOf F _ _ e) (SPathOf G _ _ e))
    -> SmallTranslationsEquivalent.
    unfold SmallTranslationsEquivalent;
      destruct F as [ vo po tp eo ], G as [ vo' po' tp' eo' ];
        simpl; intros; subst tp tp'; intuition; repeat subst;
          repeat esplit; f_equal; intros.
    match goal with
      | [ s : _, d : _, e : _, H : _ |- _ ] => specialize (H s d e); simpl_GeneralizedSPathsEquivalent; assumption
    end.
  Qed.
End SmallTranslationsEquivalent.

Ltac stranslation_eqv_step_with tac := intros; simpl;
  match goal with
    | _ => reflexivity
    | [ |- SmallTranslationsEquivalent _ _ ] => apply stranslations_equivalent
    | [ |- (fun _ : ?A => _) = _ ] => apply functional_extensionality_dep; intro
    | [ |- (fun _ : ?A => _) == _ ] => apply (@functional_extensionality_dep_JMeq A); intro
    | [ |- (forall _ : ?A, _) = _ ] => apply (@forall_extensionality_dep A); intro
    | [ H := _ |- _ ] => subst H
    | _ => simpl in *; repeat subst; try simpl_GeneralizedSPathsEquivalent; tac
  end; repeat simpl in *; JMeq_eq.

Ltac stranslation_eqv_with tac := repeat stranslation_eqv_step_with tac.

Ltac stranslation_eqv_step := stranslation_eqv_step_with idtac.
Ltac stranslation_eqv := stranslation_eqv_with idtac.

Section SmallTranslationsEquivalent_Relation.
  Variables C D E : SmallSchema.

  Lemma SmallTranslationsEquivalent_refl (T : SmallTranslation C D) : SmallTranslationsEquivalent T T.
    stranslation_eqv.
  Qed.

  Lemma SmallTranslationsEquivalent_sym (T U : SmallTranslation C D) :
    SmallTranslationsEquivalent T U -> SmallTranslationsEquivalent U T.
    intro H; destruct H; destruct_hypotheses.
    stranslation_eqv; symmetry; intuition.
  Qed.

  Lemma SmallTranslationsEquivalent_trans (T U V : SmallTranslation C D) :
    SmallTranslationsEquivalent T U -> SmallTranslationsEquivalent U V -> SmallTranslationsEquivalent T V.
    intros H0 H1; destruct H0, H1; destruct_hypotheses.
    stranslation_eqv;
    match goal with
      | [ H : _ |- _ ] => apply stranslations_equal_parts in H; unfold SPathOf, SVertexOf in H; destruct H; repeat subst
    end; try reflexivity.
    etransitivity; eauto.
  Qed.

  Hint Resolve STEquivalenceOf.

  Lemma PreComposeSmallTranslationsEquivalent (T T' : SmallTranslation C D) (U : SmallTranslation D E) :
    SmallTranslationsEquivalent T T' -> SmallTranslationsEquivalent (ComposeSmallTranslations U T) (ComposeSmallTranslations U T').
    intro H; destruct H; stranslation_eqv_with ltac:(destruct_hypotheses; eauto).
  Qed.

  Hint Resolve concatenate_mor.

  Lemma PostComposeSmallTranslationsEquivalent (T : SmallTranslation C D) (U U' : SmallTranslation D E) :
    SmallTranslationsEquivalent U U' -> SmallTranslationsEquivalent (ComposeSmallTranslations U T) (ComposeSmallTranslations U' T).
    intro H; destruct H; stranslation_eqv_with ltac:(destruct_hypotheses; eauto).
    destruct T; unfold STransferPath; stranslation_eqv.
    match goal with
      | [ |- ?Rel (transferPath _ _ ?p) (transferPath _ _ ?p) ] => induction p; simpl; try reflexivity
    end; eauto.
  Qed.
End SmallTranslationsEquivalent_Relation.

Add Parametric Relation C D : _ (@SmallTranslationsEquivalent C D)
  reflexivity proved by (@SmallTranslationsEquivalent_refl _ _)
  symmetry proved by (@SmallTranslationsEquivalent_sym _ _)
  transitivity proved by (@SmallTranslationsEquivalent_trans _ _)
    as SmallTranslationsEquivalent_rel.

Add Parametric Morphism C D E : (@ComposeSmallTranslations C D E)
  with signature (@SmallTranslationsEquivalent _ _) ==> (@SmallTranslationsEquivalent _ _) ==> (@SmallTranslationsEquivalent _ _)
    as ComposeSmallTranslations_mor.
  intros ? ? H0 ? ? H1.
  etransitivity; try apply PostComposeSmallTranslationsEquivalent; eauto;
    apply PreComposeSmallTranslationsEquivalent; eauto.
Qed.

Hint Resolve ComposeSmallTranslations_mor.

(*
Section Small2Large.
  Variables C D : SmallSchema.
  Variable T : SmallTranslation C D.

  Hint Resolve STEquivalenceOf.

  Hint Rewrite concatenate2concatenate spath_roundtrip spath_roundtrip'.

  Ltac equiv_by_equal :=
    match goal with
      | [ |- ?Rel ?a ?b ] => cut (a = b); try solve [ let H := fresh in intro H; rewrite H || rewrite <- H; reflexivity ]
    end.

  Ltac equiv_by_SPathsEquivalent :=
    match goal with
      | [ |- ?Rel ?a ?b ] => cut (SPathsEquivalent _ _ _ a b); simpl in *;
        repeat rewrite spath_roundtrip in *; repeat rewrite spath_roundtrip' in *;
          try solve [ let H := fresh in intro H; eauto; rewrite H || rewrite <- H; eauto; try reflexivity ]
    end.

  (* XXX TODO: Automate this better *)
  Definition SmallTranslation2Translation : Translation C D.
    refine {| VertexOf := (fun c : @Vertex C => @SVertexOf _ _ T (c : SVertex C) : Vertex D);
      PathOf := @SPathOf _ _ T
    |}.
      intros s d p1 p2 H;
        unfold path in p1, p2; simpl in p1, p2, s, d;
          cut (SPathsEquivalent C s d p1 p2); auto; clear H;
            intro H;
              pose stransferPath_transferPath as H1;
                autorewrite with core in H1; simpl in H1;
                  specialize (H1 C D);
                    match goal with
                      | [ |- ?Rel (transferPath ?vertexOf _ _) _ ] => specialize (H1 vertexOf)
                    end;
                    specialize (H1 T.(SPathOf));
                      pose (H1 _ _ p1) as H2;
                        pose (H1 _ _ p2) as H3;
                          repeat rewrite spath_roundtrip in *;
                            repeat rewrite spath_roundtrip' in *;
                              simpl in H2, H3.

      simpl. simpl in *.
  (* XXX Stupid tactics that don't type-check their arguments...  I'm frustrated with lack of universe polymorphism and the hoops I have to jump through to get Coq to accept trivial proofs. *)
                                  rewrite <- H2;
                                    rewrite <- H3;
                                      clear H1 H2 H3.
                                  Goal forall C s d (p p' : spath' C.(SEdge) s d), SPathsEquivalent _ _ _ p p' -> PathsEquivalent _ _ _ p p'.
                                  apply SmallSchema2Schema.

                                        equiv_by_SPathsEquivalent.
                                  intro H1. simpl in *; auto.
      admit. Defined.
                              pose STEquivalenceOf as H1;
                                unfold STransferPath in *;
                                  simpl in *;
                                    etransitivity; autorewrite with core;
                                      try solve [ symmetry; etransitivity; solve [ symmetry; apply H1; eauto ] || reflexivity ]; reflexivity.
  Defined.
End Small2Large.

Coercion SmallSchema2Schema : SmallSchema >-> Schema.
*)
