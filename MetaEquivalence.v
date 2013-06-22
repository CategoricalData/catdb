Require Import Setoid Eqdep.
Import Eq_rect_eq.
Require Export MetaTranslation.
Require Import Common.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section MetaEquivalence.
  Variable C D : Schema.
  Variable F G : Translation C D.

  Definition MetaEquivalence (T : MetaTranslation F G) :=
    forall x : C.(Vertex), SchemaIsomorphism (T.(SComponentsOf) x).

  Definition TranslationsNaturallyEquivalent : Prop :=
    exists T : MetaTranslation F G, exists TE : MetaEquivalence T, True.
End MetaEquivalence.

Section MetaEquivalenceOfSchemas.
  Variable C D : Schema.

  Definition MetaEquivalenceOfSchemas (F : Translation C D) (G : Translation D C) : Prop :=
    (TranslationsNaturallyEquivalent (IdentityTranslation C) (ComposeTranslations G F)) /\
    (TranslationsNaturallyEquivalent (IdentityTranslation D) (ComposeTranslations F G)).

  Definition SchemasNaturallyEquivalent : Prop :=
    exists F : Translation C D, exists G : Translation D C, MetaEquivalenceOfSchemas F G.
End MetaEquivalenceOfSchemas.

Section MetaEquivalenceInverse.
  Variable C D : Schema.
  Variable F G : Translation C D.
  Variable T : MetaTranslation F G.

  Hint Unfold SInverseOf.
  Hint Resolve f_equal f_equal2 SCommutes.

  Definition MetaEquivalenceInverse : MetaEquivalence T -> MetaTranslation G F.
    refine (fun X => {| SComponentsOf := (fun c => proj1_sig (X c)) |});
      abstract (intros; destruct (X s); destruct (X d); simpl; firstorder;
        eapply s_iso_is_epi; [ eauto | ]; eapply s_iso_is_mono; [ eauto | ];
          symmetry;
            repeat match goal with
                     | [ H : _ |- _ ]
                       => try_rewrite
                       concatenate_associative
                       ltac:(try rewrite H; (rewrite concatenate_noedges_p || rewrite concatenate_p_noedges); eauto)
                   end).
  Defined.

  Hint Immediate SInverseOf_sym.

  Lemma MetaEquivalenceInverse_MetaEquivalence (TE : MetaEquivalence T) : MetaEquivalence (MetaEquivalenceInverse TE).
    unfold MetaEquivalence, SchemaIsomorphism in *; simpl in *;
      intro x; destruct (TE x); eauto.
  Qed.
End MetaEquivalenceInverse.

Section IdentityMetaTranslation.
  Variable C D : Schema.
  Variable F : Translation C D.

  Lemma SInverseOf_Identity : forall C (x : C.(Vertex)), SInverseOf (@NoEdges _ _ x) (@NoEdges _ _ x).
    firstorder; unfold concatenate; reflexivity.
  Qed.

  Hint Resolve SInverseOf_Identity.

  Theorem IdentityMetaEquivalence : MetaEquivalence (IdentityMetaTranslation F).
    hnf; intros; hnf; simpl; eauto.
  Qed.
End IdentityMetaTranslation.

Section TranslationMetaEquivalenceRelation.
  Variable C D : Schema.

  Hint Resolve IdentityMetaEquivalence.

  Lemma translations_naturally_equivalent_refl (F : Translation C D) : TranslationsNaturallyEquivalent F F.
    exists (IdentityMetaTranslation F); eauto.
  Qed.

  Hint Resolve MetaEquivalenceInverse_MetaEquivalence.

  Lemma translations_naturally_equivalent_sym (F G : Translation C D) :
    TranslationsNaturallyEquivalent F G -> TranslationsNaturallyEquivalent G F.
    destruct 1 as [ ? [ H ] ]; exists (MetaEquivalenceInverse H); eauto.
  Qed.

  Hint Resolve SchemaIsomorphismComposition.

  Lemma translations_naturally_equivalent_trans (F G H : Translation C D) :
    TranslationsNaturallyEquivalent F G -> TranslationsNaturallyEquivalent G H -> TranslationsNaturallyEquivalent F H.
    destruct 1 as [ T [ ] ]; destruct 1 as [ U [ ] ];
      exists (MTComposeMT U T); eexists; hnf; simpl; eauto.
  Qed.

End TranslationMetaEquivalenceRelation.

Add Parametric Relation (C D : Schema) : _ (@TranslationsNaturallyEquivalent C D)
  reflexivity proved by (@translations_naturally_equivalent_refl _ _)
  symmetry proved by (@translations_naturally_equivalent_sym _ _)
  transitivity proved by (@translations_naturally_equivalent_trans _ _)
    as translations_naturally_equivalent.

(* XXX TODO: Automate this better *)
Add Parametric Morphism C D E :
  (@ComposeTranslations C D E)
  with signature (@TranslationsNaturallyEquivalent _ _) ==> (@TranslationsNaturallyEquivalent _ _) ==> (@TranslationsNaturallyEquivalent _ _) as functor_n_eq_mor.
  intros F F' NEF G G' NEG; unfold TranslationsNaturallyEquivalent, MetaEquivalence, SchemaIsomorphism, SInverseOf in *;
    destruct_hypotheses.
  match goal with
    | [ T1 : _ , T2 : _ |- _ ] => exists (MTComposeT T1 T2); try (constructor; trivial)
  end.
  intros; simpl.
  match goal with
    | [ x : ?C, H : (forall _ : ?C, _) |- _ ] => specialize (H x)
  end.
  match goal with
    | [ H : (forall _ : ?D, { _ : path _ (?F' _) (?F _) | _ }) |- { _ : path _ (?F' ?x') (?F ?x) | _ } ]
      => generalize (H x); generalize (H x'); intros ? ?; clear H
  end.
  destruct_type sig; destruct_type and.
  match goal with
    | [ F' : _, mG'x2Gx : _, mF'Gx2FGx : _ |- _ ] => exists (concatenate (F'.(TransferPath) mG'x2Gx) mF'Gx2FGx)
  end; split; concatenate4associativity; repeat (try rewrite <- concatenate_TransferPath; t_con @PathsEquivalent).
Qed.

Section TranslationMetaEquivalenceLemmas.
  Variable B C D E : Schema.

  Hint Resolve LeftIdentityTranslation RightIdentityTranslation.

  Lemma LeftIdentityTranslationNE (F : Translation D C) : TranslationsNaturallyEquivalent (ComposeTranslations (IdentityTranslation _) F) F.
    match goal with
      | [ |- TranslationsNaturallyEquivalent ?a ?b ] => assert (H : a = b); eauto; try (rewrite H; reflexivity)
    end.
  Qed.

  Lemma RightIdentityTranslationNE (F : Translation C D) : TranslationsNaturallyEquivalent (ComposeTranslations F (IdentityTranslation _)) F.
    match goal with
      | [ |- TranslationsNaturallyEquivalent ?a ?b ] => assert (H : a = b); eauto; try (rewrite H; reflexivity)
    end.
  Qed.

  Hint Unfold TranslationsNaturallyEquivalent ComposeTranslations MetaEquivalence SchemaIsomorphism SInverseOf.

  (* XXX TODO: Automate this better. *)
  Lemma PreComposeTranslationsNE (G : Translation D E) (F1 F2 : Translation C D) :
    TranslationsNaturallyEquivalent F1 F2 -> TranslationsNaturallyEquivalent (ComposeTranslations G F1) (ComposeTranslations G F2).
    intro H.
    destruct H as [ T [ H t ] ]; clear t.
    eexists (MTComposeT (IdentityMetaTranslation _) _).
    constructor; trivial; simpl.
    repeat autounfold with core in *; simpl.
    intro x0; specialize (H x0).
    destruct_type sig; destruct_type and.
    autorewrite with core in *.
    eexists (TransferPath G x);
      repeat (rewrite concatenate_p_noedges || rewrite concatenate_noedges_p);
        repeat rewrite <- concatenate_TransferPath;
          split;
            rewrite <- TransferPath_NoEdges;
              apply TEquivalenceOf;
                etransitivity; eauto; try reflexivity.
  Qed.

  Lemma PostComposeTranslationsNE (G1 G2 : Translation D E) (F : Translation C D) :
    TranslationsNaturallyEquivalent G1 G2 -> TranslationsNaturallyEquivalent (ComposeTranslations G1 F) (ComposeTranslations G2 F).
    intro H.
    destruct H as [ T [ H t ] ]; clear t.
    eexists (MTComposeT _ (IdentityMetaTranslation _)).
    constructor; trivial; simpl.
    repeat autounfold with core in *; simpl.
    intro x0; specialize (H (F x0)).
    destruct_type sig; destruct_type and.
    eexists; eauto.
  Qed.

  Hint Resolve ComposeTranslationsAssociativity.

  Lemma ComposeTranslationsAssociativityNE (F : Translation B C) (G : Translation C D) (H : Translation D E) :
    TranslationsNaturallyEquivalent (ComposeTranslations (ComposeTranslations H G) F) (ComposeTranslations H (ComposeTranslations G F)).
    match goal with
      | [ |- TranslationsNaturallyEquivalent ?a ?b ] => cut (a = b); try let H' := fresh in solve [ intro H'; rewrite H'; trivial || reflexivity ]
    end; eauto.
  Qed.
End TranslationMetaEquivalenceLemmas.

Section SchemaMetaEquivalenceRelation.
  Hint Unfold MetaEquivalenceOfSchemas.

  Hint Resolve IdentityMetaEquivalence IdentityTranslation.

  Hint Resolve LeftIdentityTranslation RightIdentityTranslation.

  Lemma schemas_naturally_equivalent_refl C : SchemasNaturallyEquivalent C C.
    repeat (exists (IdentityTranslation C)); split;
      match goal with
        | [ |- TranslationsNaturallyEquivalent ?a ?b ] => cut (a = b); try let H' := fresh in solve [ intro H'; rewrite <- H'; reflexivity || trivial ]
      end; eauto.
  Qed.

  Hint Resolve MetaEquivalenceInverse_MetaEquivalence.

  Lemma schemas_naturally_equivalent_sym C D :
    SchemasNaturallyEquivalent C D -> SchemasNaturallyEquivalent D C.
    destruct 1 as [ F [ G [ ? ] ] ]; eexists; eauto.
  Qed.

  Hint Resolve SchemaIsomorphismComposition.

  Ltac solve_4_associativity :=
    match goal with
      | [ |- ?Rel _ (ComposeTranslations (ComposeTranslations ?a ?b) (ComposeTranslations ?c ?d)) ] =>
        transitivity (ComposeTranslations a (ComposeTranslations (ComposeTranslations b c) d));
          try solve [ repeat (rewrite ComposeTranslationsAssociativity); reflexivity || trivial ]
    end.
  Hint Extern 1 (TranslationsNaturallyEquivalent _ (ComposeTranslations ?a (ComposeTranslations (IdentityTranslation _) ?c))) => transitivity (ComposeTranslations a c).

  Hint Resolve PreComposeTranslationsNE PostComposeTranslationsNE.
  Hint Rewrite LeftIdentityTranslationNE RightIdentityTranslationNE.

  Lemma schemas_naturally_equivalent_trans C D E :
    SchemasNaturallyEquivalent C D -> SchemasNaturallyEquivalent D E -> SchemasNaturallyEquivalent C E.
    destruct 1 as [ F [ F' [ T T' ] ] ]; destruct 1 as [ G [ G' [ U U' ] ] ].
    exists (ComposeTranslations G F); exists (ComposeTranslations F' G').
    split; solve_4_associativity;
    match goal with
      | [ H : _ |- _ ] => rewrite <- H
    end; t.
  Qed.
End SchemaMetaEquivalenceRelation.

Add Parametric Relation : _ SchemasNaturallyEquivalent
  reflexivity proved by schemas_naturally_equivalent_refl
  symmetry proved by schemas_naturally_equivalent_sym
  transitivity proved by schemas_naturally_equivalent_trans
    as schemas_naturally_equivalent.
