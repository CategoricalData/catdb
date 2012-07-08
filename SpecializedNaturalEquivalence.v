Require Import Setoid.
Require Export SpecializedNaturalTransformation.
Require Import Common.

Set Implicit Arguments.

Local Ltac intro_object_of :=
  repeat match goal with
           | [ |- appcontext[ObjectOf ?G ?x] ] => unique_pose_with_body (ObjectOf G x)
         end.

Section NaturalEquivalence.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable F G : SpecializedFunctor C D.

  Definition SpecializedNaturalEquivalence (T : SpecializedNaturalTransformation F G) :=
    forall x : C.(Object), CategoryIsomorphism (T.(ComponentsOf) x).

  Definition SpecializedFunctorsNaturallyEquivalent : Prop :=
    exists T : SpecializedNaturalTransformation F G, exists TE : SpecializedNaturalEquivalence T, True.
End NaturalEquivalence.

Section NaturalEquivalenceOfCategories.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.

  Definition SpecializedNaturalEquivalenceOfSpecializedCategories (F : SpecializedFunctor C D) (G : SpecializedFunctor D C) : Prop :=
    (SpecializedFunctorsNaturallyEquivalent (IdentitySpecializedFunctor C) (ComposeSpecializedFunctors G F)) /\
    (SpecializedFunctorsNaturallyEquivalent (IdentitySpecializedFunctor D) (ComposeSpecializedFunctors F G)).

  Definition SpecializedCategoriesNaturallyEquivalent : Prop :=
    exists F : SpecializedFunctor C D, exists G : SpecializedFunctor D C, SpecializedNaturalEquivalenceOfSpecializedCategories F G.
End NaturalEquivalenceOfCategories.

Section SpecializedNaturalTransformationInverse.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable F G : SpecializedFunctor C D.
  Variable T : SpecializedNaturalTransformation F G.

  Hint Unfold InverseOf InverseOf'.
  Hint Resolve f_equal f_equal2 Commutes.
  Hint Rewrite LeftIdentity RightIdentity.

  Definition SpecializedNaturalEquivalenceInverse : SpecializedNaturalEquivalence T -> SpecializedNaturalTransformation G F.
    Transparent Morphism.
    refine (fun X => {| ComponentsOf' := (fun c => proj1_sig (X c)) |});
      abstract (
        intros; destruct (X s); destruct (X d);
          simpl; unfold InverseOf, InverseOf' in *; destruct_hypotheses;
            present_spnt;
            pre_compose_to_identity; post_compose_to_identity;
            auto
      ).
    (*morphisms 2*)
  Defined.

  Hint Immediate InverseOf_sym.

  Lemma SpecializedNaturalEquivalenceInverse_SpecializedNaturalEquivalence (TE : SpecializedNaturalEquivalence T) : SpecializedNaturalEquivalence (SpecializedNaturalEquivalenceInverse TE).
    unfold SpecializedNaturalEquivalence, CategoryIsomorphism, CategoryIsomorphism', InverseOf' in *; simpl in *;
      intro x; destruct (TE x);
        destruct_hypotheses;
        eauto.
  Qed.
End SpecializedNaturalTransformationInverse.

Section IdentitySpecializedNaturalTransformation.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable F : SpecializedFunctor C D.

  Hint Resolve CategoryIdentityInverse.

  Theorem IdentitySpecializedNaturalEquivalence : SpecializedNaturalEquivalence (IdentitySpecializedNaturalTransformation F).
    hnf; intros; hnf; simpl; unfold InverseOf' in *; eexists; t_with eauto.
  Qed.
End IdentitySpecializedNaturalTransformation.

Section SpecializedFunctorSpecializedNaturalEquivalenceRelation.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.

  Hint Resolve IdentitySpecializedNaturalEquivalence.

  Lemma SpecializedFunctorsNaturallyEquivalent_refl (F : SpecializedFunctor C D) : SpecializedFunctorsNaturallyEquivalent F F.
    exists (IdentitySpecializedNaturalTransformation F); eauto.
  Qed.

  Hint Resolve SpecializedNaturalEquivalenceInverse_SpecializedNaturalEquivalence.

  Lemma SpecializedFunctorsNaturallyEquivalent_sym (F G : SpecializedFunctor C D) :
    SpecializedFunctorsNaturallyEquivalent F G -> SpecializedFunctorsNaturallyEquivalent G F.
    destruct 1 as [ ? [ H ] ]; exists (SpecializedNaturalEquivalenceInverse H); eauto.
  Qed.

  Hint Resolve CategoryIsomorphismComposition.

  Lemma SpecializedFunctorsNaturallyEquivalent_trans (F G H : SpecializedFunctor C D) :
    SpecializedFunctorsNaturallyEquivalent F G -> SpecializedFunctorsNaturallyEquivalent G H -> SpecializedFunctorsNaturallyEquivalent F H.
    destruct 1 as [ T [ ] ]; destruct 1 as [ U [ ] ];
      exists (SPNTComposeT U T); eexists; hnf; simpl; eauto.
  Qed.
End SpecializedFunctorSpecializedNaturalEquivalenceRelation.

Add Parametric Relation objC morC objD morD (C : @SpecializedCategory objC morC) (D : @SpecializedCategory objD morD) :
  _ (@SpecializedFunctorsNaturallyEquivalent _ _ _ _ C D)
  reflexivity proved by (@SpecializedFunctorsNaturallyEquivalent_refl _ _ _ _ _ _)
  symmetry proved by (@SpecializedFunctorsNaturallyEquivalent_sym _ _ _ _ _ _)
  transitivity proved by (@SpecializedFunctorsNaturallyEquivalent_trans _ _ _ _ _ _)
    as specialized_functors_naturally_equivalent.

(* XXX TODO: Automate this better *)
Add Parametric Morphism objC morC objD morD objE morE (C : @SpecializedCategory objC morC) (D : @SpecializedCategory objD morD) (E : @SpecializedCategory objE morE) :
  (@ComposeSpecializedFunctors _ _ _ _ _ _ C D E)
  with signature
    (@SpecializedFunctorsNaturallyEquivalent _ _ _ _ _ _)
    ==> (@SpecializedFunctorsNaturallyEquivalent _ _ _ _ _ _)
    ==> (@SpecializedFunctorsNaturallyEquivalent _ _ _ _ _ _)
    as specialized_functors_naturally_equivalent_mor.
  intros F F' NEF G G' NEG; unfold SpecializedFunctorsNaturallyEquivalent, SpecializedNaturalEquivalence, CategoryIsomorphism, InverseOf, InverseOf' in *;
    destruct_hypotheses; unfold CategoryIsomorphism', InverseOf, InverseOf' in *.
  simpl in *.
  match goal with
    | [ T1 : _ , T2 : _ |- _ ] => exists (SPNTComposeF T1 T2); try (constructor; trivial)
  end.
  intros; simpl.
  intro_object_of.
  specialize_all_ways.
  destruct_sig; destruct_hypotheses.
  repeat match goal with
           | [ H := _ |- _ ] => subst H
         end.
  Hint Rewrite <- FCompositionOf.
  Hint Rewrite FIdentityOf.
  eexists (Compose _ (MorphismOf _ _));
    split; compose4associativity;
      repeat (try find_composition_to_identity; autorewrite with core);
        reflexivity.
Qed.

Section SpecializedFunctorSpecializedNaturalEquivalenceLemmas.
  Variable objB : Type.
  Variable morB : objB -> objB -> Type.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable objE : Type.
  Variable morE : objE -> objE -> Type.
  Variable B : SpecializedCategory morB.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable E : SpecializedCategory morE.

  Hint Resolve LeftIdentitySpecializedFunctor RightIdentitySpecializedFunctor.

  Lemma LeftIdentitySpecializedFunctorNE (F : SpecializedFunctor D C) : SpecializedFunctorsNaturallyEquivalent (ComposeSpecializedFunctors (IdentitySpecializedFunctor _) F) F.
    match goal with
      | [ |- SpecializedFunctorsNaturallyEquivalent ?a ?b ] => assert (H : a = b); eauto; try (rewrite H; reflexivity)
    end.
  Qed.

  Lemma RightIdentitySpecializedFunctorNE (F : SpecializedFunctor C D) : SpecializedFunctorsNaturallyEquivalent (ComposeSpecializedFunctors F (IdentitySpecializedFunctor _)) F.
    match goal with
      | [ |- SpecializedFunctorsNaturallyEquivalent ?a ?b ] => assert (H : a = b); eauto; try (rewrite H; reflexivity)
    end.
  Qed.

  Hint Resolve FCompositionOf FIdentityOf.
  Hint Rewrite FIdentityOf.

  Hint Resolve f_equal f_equal2.

  Hint Rewrite LeftIdentity RightIdentity.

  Hint Unfold SpecializedFunctorsNaturallyEquivalent ComposeSpecializedFunctors SpecializedNaturalEquivalence CategoryIsomorphism CategoryIsomorphism' InverseOf InverseOf'.

  (* XXX TODO: Automate this better. *)
  Lemma PreComposeSpecializedFunctorsNE (G : SpecializedFunctor D E) (F1 F2 : SpecializedFunctor C D) :
    SpecializedFunctorsNaturallyEquivalent F1 F2 -> SpecializedFunctorsNaturallyEquivalent (ComposeSpecializedFunctors G F1) (ComposeSpecializedFunctors G F2).
    intro H.
    destruct H as [ T [ H t ] ]; clear t.
    eexists (SPNTComposeF (IdentitySpecializedNaturalTransformation _) _).
    constructor; trivial; repeat (hnf; intros);
      repeat autounfold with core in *;
        simpl in *.
    specialize_all_ways;
    destruct_sig; destruct_hypotheses.
    eexists (MorphismOf G _);
      repeat (rewrite LeftIdentity || rewrite RightIdentity);
      repeat (rewrite <- FIdentityOf || rewrite <- FCompositionOf);
        split; rewrite FIdentityOf; eauto 15.
  Qed.

  Lemma PostComposeSpecializedFunctorsNE (G1 G2 : SpecializedFunctor D E) (F : SpecializedFunctor C D) :
    SpecializedFunctorsNaturallyEquivalent G1 G2 -> SpecializedFunctorsNaturallyEquivalent (ComposeSpecializedFunctors G1 F) (ComposeSpecializedFunctors G2 F).
    intro H.
    destruct H as [ T [ H t ] ]; clear t.
    eexists (SPNTComposeF _ (IdentitySpecializedNaturalTransformation _)).
    constructor; trivial; repeat (hnf; intros);
      repeat autounfold with core in *;
        simpl in *.
    intro_object_of.
    specialize_all_ways;
    destruct_sig; destruct_hypotheses.
    repeat match goal with
             | [ H := _ |- _ ] => subst H
           end.
    eexists; split; t_rev_with t'.
  Qed.

  Hint Resolve ComposeSpecializedFunctorsAssociativity.

  Lemma ComposeSpecializedFunctorsAssociativityNE (F : SpecializedFunctor B C) (G : SpecializedFunctor C D) (H : SpecializedFunctor D E) :
    SpecializedFunctorsNaturallyEquivalent (ComposeSpecializedFunctors (ComposeSpecializedFunctors H G) F) (ComposeSpecializedFunctors H (ComposeSpecializedFunctors G F)).
    match goal with
      | [ |- SpecializedFunctorsNaturallyEquivalent ?a ?b ] => cut (a = b); try let H' := fresh in solve [ intro H'; rewrite H'; trivial || reflexivity ]
    end; eauto.
  Qed.
End SpecializedFunctorSpecializedNaturalEquivalenceLemmas.

Section CategorySpecializedNaturalEquivalenceRelation.
  Hint Unfold SpecializedNaturalEquivalenceOfSpecializedCategories.

  Hint Resolve IdentitySpecializedNaturalEquivalence IdentitySpecializedFunctor.

  Hint Resolve LeftIdentitySpecializedFunctor RightIdentitySpecializedFunctor.

  Lemma SpecializedCategoriesNaturallyEquivalent_refl objC morC C : @SpecializedCategoriesNaturallyEquivalent objC morC _ _ C C.
    repeat (exists (IdentitySpecializedFunctor C)); split;
      match goal with
        | [ |- SpecializedFunctorsNaturallyEquivalent ?a ?b ] => cut (a = b); try let H' := fresh in solve [ intro H'; rewrite <- H'; reflexivity || trivial ]
      end; eauto.
  Qed.

  Hint Resolve SpecializedNaturalEquivalenceInverse_SpecializedNaturalEquivalence.

  Lemma SpecializedCategoriesNaturallyEquivalent_sym objC morC objD morD (C : @SpecializedCategory objC morC) (D : @SpecializedCategory objD morD) :
    SpecializedCategoriesNaturallyEquivalent C D -> SpecializedCategoriesNaturallyEquivalent D C.
    destruct 1 as [ F [ G [ ? ] ] ]; eexists; eauto.
  Qed.

  Hint Resolve CategoryIsomorphismComposition.

  Ltac solve_4_associativity :=
    match goal with
      | [ |- ?Rel _ (ComposeSpecializedFunctors (ComposeSpecializedFunctors ?a ?b) (ComposeSpecializedFunctors ?c ?d)) ] =>
        transitivity (ComposeSpecializedFunctors a (ComposeSpecializedFunctors (ComposeSpecializedFunctors b c) d));
          try solve [ repeat (rewrite ComposeSpecializedFunctorsAssociativity); reflexivity || trivial ]
    end.
  Hint Extern 1 (SpecializedFunctorsNaturallyEquivalent _ (ComposeSpecializedFunctors ?a (ComposeSpecializedFunctors (IdentitySpecializedFunctor _) ?c))) => transitivity (ComposeSpecializedFunctors a c).

  Hint Resolve PreComposeSpecializedFunctorsNE PostComposeSpecializedFunctorsNE.
  Hint Rewrite LeftIdentitySpecializedFunctorNE RightIdentitySpecializedFunctorNE.

  Lemma SpecializedCategoriesNaturallyEquivalent_trans objC morC objD morD objE morE
    (C : @SpecializedCategory objC morC) (D : @SpecializedCategory objD morD) (E : @SpecializedCategory objE morE) :
    SpecializedCategoriesNaturallyEquivalent C D -> SpecializedCategoriesNaturallyEquivalent D E -> SpecializedCategoriesNaturallyEquivalent C E.
    destruct 1 as [ F [ F' [ T T' ] ] ]; destruct 1 as [ G [ G' [ U U' ] ] ].
    exists (ComposeSpecializedFunctors G F); exists (ComposeSpecializedFunctors F' G').
    split; solve_4_associativity;
    match goal with
      | [ H : _ |- _ ] => rewrite <- H
    end; t.
  Qed.
End CategorySpecializedNaturalEquivalenceRelation.

Add Parametric Relation obj mor : _ (@SpecializedCategoriesNaturallyEquivalent obj mor obj mor)
  reflexivity proved by (@SpecializedCategoriesNaturallyEquivalent_refl _ _)
  symmetry proved by (@SpecializedCategoriesNaturallyEquivalent_sym _ _ _ _)
  transitivity proved by (@SpecializedCategoriesNaturallyEquivalent_trans _ _ _ _ _ _)
    as specialized_categories_naturally_equivalent.
