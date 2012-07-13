Require Import Setoid.
Require Export Category NaturalTransformation.
Require Import Common.

Set Implicit Arguments.

Local Ltac intro_object_of :=
  repeat match goal with
           | [ |- appcontext[ObjectOf ?G ?x] ] => unique_pose_with_body (ObjectOf G x)
         end.

Section NaturalEquivalence.
  Variable C D : Category.
  Variable F G : Functor C D.

  Definition NaturalEquivalence (T : NaturalTransformation F G) :=
    forall x : C.(Object), CategoryIsomorphism (T.(ComponentsOf) x).

  Definition FunctorsNaturallyEquivalent : Prop :=
    exists T : NaturalTransformation F G, exists TE : NaturalEquivalence T, True.
End NaturalEquivalence.

(* grumble, grumble, grumble, [Functors] take [SpecializedCategories] and so we don't get type inference.
   Perhaps I should fix this?  But I don't like having to prefix so many things with [Specialized] and
   having duplicated code just so I get type inference.
   *)
Arguments NaturalEquivalence [C D F G] T.
Arguments FunctorsNaturallyEquivalent [C D] F G.

Section NaturalEquivalenceOfCategories.
  Variable C D : Category.

  Definition NaturalEquivalenceOfCategories (F : Functor C D) (G : Functor D C) : Prop :=
    (FunctorsNaturallyEquivalent (IdentityFunctor C) (ComposeFunctors G F)) /\
    (FunctorsNaturallyEquivalent (IdentityFunctor D) (ComposeFunctors F G)).

  Definition CategoriesNaturallyEquivalent : Prop :=
    exists F : Functor C D, exists G : Functor D C, NaturalEquivalenceOfCategories F G.
End NaturalEquivalenceOfCategories.

Arguments NaturalEquivalenceOfCategories [C D] F G.

Section NaturalTransformationInverse.
  Variable C D : Category.
  Variable F G : Functor C D.
  Variable T : NaturalTransformation F G.

  Hint Unfold InverseOf.
  Hint Resolve f_equal f_equal2 Commutes.
  Hint Rewrite LeftIdentity RightIdentity.

  Definition NaturalEquivalenceInverse : NaturalEquivalence T -> NaturalTransformation G F.
    refine (fun X => {| ComponentsOf' := (fun c => proj1_sig (X c)) |});
      abstract (
        intros; destruct (X s); destruct (X d);
          simpl; unfold InverseOf in *; destruct_hypotheses;
            present_spnt; present_spcategory_all;
            pre_compose_to_identity; post_compose_to_identity;
            auto
      ).
    (*morphisms 2*)
  Defined.

  Hint Immediate InverseOf_sym.

  Lemma NaturalEquivalenceInverse_NaturalEquivalence (TE : NaturalEquivalence T) : NaturalEquivalence (NaturalEquivalenceInverse TE).
    unfold NaturalEquivalence, CategoryIsomorphism in *; simpl in *;
      intro x; destruct (TE x); eauto.
  Qed.
End NaturalTransformationInverse.

Section IdentityNaturalTransformation.
  Variable C D : Category.
  Variable F : Functor C D.

  Hint Resolve CategoryIdentityInverse.

  Theorem IdentityNaturalEquivalence : NaturalEquivalence (IdentityNaturalTransformation F).
    hnf; intros; hnf; simpl; unfold InverseOf in *; eexists; t_with eauto.
  Qed.
End IdentityNaturalTransformation.

Arguments IdentityNaturalEquivalence [C D] F x.

Section FunctorNaturalEquivalenceRelation.
  Variable C D : Category.

  Hint Resolve IdentityNaturalEquivalence.

  Lemma functors_naturally_equivalent_refl (F : Functor C D) : FunctorsNaturallyEquivalent F F.
    exists (IdentityNaturalTransformation F); eauto.
  Qed.

  Hint Resolve NaturalEquivalenceInverse_NaturalEquivalence.

  Lemma functors_naturally_equivalent_sym (F G : Functor C D) :
    FunctorsNaturallyEquivalent F G -> FunctorsNaturallyEquivalent G F.
    destruct 1 as [ ? [ H ] ]; exists (NaturalEquivalenceInverse H); eauto.
  Qed.

  Hint Resolve CategoryIsomorphismComposition.

  Lemma functors_naturally_equivalent_trans (F G H : Functor C D) :
    FunctorsNaturallyEquivalent F G -> FunctorsNaturallyEquivalent G H -> FunctorsNaturallyEquivalent F H.
    destruct 1 as [ T [ ] ]; destruct 1 as [ U [ ] ];
      exists (NTComposeT U T); eexists; hnf; simpl; eauto.
  Qed.

End FunctorNaturalEquivalenceRelation.

Add Parametric Relation (C D : Category) : _ (@FunctorsNaturallyEquivalent C D)
  reflexivity proved by (@functors_naturally_equivalent_refl _ _)
  symmetry proved by (@functors_naturally_equivalent_sym _ _)
  transitivity proved by (@functors_naturally_equivalent_trans _ _)
    as functors_naturally_equivalent.

(* XXX TODO: Automate this better *)
Add Parametric Morphism (C D E : Category) :
  (@ComposeFunctors _ _ C _ _ D _ _ E)
  with signature (@FunctorsNaturallyEquivalent _ _) ==> (@FunctorsNaturallyEquivalent _ _) ==> (@FunctorsNaturallyEquivalent _ _) as functor_n_eq_mor.
  intros F F' NEF G G' NEG; unfold FunctorsNaturallyEquivalent, NaturalEquivalence, CategoryIsomorphism, InverseOf in *;
    destruct_hypotheses.
  match goal with
    | [ T1 : _ , T2 : _ |- _ ] => exists (NTComposeF T1 T2); try (constructor; trivial)
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

Section FunctorNaturalEquivalenceLemmas.
  Variable B C D E : Category.

  Hint Resolve LeftIdentityFunctor RightIdentityFunctor.

  Lemma LeftIdentityFunctorNE (F : Functor D C) : FunctorsNaturallyEquivalent (ComposeFunctors (IdentityFunctor _) F) F.
    match goal with
      | [ |- FunctorsNaturallyEquivalent ?a ?b ] => assert (H : a = b); eauto; try (rewrite H; reflexivity)
    end.
  Qed.

  Lemma RightIdentityFunctorNE (F : Functor C D) : FunctorsNaturallyEquivalent (ComposeFunctors F (IdentityFunctor _)) F.
    match goal with
      | [ |- FunctorsNaturallyEquivalent ?a ?b ] => assert (H : a = b); eauto; try (rewrite H; reflexivity)
    end.
  Qed.

  Hint Resolve FCompositionOf FIdentityOf.
  Hint Rewrite FIdentityOf.

  Hint Resolve f_equal f_equal2.

  Hint Rewrite LeftIdentity RightIdentity.

  Hint Unfold FunctorsNaturallyEquivalent ComposeFunctors NaturalEquivalence CategoryIsomorphism InverseOf.

  (* XXX TODO: Automate this better. *)
  Lemma PreComposeFunctorsNE (G : Functor D E) (F1 F2 : Functor C D) :
    FunctorsNaturallyEquivalent F1 F2 -> FunctorsNaturallyEquivalent (ComposeFunctors G F1) (ComposeFunctors G F2).
    intro H.
    destruct H as [ T [ H t ] ]; clear t.
    eexists (NTComposeF (IdentityNaturalTransformation _) _).
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

  Lemma PostComposeFunctorsNE (G1 G2 : Functor D E) (F : Functor C D) :
    FunctorsNaturallyEquivalent G1 G2 -> FunctorsNaturallyEquivalent (ComposeFunctors G1 F) (ComposeFunctors G2 F).
    intro H.
    destruct H as [ T [ H t ] ]; clear t.
    eexists (NTComposeF _ (IdentityNaturalTransformation _)).
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

  Hint Resolve ComposeFunctorsAssociativity.

  Lemma ComposeFunctorsAssociativityNE (F : Functor B C) (G : Functor C D) (H : Functor D E) :
    FunctorsNaturallyEquivalent (ComposeFunctors (ComposeFunctors H G) F) (ComposeFunctors H (ComposeFunctors G F)).
    match goal with
      | [ |- FunctorsNaturallyEquivalent ?a ?b ] => cut (a = b); try let H' := fresh in solve [ intro H'; rewrite H'; trivial || reflexivity ]
    end; eauto.
  Qed.
End FunctorNaturalEquivalenceLemmas.

Section CategoryNaturalEquivalenceRelation.
  Hint Unfold NaturalEquivalenceOfCategories.

  Hint Resolve IdentityNaturalEquivalence IdentityFunctor.

  Hint Resolve LeftIdentityFunctor RightIdentityFunctor.

  Lemma categories_naturally_equivalent_refl C : CategoriesNaturallyEquivalent C C.
    repeat (exists (IdentityFunctor C)); split;
      match goal with
        | [ |- FunctorsNaturallyEquivalent ?a ?b ] => cut (a = b); try let H' := fresh in solve [ intro H'; rewrite <- H'; reflexivity || trivial ]
      end; eauto.
  Qed.

  Hint Resolve NaturalEquivalenceInverse_NaturalEquivalence.

  Lemma categories_naturally_equivalent_sym C D :
    CategoriesNaturallyEquivalent C D -> CategoriesNaturallyEquivalent D C.
    destruct 1 as [ F [ G [ ? ] ] ]; eexists; eauto.
  Qed.

  Hint Resolve CategoryIsomorphismComposition.

  Ltac solve_4_associativity :=
    match goal with
      | [ |- ?Rel _ (ComposeFunctors (ComposeFunctors ?a ?b) (ComposeFunctors ?c ?d)) ] =>
        transitivity (ComposeFunctors a (ComposeFunctors (ComposeFunctors b c) d));
          try solve [ repeat (rewrite ComposeFunctorsAssociativity); reflexivity || trivial ]
    end.
  Hint Extern 1 (FunctorsNaturallyEquivalent _ (ComposeFunctors ?a (ComposeFunctors (IdentityFunctor _) ?c))) => transitivity (ComposeFunctors a c).

  Hint Resolve PreComposeFunctorsNE PostComposeFunctorsNE.
  Hint Rewrite LeftIdentityFunctorNE RightIdentityFunctorNE.

  Lemma categories_naturally_equivalent_trans C D E :
    CategoriesNaturallyEquivalent C D -> CategoriesNaturallyEquivalent D E -> CategoriesNaturallyEquivalent C E.
    destruct 1 as [ F [ F' [ T T' ] ] ]; destruct 1 as [ G [ G' [ U U' ] ] ].
    exists (ComposeFunctors G F); exists (ComposeFunctors F' G').
    split; solve_4_associativity;
    match goal with
      | [ H : _ |- _ ] => rewrite <- H
    end; t.
  Qed.
End CategoryNaturalEquivalenceRelation.

Add Parametric Relation : _ CategoriesNaturallyEquivalent
  reflexivity proved by categories_naturally_equivalent_refl
  symmetry proved by categories_naturally_equivalent_sym
  transitivity proved by categories_naturally_equivalent_trans
    as categories_naturally_equivalent.
