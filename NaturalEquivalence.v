Require Import Setoid.
Require Import Common EquivalenceRelation Category Functor NaturalTransformation.

Section NaturalEquivalence.
  Variable C D : Category.
  Variable F G : Functor C D.

  Definition NaturalEquivalence (T : NaturalTransformation F G) :=
    forall x : C.(Object), CategoryIsomorphism (T.(ComponentsOf) x).

  Definition FunctorsNaturallyEquivalent : Prop :=
    exists T : NaturalTransformation F G, exists TE : NaturalEquivalence T, True.
End NaturalEquivalence.

Implicit Arguments NaturalEquivalence [C D F G].
Implicit Arguments FunctorsNaturallyEquivalent [C D].

Section NaturalTransformationInverse.
  Variable C D : Category.
  Variable F G : Functor C D.
  Variable T : NaturalTransformation F G.

  Hint Unfold InverseOf Morphism.
  Hint Extern 1 (RelationsEquivalent _ _ _ _ ?M1 ?M2) => identity_transitvity.
  Hint Resolve PostComposeMorphisms PreComposeMorphisms.

  (* XXX TODO: Figure out a way to better automate this proof *)
  Definition NaturalEquivalenceInverse : (NaturalEquivalence T) -> (NaturalTransformation G F).
    unfold NaturalEquivalence; unfold CategoryIsomorphism; intros.
    refine {| ComponentsOf := (fun c => proj1_sig (X c))
    |}.
    intros.
    assert (InverseOf (T d) (proj1_sig (X d))). apply proj2_sig.
    assert (InverseOf (T s) (proj1_sig (X s))). apply proj2_sig.
    unfold InverseOf in *; t.

    pre_compose_mono (T d).
    unfold Monomorphism.
    intros.
    pre_compose_to_identity.

    rewrite_to_identity.

    post_compose_epi (T s).
    unfold Epimorphism.
    intros.
    post_compose_to_identity.

    rewrite_to_identity.
    symmetry.
    apply Commutes.
  Defined.

  Lemma NaturalEquivalenceInverse_NaturalEquivalence (TE : NaturalEquivalence T) : NaturalEquivalence (NaturalEquivalenceInverse TE).
    unfold NaturalEquivalence in *; simpl.
    unfold CategoryIsomorphism in *.
    intros.
    exists (T _).
    match goal with
      | [ |- InverseOf ?A ?B ] => cut (InverseOf B A)
    end.
    unfold InverseOf; t.
    exact (proj2_sig (TE _)).
  Qed.
End NaturalTransformationInverse.

Implicit Arguments NaturalEquivalenceInverse [C D F G T].

Section IdentityNaturalTransformation.
  Variable C D : Category.
  Variable F : Functor C D.

  Theorem IdentityNaturalEquivalence : NaturalEquivalence (IdentityNaturalTransformation F).
    unfold NaturalEquivalence. intros.
    exists (Identity _).
    unfold InverseOf.
    t.
  Qed.
End IdentityNaturalTransformation.

Section FunctorNaturalEquivalenceRelation.
  Variable C D : Category.

  Lemma functors_naturally_equivalent_refl (F : Functor C D) : FunctorsNaturallyEquivalent F F.
    unfold FunctorsNaturallyEquivalent.
    exists (IdentityNaturalTransformation F).
    firstorder.
    apply IdentityNaturalEquivalence.
  Qed.

  Lemma functors_naturally_equivalent_symm (F G : Functor C D) :
    FunctorsNaturallyEquivalent F G -> FunctorsNaturallyEquivalent G F.
    unfold FunctorsNaturallyEquivalent.
    firstorder.
    match goal with
      | [
        x0 : NaturalEquivalence _
        |- _
        ] => exists (NaturalEquivalenceInverse x0);
      constructor; try trivial
    end.
    apply NaturalEquivalenceInverse_NaturalEquivalence.
  Qed.

  Hint Resolve CategoryIsomorphismComposition.

  Lemma functors_naturally_equivalent_trans (F G H : Functor C D) :
    FunctorsNaturallyEquivalent F G -> FunctorsNaturallyEquivalent G H -> FunctorsNaturallyEquivalent F H.
    unfold FunctorsNaturallyEquivalent; firstorder.
    match goal with
      | [
        T : NaturalTransformation F G,
        U : NaturalTransformation G H
        |- exists _ : NaturalTransformation F H, _
      ] => exists (NTComposeT T U)
    end.
    firstorder.
    unfold NaturalEquivalence in *.
    t.
  Qed.

  Definition FunctorsNaturallyEquivalentRelation : Relation_Definitions.relation (Functor C D) := (@FunctorsNaturallyEquivalent C D).
End FunctorNaturalEquivalenceRelation.

Add Parametric Relation (C D : Category) : _ (@FunctorsNaturallyEquivalent C D)
  reflexivity proved by (functors_naturally_equivalent_refl _ _)
  symmetry proved by (functors_naturally_equivalent_symm _ _)
    transitivity proved by (functors_naturally_equivalent_trans _ _)
      as functors_naturally_equivalent.

(*Add Parametric Morphism C D E :
  (@ComposeFunctor C D E)
  with signature (@FunctorsNaturallyEquivalent _ _) ==> (@FunctorsNaturallyEquivalent _ _) ==> (@FunctorsNaturallyEquivalent _ _) as functor_eq_mor.
  t. transitivity (ComposeFunctor x y0).
  unfold FunctorsNaturallyEquivalent in *.
  simpl in *.*)
