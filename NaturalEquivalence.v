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
  Hint Resolve PostComposeMorphisms PreComposeMorphisms Commutes Transitive.
  Hint Immediate Symmetric.

  Definition NaturalEquivalenceInverse : NaturalEquivalence T -> NaturalTransformation G F.
    refine (fun X => {| ComponentsOf := (fun c => proj1_sig (X c)) |});
      abstract (intros; destruct (X s); destruct (X d); simpl; firstorder;
        eapply iso_is_epi; [ eauto | ]; eapply iso_is_mono; [ eauto | ];
          morphisms 2).
  Defined.

  Lemma InverseOf_symm : forall C x y (m : C.(Morphism) x y) m', InverseOf m m'
    -> InverseOf m' m.
    firstorder.
  Qed.

  Hint Immediate InverseOf_symm.

  Lemma NaturalEquivalenceInverse_NaturalEquivalence (TE : NaturalEquivalence T) : NaturalEquivalence (NaturalEquivalenceInverse TE).
    unfold NaturalEquivalence, CategoryIsomorphism in *; simpl in *;
      intro x; destruct (TE x); eauto.
  Qed.
End NaturalTransformationInverse.

Implicit Arguments NaturalEquivalenceInverse [C D F G T].

Section IdentityNaturalTransformation.
  Variable C D : Category.
  Variable F : Functor C D.

  Hint Resolve LeftIdentity RightIdentity.
  Hint Resolve Symmetric.

  Lemma InverseOf_Identity : forall C (x : C.(Object)), InverseOf (Identity x) (Identity x).
    firstorder.
  Qed.

  Hint Resolve InverseOf_Identity.

  Theorem IdentityNaturalEquivalence : NaturalEquivalence (IdentityNaturalTransformation F).
    hnf; intros; hnf; simpl; eauto.
  Qed.
End IdentityNaturalTransformation.

Section FunctorNaturalEquivalenceRelation.
  Variable C D : Category.

  Hint Resolve IdentityNaturalEquivalence.

  Lemma functors_naturally_equivalent_refl (F : Functor C D) : FunctorsNaturallyEquivalent F F.
    exists (IdentityNaturalTransformation F); eauto.
  Qed.

  Hint Resolve NaturalEquivalenceInverse_NaturalEquivalence.

  Lemma functors_naturally_equivalent_symm (F G : Functor C D) :
    FunctorsNaturallyEquivalent F G -> FunctorsNaturallyEquivalent G F.
    destruct 1 as [ ? [ H ] ]; exists (NaturalEquivalenceInverse H); eauto.
  Qed.

  Hint Resolve CategoryIsomorphismComposition.

  Lemma functors_naturally_equivalent_trans (F G H : Functor C D) :
    FunctorsNaturallyEquivalent F G -> FunctorsNaturallyEquivalent G H -> FunctorsNaturallyEquivalent F H.
    destruct 1 as [ T [ ] ]; destruct 1 as [ U [ ] ];
      exists (NTComposeT U T); eexists; hnf; simpl; eauto.
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
