Require Import Setoid.
Require Export Category NaturalTransformation CategoryIsomorphisms.
Require Import Common.

Set Implicit Arguments.

Local Ltac intro_object_of :=
  repeat match goal with
           | [ |- appcontext[ObjectOf ?G ?x] ] => unique_pose_with_body (ObjectOf G x)
         end.

Section NaturalIsomorphism.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.
  Variables F G : SpecializedFunctor C D.

  Record NaturalIsomorphism := {
    NaturalIsomorphism_Transformation :> SpecializedNaturalTransformation F G;
    NaturalIsomorphism_Isomorphism : forall x : objC, IsomorphismOf (NaturalIsomorphism_Transformation x)
  }.
End NaturalIsomorphism.

Section NaturalIsomorphismOfCategories.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.

  Local Reserved Notation "'F'".
  Local Reserved Notation "'G'".

  Record NaturalIsomorphismOfCategories := {
    NaturalIsomorphismOfCategories_F : SpecializedFunctor C D where "'F'" := NaturalIsomorphismOfCategories_F;
    NaturalIsomorphismOfCategories_G : SpecializedFunctor D C where "'G'" := NaturalIsomorphismOfCategories_G;
    NaturalIsomorphismOfCategories_Isomorphism_C :> NaturalIsomorphism (IdentityFunctor C) (ComposeFunctors G F);
    NaturalIsomorphismOfCategories_Isomorphism_D : NaturalIsomorphism (IdentityFunctor D) (ComposeFunctors F G)
  }.

  Record IsomorphismOfCategories := {
    IsomorphismOfCategories_F : SpecializedFunctor C D where "'F'" := IsomorphismOfCategories_F;
    IsomorphismOfCategories_G : SpecializedFunctor D C where "'G'" := IsomorphismOfCategories_G;
    IsomorphismOfCategories_Isomorphism_C : ComposeFunctors G F = IdentityFunctor C;
    IsomorphismOfCategories_Isomorphism_D : ComposeFunctors F G = IdentityFunctor D
  }.
End NaturalIsomorphismOfCategories.

Section NaturalEquivalence.
  Variable C D : Category.
  Variable F G : Functor C D.

  Definition NaturalEquivalenceOf (T : NaturalTransformation F G) :=
    forall x : C.(Object), IsomorphismOf (T.(ComponentsOf) x).

  Definition FunctorsNaturallyEquivalent : Prop :=
    exists T : NaturalTransformation F G, exists NE : NaturalEquivalenceOf T, True.
End NaturalEquivalence.

(* grumble, grumble, grumble, [Functors] take [SpecializedCategories] and so we don't get type inference.
   Perhaps I should fix this?  But I don't like having to prefix so many things with [Specialized] and
   having duplicated code just so I get type inference.
   *)
Arguments NaturalEquivalenceOf [C D F G] T.
Arguments FunctorsNaturallyEquivalent [C D] F G.

Section Coercions.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.
  Variables F G : SpecializedFunctor C D.

  Variables C' D' : Category.
  Variables F' G' : Functor C' D'.

  Definition NaturalEquivalence_of_NaturalIsomorphism (T : NaturalIsomorphism F G) : NaturalEquivalenceOf T
    := fun x => NaturalIsomorphism_Isomorphism T x.

  Definition NaturalIsomorphism_of_NaturalEquivalence (T : NaturalTransformation F' G') (NE : NaturalEquivalenceOf T) : NaturalIsomorphism F' G'.
    exists T.
    exact (fun x => NE x : IsomorphismOf _).
  Defined.
End Coercions.

Coercion NaturalEquivalence_of_NaturalIsomorphism : NaturalIsomorphism >-> NaturalEquivalenceOf.
Coercion NaturalIsomorphism_of_NaturalEquivalence : NaturalEquivalenceOf >-> NaturalIsomorphism.
(* gives "Ambiguous paths"... Is this bad? *)

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

  Definition NaturalEquivalenceInverse : NaturalEquivalenceOf T -> NaturalTransformation G F.
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

  Hint Immediate IsInverseOf_sym.

  Lemma NaturalEquivalenceInverse_NaturalEquivalence (TE : NaturalEquivalenceOf T) : NaturalEquivalenceOf (NaturalEquivalenceInverse TE).
    intro; apply InverseOf.
  Qed.
End NaturalTransformationInverse.

Section IdentityNaturalTransformation.
  Variable C D : Category.
  Variable F : Functor C D.

  Theorem IdentityNaturalEquivalence : NaturalEquivalenceOf (IdentityNaturalTransformation F).
    hnf; intros; hnf; simpl; unfold InverseOf in *; eexists; t_with eauto.
    Grab Existential Variables.
    eauto.
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

  Hint Resolve @ComposeIsmorphismOf.

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
  intros F F' NEF G G' NEG; unfold FunctorsNaturallyEquivalent, NaturalEquivalenceOf, InverseOf in *;
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
  destruct_type @IsomorphismOf.
  eexists (Compose _ (MorphismOf _ _));
    compose4associativity;
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

  Hint Unfold FunctorsNaturallyEquivalent ComposeFunctors NaturalEquivalenceOf InverseOf.

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
        rewrite FIdentityOf; eauto.
    Grab Existential Variables.
    eauto.
  Qed.

  Hint Resolve @ComposeIsmorphismOf.

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
    eexists; t_rev_with t'.
    Grab Existential Variables.
    autorewrite with core; eauto.
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
