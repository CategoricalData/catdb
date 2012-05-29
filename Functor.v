Require Import Setoid Coq.Program.Basics Program.
Require Import Common EquivalenceRelation Category.

Section Functor.
  Variable C D : Category.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of categories is known as a functor. Namely, given
     categories [C] and [C'], a (covariant) functor [F : C -> C'] is a rule that assigns to
     each object [A] of [C] an object [F A] of [C'] and to each map [m : A -> B] of [C] a map
     [F m : F A -> F B] of [C'] preserving composition and identity; that is,
     (1) [F (m' ○ m) = (F m') ○ (F m)] for maps [m : A -> B] and [m' : B -> C] of [C], and
     (2) [F (id A) = id (F A)] for any object [A] of [C], where [id A] is the identity morphism of [A].

     Since we are using [MorhpismsEquivalent] rather than [=], we must additionally require
     that [F] preserves [MorphismsEquivalent].
     **)
  Record Functor := {
    ObjectOf :> C -> D;
    MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d);
    FEquivalenceOf : forall s d (m1 m2 : C.(Morphism) s d),
      MorphismsEquivalent _ _ _ m1 m2
      -> MorphismsEquivalent _ _ _ (MorphismOf _ _ m1) (MorphismOf _ _ m2);
    FCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
      MorphismsEquivalent _ _ _ (MorphismOf _ _ (Compose m2 m1))
      (Compose (MorphismOf _ _ m2) (MorphismOf _ _ m1));
    FIdentityOf : forall o, MorphismsEquivalent _ _ _ (MorphismOf _ _ (Identity o)) (Identity (ObjectOf o))
  }.
End Functor.

Implicit Arguments MorphismOf [C D s d].
Implicit Arguments FEquivalenceOf [C D s d m1 m2].
Implicit Arguments FCompositionOf [C D s d d' m1 m2].
Implicit Arguments FIdentityOf [C D].

Add Parametric Morphism C D s d F :
  (@MorphismOf C D F s d)
    with signature (MorphismsEquivalent C _ _) ==> (MorphismsEquivalent D _ _) as functor_morphism_eq_mor.
  intros; apply FEquivalenceOf; assumption.
Qed.

Section FunctorsEquivalent.
  Variable C D : Category.
  Variable F G : Functor C D.

  Definition FunctorsEquivalent : Prop :=
    forall s d (m : C.(Morphism) s d),
      GeneralizedMorphismsEquivalent (F.(MorphismOf) m) (G.(MorphismOf) m).
End FunctorsEquivalent.

Implicit Arguments FunctorsEquivalent [C D].

Section FunctorsEquivalenceReltation.
  Variable C D : Category.

  Hint Unfold FunctorsEquivalent GeneralizedMorphismsEquivalent.

  Lemma functors_equivalent_refl (F : Functor C D) : FunctorsEquivalent F F.
    repeat (autounfold with core in *); t.
  Qed.

  Lemma functors_equivalent_sym (F G : Functor C D) :
    FunctorsEquivalent F G -> FunctorsEquivalent G F.
    repeat (autounfold with core in *); t.
  Qed.

  Lemma functors_equivalent_trans (F G H : Functor C D) :
    FunctorsEquivalent F G -> FunctorsEquivalent G H -> FunctorsEquivalent F H.
    repeat (autounfold with core in *); intros.
    (* XXX ?GeneralizedRelationsEquivalent is a kludge *)
    match goal with
      [
        H0 : (forall _ _ _, ?GeneralizedRelationsEquivalent _ _ _ _ _ _),
        H1 : (forall _ _ _, ?GeneralizedRelationsEquivalent _ _ _ _ _ _)
        |- ?GeneralizedRelationsEquivalent _ _ _ _ _ _
      ] => apply (generalized_relations_equivalent_trans (H0 _ _ _) (H1 _ _ _)) ||
      apply (generalized_relations_equivalent_trans (H1 _ _ _) (H0 _ _ _))
    end.
  Qed.
End FunctorsEquivalenceReltation.

Add Parametric Relation (C D : Category) : _ (@FunctorsEquivalent C D)
  reflexivity proved by (functors_equivalent_refl _ _)
  symmetry proved by (functors_equivalent_sym _ _)
  transitivity proved by (functors_equivalent_trans _ _)
    as functors_equivalent.

Section FunctorComposition.
  Variable B C D E : Category.

  Hint Resolve FEquivalenceOf FCompositionOf FIdentityOf.

  (* XXX TODO: automate theis proof better so that we don't refer to [m1], [m2], or [o] explicitly *)
  Definition ComposeFunctors (G : Functor D E) (F : Functor C D) : Functor C E.
    refine {| ObjectOf := (fun c => G (F c));
      MorphismOf := (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
      |}; t.
    transitivity (MorphismOf G (Compose (MorphismOf F m2) (MorphismOf F m1))); t.
    transitivity (MorphismOf G (Identity (F o))); t.
  Defined.
End FunctorComposition.

Implicit Arguments ComposeFunctors [C D E].

(*
Add Parametric Morphism C D E :
  (@ComposeFunctors C D E)
  with signature (@FunctorsEquivalent _ _) ==> (@FunctorsEquivalent _ _) ==> (@FunctorsEquivalent _ _) as functor_eq_mor.
  intros.
  match goal with
    [
      H : FunctorsEquivalent ?a ?a',
      H' : FunctorsEquivalent ?b ?b'
      |- FunctorsEquivalent (ComposeFunctors ?a ?b) (ComposeFunctors ?a' ?b')
    ] => transitivity (ComposeFunctors a b')
  end; t.
  unfold FunctorsEquivalent; unfold GeneralizedMorphismsEquivalent. intros F G e F' G' e' s d m.
  specialize (e s d m).
  dependent destruction e.
  transitivity (F'.(MorphismOf) (F.(MorphismOf) m)).
  cbv delta.
  rewrite FCompositionOf.
  unfold ComposeFunctors MorphismOf.
  apply
  t.
  t. transitivity (ComposeFunctors x y0).
  unfold FunctorsNaturallyEquivalent in *.
  simpl in *.*)


Section Category.
  Variable C D : Category.

  (* There is an identity functor.  It does the obvious thing. *)
  Definition IdentityFunctor : Functor C C.
    refine {| ObjectOf := (fun x => x);
      MorphismOf := (fun _ _ x => x)
    |};
    abstract t.
  Defined.

  Lemma LeftIdentityFunctor (F : Functor D C) : FunctorsEquivalent (ComposeFunctors IdentityFunctor F) F.
    unfold IdentityFunctor; unfold FunctorsEquivalent; unfold GeneralizedMorphismsEquivalent; t.
  Qed.

  Lemma RightIdentityFunctor (F : Functor C D) : FunctorsEquivalent (ComposeFunctors F IdentityFunctor) F.
    unfold IdentityFunctor; unfold FunctorsEquivalent; unfold GeneralizedMorphismsEquivalent; t.
  Qed.
End Category.

Section FunctorCompositionLemmas.
  Variable B C D E : Category.

  Hint Unfold FunctorsEquivalent GeneralizedMorphismsEquivalent.
  Hint Resolve FEquivalenceOf FCompositionOf FIdentityOf.

  Lemma PreComposeFunctors (G : Functor D E) (F1 F2 : Functor C D) :
    FunctorsEquivalent F1 F2 -> FunctorsEquivalent (ComposeFunctors G F1) (ComposeFunctors G F2).
    admit.
    (*
    repeat ( autounfold with core in * ); t.
    match goal with
      | [ HT : Morphism _ ?s ?d, H : (forall s d (m : Morphism _ s d), _) |- _ ] => specialize (H s d HT)
    end.
    cut (
      GeneralizedRelationsEquivalent (MorphismsEquivalent E) (MorphismOf (ComposeFunctors G F1) m) (MorphismOf G (MorphismOf F1 m))
      /\
      GeneralizedRelationsEquivalent (MorphismsEquivalent E) (MorphismOf (ComposeFunctors G F2) m) (MorphismOf G (MorphismOf F1 m))
      ); split || destruct 1; t.
    inversion H; t.
    Print Ltac simpl_existT.
    match goal with
      | [ H : existT _ ?x _ = existT _ ?x _ |- _ ] =>
              let Hi := fresh H in
      pose proof (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H) as Hi; clear H
end.
    simpl_existTs in H6.
    dependent destruction H.
    dependent destruction x.
    autounfold with core in *.
    match goal with
      | [ H : @MorphismsEquivalent' _ _ _ ?m1 ?m2 |- _ ] => generalize (G.(FEquivalenceOf) H)
    end.
    Search (_ ~= _ -> _ = _).
    intro H'.
    Check JMeq_congr
    rewrite (JMeq_congr _ x) in H.
    match goal with
      [ H : ?a ~= ?b |- _ ] => cut (a = b)
    end.

    rewrite <- x.
    generalize (FEquivalenceOf G H).
    Check @JMeq_eq.
    rewrite (@JMeq_eq _ r2 (MorphismOf F2 m) x) in H.
    Search (_ ~= _ -> _ = _).
    rewrite x in H.
    Check @JMeq_eq.

(*    match goal with
      | [ |- ?Rel (MorphismOf (ComposeFunctors ?F ?G) ?m) ?H ] => cut (Rel ( *)
    apply generalized_relations_equivalent_trans.*)
  Qed.

  Lemma PostComposeFunctors (G1 G2 : Functor D E) (F : Functor C D) :
    FunctorsEquivalent G1 G2 -> FunctorsEquivalent (ComposeFunctors G1 F) (ComposeFunctors G2 F).
    admit.
  Qed.

  Lemma ComposeFunctorsAssociativity (F : Functor B C) (G : Functor C D) (H : Functor D E) :
    FunctorsEquivalent (ComposeFunctors (ComposeFunctors H G) F) (ComposeFunctors H (ComposeFunctors G F)).
    admit.
  Qed.
End FunctorCompositionLemmas.
