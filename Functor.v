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

  Definition FunctorsEquivalent :=
    exists objOf,
      exists morOf1, exists morOf2,
        exists feq1, exists feq2,
          exists fco1, exists fco2,
            exists fid1, exists fid2,
              F = {| ObjectOf := objOf;
                MorphismOf := morOf1;
                FEquivalenceOf := feq1;
                FCompositionOf := fco1;
                FIdentityOf := fid1 |}
              /\ G = {| ObjectOf := objOf;
                MorphismOf := morOf2;
                FEquivalenceOf := feq2;
                FCompositionOf := fco2;
                FIdentityOf := fid2 |}
              /\ forall s d (m : C.(Morphism) s d),
                D.(MorphismsEquivalent) _ _ (morOf1 _ _ m) (morOf2 _ _ m).
End FunctorsEquivalent.

Implicit Arguments FunctorsEquivalent [C D].

Ltac functors_equivalent_destruct :=
  repeat match goal with
           | [ H : @sigT _ _ |- _ ] => destruct H
           | [ H : @sig _ _ |- _ ] => destruct H
           | [ H : @and _ _ |- _ ] => destruct H
           | [ H : ex _ |- _ ] => destruct H
         end.

Ltac start_functors_equivalent :=
  intros; repeat (functors_equivalent_destruct; repeat (autounfold with core in *)).

Ltac feq :=
  start_functors_equivalent;
  subst; repeat (match goal with
                   | [ H : Build_Functor _ _ _ _ _ _ _ = Build_Functor _ _ _ _ _ _ _ |- _ ] =>
                     injection H; clear H; intros
                   | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H
                 end; subst); simpl.

Hint Extern 1 (MorphismsEquivalent' _ _) => reflexivity.
Local Hint Extern 1 (MorphismsEquivalent' _ _) => symmetry.
Local Hint Extern 1 (MorphismsEquivalent' _ _) => etransitivity.

Section FunctorsEquivalenceReltation.
  Variable C D : Category.

  Hint Unfold FunctorsEquivalent.

  Lemma functors_equivalent_refl (F : Functor C D) : FunctorsEquivalent F F.
    destruct F; feq; eauto 15.
  Qed.

  Lemma functors_equivalent_sym (F G : Functor C D) :
    FunctorsEquivalent F G -> FunctorsEquivalent G F.
    feq; eauto 15.
  Qed.

  Lemma functors_equivalent_trans (F G H : Functor C D) :
    FunctorsEquivalent F G -> FunctorsEquivalent G H -> FunctorsEquivalent F H.
    start_functors_equivalent; feq; eauto 15.
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

  Definition ComposeFunctors (G : Functor D E) (F : Functor C D) : Functor C E.
    refine {| ObjectOf := (fun c => G (F c));
      MorphismOf := (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
      |}; abstract (t; etransitivity; eauto).
  Defined.
End FunctorComposition.

Implicit Arguments ComposeFunctors [C D E].

Hint Extern 1 (Build_Functor _ _ _ ?mo _ _ _ = Build_Functor _ _ _ ?mo' _ _ _) =>
  match mo with
    | mo' => fail 1
    | _ => let H := fresh in assert (H : mo = mo') by reflexivity; clear H
  end.

Add Parametric Morphism C D E :
  (@ComposeFunctors C D E)
  with signature (@FunctorsEquivalent _ _) ==> (@FunctorsEquivalent _ _) ==> (@FunctorsEquivalent _ _) as functor_eq_mor.
  unfold FunctorsEquivalent, ComposeFunctors; feq; eauto 20.
Qed.

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
    destruct F; unfold FunctorsEquivalent, ComposeFunctors; feq; eauto 15.
  Qed.

  Lemma RightIdentityFunctor (F : Functor C D) : FunctorsEquivalent (ComposeFunctors F IdentityFunctor) F.
    destruct F; unfold FunctorsEquivalent, ComposeFunctors; feq; eauto 15.
  Qed.
End Category.

Section FunctorCompositionLemmas.
  Variable B C D E : Category.

  Hint Unfold FunctorsEquivalent GeneralizedMorphismsEquivalent.
  Hint Resolve FEquivalenceOf FCompositionOf FIdentityOf.

  Hint Extern 1 (MorphismsEquivalent' _ _) => apply FEquivalenceOf.

  Lemma PreComposeFunctors (G : Functor D E) (F1 F2 : Functor C D) :
    FunctorsEquivalent F1 F2 -> FunctorsEquivalent (ComposeFunctors G F1) (ComposeFunctors G F2).
    unfold FunctorsEquivalent, ComposeFunctors; feq; eauto 20.
  Qed.

  Lemma PostComposeFunctors (G1 G2 : Functor D E) (F : Functor C D) :
    FunctorsEquivalent G1 G2 -> FunctorsEquivalent (ComposeFunctors G1 F) (ComposeFunctors G2 F).
    unfold FunctorsEquivalent, ComposeFunctors; feq; eauto 20.
  Qed.

  Lemma ComposeFunctorsAssociativity (F : Functor B C) (G : Functor C D) (H : Functor D E) :
    FunctorsEquivalent (ComposeFunctors (ComposeFunctors H G) F) (ComposeFunctors H (ComposeFunctors G F)).
    unfold FunctorsEquivalent, ComposeFunctors; feq; eauto 20.
  Qed.
End FunctorCompositionLemmas.
