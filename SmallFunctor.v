Require Import FunctionalExtensionality ProofIrrelevance JMeq.
Require Export Category SmallCategory.
Require Import Common FEqualDep Functor.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

Section Functor.
  Variable C D : SmallCategory.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of categories is known as a functor. Namely, given
     categories [C] and [C'], a (covariant) functor [F : C -> C'] is a rule that assigns to
     each object [A] of [C] an object [F A] of [C'] and to each map [m : A -> B] of [C] a map
     [F m : F A -> F B] of [C'] preserving composition and identity; that is,
     (1) [F (m' ○ m) = (F m') ○ (F m)] for maps [m : A -> B] and [m' : B -> C] of [C], and
     (2) [F (id A) = id (F A)] for any object [A] of [C], where [id A] is the identity morphism of [A].
     **)
  Record SmallFunctor := {
    SObjectOf :> C -> D;
    SMorphismOf : forall s d, C.(SMorphism) s d -> D.(SMorphism) (SObjectOf s) (SObjectOf d);
    SFCompositionOf : forall s d d' (m1 : C.(SMorphism) s d) (m2: C.(SMorphism) d d'),
      SMorphismOf _ _ (SCompose m2 m1) = SCompose (SMorphismOf _ _ m2) (SMorphismOf _ _ m1);
    SFIdentityOf : forall o, SMorphismOf _ _ (SIdentity o) = SIdentity (SObjectOf o)
  }.
End Functor.

Implicit Arguments SMorphismOf [C D s d].

Section Small2Large.
  Variables C D : SmallCategory.
  Variable F : SmallFunctor C D.

  Hint Resolve SFCompositionOf SFIdentityOf.

  Definition SmallFunctor2Functor : Functor C D.
    refine {| ObjectOf := F.(SObjectOf) : C.(Object) -> D.(Object);
      MorphismOf := (@SMorphismOf _ _ F) : forall s d, C.(Morphism) _ _ -> D.(Morphism) (_ s) (_ d)
      |}; abstract (unfold smallcat2cat; simpl; auto).
  Defined.
End Small2Large.

Coercion SmallFunctor2Functor : SmallFunctor >-> Functor.

Section Small2LargeId.
  Variables C D : SmallCategory.
  Variable F F' : SmallFunctor C D.

  Lemma SmallFunctor2FunctorId :
    SmallFunctor2Functor F = SmallFunctor2Functor F' -> F = F'.
    intro H.
    assert (ObjectOf F = ObjectOf F') by (rewrite H; reflexivity).
    assert (MorphismOf F == MorphismOf F') by (rewrite H; reflexivity).
    destruct F, F'; simpl in *;
      repeat subst; f_equal; apply proof_irrelevance.
  Qed.
End Small2LargeId.

Hint Resolve SmallFunctor2FunctorId.

Ltac sfunctor_eq_step_with tac := try apply SmallFunctor2FunctorId;
  functor_eq_step_with ltac:(try apply SmallFunctor2FunctorId; tac).

Ltac sfunctor_eq_with tac := repeat sfunctor_eq_step_with tac.

Ltac sfunctor_eq_step := sfunctor_eq_step_with idtac.
Ltac sfunctor_eq := sfunctor_eq_with idtac.

Section FunctorComposition.
  Variable B C D E : SmallCategory.

  Hint Rewrite SFCompositionOf SFIdentityOf.

  Definition ComposeSmallFunctors (G : SmallFunctor D E) (F : SmallFunctor C D) : SmallFunctor C E.
    refine {| SObjectOf := (fun c => G (F c));
      SMorphismOf := (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
      |}; abstract t.
  Defined.
End FunctorComposition.

Section Category.
  Variable C D : SmallCategory.

  (* There is an identity functor.  It does the obvious thing. *)
  Definition IdentitySmallFunctor : SmallFunctor C C.
    refine {| SObjectOf := (fun x => x);
      SMorphismOf := (fun _ _ x => x)
    |};
    abstract t.
  Defined.

  Hint Unfold ComposeFunctors IdentityFunctor ObjectOf MorphismOf.

  Lemma LeftIdentitySmallFunctor (F : SmallFunctor D C) : ComposeSmallFunctors IdentitySmallFunctor F = F.
    sfunctor_eq.
  Qed.

  Lemma RightIdentitySmallFunctor (F : SmallFunctor C D) : ComposeSmallFunctors F IdentitySmallFunctor = F.
    sfunctor_eq.
  Qed.
End Category.

Section FunctorCompositionLemmas.
  Variable B C D E : SmallCategory.

  Lemma ComposeSmallFunctorsAssociativity (F : SmallFunctor B C) (G : SmallFunctor C D) (H : SmallFunctor D E) :
    ComposeSmallFunctors (ComposeSmallFunctors H G) F = ComposeSmallFunctors H (ComposeSmallFunctors G F).
    sfunctor_eq.
  Qed.
End FunctorCompositionLemmas.
