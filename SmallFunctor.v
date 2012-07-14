Require Import ProofIrrelevance JMeq.
Require Export Category SmallCategory Functor.
Require Import Common FEqualDep StructureEquality.

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

Arguments SMorphismOf [C D] s [s0 d] _.

Section SmallFunctors_Equal.
  Lemma SmallFunctors_Equal : forall C D (F G : SmallFunctor C D),
    @SObjectOf _ _ F = @SObjectOf _ _ G
    -> (@SObjectOf _ _ F = @SObjectOf _ _ G -> @SMorphismOf _ _ F == @SMorphismOf _ _ G)
    -> F = G.
    destruct F, G; simpl; intros; firstorder; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.

  Lemma SmallFunctors_JMeq : forall C D C' D' (F : SmallFunctor C D) (G : SmallFunctor C' D'),
    C = C'
    -> D = D'
    -> (C = C' -> D = D' -> @SObjectOf _ _ F == @SObjectOf _ _ G)
    -> (C = C' -> D = D' -> @SObjectOf _ _ F == @SObjectOf _ _ G -> @SMorphismOf _ _ F == @SMorphismOf _ _ G)
    -> F == G.
    intros; repeat subst; firstorder;
      destruct F, G; simpl in *; repeat subst;
        JMeq_eq;
        f_equal; apply proof_irrelevance.
  Qed.
End SmallFunctors_Equal.

Ltac sfunctor_eq_step_with tac := structures_eq_step_with_tac ltac:(apply SmallFunctors_Equal || apply SmallFunctors_JMeq) tac.

Ltac sfunctor_eq_with tac := repeat sfunctor_eq_step_with tac.

Ltac sfunctor_eq_step := sfunctor_eq_step_with idtac.
Ltac sfunctor_eq := sfunctor_eq_with idtac.

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

Section Large2Small.
  Definition FunctorOnSmall {C D : SmallCategory} := Functor C D.

  Variables C D : SmallCategory.
  Variable F : @FunctorOnSmall C D.

  Definition Functor2SmallFunctor : SmallFunctor C D.
    refine {| SObjectOf := F.(ObjectOf) : C.(SObject) -> D.(SObject);
      SMorphismOf := (@MorphismOf _ _ F) : forall s d, C.(SMorphism) _ _ -> D.(SMorphism) (_ s) (_ d)
      |}; abstract (intros; simpl; destruct C, D, F; simpl in *; t_with t').
  Defined.
End Large2Small.

Coercion SmallFunctor2Functor : SmallFunctor >-> Functor.
Identity Coercion FunctorOnSmall_Functor_Id : FunctorOnSmall >-> Functor.
Coercion Functor2SmallFunctor : FunctorOnSmall >-> SmallFunctor.

Section Small2Large2Small_RoundTrip.
  Variables C D : SmallCategory.
  Variable F : SmallFunctor C D.
  Variable F' : Functor C D.

  Lemma SmallFunctor2Functor2SmallFunctorId : Functor2SmallFunctor (SmallFunctor2Functor F) = F.
    sfunctor_eq.
  Qed.

  Lemma Functor2SmallFunctor2FunctorId : SmallFunctor2Functor (Functor2SmallFunctor F') = F'.
    functor_eq.
  Qed.
End Small2Large2Small_RoundTrip.

Hint Rewrite SmallFunctor2Functor2SmallFunctorId Functor2SmallFunctor2FunctorId.
Hint Resolve Functor2SmallFunctor SmallFunctor2Functor.

Definition ComposeSmallFunctors C D E (G : SmallFunctor D E) (F : SmallFunctor C D) : SmallFunctor C E
  := ComposeFunctors G F : FunctorOnSmall.
Definition IdentitySmallFunctor C : SmallFunctor C C := IdentityFunctor C : FunctorOnSmall.

Lemma LeftIdentitySmallFunctor C D (F : SmallFunctor C D) : ComposeSmallFunctors (IdentitySmallFunctor _) F = F.
  sfunctor_eq.
Qed.

Lemma RightIdentitySmallFunctor C D (F : SmallFunctor C D) : ComposeSmallFunctors F (IdentitySmallFunctor _) = F.
  sfunctor_eq.
Qed.

Lemma ComposeFunctorsAssociativity B C D E (F : SmallFunctor B C) (G : SmallFunctor C D) (H : SmallFunctor D E) :
  ComposeSmallFunctors (ComposeSmallFunctors H G) F = ComposeSmallFunctors H (ComposeSmallFunctors G F).
  sfunctor_eq.
Qed.

Hint Unfold ComposeSmallFunctors IdentitySmallFunctor.
Hint Rewrite LeftIdentitySmallFunctor RightIdentitySmallFunctor.
