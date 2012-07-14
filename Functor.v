Require Import ProofIrrelevance JMeq.
Require Export Category.
Require Import Common FEqualDep StructureEquality.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

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
     **)
  Record Functor := {
    ObjectOf :> C -> D;
    MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d);
    FCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
      MorphismOf _ _ (Compose m2 m1) = Compose (MorphismOf _ _ m2) (MorphismOf _ _ m1);
    FIdentityOf : forall o, MorphismOf _ _ (Identity o) = Identity (ObjectOf o)
  }.
End Functor.

Implicit Arguments MorphismOf [C D s d].

Section Functors_Equal.
  Lemma Functors_Equal : forall C D (F G : Functor C D),
    ObjectOf F = ObjectOf G
    -> (ObjectOf F = ObjectOf G -> MorphismOf F == MorphismOf G)
    -> F = G.
    destruct F, G; simpl; intros; firstorder; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.

  Lemma Functors_JMeq : forall C D C' D' (F : Functor C D) (G : Functor C' D'),
    C = C'
    -> D = D'
    -> (C = C' -> D = D' -> ObjectOf F == ObjectOf G)
    -> (C = C' -> D = D' -> ObjectOf F == ObjectOf G -> MorphismOf F == MorphismOf G)
    -> F == G.
    intros; repeat subst; firstorder;
      destruct F, G; simpl in *; repeat subst;
        JMeq_eq;
        f_equal; apply proof_irrelevance.
  Qed.
End Functors_Equal.

Ltac functor_eq_step_with tac :=
  structures_eq_step_with_tac ltac:(apply Functors_Equal || apply Functors_JMeq) tac.

Ltac functor_eq_with tac := repeat functor_eq_step_with tac.

Ltac functor_eq_step := functor_eq_step_with idtac.
Ltac functor_eq := functor_eq_with idtac.

Section FunctorComposition.
  Variable B C D E : Category.

  Hint Rewrite FCompositionOf FIdentityOf.

  Definition ComposeFunctors (G : Functor D E) (F : Functor C D) : Functor C E.
    refine {| ObjectOf := (fun c => G (F c));
      MorphismOf := (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
      |}; abstract t.
  Defined.
End FunctorComposition.

Section Category.
  Variable C D : Category.

  (* There is an identity functor.  It does the obvious thing. *)
  Definition IdentityFunctor : Functor C C.
    refine {| ObjectOf := (fun x => x);
      MorphismOf := (fun _ _ x => x)
    |};
    abstract t.
  Defined.

  Hint Unfold ComposeFunctors IdentityFunctor ObjectOf MorphismOf.

  Lemma LeftIdentityFunctor (F : Functor D C) : ComposeFunctors IdentityFunctor F = F.
    functor_eq.
  Qed.

  Lemma RightIdentityFunctor (F : Functor C D) : ComposeFunctors F IdentityFunctor = F.
    functor_eq.
  Qed.
End Category.

Section FunctorCompositionLemmas.
  Variable B C D E : Category.

  Lemma ComposeFunctorsAssociativity (F : Functor B C) (G : Functor C D) (H : Functor D E) :
    ComposeFunctors (ComposeFunctors H G) F = ComposeFunctors H (ComposeFunctors G F).
    functor_eq.
  Qed.
End FunctorCompositionLemmas.
