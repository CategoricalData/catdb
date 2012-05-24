Require Import Setoid Coq.Program.Basics.
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

Add Parametric Morphism C D s d F :
  (@MorphismOf C D F s d)
    with signature (MorphismsEquivalent C _ _) ==> (MorphismsEquivalent D _ _) as functor_morphism_eq_mor.
  intros; apply FEquivalenceOf; assumption.
Qed.

Section FunctorComposition.
  Variable C D E : Category.

  Hint Resolve FEquivalenceOf FCompositionOf FIdentityOf.

  (* this can probably be better automated *)
  Definition ComposeFunctor (F : Functor C D) (G : Functor D E) : Functor C E.
    refine {| ObjectOf := (fun c => G (F c));
      MorphismOf := (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
      |}; t.
    transitivity (MorphismOf G (Compose (MorphismOf F m2) (MorphismOf F m1))); t.
    transitivity (MorphismOf G (Identity (F o))); t.
  Defined.
End FunctorComposition.

Section Category.
  Variable C : Category.

  (* There is an identity functor.  It does the obvious thing. *)
  Definition IdentityFunctor : Functor C C.
    refine {| ObjectOf := (fun x => x);
      MorphismOf := (fun _ _ x => x)
    |};
    t.
  Defined.

End Category.
