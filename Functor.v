Require Import Setoid Coq.Program.Basics Program.
Require Export Category.

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
Implicit Arguments FCompositionOf [C D s d d' m1 m2].
Implicit Arguments FIdentityOf [C D].

Section FunctorComposition.
  Variable B C D E : Category.

  Hint Rewrite FCompositionOf FIdentityOf.

  Definition ComposeFunctors (G : Functor D E) (F : Functor C D) : Functor C E.
    refine {| ObjectOf := (fun c => G (F c));
      MorphismOf := (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
      |}; abstract (intros; autorewrite with core; reflexivity).
  Defined.
End FunctorComposition.

Implicit Arguments ComposeFunctors [C D E].

Ltac destruct_functors :=
  repeat match goal with
           | [ F : Functor _ _ |- _ ] => destruct F
         end.
Ltac feq_with_tac tac := autounfold with core in *;
  destruct_functors;
  repeat match goal with
           | [ |- Build_Functor _ _ ?oo ?mo ?co ?io = Build_Functor _ _ ?oo ?mo ?co' ?io' ] =>
             let H0 := fresh in
               let H1 := fresh in
                 assert (H0 : co = co') by (reflexivity || apply proof_irrelevance);
                   assert (H1 : io = io') by (reflexivity || apply proof_irrelevance);
                     rewrite H0, H1; reflexivity
           | [ |- Build_Functor _ _ ?oo ?mo ?co ?io = Build_Functor _ _ ?oo ?mo' ?co' ?io' ] => transitivity (Build_Functor _ _ oo mo co' io');
             repeat (apply f_equal); tac
           | [ |- Build_Functor _ _ ?oo ?mo ?co ?io = Build_Functor _ _ ?oo' ?mo' ?co' ?io' ] => transitivity (Build_Functor _ _ oo mo' co' io');
             repeat (apply f_equal); tac
         end.
Ltac feq := feq_with_tac ltac:(try reflexivity).

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
    feq.
  Qed.

  Lemma RightIdentityFunctor (F : Functor C D) : ComposeFunctors F IdentityFunctor = F.
    feq.
  Qed.
End Category.

Section FunctorCompositionLemmas.
  Variable B C D E : Category.

  Lemma ComposeFunctorsAssociativity (F : Functor B C) (G : Functor C D) (H : Functor D E) :
    ComposeFunctors (ComposeFunctors H G) F = ComposeFunctors H (ComposeFunctors G F).
    unfold ComposeFunctors; feq.
  Qed.
End FunctorCompositionLemmas.
