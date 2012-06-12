Require Export Category Functor.
Require Import Common SetCategory.

Set Implicit Arguments.

Section Grothendieck.
  (**
     Quoting Wikipedia:
     The Grothendieck construction is an auxiliary construction used
     in the mathematical field of category theory.

     Let
     [F : C -> Set]
     be a functor from any small category to the category of sets.
     The Grothendieck construct for [F] is the category [Γ F] whose
     objects are pairs [(c, x)], where <math>c\in C</math> is an
     object and [x : F c] is an element, and for which the set
     [Hom (Γ F) (c1, x1) (c2, x2)] is the set of morphisms
     [f : c1 -> c2] in [C] such that [F.(MorphismOf) f x1 = x2].
     *)

  Variable C : Category.

  Variable F : Functor C TypeCat.

  Record GrothendiekPair := {
    GrothendiekC : C.(Object);
    GrothendiekX : F GrothendiekC
  }.

  Definition GrothendiekCompose cs xs cd xd cd' xd' :
    { f : C.(Morphism) cd cd' | F.(MorphismOf) f xd = xd' } -> { f : C.(Morphism) cs cd | F.(MorphismOf) f xs = xd } ->
    { f : C.(Morphism) cs cd' | F.(MorphismOf) f xs = xd' }.
    intros m2 m1; destruct m1 as [ f1 ], m2 as [ f2 ].
    exists (Compose f2 f1).
    rewrite FCompositionOf.
    unfold TypeCat, Compose.
    t_rev_with t'.
  Defined.

  Implicit Arguments GrothendiekCompose [cs xs cd xd cd' xd'].

  Definition GrothendiekIdentity c x : { f : C.(Morphism) c c | F.(MorphismOf) f x = x }.
    exists (Identity c).
    rewrite FIdentityOf.
    unfold TypeCat, Identity.
    reflexivity.
  Defined.

  Hint Resolve Associativity LeftIdentity RightIdentity.
  Hint Extern 1 (exist _ _ _ = exist _ _ _) => simpl_exist.

  Definition CategoryOfElements : Category.
    refine {| Object := GrothendiekPair;
      Morphism := (fun s d =>
        { f : C.(Morphism) (GrothendiekC s) (GrothendiekC d) | F.(MorphismOf) f (GrothendiekX s) = (GrothendiekX d) });
      Compose := (fun _ _ _ m1 m2 => GrothendiekCompose m1 m2);
      Identity := (fun o => GrothendiekIdentity (GrothendiekC o) (GrothendiekX o))
    |}; abstract (
      unfold GrothendiekC, GrothendiekX, GrothendiekCompose, GrothendiekIdentity in *;
        intros; destruct_type GrothendiekPair; destruct_type sig; eauto
    ).
  Defined.

  Definition GrothendieckFunctor : Functor CategoryOfElements C.
    refine {| ObjectOf := (fun o : CategoryOfElements.(Object) => GrothendiekC o);
      MorphismOf := (fun s d (m : CategoryOfElements.(Morphism) s d) => proj1_sig m)
    |}; eauto; intros; destruct_type CategoryOfElements; simpl; reflexivity.
  Defined.
End Grothendieck.
