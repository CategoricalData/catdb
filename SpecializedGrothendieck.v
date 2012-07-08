Require Export SpecializedCategory SpecializedFunctor.
Require Import Common SpecializedSetCategory.

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

  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Variable F : SpecializedFunctor C TypeCat.

  Record GrothendiekPair := {
    GrothendiekC' : objC;
    GrothendiekX' : F GrothendiekC'
  }.

  Section GrothendiekInterface.
    Variable G : GrothendiekPair.

    Definition GrothendiekC : C := G.(GrothendiekC').
    Definition GrothendiekX : F GrothendiekC := G.(GrothendiekX').
  End GrothendiekInterface.

  Definition GrothendiekCompose cs xs cd xd cd' xd' :
    { f : C.(Morphism) cd cd' | F.(MorphismOf) f xd = xd' } -> { f : C.(Morphism) cs cd | F.(MorphismOf) f xs = xd } ->
    { f : C.(Morphism) cs cd' | F.(MorphismOf) f xs = xd' }.
    Transparent Compose.
    intros m2 m1.
    exists (Compose (proj1_sig m2) (proj1_sig m1)).
    abstract (
      destruct m1, m2;
        rewrite FCompositionOf;
          unfold TypeCat, Compose;
            t_rev_with t'
    ).
  Defined.

  Arguments GrothendiekCompose [cs xs cd xd cd' xd'] m2 m1.

  Definition GrothendiekIdentity c x : { f : C.(Morphism) c c | F.(MorphismOf) f x = x }.
    Transparent Identity.
    exists (Identity c).
    abstract (
      rewrite FIdentityOf;
        unfold TypeCat, Identity;
          reflexivity
    ).
  Defined.

  Hint Resolve Associativity LeftIdentity RightIdentity.
  Hint Extern 1 (exist _ _ _ = exist _ _ _) => simpl_exist.

  Definition CategoryOfElements : @SpecializedCategory
    GrothendiekPair
    (fun s d =>
      { f : C.(Morphism) (GrothendiekC s) (GrothendiekC d) | F.(MorphismOf) f (GrothendiekX s) = (GrothendiekX d) }).
    refine {|
      Compose' := (fun _ _ _ m1 m2 => GrothendiekCompose m1 m2);
      Identity' := (fun o => GrothendiekIdentity (GrothendiekC o) (GrothendiekX o))
    |};
    abstract (
      unfold GrothendiekC, GrothendiekX, GrothendiekCompose, GrothendiekIdentity in *;
        intros; destruct_type GrothendiekPair; destruct_sig; simpl_exist; eauto
    ).
  Defined.

  Definition GrothendieckFunctor : SpecializedFunctor CategoryOfElements C.
    refine {| ObjectOf' := (fun o : CategoryOfElements.(Object) => GrothendiekC o);
      MorphismOf' := (fun s d (m : CategoryOfElements.(Morphism) s d) => proj1_sig m)
    |}; abstract (eauto; intros; destruct_type CategoryOfElements; simpl; reflexivity).
  Defined.
End Grothendieck.
