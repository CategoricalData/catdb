Require Export Category Functor.
Require Import Common SetCategory.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

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
  Variable F' : Functor C SetCat.

  Record GrothendieckPair := {
    GrothendieckC' : C;
    GrothendieckX' : F GrothendieckC'
  }.

  Section GrothendieckInterface.
    Variable G : GrothendieckPair.

    Definition GrothendieckC : C := G.(GrothendieckC').
    Definition GrothendieckX : F GrothendieckC := G.(GrothendieckX').
  End GrothendieckInterface.

  Lemma GrothendieckPair_eta (x : GrothendieckPair) : Build_GrothendieckPair (GrothendieckC x) (GrothendieckX x) = x.
    destruct x; reflexivity.
  Qed.

  Record SetGrothendieckPair := {
    SetGrothendieckC' : C;
    SetGrothendieckX' : F' SetGrothendieckC'
  }.

  Section SetGrothendieckInterface.
    Variable G : SetGrothendieckPair.

    Definition SetGrothendieckC : C := G.(SetGrothendieckC').
    Definition SetGrothendieckX : F' SetGrothendieckC := G.(SetGrothendieckX').
  End SetGrothendieckInterface.

  Lemma SetGrothendieckPair_eta (x : SetGrothendieckPair) : Build_SetGrothendieckPair (SetGrothendieckC x) (SetGrothendieckX x) = x.
    destruct x; reflexivity.
  Qed.

  Definition GrothendieckCompose cs xs cd xd cd' xd' :
    { f : C.(Morphism) cd cd' | F.(MorphismOf) f xd = xd' } -> { f : C.(Morphism) cs cd | F.(MorphismOf) f xs = xd } ->
    { f : C.(Morphism) cs cd' | F.(MorphismOf) f xs = xd' }.
    intros m2 m1.
    exists (Compose (proj1_sig m2) (proj1_sig m1)).
    abstract (
      destruct m1, m2;
        rewrite FCompositionOf;
          unfold TypeCat, Compose;
            t_rev_with t'
    ).
  Defined.

  Arguments GrothendieckCompose [cs xs cd xd cd' xd'] / _ _.

  Definition GrothendieckIdentity c x : { f : C.(Morphism) c c | F.(MorphismOf) f x = x }.
    exists (Identity c).
    abstract (
      rewrite FIdentityOf;
        unfold TypeCat, Identity;
          reflexivity
    ).
  Defined.

  Hint Extern 1 (@eq (sig _) _ _) => simpl_eq : category.

  Definition CategoryOfElements : Category.
    refine (@Build_Category GrothendieckPair
                                       (fun s d =>
                                          { f : C.(Morphism) (GrothendieckC s) (GrothendieckC d) | F.(MorphismOf) f (GrothendieckX s) = (GrothendieckX d) })
                                       (fun o => GrothendieckIdentity (GrothendieckC o) (GrothendieckX o))
                                       (fun _ _ _ m1 m2 => GrothendieckCompose m1 m2)
                                       _
                                       _
                                       _);
    abstract (
        unfold GrothendieckC, GrothendieckX, GrothendieckCompose, GrothendieckIdentity in *;
        intros; destruct_type GrothendieckPair; destruct_sig; eauto with category
      ).
  Defined.

  Definition GrothendieckFunctor : Functor CategoryOfElements C.
    refine {| ObjectOf := (fun o : CategoryOfElements => GrothendieckC o);
      MorphismOf := (fun s d (m : CategoryOfElements.(Morphism) s d) => proj1_sig m)
    |}; abstract (eauto with category; intros; destruct_type CategoryOfElements; simpl; reflexivity).
  Defined.
End Grothendieck.

Section SetGrothendieckCoercion.
  Variable C : Category.
  Variable F : Functor C SetCat.
  Let F' := (F : FunctorToSet _) : FunctorToType _.

  Definition SetGrothendieck2Grothendieck (G : SetGrothendieckPair F) : GrothendieckPair F'
    := {| GrothendieckC' := G.(SetGrothendieckC'); GrothendieckX' := G.(SetGrothendieckX') : F' _ |}.
End SetGrothendieckCoercion.

Coercion SetGrothendieck2Grothendieck : SetGrothendieckPair >-> GrothendieckPair.
