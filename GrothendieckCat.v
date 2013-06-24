Require Export Category Functor ComputableCategory.
Require Import Common Notations NaturalTransformation.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Grothendieck.
  Context `(Index2Cat : forall i : Index, Category (Index2Object i)).
  Let Cat := @ComputableCategory _ Index2Object Index2Cat.

  Local Coercion Index2Cat : Index >-> Category.

  (**
     Quoting Wikipedia:
     The Grothendieck construction is an auxiliary construction used
     in the mathematical field of category theory.

     Let
     [F : C -> Set]
     be a functor from any small category to the category of sets.
     The Grothendieck construct for [F] is the category [Γ F] whose
     objects are pairs [(c, x)], where [c : C] is an
     object and [x : F c] is an element, and for which the set
     [Hom (Γ F) (c1, x1) (c2, x2)] is the set of morphisms
     [f : c1 -> c2] in [C] such that [F.(MorphismOf) f x1 = x2].
     *)
  Variable C : Category.
  Variable F : Functor C Cat.

  Record CatGrothendieckPair := {
    CatGrothendieckC' : C;
    CatGrothendieckX' : F CatGrothendieckC'
  }.

  Section GrothendieckInterface.
    Variable G : CatGrothendieckPair.

    Definition CatGrothendieckC : C := G.(CatGrothendieckC').
    Definition CatGrothendieckX : F CatGrothendieckC := G.(CatGrothendieckX').
  End GrothendieckInterface.

  Lemma CatGrothendieckPair_eta (x : CatGrothendieckPair) : Build_CatGrothendieckPair (CatGrothendieckC x) (CatGrothendieckX x) = x.
    destruct x; reflexivity.
  Qed.

  Definition CatGrothendieckCompose cs xs cd xd cd' xd' :
    { f : C.(Morphism) cd cd' & Morphism _ (F.(MorphismOf) f xd) xd' }
    -> { f : C.(Morphism) cs cd & Morphism _ (F.(MorphismOf) f xs) xd }
    -> { f : C.(Morphism) cs cd' & Morphism _ (F.(MorphismOf) f xs) xd' }.
    intros m2 m1.
    exists (Compose (projT1 m2) (projT1 m1)).
    refine (Compose (projT2 m2) _).
    rewrite FCompositionOf. (* ugh *)
    refine (MorphismOf (MorphismOf F (projT1 m2)) (projT2 m1)).
  Defined.

  Arguments CatGrothendieckCompose [cs xs cd xd cd' xd'] / _ _.

  Definition CatGrothendieckIdentity c x : { f : C.(Morphism) c c & Morphism _ (F.(MorphismOf) f x) x }.
    exists (Identity c).
    rewrite FIdentityOf.
    exact (Identity _).
  Defined.
(*
  Local Hint Extern 1 (@eq (sig _) _ _) => simpl_eq : category.
  Local Hint Extern 1 (@eq (sigT _) _ _) => simpl_eq : category.

  Definition CategoryOfCatElements : @Category CatGrothendieckPair.
    refine {|
        Morphism := (fun s d => _);
        Compose' := (fun _ _ _ m1 m2 => CatGrothendieckCompose m1 m2);
        Identity' := (fun o => CatGrothendieckIdentity (CatGrothendieckC o) (CatGrothendieckX o))
      |};
    repeat intro; hnf in *; expand;
    simpl_eq;
    destruct_sig;
    auto with category.
    Focus 3.
    unfold eq_rect_r.
    unfold eq_rect.
    unfold eq_sym.
    repeat match goal with
      | [ |- context[match ?E with _ => _ end] ] => (atomic E; fail 1) || let H := fresh in set (H := E)
    end.
        etransitivity.
        destruct
    Focus 2.
    rewrite FIdentityOf.
    destruct H0.

    simpl.
    repeat rewrite Associativity.
    repeat rewrite <- FCompositionOf.
    unfold eq_rect_r.
    unfold eq_sym.
    unfold eq_rect.
    destruct H0.
    destruct H.
    unfold
    destruct_head CatGrothendieckPair;
    simpl_eq.
    abstract (
        repeat intro; hnf in *; expand;
        destruct_head CatGrothendieckPair;
        destruct_sig;
        eauto with category
      ).
  Defined.

  Definition CatGrothendieckProjectionFunctor1 : Functor CategoryOfCatElements C.
    refine {|
        ObjectOf := (fun o : CategoryOfCatElements => CatGrothendieckC o);
        MorphismOf := (fun s d (m : CategoryOfCatElements.(Morphism) s d) => proj1_sig m)
      |};
    abstract (eauto with category; intros; simpl; reflexivity).
  Defined. *)
End Grothendieck.
