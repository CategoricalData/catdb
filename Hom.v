Require Import FunctionalExtensionality.
Require Export Category Functor Duals SetCategory ProductCategory.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

(*
   We could do covariant and contravariant as

Section covariant_contravariant.
  Local Arguments InducedProductSndFunctor / _ _ _ _ _ _ _ _ _ _ _.
  Definition CovariantHomFunctor (C : Category) (A : OppositeCategory C) :=
    Eval simpl in ((HomFunctor C) [ A, - ])%functor.
  Definition ContravariantHomFunctor (C : Category) (A : C) := ((HomFunctor C) [ -, A ])%functor.

  Definition CovariantHomSetFunctor `(C : @Category morC) (A : OppositeCategory C) := ((HomSetFunctor C) [ A, - ])%functor.
  Definition ContravariantHomSetFunctor `(C : @Category morC) (A : C) := ((HomSetFunctor C) [ -, A ])%functor.
End covariant_contravariant.

but that would introduce an extra identity morphism which some tactics
have a bit of trouble with.  *sigh*
*)

Section HomFunctor.
  Variable C : Category.
  Let COp := OppositeCategory C.

  Section Covariant.
    Variable A : COp.

    Definition CovariantHomFunctor : Functor C TypeCat.
      refine (Build_Functor C TypeCat
        (fun X : C => C.(Morphism) A X : TypeCat)
        (fun X Y f => (fun g : C.(Morphism) A X => Compose f g))
        _
        _
      );
      abstract (simpl; intros; repeat (apply functional_extensionality_dep; intro); auto with morphism).
    Defined.
  End Covariant.

  Section Contravariant.
    Variable B : C.

    Definition ContravariantHomFunctor : Functor COp TypeCat.
      refine (Build_Functor COp TypeCat
        (fun X : COp => COp.(Morphism) B X : TypeCat)
        (fun X Y (h : COp.(Morphism) X Y) => (fun g : COp.(Morphism) B X => Compose h g))
        _
        _
      );
      abstract (simpl; intros; repeat (apply functional_extensionality_dep; intro); auto with morphism).
    Defined.
  End Contravariant.

  Definition hom_functor_object_of (c'c : COp * C) := C.(Morphism) (fst c'c) (snd c'c) : TypeCat.

  Definition hom_functor_morphism_of (s's : (COp * C)%type) (d'd : (COp * C)%type) (hf : (COp * C).(Morphism) s's d'd) :
    TypeCat.(Morphism) (hom_functor_object_of s's) (hom_functor_object_of d'd).
    unfold hom_functor_object_of in *.
    destruct s's as [ s' s ], d'd as [ d' d ].
    destruct hf as [ h f ].
    intro g.
    exact (Compose f (Compose g h)).
  Defined.

  Definition HomFunctor : Functor (COp * C) TypeCat.
    refine (Build_Functor (COp * C) TypeCat
      (fun c'c : COp * C => C.(Morphism) (fst c'c) (snd c'c) : TypeCat)
      (fun X Y (hf : (COp * C).(Morphism) X Y) => hom_functor_morphism_of hf)
      _
      _
    );
    abstract (
        intros; simpl in *; destruct_hypotheses;
        simpl in *;
          repeat (apply functional_extensionality_dep; intro);
        autorewrite with morphism; reflexivity
      ).
  Defined.
End HomFunctor.

Section SplitHomFunctor.
  Variable C : Category.
  Let COp := OppositeCategory C.

  Lemma SplitHom (X Y : COp * C) : forall gh,
    MorphismOf (HomFunctor C) (s := X) (d := Y) gh =
    (Compose
      (MorphismOf (ContravariantHomFunctor C (snd Y)) (s := fst X) (d := fst Y) (fst gh))
      (MorphismOf (CovariantHomFunctor C (fst X)) (s := snd X) (d := snd Y) (snd gh))).
  Proof.
    destruct X, Y.
    intro gh; destruct gh.
    simpl in *.
    apply functional_extensionality_dep; intro.
    autorewrite with morphism.
    reflexivity.
  Qed.

  Lemma SplitHom' (X Y : COp * C) : forall gh,
    MorphismOf (HomFunctor C) (s := X) (d := Y) gh =
    (Compose
      (MorphismOf (CovariantHomFunctor C (fst Y)) (s := snd X) (d := snd Y) (snd gh))
      (MorphismOf (ContravariantHomFunctor C (snd X)) (s := fst X) (d := fst Y) (fst gh))).
  Proof.
    destruct X, Y.
    intro gh; destruct gh.
    simpl in *.
    apply functional_extensionality_dep; intro.
    autorewrite with morphism.
    reflexivity.
  Qed.
End SplitHomFunctor.
