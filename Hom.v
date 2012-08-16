Require Import FunctionalExtensionality.
Require Export SpecializedCategory Functor Duals SetCategory ProductCategory.
Require Import Common.

Set Implicit Arguments.

Local Open Scope category_scope.

Section HomFunctor.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable morC' : objC -> objC -> Set.
  Variable C : SpecializedCategory morC.
  Variable C' : LocallySmallSpecializedCategory morC'.
  Let COp := OppositeCategory C.
  Let C'Op := OppositeCategory C' : LocallySmallSpecializedCategory _.

  Section Covariant.
    Variable A : COp.
    Variable A' : C'Op.

    Definition CovariantHomFunctor : SpecializedFunctor C TypeCat.
      refine (Build_SpecializedFunctor C TypeCat
        (fun X : C => C.(Morphism) A X : TypeCat)
        (fun X Y f => (fun g : C.(Morphism) A X => Compose f g))
        _
        _
      );
      abstract (simpl; intros; repeat (apply functional_extensionality_dep; intro); t_with t').
    Defined.

    Definition CovariantHomSetFunctor : SpecializedFunctor C' SetCat.
      refine (Build_SpecializedFunctor C' SetCat
        (fun X : C' => morC' A' X : SetCat)
        (fun X Y f => (fun g : C'.(Morphism) A' X => Compose f g))
        _
        _
      );
      abstract (simpl; intros; repeat (apply functional_extensionality_dep; intro); t_with t').
    Defined.
  End Covariant.

  Section Contravariant.
    Variable B : C.
    Variable B' : C'.

    Definition ContravariantHomFunctor : SpecializedFunctor COp TypeCat.
      refine (Build_SpecializedFunctor COp TypeCat
        (fun X : COp => COp.(Morphism) B X : TypeCat)
        (fun X Y (h : COp.(Morphism) X Y) => (fun g : COp.(Morphism) B X => Compose h g))
        _
        _
      );
      abstract (simpl; intros; repeat (apply functional_extensionality_dep; intro); t_with t').
    Defined.

    Definition ContravariantHomSetFunctor : SpecializedFunctor C'Op SetCat.
      clear morC C COp B.
      refine (Build_SpecializedFunctor C'Op SetCat
        (fun X : C'Op => morC' X B' : SetCat)
        (fun X Y (h : C'Op.(Morphism) X Y) => (fun g : C'Op.(Morphism) B' X => Compose h g))
        _
        _
      );
      abstract (simpl; intros; repeat (apply functional_extensionality_dep; intro); t_with t').
    Defined.
  End Contravariant.

  Definition hom_functor_object_of (c'c : COp * C) := C.(Morphism) (fst c'c) (snd c'c) : TypeCat.
  Definition hom_set_functor_object_of (c'c : C'Op * C') := morC' (fst c'c) (snd c'c) : SetCat.

  Definition hom_functor_morphism_of (s's : (COp * C)%type) (d'd : (COp * C)%type) (hf : (COp * C).(Morphism) s's d'd) :
    TypeCat.(Morphism) (hom_functor_object_of s's) (hom_functor_object_of d'd).
    unfold hom_functor_object_of in *.
    destruct s's as [ s' s ], d'd as [ d' d ].
    destruct hf as [ h f ].
    intro g.
    exact (Compose f (Compose g h)).
  Defined.

  Definition hom_set_functor_morphism_of (s's : (C'Op * C')%type) (d'd : (C'Op * C')%type) (hf : (C'Op * C').(Morphism) s's d'd) :
    SetCat.(Morphism) (hom_set_functor_object_of s's) (hom_set_functor_object_of d'd).
    unfold hom_set_functor_object_of in *.
    destruct s's as [ s' s ], d'd as [ d' d ].
    destruct hf as [ h f ].
    intro g.
    unfold LocallySmallSpecializedCategory in *.
    present_spcategory_all.
    exact (Compose f (Compose g h)).
  Defined.

  Definition HomFunctor : SpecializedFunctor (COp * C) TypeCat.
    refine (Build_SpecializedFunctor (COp * C) TypeCat
      (fun c'c : COp * C => C.(Morphism) (fst c'c) (snd c'c) : TypeCat)
      (fun X Y (hf : (COp * C).(Morphism) X Y) => hom_functor_morphism_of hf)
      _
      _
    );
    abstract (
      intros; simpl in *; destruct_hypotheses; simpl in *;
        repeat (apply functional_extensionality_dep; intro); t_with t'
    ).
  Defined.

  Definition HomSetFunctor : SpecializedFunctor (C'Op * C') SetCat.
    clear morC C COp.
    refine (Build_SpecializedFunctor (C'Op * C') SetCat
      (fun c'c : C'Op * C' => morC' (fst c'c) (snd c'c) : SetCat)
      (fun X Y (hf : (C'Op * C').(Morphism) X Y) => hom_set_functor_morphism_of hf)
      _
      _
    );
    abstract (
      intros; simpl in *; destruct_hypotheses; simpl in *;
        repeat (apply functional_extensionality_dep; intro); t_with t'
    ).
  Defined.
End HomFunctor.

Section SplitHomFunctor.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Let COp := OppositeCategory C.

  Lemma SplitHom (X Y : COp * C) : forall gh,
    @MorphismOf _ _ _ _ _ _ (HomFunctor C) X Y gh =
    (Compose
      (@MorphismOf _ _ _ _ _ _ (ContravariantHomFunctor C (snd Y)) (fst X) (fst Y) (fst gh))
      (@MorphismOf _ _ _ _ _ _ (CovariantHomFunctor C (fst X)) (snd X) (snd Y) (snd gh))).
  Proof.
    destruct X, Y.
    intro gh; destruct gh.
    simpl in *.
    apply functional_extensionality_dep; intro.
    autorewrite with core.
    reflexivity.
  Qed.

  Lemma SplitHom' (X Y : COp * C) : forall gh,
    @MorphismOf _ _ _ _ _ _ (HomFunctor C) X Y gh =
    (Compose
      (@MorphismOf _ _ _ _ _ _ (CovariantHomFunctor C (fst Y)) (snd X) (snd Y) (snd gh))
      (@MorphismOf _ _ _ _ _ _ (ContravariantHomFunctor C (snd X)) (fst X) (fst Y) (fst gh))).
  Proof.
    destruct X, Y.
    intro gh; destruct gh.
    simpl in *.
    apply functional_extensionality_dep; intro.
    autorewrite with core.
    reflexivity.
  Qed.
End SplitHomFunctor.
