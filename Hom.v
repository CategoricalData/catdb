Require Import Program.
Require Export Category Functor.
Require Import Common SmallCategory Duals SmallDuals ProductCategory SetCategory.

Set Implicit Arguments.

Local Infix "*" := ProductCategory.

Section HomFunctor.
  Variable C : Category.
  Variable C' : SmallCategory.
  Let COp := OppositeCategory C.
  Let COp' := OppositeSmallCategory C'.

  Section Covariant.
    Variable A : COp.

    Definition CovariantHomFunctor : Functor C TypeCat.
      refine {| ObjectOf := (fun X : C => Morphism C A X : TypeCat);
        MorphismOf := (fun X Y f => (fun g : Morphism C A X => Compose f g))
        |}; abstract (simpl; intros; repeat (apply functional_extensionality_dep; intro); t_with t').
    Defined.
  End Covariant.

  Section Contravariant.
    Variable B : C.

    Definition ContravariantHomFunctor : Functor COp TypeCat.
      refine {| ObjectOf := (fun X : COp => Morphism COp B X : TypeCat);
        MorphismOf := (fun X Y h => (fun g : Morphism COp B X => Compose h g))
        |}; abstract (simpl; intros; repeat (apply functional_extensionality_dep; intro); t_with t').
    Defined.
  End Contravariant.

  Section Contravariant'.
    Variable B : C'.

    Hint Resolve SAssociativity SRightIdentity SLeftIdentity.

    Definition SmallContravariantHomFunctor : Functor COp' TypeCat.
      refine {| ObjectOf := (fun X : COp'.(Object) => SMorphism COp' B X : TypeCat);
        MorphismOf := (fun X Y h => (fun g : SMorphism COp' B X => SCompose h g))
        |}; abstract (simpl; intros; repeat (apply functional_extensionality_dep; intro); auto).
    Defined.
  End Contravariant'.

  Definition hom_functor_object_of (c'c : Object (COp * C)) := Morphism C (fst c'c) (snd c'c) : TypeCat.

  Definition hom_functor_morphism_of (s's : (COp * C)%type) (d'd : (COp * C)%type) (hf : Morphism (COp * C) s's d'd) : Morphism _ (hom_functor_object_of s's) (hom_functor_object_of d'd).
    destruct s's as [ s' s ], d'd as [ d' d ].
    destruct hf as [ h f ].
    intro g.
    exact (Compose f (Compose g h)).
  Defined.

  Definition HomFunctor : Functor (COp * C) TypeCat.
    refine {| ObjectOf := (fun c'c : Object (COp * C) => Morphism C (fst c'c) (snd c'c) : TypeCat);
      MorphismOf := (fun X Y (hf : Morphism (COp * C) X Y) => hom_functor_morphism_of hf)
      |};
    abstract (
      unfold hom_functor_morphism_of, hom_functor_object_of in *; simpl in *;
        intros; subst COp; simpl in *; destruct_hypotheses; simpl in *;
          repeat (apply functional_extensionality_dep; intro); t_with t'
    ).
  Defined.
End HomFunctor.

Section SplitHomFunctor.
  Variable C : Category.
  Let COp := OppositeCategory C.

  Lemma SplitHom (X Y : C * C) : forall gh,
    @MorphismOf _ _ (HomFunctor C) X Y gh =
    (Compose
      (@MorphismOf _ _ (HomFunctor C) (fst X, snd Y) Y (fst gh, @Identity C _))
      (@MorphismOf _ _ (HomFunctor C) X (fst X, snd Y) (@Identity C _, snd gh))).
  Proof.
    destruct X, Y.
    intro gh; destruct gh.
    simpl in *.
    apply functional_extensionality_dep; intro.
    autorewrite with core.
    reflexivity.
  Qed.

  Lemma SplitHom' (X Y : C * C) : forall gh,
    @MorphismOf _ _ (HomFunctor C) X Y gh =
    (Compose
      (@MorphismOf _ _ (HomFunctor C) (fst Y, snd X) Y (@Identity C _, snd gh))
      (@MorphismOf _ _ (HomFunctor C) X (fst Y, snd X) (fst gh, @Identity C _))).
  Proof.
    destruct X, Y.
    intro gh; destruct gh.
    simpl in *.
    apply functional_extensionality_dep; intro.
    autorewrite with core.
    reflexivity.
  Qed.
End SplitHomFunctor.
