Require Import FunctionalExtensionality.
Require Export SpecializedCategory Functor Duals SetCategory ProductCategory.
Require Import Common.

Set Implicit Arguments.

Local Infix "*" := ProductCategory.

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
        (fun X Y (f : C.(Morphism) X Y) => (fun g : C.(Morphism) A X => Compose f g))
        _
        _
      );
      abstract (simpl; intros; present_spfunctor; repeat (apply functional_extensionality_dep; intro); t_with t').
    Defined.

    Definition CovariantHomSetFunctor : SpecializedFunctor C' SetCat.
      refine (Build_SpecializedFunctor C' SetCat
        (fun X : C' => morC' A' X : SetCat)
        (fun X Y (f : C'.(Morphism) X Y) => (fun g : C'.(Morphism) A' X => Compose f g))
        _
        _
      );
      abstract (simpl; intros; present_spfunctor; repeat (apply functional_extensionality_dep; intro); t_with t').
    Defined.
  End Covariant.

  Section Contravariant.
    Variable B : C.
    Variable B' : C'.

    (* TODO: Figure out a better way to do this proof *)
    Definition ContravariantHomFunctor : SpecializedFunctor COp TypeCat.
      clear morC' C' C'Op B'.
      refine (Build_SpecializedFunctor COp TypeCat
        (fun X : COp => COp.(Morphism) B X : TypeCat)
        (fun (X Y : COp) (h : COp.(Morphism) X Y) => (fun g : COp.(Morphism) B X => Compose h g))
        _
        _
      );
      abstract (
        subst COp; destruct C; clear C;
          unfold OppositeCategory, Compose; simpl in *;
            intros;
              repeat (apply functional_extensionality_dep; intro); simpl in *;
                auto
      ).
    Defined.

    Definition ContravariantHomSetFunctor : SpecializedFunctor C'Op SetCat.
      clear morC C COp B.
      refine (Build_SpecializedFunctor C'Op SetCat
        (fun X : C'Op => morC' X B' : SetCat)
        (fun X Y (h : C'Op.(Morphism) X Y) => (fun g : C'Op.(Morphism) B' X => Compose h g))
        _
        _
      );
      abstract (
        subst C'Op; destruct C'; clear C';
          unfold OppositeCategory, Compose; simpl in *;
            intros;
              repeat (apply functional_extensionality_dep; intro); simpl in *;
                auto
      ).
    Defined.
  End Contravariant.

  Definition hom_functor_object_of (c'c : COp * C) := C.(Morphism) (fst c'c) (snd c'c) : TypeCat.
  Definition hom_set_functor_object_of (c'c : C'Op * C') := morC' (fst c'c) (snd c'c) : SetCat.

  Definition hom_functor_morphism_of (s's : (COp * C)%type) (d'd : (COp * C)%type) (hf : (COp * C).(Morphism) s's d'd) :
    TypeCat.(Morphism) (hom_functor_object_of s's) (hom_functor_object_of d'd).
    Transparent Morphism Object.
    unfold hom_functor_object_of in *.
    destruct s's as [ s' s ], d'd as [ d' d ].
    destruct hf as [ h f ].
    intro g.
    exact (Compose (C := C) f (Compose g h)).
  Defined.

  Definition hom_set_functor_morphism_of (s's : (C'Op * C')%type) (d'd : (C'Op * C')%type) (hf : (C'Op * C').(Morphism) s's d'd) :
    SetCat.(Morphism) (hom_set_functor_object_of s's) (hom_set_functor_object_of d'd).
    Transparent Morphism Object.
    unfold hom_set_functor_object_of in *.
    destruct s's as [ s' s ], d'd as [ d' d ].
    destruct hf as [ h f ].
    intro g.
    unfold LocallySmallSpecializedCategory in *.
    exact (Compose (C := C') f (Compose (C := C') g h)).
  Defined.

  Definition HomFunctor : SpecializedFunctor (COp * C) TypeCat.
    Transparent Morphism Object Compose Identity.
    refine (Build_SpecializedFunctor (COp * C) TypeCat
      (fun c'c : COp * C => C.(Morphism) (fst c'c) (snd c'c) : TypeCat)
      (fun X Y (hf : (COp * C).(Morphism) X Y) => hom_functor_morphism_of hf)
      _
      _
    );
    abstract (
      intros; simpl in *; destruct_hypotheses; subst COp; simpl in *; destruct C; simpl in *;
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
      intros; simpl in *; destruct_hypotheses; subst C'Op; simpl in *; destruct C'; simpl in *;
        repeat (apply functional_extensionality_dep; intro); t_with t'
    ).
  Defined.
End HomFunctor.

Section SplitHomFunctor.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Let COp := OppositeCategory C.

  Lemma SplitHom (X Y : C * C) : forall gh,
    @MorphismOf' _ _ _ _ _ _ (HomFunctor C) X Y gh =
    (Compose' _ _ _ _
      (@MorphismOf' _ _ _ _ _ _ (HomFunctor C) (fst X, snd Y) Y (fst gh, @Identity' _ _ C _))
      (@MorphismOf' _ _ _ _ _ _ (HomFunctor C) X (fst X, snd Y) (@Identity' _ _ C _, snd gh))).
  Proof.
    Transparent Object Morphism Identity Compose ObjectOf MorphismOf.
    destruct X, Y.
    intro gh; destruct gh.
    simpl in *.
    apply functional_extensionality_dep; intro.
    autorewrite with core.
    reflexivity.
  Qed.

  Lemma SplitHom' (X Y : C * C) : forall gh,
    @MorphismOf _ _ _ _ _ _ (HomFunctor C) X Y gh =
    (Compose
      (@MorphismOf _ _ _ _ _ _ (HomFunctor C) (fst Y, snd X) Y (@Identity _ _ C _, snd gh))
      (@MorphismOf _ _ _ _ _ _ (HomFunctor C) X (fst Y, snd X) (fst gh, @Identity _ _ C _))).
  Proof.
    Transparent Object Morphism Identity Compose ObjectOf MorphismOf.
    destruct X, Y.
    intro gh; destruct gh.
    simpl in *.
    apply functional_extensionality_dep; intro.
    autorewrite with core.
    reflexivity.
  Qed.
End SplitHomFunctor.
