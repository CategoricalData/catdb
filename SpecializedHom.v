Require Import FunctionalExtensionality.
Require Export SpecializedCategory SpecializedFunctor SpecializedDuals SpecializedSetCategory SpecializedProductCategory.
Require Import Common.

Set Implicit Arguments.

Local Infix "*" := ProductSpecializedCategory.

Section HomSpecializedFunctor.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Let COp := OppositeSpecializedCategory C.

  Section Covariant.
    Variable A : COp.

    Definition CovariantHomSpecializedFunctor : SpecializedFunctor C TypeCat.
      refine (Build_SpecializedFunctor C TypeCat
        (fun X : C => C.(Morphism) A X : TypeCat)
        (fun X Y f => (fun g : C.(Morphism) A X => Compose f g))
        _
        _
      );
      abstract (simpl; intros; repeat (apply functional_extensionality_dep; intro); t_with t').
    Defined.
  End Covariant.

  Section Contravariant.
    Variable B : C.

    Definition ContravariantHomSpecializedFunctor : SpecializedFunctor COp TypeCat.
      Transparent Morphism Object Compose Identity.
      refine (Build_SpecializedFunctor COp TypeCat
        (fun X : COp => COp.(Morphism) B X : TypeCat)
        (fun X Y (h : COp.(Morphism) X Y) => (fun g : COp.(Morphism) B X => Compose h g))
        _
        _
      );
      abstract (simpl; intros; repeat (apply functional_extensionality_dep; intro); t_with t').
    Defined.
  End Contravariant.

  Definition hom_functor_object_of (c'c : COp * C) := C.(Morphism) (fst c'c) (snd c'c) : TypeCat.

  Definition hom_functor_morphism_of (s's : (COp * C)%type) (d'd : (COp * C)%type) (hf : (COp * C).(Morphism) s's d'd) :
    TypeCat.(Morphism) (hom_functor_object_of s's) (hom_functor_object_of d'd).
    Transparent Morphism Object.
    unfold hom_functor_object_of in *.
    destruct s's as [ s' s ], d'd as [ d' d ].
    destruct hf as [ h f ].
    intro g.
    exact (Compose f (Compose g h)).
  Defined.

  Definition HomSpecializedFunctor : SpecializedFunctor (COp * C) TypeCat.
    Transparent Morphism Object Compose Identity.
    refine (Build_SpecializedFunctor (COp * C) TypeCat
      (fun c'c : COp * C => C.(Morphism) (fst c'c) (snd c'c) : TypeCat)
      (fun X Y (hf : (COp * C).(Morphism) X Y) => hom_functor_morphism_of hf)
      _
      _
    );
    abstract (
      unfold hom_functor_morphism_of, hom_functor_object_of in *; simpl in *;
        intros; subst COp; simpl in *; destruct_hypotheses; simpl in *;
          repeat (apply functional_extensionality_dep; intro); t_with t'
    ).
  Defined.
End HomSpecializedFunctor.
