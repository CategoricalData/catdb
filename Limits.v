Require Export Category Functor UniversalProperties.
Require Import Common FunctorCategory NaturalTransformation.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Section DiagonalFunctor.
  Variable C : Category.
  Variable D : Category.

  (**
     Quoting Dwyer and Spalinski:

     There is a diagonal or ``constant diagram'' functor
       Δ : C -> C^D,
     which carries an object [X : C] to the constant functor [Δ X : D -> C] (by definition,
     this ``constant functor'' sends each object of [D] to [X] and each morphism of [D]
     to [Identity X]). The functor Δ assigns to each morphism [f : X -> X'] of [C] the constant
     natural transformation [t(f) : Δ X -> Δ X'] determined by the formula [t(f) d = f] for
     each object [d] of [D].
     **)

  Definition diagonal_functor_object_of (c : C) : C ^ D.
    refine {| ObjectOf := fun _ => c;
      MorphismOf := (fun _ _ _ => Identity c)
    |}; abstract t.
  Defined.

  Definition diagonal_functor_morphism_of o1 o2 : C.(Morphism) o1 o2 -> (C ^ D).(Morphism) (diagonal_functor_object_of o1) (diagonal_functor_object_of o2).
    simpl; unfold diagonal_functor_object_of; intro m.
    hnf.
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun d => m : C.(Morphism) ((diagonal_functor_object_of o1) d) ((diagonal_functor_object_of o2) d))
          _
        )
    end;
      simpl; abstract (intros; autorewrite with morphism; trivial).
  Defined.

  Definition DiagonalFunctor' : Functor C (C ^ D).
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor C D
          diagonal_functor_object_of
          diagonal_functor_morphism_of
          _
          _
        )
    end;
    abstract nt_eq.
  Defined.

  Definition DiagonalFunctor := Eval cbv beta iota zeta delta [DiagonalFunctor' diagonal_functor_object_of (*diagonal_functor_morphism_of*)] in DiagonalFunctor'.
End DiagonalFunctor.

Section DiagonalFunctorLemmas.
  Variable C : Category.
  Variable D : Category.
  Variable D' : Category.

  Lemma Compose_DiagonalFunctor x (F : Functor D' D) :
    ComposeFunctors (DiagonalFunctor C D x) F = DiagonalFunctor _ _ x.
    functor_eq.
  Qed.

  Definition Compose_DiagonalFunctor_NT x (F : Functor D' D) :
    NaturalTransformation (ComposeFunctors (DiagonalFunctor C D x) F) (DiagonalFunctor _ _ x)
    := Build_NaturalTransformation (ComposeFunctors (DiagonalFunctor C D x) F)
                                              (DiagonalFunctor _ _ x)
                                              (fun z => Identity x)
                                              (fun _ _ _ => eq_refl).
End DiagonalFunctorLemmas.

Hint Rewrite @Compose_DiagonalFunctor.

Section Limit.
  Variable C : Category.
  Variable D : Category.
  Variable F : Functor D C.

  (**
     Quoting Dwyer and Spalinski:

     Let [D] be a small category and [F : D -> C] a functor. A limit
     for [F] is an object [L] of [C] together with a natural transformation [t : Δ L -> F]
     such that for every object [X] of [C] and every natural transformation [s : Δ X -> F],
     there exists a unique map [s' : X -> L] in [C] such that [t (Δ s') = s].
     **)
  Definition Limit := TerminalMorphism (DiagonalFunctor C D) F.
  Definition IsLimit := IsTerminalMorphism (U := DiagonalFunctor C D) (X := F).
  (*  Definition Limit (L : C) :=
    { t : SmallNaturalTransformation ((DiagonalFunctor C D) L) F &
      forall X : C, forall s : SmallNaturalTransformation ((DiagonalFunctor C D) X) F,
        { s' : C.(Morphism) X L |
          unique
          (fun s' => SNTComposeT t ((DiagonalFunctor C D).(MorphismOf) s') = s)
          s'
        }
    }.*)

  (**
     Quoting Dwyer and Spalinski:

     Let [D] be a small category and [F : D -> C] a functor. A colimit
     for [F] is an object [c] of [C] together with a natural transformation [t : F -> Δ c]
     such that for every object [X] of [C] and every natural transformation [s : F -> Δ X],
     there exists a unique map [s' : c -> X] in [C] such that [(Δ s') t = s].
     **)
  Definition Colimit := @InitialMorphism (C ^ D) _ F (DiagonalFunctor C D).
  Definition IsColimit := @IsInitialMorphism (C ^ D) _ F (DiagonalFunctor C D).
  (*  Definition Colimit (c : C) :=
    { t : SmallNaturalTransformation F ((DiagonalFunctor C D) c) &
      forall X : C, forall s : SmallNaturalTransformation F ((DiagonalFunctor C D) X),
        { s' : C.(Morphism) c X | is_unique s' /\
          SNTComposeT ((DiagonalFunctor C D).(MorphismOf) s') t = s
        }
    }.*)

  Section coercions.
    Definition Limit_IsLimit : forall o : Limit, IsLimit o
      := fun o => TerminalMorphism_IsTerminalMorphism o.
    Definition IsLimit_Limit : forall o, IsLimit o -> Limit
      := fun o H => IsTerminalMorphism_TerminalMorphism H.

    Global Coercion Limit_IsLimit : Limit >-> IsLimit.
    Global Coercion IsLimit_Limit : IsLimit >-> Limit.

    Definition Colimit_IsColimit : forall o : Colimit, IsColimit o
      := fun o => InitialMorphism_IsInitialMorphism o.
    Definition IsColimit_Colimit : forall o, IsColimit o -> Colimit
      := fun o H => IsInitialMorphism_InitialMorphism H.

    Global Coercion Colimit_IsColimit : Colimit >-> IsColimit.
    Global Coercion IsColimit_Colimit : IsColimit >-> Colimit.
  End coercions.

  Section AbstractionBarrier.
    Variable l : Limit.
    Variable c : Colimit.

    Definition LimitObject := TerminalMorphism_Object l.
    Definition LimitMorphism := TerminalMorphism_Morphism l.
    Definition LimitProperty_Morphism := TerminalProperty_Morphism l.
    Definition LimitProperty := TerminalProperty l.

    Definition ColimitObject := InitialMorphism_Object c.
    Definition ColimitMorphism := InitialMorphism_Morphism c.
    Definition ColimitProperty_Morphism := InitialProperty_Morphism c.
    Definition ColimitProperty := InitialProperty c.
  End AbstractionBarrier.
End Limit.

Section LimitMorphisms.
  Variable C : Category.
  Variable D : Category.
  Variable F : Functor D C.

  Definition MorphismBetweenLimits (L L' : Limit F) : C.(Morphism) (LimitObject L) (LimitObject L').
    unfold Limit, LimitObject in *.
    intro_universal_morphisms.
    intro_universal_property_morphisms.
    match goal with
      | [ |- Morphism _ ?a ?b ] => pose a; pose b
    end.
    specialized_assumption idtac.
  Defined.

  Definition MorphismBetweenColimits (c c' : Colimit F) : C.(Morphism) (ColimitObject c) (ColimitObject c').
    unfold Colimit, ColimitObject in *.
    intro_universal_morphisms.
    intro_universal_property_morphisms.
    match goal with
      | [ |- Morphism _ ?a ?b ] => pose a; pose b
    end.
    specialized_assumption idtac.
  Defined.
End LimitMorphisms.
