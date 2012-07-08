Require Export SpecializedCategory SpecializedFunctor SpecializedUniversalProperties.
Require Import Common SpecializedFunctorCategory SpecializedNaturalTransformation.

Set Implicit Arguments.

Local Notation "C ^ D" := (SpecializedFunctorCategory D C).

Section DiagonalSpecializedFunctor.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.

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
    refine {| ObjectOf' := fun _ => c;
      MorphismOf' := (fun _ _ _ => Identity c)
    |}; abstract t.
  Defined.

  Definition diagonal_functor_morphism_of o1 o2 : C.(Morphism) o1 o2 -> (C ^ D).(Morphism) (diagonal_functor_object_of o1) (diagonal_functor_object_of o2).
    simpl; unfold diagonal_functor_object_of; intro m.
    refine {| ComponentsOf' := fun d => m : C.(Morphism) ((diagonal_functor_object_of o1) d) ((diagonal_functor_object_of o2) d)
      |}; abstract t.
  Defined.

  Definition DiagonalSpecializedFunctor' : SpecializedFunctor C (C ^ D).
    Transparent Morphism.
    refine {| ObjectOf' := diagonal_functor_object_of;
      MorphismOf' := diagonal_functor_morphism_of
      |}; abstract spnt_eq.
  Defined.

  Definition DiagonalSpecializedFunctor := Eval cbv beta iota zeta delta [DiagonalSpecializedFunctor' diagonal_functor_object_of (*diagonal_functor_morphism_of*)] in DiagonalSpecializedFunctor'.
End DiagonalSpecializedFunctor.

Section DiagonalSpecializedFunctorLemmas.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable objD' : Type.
  Variable morD' : objD' -> objD' -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable D' : SpecializedCategory morD'.

  Lemma Compose_DiagonalSpecializedFunctor x (F : SpecializedFunctor D' D) :
    ComposeSpecializedFunctors (DiagonalSpecializedFunctor C D x) F = DiagonalSpecializedFunctor _ _ x.
    spfunctor_eq.
  Qed.
End DiagonalSpecializedFunctorLemmas.

Hint Rewrite Compose_DiagonalSpecializedFunctor.

Section Limit.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable F : SpecializedFunctor D C.

  (**
     Quoting Dwyer and Spalinski:

     Let [D] be a small category and [F : D -> C] a functor. A limit
     for [F] is an object [L] of [C] together with a natural transformation [t : Δ L -> F]
     such that for every object [X] of [C] and every natural transformation [s : Δ X -> F],
     there exists a unique map [s' : X -> L] in [C] such that [t (Δ s') = s].
     **)
  Definition Limit := TerminalMorphism (DiagonalSpecializedFunctor C D) F.
  (*  Definition Limit (L : C) :=
    { t : SmallSpecializedNaturalTransformation ((DiagonalSpecializedFunctor C D) L) F &
      forall X : C, forall s : SmallSpecializedNaturalTransformation ((DiagonalSpecializedFunctor C D) X) F,
        { s' : C.(Morphism) X L |
          unique
          (fun s' => SNTComposeT t ((DiagonalSpecializedFunctor C D).(MorphismOf) s') = s)
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
  Definition Colimit := @InitialMorphism _ _ _ _ (C ^ D) _ F (DiagonalSpecializedFunctor C D).
  (*  Definition Colimit (c : C) :=
    { t : SmallSpecializedNaturalTransformation F ((DiagonalSpecializedFunctor C D) c) &
      forall X : C, forall s : SmallSpecializedNaturalTransformation F ((DiagonalSpecializedFunctor C D) X),
        { s' : C.(Morphism) c X | is_unique s' /\
          SNTComposeT ((DiagonalSpecializedFunctor C D).(MorphismOf) s') t = s
        }
    }.*)

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
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable F : SpecializedFunctor D C.

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
