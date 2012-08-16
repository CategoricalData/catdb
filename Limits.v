Require Export SpecializedCategory Functor UniversalProperties.
Require Import Common FunctorCategory NaturalTransformation.

Set Implicit Arguments.

Local Notation "C ^ D" := (FunctorCategory D C).

Section DiagonalFunctor.
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
    hnf.
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun d => m : C.(Morphism) ((diagonal_functor_object_of o1) d) ((diagonal_functor_object_of o2) d))
          _
        )
    end;
    abstract t.
  Defined.

  Definition DiagonalFunctor' : SpecializedFunctor C (C ^ D).
    refine {| ObjectOf' := diagonal_functor_object_of;
      MorphismOf' := diagonal_functor_morphism_of
      |}; abstract nt_eq.
  Defined.

  Definition DiagonalFunctor := Eval cbv beta iota zeta delta [DiagonalFunctor' diagonal_functor_object_of (*diagonal_functor_morphism_of*)] in DiagonalFunctor'.
End DiagonalFunctor.

Section DiagonalFunctorLemmas.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable objD' : Type.
  Variable morD' : objD' -> objD' -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable D' : SpecializedCategory morD'.

  Lemma Compose_DiagonalFunctor x (F : SpecializedFunctor D' D) :
    ComposeFunctors (DiagonalFunctor C D x) F = DiagonalFunctor _ _ x.
    functor_eq.
  Qed.
End DiagonalFunctorLemmas.

Hint Rewrite Compose_DiagonalFunctor.

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
  Definition Limit := TerminalMorphism (DiagonalFunctor C D) F.
  (*  Definition Limit (L : C) :=
    { t : SmallSpecializedNaturalTransformation ((DiagonalFunctor C D) L) F &
      forall X : C, forall s : SmallSpecializedNaturalTransformation ((DiagonalFunctor C D) X) F,
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
  (*  Definition Colimit (c : C) :=
    { t : SmallSpecializedNaturalTransformation F ((DiagonalFunctor C D) c) &
      forall X : C, forall s : SmallSpecializedNaturalTransformation F ((DiagonalFunctor C D) X),
        { s' : C.(Morphism) c X | is_unique s' /\
          SNTComposeT ((DiagonalFunctor C D).(MorphismOf) s') t = s
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
