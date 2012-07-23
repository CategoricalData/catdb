Require Export LimitFunctors.
Require Import Common DefinitionSimplification SpecializedCategory Functor FunctorCategory NaturalTransformation.

Set Implicit Arguments.

Section InducedMaps.
  (** Quoting David:
     Given a commutative triangle consisting of
     [[
            G
     C_1 -------> C_2
      \            /
       \          /
        \        /
     F_1 \      / F_2
         _\|  |/_
            D
     ]]
     there are induced maps in [D],
     [colim G : colim F_1 -> colim F_2]
     and
     [lim G : lim F_2 -> lim F_1]

     To get a feel for why this is true (and for the variance of colim
     vs. lim), imagine that [C_1] is the discrete category on 1 object,
     that [C_2] is the discrete category on 2 objects, that that [G]
     is one or the other inclusion, and that [D = Set]. Then [colim G]
     injects one set into its union with another and [lim G] projects a
     product of two sets onto one factor.
     *)
  Variable objC1 : Type.
  Variable morC1 : objC1 -> objC1 -> Type.
  Variable objC2 : Type.
  Variable morC2 : objC2 -> objC2 -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C1 : SpecializedCategory morC1.
  Variable C2 : SpecializedCategory morC2.
  Variable D : SpecializedCategory morD.
  Variable F1 : SpecializedFunctor C1 D.
  Variable F2 : SpecializedFunctor C2 D.
  Variable G : SpecializedFunctor C1 C2.

  Hypothesis TriangleCommutes : ComposeFunctors F2 G = F1.

  Section Limit.
    Hypothesis F1_Limit : Limit F1.
    Hypothesis F2_Limit : Limit F2.

    Let limF1 := LimitObject F1_Limit.
    Let limF2 := LimitObject F2_Limit.

    Definition InducedLimitMap' : D.(Morphism) limF2 limF1.
      Transparent Object Morphism.
      unfold LimitObject, Limit in *.
      intro_universal_morphisms.
      match goal with
        | [ t : _, F : _ |- _ ] => unique_pose (NTComposeF t (IdentityNaturalTransformation F))
      end.
      repeat match goal with
               | [ H : _ |- _ ] => rewrite TriangleCommutes in H; autorewrite with core in H
             end.
      intro_universal_property_morphisms.
      unfold Morphism in *; simpl in *.
      specialized_assumption idtac.
    Defined.

    Definition InducedLimitMap'' : Morphism D limF2 limF1.
      simpl_definition_by_exact InducedLimitMap'.
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedLimitMap := Eval cbv beta iota zeta delta [InducedLimitMap''] in InducedLimitMap''.
  End Limit.

  Section Colimit.
    Hypothesis F1_Colimit : Colimit F1.
    Hypothesis F2_Colimit : Colimit F2.

    Let colimF1 := ColimitObject F1_Colimit.
    Let colimF2 := ColimitObject F2_Colimit.

    Definition InducedColimitMap' : Morphism D colimF1 colimF2.
      Transparent Object Morphism.
      unfold ColimitObject, Colimit in *.
      intro_universal_morphisms.
      match goal with
        | [ t : _, F : _ |- _ ] => unique_pose (NTComposeF t (IdentityNaturalTransformation F))
      end.
      repeat match goal with
               | [ H : _ |- _ ] => rewrite TriangleCommutes in H; autorewrite with core in H
             end.
      intro_universal_property_morphisms.
      unfold Morphism in *; simpl in *.
      specialized_assumption idtac.
    Defined.

    Definition InducedColimitMap'' : Morphism D colimF1 colimF2.
      simpl_definition_by_exact InducedColimitMap'.
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedColimitMap := Eval cbv beta iota zeta delta [InducedColimitMap''] in InducedColimitMap''.
  End Colimit.
End InducedMaps.
