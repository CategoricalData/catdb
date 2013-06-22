Require Export LimitFunctors.
Require Import Common DefinitionSimplification SpecializedCategory Functor NaturalTransformation.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

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
  Context `(C1 : SpecializedCategory).
  Context `(C2 : SpecializedCategory).
  Context `(D : SpecializedCategory).
  Variable F1 : SpecializedFunctor C1 D.
  Variable F2 : SpecializedFunctor C2 D.
  Variable G : SpecializedFunctor C1 C2.

  Section Limit.
    Variable T : NaturalTransformation (ComposeFunctors F2 G) F1.

    Hypothesis F1_Limit : Limit F1.
    Hypothesis F2_Limit : Limit F2.

    Let limF1 := LimitObject F1_Limit.
    Let limF2 := LimitObject F2_Limit.

    Definition InducedLimitMapNT' : SpecializedNaturalTransformation ((DiagonalFunctor D C1) limF2) F1.
      unfold LimitObject, Limit in *;
        intro_universal_morphisms.
      subst limF1 limF2.
      match goal with
        | [ t : _, F : _, T : _ |- _ ] => eapply (NTComposeT (NTComposeT T (NTComposeF t (IdentityNaturalTransformation F))) _)
      end.
      Grab Existential Variables.
      unfold ComposeFunctors at 1.
      simpl.
      match goal with
        | [ |- SpecializedNaturalTransformation ?F ?G ] =>
          refine (Build_SpecializedNaturalTransformation F G
            (fun x => Identity _)
            _
          )
      end.
      simpl; reflexivity.
    Defined.

    Definition InducedLimitMapNT'' : SpecializedNaturalTransformation ((DiagonalFunctor D C1) limF2) F1.
      simpl_definition_by_exact InducedLimitMapNT'.
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedLimitMapNT : SpecializedNaturalTransformation ((DiagonalFunctor D C1) limF2) F1
      := Eval cbv beta iota zeta delta [InducedLimitMapNT''] in InducedLimitMapNT''.

    Definition InducedLimitMap : D.(Morphism) limF2 limF1
      := TerminalProperty_Morphism F1_Limit _ InducedLimitMapNT.
  End Limit.

  Section Colimit.
    Variable T : NaturalTransformation F1 (ComposeFunctors F2 G).

    Hypothesis F1_Colimit : Colimit F1.
    Hypothesis F2_Colimit : Colimit F2.

    Let colimF1 := ColimitObject F1_Colimit.
    Let colimF2 := ColimitObject F2_Colimit.

    Definition InducedColimitMapNT' : SpecializedNaturalTransformation F1 ((DiagonalFunctor D C1) colimF2).
      unfold ColimitObject, Colimit in *;
        intro_universal_morphisms.
      subst colimF1 colimF2.
      match goal with
        | [ t : _, F : _, T : _ |- _ ] => eapply (NTComposeT _ (NTComposeT (NTComposeF t (IdentityNaturalTransformation F)) T))
      end.
      Grab Existential Variables.
      unfold ComposeFunctors at 1.
      simpl.
      match goal with
        | [ |- SpecializedNaturalTransformation ?F ?G ] =>
          refine (Build_SpecializedNaturalTransformation F G
            (fun x => Identity _)
            _
          )
      end.
      simpl; reflexivity.
    Defined.

    Definition InducedColimitMapNT'' : SpecializedNaturalTransformation F1 ((DiagonalFunctor D C1) colimF2).
      simpl_definition_by_exact InducedColimitMapNT'.
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedColimitMapNT : SpecializedNaturalTransformation F1 ((DiagonalFunctor D C1) colimF2)
      := Eval cbv beta iota zeta delta [InducedColimitMapNT''] in InducedColimitMapNT''.

    Definition InducedColimitMap : Morphism D colimF1 colimF2
      := InitialProperty_Morphism F1_Colimit _ InducedColimitMapNT.
  End Colimit.
End InducedMaps.
