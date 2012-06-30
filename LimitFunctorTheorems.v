Require Export LimitFunctors.
Require Import Common Category Functor FunctorCategory SmallCategory SmallNaturalTransformation DefinitionSimplification.

Set Implicit Arguments.

Local Notation "C ^ D" := (FunctorCategory D C).

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
  Variables C1 C2 : SmallCategory.
  Variable D : Category.
  Variable F1 : Functor C1 D.
  Variable F2 : Functor C2 D.
  Variable G : Functor C1 C2.

  Hypothesis TriangleCommutes : ComposeFunctors F2 G = F1.

  Section Limit.
    Hypothesis F1_HasLimit : FunctorHasLimit F1.
    Hypothesis F2_HasLimit : FunctorHasLimit F2.

    Let limF1 := projT1 F1_HasLimit.
    Let limF2 := projT1 F2_HasLimit.

    Definition InducedLimitMap' : Morphism D limF2 limF1.
      intro_projT2.
      unfold Limit in *.
      destruct_sig.
      specialize_all_ways.
      repeat match goal with
               | [ t : _, F : _ |- _ ] => unique_pose (SNTComposeF t (IdentitySmallNaturalTransformation F))
             end.
      simpl in *.
      repeat match goal with
               | [ H : _ |- _ ] => rewrite TriangleCommutes in H; autorewrite with core in H
             end.
      subst limF1 limF2.
      specialized_assumption destruct_sig.
    Defined.

    Definition InducedLimitMap'' : Morphism D limF2 limF1.
      simpl_definition_by_exact InducedLimitMap'.
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedLimitMap := Eval cbv beta iota zeta delta [InducedLimitMap''] in InducedLimitMap''.
  End Limit.

  Section Colimit.
    Hypothesis F1_HasColimit : FunctorHasColimit F1.
    Hypothesis F2_HasColimit : FunctorHasColimit F2.

    Let colimF1 := projT1 F1_HasColimit.
    Let colimF2 := projT1 F2_HasColimit.

    Definition InducedColimitMap' : Morphism D colimF1 colimF2.
      intro_projT2.
      unfold Colimit in *.
      destruct_sig.
      specialize_all_ways.
      repeat match goal with
               | [ t : _, F : _ |- _ ] => unique_pose (SNTComposeF t (IdentitySmallNaturalTransformation F))
             end.
      simpl in *.
      repeat match goal with
               | [ H : _ |- _ ] => rewrite TriangleCommutes in H; autorewrite with core in H
             end.
      subst colimF1 colimF2.
      specialized_assumption destruct_sig.
    Defined.

    Definition InducedColimitMap'' : Morphism D colimF1 colimF2.
      simpl_definition_by_exact InducedColimitMap'.
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedColimitMap := Eval cbv beta iota zeta delta [InducedColimitMap''] in InducedColimitMap''.
  End Colimit.
End InducedMaps.
