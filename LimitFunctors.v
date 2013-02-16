Require Export Limits.
Require Import Notations FunctorCategory Adjoint AdjointUniversalMorphisms.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope category_scope.

Section LimitFunctors.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Definition HasLimits' := forall F : SpecializedFunctor D C, exists _ : Limit F, True.
  Definition HasLimits := forall F : SpecializedFunctor D C, Limit F.

  Definition HasColimits' := forall F : SpecializedFunctor D C, exists _ : Colimit F, True.
  Definition HasColimits := forall F : SpecializedFunctor D C, Colimit F.

  Hypothesis HL : HasLimits.
  Hypothesis HC : HasColimits.

  Definition LimitFunctor : SpecializedFunctor (C ^ D) C
    := Eval unfold AdjointFunctorOfTerminalMorphism in AdjointFunctorOfTerminalMorphism HL.
  Definition ColimitFunctor : SpecializedFunctor (C ^ D) C
    := Eval unfold AdjointFunctorOfInitialMorphism in AdjointFunctorOfInitialMorphism HC.

  Definition LimitAdjunction : Adjunction (DiagonalFunctor C D) LimitFunctor
    := AdjunctionOfTerminalMorphism _.

  Definition ColimitAdjunction : Adjunction ColimitFunctor (DiagonalFunctor C D)
    := AdjunctionOfInitialMorphism _.
End LimitFunctors.
