Require Export Limits.
Require Import Notations FunctorCategory Adjoint AdjointUniversalMorphisms.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Section LimitFunctors.
  Variable C : Category.
  Variable D : Category.

  Definition HasLimits' := forall F : Functor D C, exists _ : Limit F, True.
  Definition HasLimits := forall F : Functor D C, Limit F.

  Definition HasColimits' := forall F : Functor D C, exists _ : Colimit F, True.
  Definition HasColimits := forall F : Functor D C, Colimit F.

  Hypothesis HL : HasLimits.
  Hypothesis HC : HasColimits.

  Definition LimitFunctor : Functor (C ^ D) C
    := Eval unfold AdjointFunctorOfTerminalMorphism in AdjointFunctorOfTerminalMorphism (D := C ^ D) HL.
  Definition ColimitFunctor : Functor (C ^ D) C
    := Eval unfold AdjointFunctorOfInitialMorphism in AdjointFunctorOfInitialMorphism (C := C ^ D) HC.

  Definition LimitAdjunction : Adjunction (DiagonalFunctor C D) LimitFunctor
    := AdjunctionOfTerminalMorphism _.

  Definition ColimitAdjunction : Adjunction ColimitFunctor (DiagonalFunctor C D)
    := AdjunctionOfInitialMorphism _.
End LimitFunctors.
