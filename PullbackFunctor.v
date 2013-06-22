Require Export LimitFunctors Pullback.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Equalizer.
  Context `(C : SpecializedCategory).

  Variable HasLimits : forall F : SpecializedFunctor PullbackIndex C, Limit F.
  Variable HasColimits : forall F : SpecializedFunctor PushoutIndex C, Colimit F.

  Definition PullbackFunctor := LimitFunctor HasLimits.
  Definition PushoutFunctor := ColimitFunctor HasColimits.
End Equalizer.
