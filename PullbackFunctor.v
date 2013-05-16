Require Export LimitFunctors Pullback.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Section Equalizer.
  Context `(C : @SpecializedCategory objC).

  Variable HasLimits : forall F : SpecializedFunctor PullbackIndex C, Limit F.
  Variable HasColimits : forall F : SpecializedFunctor PushoutIndex C, Colimit F.

  Definition PullbackFunctor := LimitFunctor HasLimits.
  Definition PushoutFunctor := ColimitFunctor HasColimits.
End Equalizer.
