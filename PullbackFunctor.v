Require Export LimitFunctors Pullback.

Set Implicit Arguments.

Generalizable All Variables.

Section Equalizer.
  Context `(C : @SpecializedCategory objC).

  Variable HasLimits : forall F : SpecializedFunctor PullbackIndex C, Limit F.
  Variable HasColimits : forall F : SpecializedFunctor PushoutIndex C, Colimit F.

  Polymorphic Definition PullbackFunctor := LimitFunctor HasLimits.
  Polymorphic Definition PushoutFunctor := ColimitFunctor HasColimits.
End Equalizer.
