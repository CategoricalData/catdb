Require Export LimitFunctors Pullback.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Equalizer.
  Variable C : Category.

  Variable HasLimits : forall F : Functor PullbackIndex C, Limit F.
  Variable HasColimits : forall F : Functor PushoutIndex C, Colimit F.

  Definition PullbackFunctor := LimitFunctor HasLimits.
  Definition PushoutFunctor := ColimitFunctor HasColimits.
End Equalizer.
