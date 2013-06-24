Require Export LimitFunctors Equalizer.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Equalizer.
  Variable C : Category.

  Variable HasLimits : forall F : Functor EqualizerIndex C, Limit F.
  Variable HasColimits : forall F : Functor EqualizerIndex C, Colimit F.

  Definition EqualizerFunctor := LimitFunctor HasLimits.
  Definition CoequalizerFunctor := ColimitFunctor HasColimits.
End Equalizer.
