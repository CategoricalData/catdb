Require Export LimitFunctors Equalizer.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Equalizer.
  Context `(C : SpecializedCategory).

  Variable HasLimits : forall F : SpecializedFunctor EqualizerIndex C, Limit F.
  Variable HasColimits : forall F : SpecializedFunctor EqualizerIndex C, Colimit F.

  Definition EqualizerFunctor := LimitFunctor HasLimits.
  Definition CoequalizerFunctor := ColimitFunctor HasColimits.
End Equalizer.
