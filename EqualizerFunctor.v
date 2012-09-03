Require Export LimitFunctors Equalizer.

Set Implicit Arguments.

Generalizable All Variables.

Section Equalizer.
  Context `(C : @SpecializedCategory objC).

  Variable HasLimits : forall F : SpecializedFunctor EqualizerIndex C, Limit F.
  Variable HasColimits : forall F : SpecializedFunctor EqualizerIndex C, Colimit F.

  Definition EqualizerFunctor := LimitFunctor HasLimits.
  Definition CoequalizerFunctor := ColimitFunctor HasColimits.
End Equalizer.
