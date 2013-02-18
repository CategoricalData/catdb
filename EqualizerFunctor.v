Require Export LimitFunctors Equalizer.

Set Implicit Arguments.

Generalizable All Variables.

Section Equalizer.
  Context `(C : @SpecializedCategory objC).

  Variable HasLimits : forall F : SpecializedFunctor EqualizerIndex C, Limit F.
  Variable HasColimits : forall F : SpecializedFunctor EqualizerIndex C, Colimit F.

  Polymorphic Definition EqualizerFunctor := LimitFunctor HasLimits.
  Polymorphic Definition CoequalizerFunctor := ColimitFunctor HasColimits.
End Equalizer.
