Require Export Limits.
Require Import Common DiscreteCategory DiscreteCategoryFunctors.

Set Implicit Arguments.

Generalizable All Variables.

Section Products.
  Context `{C : @SpecializedCategory objC morC}.
  Variable I : Type.
  Variable f : I -> C.

  Definition Product := Limit (InducedDiscreteFunctor C f).
  Definition Coproduct := Colimit (InducedDiscreteFunctor C f).
End Products.

Notation "∏_{ x } f" := (@Product _ _ _ _ (fun x => f)) (at level 0, x at level 99).
Notation "∏_{ x : A } f" := (@Product _ _ _ A (fun x : A => f)) (at level 0, x at level 99).
Notation "∐_{ x } f" := (@Coproduct _ _ _ _ (fun x => f)) (at level 0, x at level 99).
Notation "∐_{ x : A } f" := (@Coproduct _ _ _ A (fun x : A => f)) (at level 0, x at level 99).
