Require Export Limits.
Require Import Common Notations DiscreteCategory DiscreteCategoryFunctors.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Products.
  Context `{C : Category}.
  Variable I : Type.
  Variable f : I -> C.

  Definition Product := Limit (InducedDiscreteFunctor C f).
  Definition Coproduct := Colimit (InducedDiscreteFunctor C f).
End Products.

(* XXX: [Reserved Notation] doesn't work here? *)
Notation "∏_{ x } f" := (@Product _ _ (fun x => f)) (at level 0, x at level 99).
Notation "∏_{ x : A } f" := (@Product _ A (fun x : A => f)) (at level 0, x at level 99).
Notation "∐_{ x } f" := (@Coproduct _ _ (fun x => f)) (at level 0, x at level 99).
Notation "∐_{ x : A } f" := (@Coproduct _ A (fun x : A => f)) (at level 0, x at level 99).
