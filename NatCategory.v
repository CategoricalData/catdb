Require Export SpecializedCategory DiscreteCategory.
Require Import Common.

Fixpoint CardinalityRepresentative (n : nat) : Type :=
  match n with
    | O => Empty_set
    | 1 => unit
    | S n' => (CardinalityRepresentative n' + unit)%type
  end.

Coercion CardinalityRepresentative : nat >-> Sortclass.

Definition NatCategory (n : nat) := Eval unfold DiscreteCategory, DiscreteCategory_Identity in DiscreteCategory n.

Coercion NatCategory : nat >-> SpecializedCategory.
