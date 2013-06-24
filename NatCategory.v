Require Export Category DiscreteCategory.
Require Import Common.

Polymorphic Fixpoint CardinalityRepresentative (n : nat) : Set :=
  match n with
    | O => Empty_set
    | 1 => unit
    | S n' => (CardinalityRepresentative n' + unit)%type
  end.

Coercion CardinalityRepresentative : nat >-> Sortclass.

Polymorphic Definition NatCategory (n : nat) := Eval unfold DiscreteCategory, DiscreteCategory_Identity in DiscreteCategory n.

Coercion NatCategory : nat >-> Category.
