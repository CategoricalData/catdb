Require Export SpecializedCategory.
Require Import Common DiscreteCategory.

Fixpoint CardinalityRepresentative (n : nat) : Type :=
  match n with
    | O => Empty_set
    | 1 => unit
    | S n' => (CardinalityRepresentative n' + unit)%type
  end.

Coercion CardinalityRepresentative : nat >-> Sortclass.

Definition NatCategory (n : nat) := DiscreteCategory n.

Coercion NatCategory : nat >-> SpecializedCategory.
