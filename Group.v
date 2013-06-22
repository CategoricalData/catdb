Require Import Notations.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Delimit Scope group_elements_scope with group.
Delimit Scope groups_scope with groups.

Section Group.
  Local Reserved Notation "'G'".
  Local Reserved Notation "1".

  Record Group :=
    {
      GroupObjects :> Type where "'G'" := GroupObjects;
      GroupIdentity : G where "1" := GroupIdentity;
      GroupOperation : G -> G -> G where "a * b" := (GroupOperation a b);
      GroupInverse : G -> G where "i ⁻¹" := (GroupInverse i);
      GroupLeftInverse : forall x, x ⁻¹ * x = 1;
      GroupRightInverse : forall x, x * x ⁻¹ = 1;
      GroupAssociativity : forall a b c, a * (b * c) = (a * b) * c;
      GroupLeftIdentity : forall x, 1 * x = x;
      GroupRightIdentity : forall x, x * 1 = x
    }.
End Group.

Bind Scope groups_scope with Group.
Bind Scope group_elements_scope with GroupObjects.

Arguments GroupOperation {g%groups} _%group _%group.
Arguments GroupIdentity {g%groups}.
Arguments GroupInverse {g%groups} _%group.

Notation "1" := (@GroupIdentity _) : group.
Infix "*" := (@GroupOperation _) : group.
Notation "i ⁻¹" := (@GroupInverse _ i) : group.
