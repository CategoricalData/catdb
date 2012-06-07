Require Import Setoid.
Require Import Common EquivalenceRelation.
Require Export Category.

Section ProductCategory.
  Variables C D : Category.

  Definition prod_object := ((@Object C) * (@Object D))%type.
  Definition prod_morphism (s d : prod_object) :=
    let (sc, sd) := s in
      let (dc, dd) := d in
        ((C.(Morphism) sc dc) * (D.(Morphism) sd dd))%type.
  Definition prod_identity (o : prod_object) : prod_morphism o o.
    destruct o as [oc od].
    exact (Identity oc, Identity od).
  Defined.
  Definition prod_compose (s d d' : prod_object) (m2 : prod_morphism d d') (m1 : prod_morphism s d) : prod_morphism s d'.
    destruct s as [sc sd], d as [dc dd], d' as [d'c d'd], m1 as [m1c m1d], m2 as [m2c m2d].
    exact (Compose m2c m1c, Compose m2d m1d).
  Defined.

  Ltac simpl_prod :=
    repeat (intros;
      unfold prod_object, prod_morphism, prod_identity, prod_compose in *;
        repeat match goal with
                 | [ H : prod _ _ |- _ ] => destruct H
               end;
        simpl
        ).

  Definition ProductCategory : Category.
    refine {| Object := prod_object;
      Morphism := prod_morphism;
      Identity := prod_identity;
      Compose := prod_compose
    |}; abstract (t; simpl_prod; t; etransitivity; eauto).
  Defined.
End ProductCategory.

Hint Unfold prod_object prod_morphism prod_identity prod_compose.
