Require Export SpecializedCategory.
Require Import Common.

Set Implicit Arguments.

Local Hint Extern 2 (_ = _) => simpl in *; tauto.

Section DCategoryDec.
  Variable O : Type.

  Variable eq_dec : forall a b : O, {a = b} + {~a = b}.

  Local Notation "x == y" := (eq_dec x y) (at level 70, no associativity).
  Local Notation "x == y == z" := (orb (x == y) (y == z)) (at level 70, no associativity, y at next level).

  Local Ltac contradict_by_transitivity :=
    match goal with
      | [ H : ~ _ |- _ ] => solve [ contradict H; etransitivity; eauto ]
    end.

  Let DiscreteCategoryDec_Morphism s d : Set := if s == d then unit else Empty_set.

  Local Ltac simpl_eq_dec := subst_body; simpl in *; intros;
  (*    unfold eq_b in *;*)
    repeat match goal with
             | [ _ : context[eq_dec ?a ?b] |- _ ] => destruct (eq_dec a b); try contradict_by_transitivity
             | [ |- context[eq_dec ?a ?b] ] => destruct (eq_dec a b); try contradict_by_transitivity
           end;
      auto.

  Definition DiscreteCategoryDec_Compose (s d d' : O) (m : DiscreteCategoryDec_Morphism d d') (m' : DiscreteCategoryDec_Morphism s d) :
    DiscreteCategoryDec_Morphism s d'.
    simpl_eq_dec.
  Defined.

  Definition DiscreteCategoryDec_Identity o : DiscreteCategoryDec_Morphism o o.
    simpl_eq_dec.
  Defined.

  Definition DiscreteCategoryDec : @SpecializedCategory O DiscreteCategoryDec_Morphism.
    refine {|
      Compose' := DiscreteCategoryDec_Compose;
      Identity' := DiscreteCategoryDec_Identity
    |};
    abstract (
      unfold DiscreteCategoryDec_Compose, DiscreteCategoryDec_Identity;
        simpl_eq_dec
    ).
  Defined.
End DCategoryDec.

Hint Unfold DiscreteCategoryDec_Compose DiscreteCategoryDec_Identity.
