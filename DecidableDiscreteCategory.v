Require Export Category.
Require Import Common Notations.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Hint Extern 2 (_ = _) => simpl in *; tauto.

Section DCategoryDec.
  Variable O : Type.

  Variable eq_dec : forall a b : O, {a = b} + {~a = b}.

  Local Infix "==" := eq_dec.
  Local Notation "x == y == z" := (orb (x == y) (y == z)).

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

  Definition DiscreteCategoryDec : Category.
    refine (@Build_Category O
                                       DiscreteCategoryDec_Morphism
                                       DiscreteCategoryDec_Identity
                                       DiscreteCategoryDec_Compose
                                       _
                                       _
                                       _);
    abstract (
        unfold DiscreteCategoryDec_Compose, DiscreteCategoryDec_Identity;
        simpl_eq_dec
      ).
  Defined.
End DCategoryDec.

Hint Unfold DiscreteCategoryDec_Compose DiscreteCategoryDec_Identity.
