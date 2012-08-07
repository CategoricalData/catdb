Require Export SpecializedCategory.
Require Import Common DefinitionSimplification.

Ltac destruct_to_empty_set :=
  match goal with
    | [ H : Empty_set |- _ ] => destruct H
    | [ H : ?T -> Empty_set, a : ?T |- _ ] => destruct (H a)
    | [ H : context[Empty_set] |- _ ] => solve [ destruct H; trivial; assumption ]
  end.

Ltac destruct_to_empty_set_in_match :=
  match goal with
    | [ |- appcontext[match ?x with end] ] => solve [ destruct x || let H := fresh in pose x as H; destruct H ]
    | [ _ : appcontext[match ?x with end] |- _ ] => solve [ destruct x || let H := fresh in pose x as H; destruct H ]
  end.

Hint Extern 2 (_ = _) => simpl in *; tauto.

Section DCategory.
  Variable O : Type.

  Variable eq_dec : forall a b : O, {a = b} + {~a = b}.

  Local Notation "x == y" := (eq_dec x y) (at level 70, no associativity).
  Local Notation "x == y == z" := (orb (x == y) (y == z)) (at level 70, no associativity, y at next level).

  Local Ltac contradict_by_transitivity :=
    match goal with
      | [ H : ~ _ |- _ ] => solve [ contradict H; etransitivity; eauto ]
    end.

  Let DiscreteCategory_Morphism s d := if s == d then unit else Empty_set.

  Local Ltac simpl_eq_dec := subst_body; simpl in *; intros;
  (*    unfold eq_b in *;*)
    repeat match goal with
             | [ _ : context[eq_dec ?a ?b] |- _ ] => destruct (eq_dec a b); try contradict_by_transitivity
             | [ |- context[eq_dec ?a ?b] ] => destruct (eq_dec a b); try contradict_by_transitivity
           end;
      auto.

  Definition DiscreteCategory_Compose (s d d' : O) (m : DiscreteCategory_Morphism d d') (m' : DiscreteCategory_Morphism s d) :
    DiscreteCategory_Morphism s d'.
    simpl_eq_dec.
  Defined.

  Definition DiscreteCategory_Identity o : (fun s d : O => if s == d then unit else Empty_set) o o.
    simpl_eq_dec.
  Defined.

  Definition DiscreteCategory : @SpecializedCategory O (fun s d => match s == d return Set with left _ => unit | right _ => Empty_set end).
    refine {|
      Compose' := DiscreteCategory_Compose;
      Identity' := DiscreteCategory_Identity
    |};
    abstract (
      unfold DiscreteCategory_Compose, DiscreteCategory_Identity;
        simpl_eq_dec
    ).
  Defined.
End DCategory.

Hint Unfold DiscreteCategory_Compose DiscreteCategory_Identity.

Section InitialTerminal.
  Let decide_empty_equality (a b : Empty_set) : {a = b} + {~a = b} := match a with end.
  Let decide_unit_equality (a b : unit) : {a = b} + {~a = b} := left
                              match a with
                              | tt =>
                                  match b with
                                  | tt => eq_refl
                                  end
                              end.

  Definition InitialCategory : SmallSpecializedCategory _ :=
    Eval unfold DiscreteCategory in DiscreteCategory Empty_set decide_empty_equality.
  Definition TerminalCategory : SmallSpecializedCategory _ :=
    Eval unfold DiscreteCategory in DiscreteCategory unit decide_unit_equality.
End InitialTerminal.
