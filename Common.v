Require Import Program.
Set Implicit Arguments.

Ltac t' := repeat progress (simpl; intros; try split; trivial).
Ltac t'_long := repeat progress (simpl; intuition).

Ltac t_with tac := tac;
  repeat (match goal with
            | [ H : context[@eq] |- _ ] => rewrite H
            | _ => progress autorewrite with core in *
          end; tac).

Ltac t_rev_with tac := tac;
  repeat (match goal with
            | [ H : context[@eq] |- _ ] => rewrite <- H
            | _ => progress autorewrite with core in *
          end; tac).

Ltac t := t_with t'; t_with t'_long.
Ltac t_rev := t_rev_with t'; t_rev_with t'_long.

Ltac simpl_transitivity :=
  try solve [ match goal with
                | [ _ : ?Rel ?a ?b, _ : ?Rel ?b ?c |- ?Rel ?a ?c ] => transitivity b; assumption
              end ].

Ltac eq2eq_refl :=
  repeat match goal with
           | [ H : _ = ?a |- _ ] => assert (H = eq_refl _) by (apply proof_irrelevance); subst
         end.

Ltac destruct_type T :=
  repeat match goal with
           | [ H : context[T] |- _ ] => destruct H
         end.

Ltac destruct_hypotheses :=
  repeat match goal with
           | [ H : ex _ |- _ ] => destruct H
           | [ H : and _ _ |- _ ] => destruct H
           | [ H : prod _ _ |- _ ] => destruct H
         end.

Ltac specialized_assumption tac := tac;
  match goal with
    | [ x : ?T, H : forall _ : ?T, _ |- _ ] => specialize (H x); specialized_assumption tac
    | _ => assumption
  end.

Ltac try_rewrite rew_H tac :=
  (repeat (rewrite rew_H); tac) ||
    (repeat (rewrite <- rew_H); tac).

Ltac simpl_exist :=
  match goal with
    | [ |- exist _ ?x1 ?p1 = exist _ ?x2 ?p2 ] => generalize p1; generalize p2; cut (x1 = x2);
      try solve [ let H := fresh in intro H; rewrite H; intros ? ?; apply f_equal; apply proof_irrelevance ]
  end.
