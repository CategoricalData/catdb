Require Import Program.
Set Implicit Arguments.

Ltac t' := repeat progress (simpl; intuition).

Ltac t := t';
  repeat (match goal with
            | [ H : context[@eq] |- _ ] => rewrite H
            | _ => progress autorewrite with core in *
          end; t').

Ltac simpl_transitivity :=
  try solve [ match goal with
                | [ _ : ?Rel ?a ?b, _ : ?Rel ?b ?c |- ?Rel ?a ?c ] => transitivity b; assumption
              end ].

Ltac eq2eq_refl :=
  repeat match goal with
           | [ H : _ = ?a |- _ ] => assert (H = eq_refl _) by (apply proof_irrelevance); subst
         end.

Ltac destruct_hypotheses :=
  repeat match goal with
           | [ H : ex _ |- _ ] => destruct H
           | [ H : and _ _ |- _ ] => destruct H
         end.

Ltac try_rewrite rew_H tac :=
  (repeat (rewrite rew_H); tac) ||
    (repeat (rewrite <- rew_H); tac).
