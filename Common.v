Set Implicit Arguments.

Lemma witness_to_exists (A : Type) (P : A -> Prop) : { x | P x } -> (exists x, P x).
  intros.
  destruct X.
  exists x.
  assumption.
Qed.

Hint Resolve witness_to_exists.

Ltac t' := simpl; intuition.

Ltac t := t';
  repeat (match goal with
            | [ H : context[@eq] |- _ ] => rewrite H
            | _ => progress autorewrite with core in *
          end; t').
