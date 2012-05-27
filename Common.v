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
