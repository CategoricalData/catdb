Require Import FunctionalExtensionality ProofIrrelevance JMeq.
Require Import Common Notations FEqualDep.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Ltac structures_eq_simpl_step_with tac := intros; simpl in *;
  match goal with
    | _ => reflexivity
    | [ |- (fun _ : ?A => _) = _ ] => apply functional_extensionality_dep; intro
    | [ |- (fun _ : ?A => _) == _ ] => apply (@functional_extensionality_dep_JMeq A); intro
    | [ |- (forall _ : ?A, _) = _ ] => apply (@forall_extensionality_dep A); intro
    | _ => tac
  end; simpl; JMeq_eq.

Ltac structures_eq_step_with_tac structures_equal_tac tac := intros; simpl in *;
  match goal with
    | _ => reflexivity
    | [ |- _ = _ ] => expand; structures_equal_tac
    | [ |- _ == _ ] => expand; structures_equal_tac
    | _ => structures_eq_simpl_step_with tac
  end.

Ltac structures_eq_step_with structures_equal_lemma tac := structures_eq_step_with_tac ltac:(apply structures_equal_lemma) tac.
