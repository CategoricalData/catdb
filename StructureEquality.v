Require Import FunctionalExtensionality ProofIrrelevance JMeq.
Require Import Common FEqualDep.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

Ltac structures_eq_step_with structures_equal_lemma tac := intros; simpl;
  match goal with
    | _ => reflexivity
    | [ |- _ = _ ] => apply structures_equal_lemma
    | [ |- (fun _ : ?A => _) = _ ] => apply functional_extensionality_dep; intro
    | [ |- (fun _ : ?A => _) == _ ] => apply (@functional_extensionality_dep_JMeq A); intro
    | [ |- (forall _ : ?A, _) = _ ] => apply (@forall_extensionality_dep A); intro
    | _ => tac
  end; repeat simpl; JMeq_eq.
