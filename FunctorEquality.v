Require Import FunctionalExtensionality ProofIrrelevance JMeq.
Require Export Functor.
Require Import Common FEqualDep.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

Section Functors_Equal.
  Lemma Functors_Equal : forall C D (F G : Functor C D),
    ObjectOf _ _ F = ObjectOf _ _ G
    -> (ObjectOf _ _ F = ObjectOf _ _ G -> MorphismOf F == MorphismOf G)
    -> F = G.
    destruct F, G; simpl; intros; firstorder; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.

End Functors_Equal.

Ltac functor_eq_step_with tac := intros; simpl;
  match goal with
    | _ => reflexivity
    | [ |- @eq (Functor _ _) _ _ ] => apply Functors_Equal
    | [ |- (fun _ : ?A => _) = _ ] => apply functional_extensionality_dep; intro
    | [ |- (fun _ : ?A => _) == _ ] => apply (@functional_extensionality_dep_JMeq A); intro
    | [ |- (forall _ : ?A, _) = _ ] => apply (@forall_extensionality_dep A); intro
    | _ => tac
  end; repeat simpl; JMeq_eq.

Ltac functor_eq_with tac := repeat functor_eq_step_with tac.

Ltac functor_eq_step := functor_eq_step_with idtac.
Ltac functor_eq := functor_eq_with idtac.
