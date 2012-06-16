Require Import FunctionalExtensionality ProofIrrelevance JMeq.
Require Export Category FEqualDep.
Require Import Common.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

Section Categories_Equal.
  Lemma Categories_Equal : forall (A B : Category),
    Object A = Object B
    -> Morphism A == Morphism B
    -> @Identity A == @Identity B
    -> @Compose A == @Compose B
    -> A = B.
    destruct A, B; simpl; intros; repeat subst;
      f_equal; reflexivity || apply proof_irrelevance.
  Qed.
End Categories_Equal.

Ltac cat_eq_step_with tac := intros; simpl;
  match goal with
    | _ => reflexivity
    | [ |- @eq Category _ _ ] => apply Categories_Equal
    | [ |- (fun _ : ?A => _) == _ ] => apply (@functional_extensionality_dep_JMeq A); intro
    | [ |- (fun _ : ?A => _) = _ ] => apply (@functional_extensionality_dep A); intro
    | [ |- (forall _ : ?A, _) = _ ] => apply (@forall_extensionality_dep A); intro
    | [ |- _ = _ ] => apply proof_irrelevance
    | _ => tac
  end; repeat simpl; JMeq_eq.

Ltac cat_eq_with tac := repeat cat_eq_step_with tac.

Ltac cat_eq_step := cat_eq_step_with idtac.
Ltac cat_eq := cat_eq_with idtac.
