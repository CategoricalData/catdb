Require Import ProofIrrelevance JMeq.
Require Export Category FEqualDep.
Require Import Common StructureEquality.

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

Ltac cat_eq_step_with tac := structures_eq_step_with Categories_Equal tac.

Ltac cat_eq_with tac := repeat cat_eq_step_with tac.

Ltac cat_eq_step := cat_eq_step_with idtac.
Ltac cat_eq := cat_eq_with idtac.
