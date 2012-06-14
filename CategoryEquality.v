Require Import FunctionalExtensionality ProofIrrelevance JMeq.
Require Export Category.
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
    destruct A, B; simpl; intros; subst;
      repeat match goal with
               | [ H : _ == _ |- _ ] => apply JMeq_eq in H; subst
             end; f_equal; apply proof_irrelevance.
  Qed.

  Theorem functional_extensionality_dep_JMeq : forall {A} {B1 B2 : A -> Type},
    forall (f : forall x : A, B1 x) (g : forall x : A, B2 x),
      (forall x, B1 x = B2 x)
      -> (forall x, f x == g x) -> f == g.
    intros.
    assert (B1 = B2) by (extensionality x; auto); subst.
    assert (f = g) by (extensionality x; apply JMeq_eq; auto).
    subst; reflexivity.
  Qed.

  Theorem forall_extensionality_dep : forall {A}
    (f g : A -> Type),
    (forall x, f x = g x) -> (forall x, f x) = (forall x, g x).
    intros.
    replace f with g; auto.
    apply functional_extensionality_dep; auto.
  Qed.

End Categories_Equal.

Ltac JMeq_eq :=
  repeat match goal with
           | [ |- _ == _ ] => apply JMeq_eq
           | [ H : _ == _ |- _ ] => apply JMeq_eq in H
         end.

Ltac cat_eq_step_with tac := intros; simpl;
  match goal with
    | _ => reflexivity
    | [ |- @eq Category _ _ ] => apply Categories_Equal
    | [ |- (fun _ : ?A => _) == _ ] => apply (@functional_extensionality_dep_JMeq A); intro
    | [ |- (forall _ : ?A, _) = _ ] => apply (@forall_extensionality_dep A); intro
    | _ => tac
  end; repeat simpl; JMeq_eq.

Ltac cat_eq_with tac := repeat cat_eq_step_with tac.

Ltac cat_eq_step := cat_eq_step_with fail.
Ltac cat_eq := cat_eq_with fail.
