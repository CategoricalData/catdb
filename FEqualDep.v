Require Import FunctionalExtensionality JMeq.
Require Import Common.
Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

Section f_equal_dep.
  Lemma f_equal_JMeq A A' B B' a b (f : forall a : A, A' a) (g : forall b : B, B' b) :
    f == g -> (f == g -> A == B) -> (f == g -> A == B -> A' == B') -> (f == g -> A == B -> a == b) -> f a == g b.
    intros.
    repeat (firstorder; repeat subst).
  Qed.

  Lemma eq_implies_JMeq T (A B : T) : A = B -> A == B.
    intro; subst; reflexivity.
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
End f_equal_dep.

Ltac JMeq_eq :=
  repeat match goal with
           | [ |- _ == _ ] => apply eq_implies_JMeq
           | [ H : _ == _ |- _ ] => apply JMeq_eq in H
         end.

Ltac f_equal_dep_cleanup := JMeq_eq; eta_red.

Ltac f_equal_dep' := intros; f_equal; simpl in *;
  match goal with
    | [ |- ?f ?a == ?g ?b ] => apply (@f_equal_JMeq _ _ _ _ a b f g); intros; try reflexivity; repeat subst; intros;
      match goal with
        | [ |- f == g ] => f_equal_dep'
        | [ |- ?x == ?y ] => f_equal_dep_cleanup; try reflexivity
        | _ => idtac
      end
  end; f_equal_dep_cleanup.

Ltac f_equal_dep := intros; f_equal; simpl in *;
  repeat match goal with
           | [ |- ?f ?a = ?g ?b ] => apply JMeq_eq; f_equal_dep'
           | [ |- ?f ?a == ?g ?b ] => f_equal_dep'
           | _ => try reflexivity
         end; f_equal_dep_cleanup.
