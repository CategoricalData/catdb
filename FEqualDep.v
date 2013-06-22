Require Export FunctionalExtensionality JMeq.
Require Import Common Notations.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Section f_equal_dep.
  Theorem f_type_equal {A B A' B'} : A = A' -> B = B' -> (A -> B) = (A' -> B').
    intros; repeat subst; reflexivity.
  Qed.

  Theorem forall_extensionality_dep : forall {A}
    (f g : A -> Type),
    (forall x, f x = g x) -> (forall x, f x) = (forall x, g x).
    intros.
    replace f with g; auto.
    apply functional_extensionality_dep; auto.
  Qed.

  Theorem forall_extensionality_dep_JMeq : forall {A B}
    (f : A -> Type) (g : B -> Type),
    A = B -> (A = B -> forall x y, x == y -> f x == g y) -> (forall x, f x) = (forall x, g x).
    intros; firstorder; intuition; repeat subst.
    apply forall_extensionality_dep.
    intro.
    apply JMeq_eq.
    eauto.
  Qed.


  Lemma JMeq_eqT A B (x : A) (y : B) : x == y -> A = B.
    intro H; destruct H; reflexivity.
  Qed.

  Lemma fg_equal_JMeq A B B' (f : forall a : A, B a) (g : forall a : A, B' a) x :
    f == g -> (f == g -> B = B') -> f x == g x.
    intros.
    repeat (firstorder; repeat subst).
  Qed.

  Lemma f_equal_JMeq A A' B B' a b (f : forall a : A, A' a) (g : forall b : B, B' b) :
    f == g -> (f == g -> A' == B') -> (f == g -> a == b) -> f a == g b.
    intros.
    firstorder.
    repeat destruct_type @JMeq.
    repeat subst; reflexivity.
  Qed.

  Lemma f_equal1_JMeq A0 B a0 b0 (f : forall (a0 : A0), B a0) :
    a0 = b0
    -> f a0 == f b0.
    intros.
    repeat (firstorder; repeat subst).
  Qed.

  Lemma f_equal2_JMeq A0 A1 B a0 b0 a1 b1 (f : forall (a0 : A0) (a1 : A1 a0), B a0 a1) :
    a0 = b0
    -> (a0 = b0 -> a1 == b1)
    -> f a0 a1 == f b0 b1.
    intros.
    repeat (firstorder; repeat subst).
  Qed.

  Lemma f_equal3_JMeq A0 A1 A2 B a0 b0 a1 b1 a2 b2 (f : forall (a0 : A0) (a1 : A1 a0) (a2 : A2 a0 a1), B a0 a1 a2) :
    a0 = b0
    -> (a0 = b0 -> a1 == b1)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2)
    -> f a0 a1 a2 == f b0 b1 b2.
    intros.
    repeat (firstorder; repeat subst).
  Qed.

  Lemma f_equal4_JMeq A0 A1 A2 A3 B a0 b0 a1 b1 a2 b2 a3 b3 (f : forall (a0 : A0) (a1 : A1 a0) (a2 : A2 a0 a1) (a3 : A3 a0 a1 a2), B a0 a1 a2 a3) :
    a0 = b0
    -> (a0 = b0 -> a1 == b1)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2 -> a3 == b3)
    -> f a0 a1 a2 a3 == f b0 b1 b2 b3.
    intros.
    repeat (firstorder; repeat subst).
  Qed.

  Lemma f_equal5_JMeq A0 A1 A2 A3 A4 B a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 (f : forall (a0 : A0) (a1 : A1 a0) (a2 : A2 a0 a1) (a3 : A3 a0 a1 a2) (a4 : A4 a0 a1 a2 a3), B a0 a1 a2 a3 a4) :
    a0 = b0
    -> (a0 = b0 -> a1 == b1)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2 -> a3 == b3)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2 -> a3 == b3 -> a4 == b4)
    -> f a0 a1 a2 a3 a4 == f b0 b1 b2 b3 b4.
    intros.
    repeat (firstorder; repeat subst).
  Qed.

  Lemma eq_JMeq T (A B : T) : A = B -> A == B.
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

  Theorem functional_extensionality_dep_JMeq' : forall {A1 A2} {B1 : A1 -> Type} {B2 : A2 -> Type},
    forall (f : forall x : A1, B1 x) (g : forall x : A2, B2 x),
      A1 = A2
      -> (A1 = A2 -> forall x y, x == y -> B1 x = B2 y)
      -> (A1 = A2 -> forall x y, x == y -> f x == g y) -> f == g.
    intros.
    intuition; repeat subst.
    apply functional_extensionality_dep_JMeq; intros;
      intuition.
  Qed.
End f_equal_dep.

Inductive identity_dep (A : Type) (a : A) : forall B : Type, B -> Type :=
  identity_dep_refl : identity_dep a a.

Section f_identity_dep.
  Local Infix "~" := identity (at level 50).
  Local Infix "~~" := identity_dep (at level 50).
  Definition f_identity (A B : Type) (f : A -> B) (x y : A) (H : x ~ y) : f x ~ f y
    := match H in (_ ~ y0) return (f x ~ f y0) with
         | identity_refl => identity_refl (f x)
       end.

  Definition f_type_identity {A B A' B'} : A ~ A' -> B ~ B' -> (A -> B) ~ (A' -> B').
    intros; destruct_head identity; reflexivity.
  Defined.

  Axiom functional_extensionality_dep_identity : forall {A : Type} {B : A -> Type} (f g : forall x : A, B x),
                                                   (forall x : A, f x ~ g x) -> f ~ g.

  Axiom identity_dep_identity : forall A (x y : A), x ~~ y -> x ~ y.

  Definition functional_extensionality_identity {A B : Type} := fun (f g : A -> B) (H : forall x : A, f x ~ g x) => functional_extensionality_dep_identity f g H.

  Theorem forall_extensionality_dep_identity : forall {A}
                                                      (f g : A -> Type),
                                                 (forall x, f x ~ g x) -> (forall x, f x) ~ (forall x, g x).
    intros.
    cut (f ~ g); [ let H := fresh in intro H; destruct H; reflexivity | ].
    apply functional_extensionality_dep_identity; assumption.
  Qed.

  Theorem forall_extensionality_dep_identity_dep : forall {A B}
                                                          (f : A -> Type) (g : B -> Type),
                                                     A ~ B -> (A ~ B -> forall x y, x ~~ y -> f x ~~ g y) -> (forall x, f x) ~ (forall x, g x).
    intros; intuition; destruct_head identity.
    apply forall_extensionality_dep_identity.
    intro.
    apply identity_dep_identity.
    match goal with | [ H : _ |- _ ] => apply H; reflexivity end.
  Qed.

  Definition identity_dep_identityT A B (x : A) (y : B) : x ~~ y -> A ~ B
    := fun H => match H in (_ ~~ b) return _ with
                  | identity_dep_refl => identity_refl A
                end.
End f_identity_dep.

Ltac JMeq_eq :=
  repeat match goal with
           | [ |- _ == _ ] => apply eq_JMeq
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

Section misc.
  Lemma sig_JMeq A0 A1 B0 B1 (a : @sig A0 A1) (b : @sig B0 B1) : A1 == B1 -> proj1_sig a == proj1_sig b -> a == b.
    intros.
    destruct_sig.
    repeat destruct_type @JMeq.
    JMeq_eq; subst.
    JMeq_eq.
    simpl_eq.
    trivial.
  Qed.
End misc.
