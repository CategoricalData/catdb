Require Import FunctionalExtensionality.
Require Export Category SetCategory DiscreteCategory CategoryIsomorphisms.
Require Import Common.

Set Implicit Arguments.

Section InitialTerminal.
  Hint Extern 1 (_ = _) => apply (@functional_extensionality_dep _); intro.
  Hint Extern 2 => destruct_to_empty_set.

  Local Ltac t := repeat (hnf in *; simpl in *; intros; try destruct_exists; try destruct_to_empty_set); auto.

  Definition TypeCatEmptyInitial : InitialObject (C := TypeCat) Empty_set. t. Defined.
  Definition TypeCatSingletonTerminal : TerminalObject (C := TypeCat) unit. t. Defined.
  Definition SetCatEmptyInitial : InitialObject (C := SetCat) Empty_set. t. Defined.
  Definition SetCatSingletonTerminal : TerminalObject (C := SetCat) unit. t. Defined.
End InitialTerminal.

Section EpiMono.
  Definition compose {A B C : Type} (f : B -> C) (g : A -> B) := (fun x => f (g x)).

  Variables S : Type.

  Local Ltac t' :=
    match goal with
      | _ => progress (intros; subst; trivial)
      | _ => eexists; reflexivity
      | _ => discriminate
      | [ H : _ -> False |- _ ] => contradict H; solve [ t' ]
      | [ H : ~_ |- _ ] => contradict H; solve [ t' ]
      | [ dec : forall _, {_} + {_} |- _ ] =>
        match goal with
          | [ _ : appcontext[dec ?x] |- _ ] => destruct (dec x)
          | [ |- appcontext[dec ?x] ] => destruct (dec x)
        end
      | _ => apply functional_extensionality_dep; intro
      | _ => progress (unfold compose in *; simpl in *; fg_equal)
      | _ => progress apply_hyp'
      | _ => progress destruct_type bool
      | [ H : (_ -> exists _, _), x : _ |- _ ] => destruct (H x); clear H
      | _ => progress specialize_uniquely
    end.

  Local Ltac t :=
    repeat match goal with
             | _ => t'
             | [ H : ?A -> _ |- _ ] =>
               match goal with
                 | [ _ : A |- _ ] => fail 1 (* don't make an [A] if we already have one *)
                 | _ => let a := fresh in assert (a : A) by (repeat t'); specialize (H a)
               end
           end.

  Lemma InjMono B (f : B -> S) :
    (forall x y : B, f x = f y -> x = y)
    -> (forall A (g g' : A -> B), (compose f g) = (compose f g') -> g = g').
  Proof.
    t.
  Qed.

  Lemma MonoInj B (f : B -> S) :
    (forall A (g g' : A -> B), (compose f g) = (compose f g') -> g = g')
    -> (forall x y : B, f x = f y -> x = y).
  Proof.
    intros H x y; t.
    pose proof (fun H' => H bool (fun b => if b then x else y) (fun _ => y) H' true).
    t.
  Qed.

  Lemma SurjEpi A (f : A -> S) :
    (forall x : S, exists y : A, f y = x)
    -> (forall C (g g' : S -> C), (compose g f) = (compose g' f) -> g = g').
  Proof.
    t.
  Qed.

  Lemma EpiSurj A (f : A -> S) (member_dec : forall x : S, {exists y, f y = x} + {~exists y, f y = x}) :
    (forall C (g g' : S -> C), (compose g f) = (compose g' f) -> g = g')
    -> (forall x : S, exists y : A, f y = x).
  Proof.
    intro H.
    assert (H' := fun H' => H bool (fun y => if member_dec y then true else false) (fun y => true) H').
    clear H.
    t.
  Qed.
End EpiMono.
