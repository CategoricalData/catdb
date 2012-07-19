Require Import Setoid ProofIrrelevance FunctionalExtensionality ClassicalDescription.
Require Export SetCategory DiscreteCategory EquivalenceSet EquivalenceClass Grothendieck EquivalenceRelationGenerator.
Require Import Common Limits Functor NaturalTransformation FunctorCategory.

Set Implicit Arguments.

Local Infix "*" := ProductCategory.
Local Notation "C ^ D" := (FunctorCategory D C).

Section InitialTerminal.
  Local Transparent Object Morphism.

  Hint Extern 1 (_ = _) => apply (@functional_extensionality_dep _); intro.

  Local Ltac t := repeat (hnf in *; simpl in *; intros; try destruct_exists; try destruct_to_empty_set); auto.

  Definition TypeCatEmptyInitial : @InitialObject _ _ TypeCat Empty_set. t. Defined.
  Definition TypeCatSingletonTerminal : @TerminalObject _ _ TypeCat unit. t. Defined.
  Definition SetCatEmptyInitial : @InitialObject _ _ SetCat Empty_set. t. Defined.
  Definition SetCatSingletonTerminal : @TerminalObject _ _ SetCat unit. t. Defined.
End InitialTerminal.


(*Require Import Common FunctionalExtensionality.
Set Implicit Arguments.


Section EpiMono.
  Definition compose {A B C : Type} (f : B -> C) (g : A -> B) := (fun x => f (g x)).

  Variables S : Type.
  Hypothesis eq_dec : forall a b : S, {a = b} + {a <> b}.

  Lemma MonoInj B (f : B -> S) :
    (forall A (g g' : A -> B), (compose f g) = (compose f g') -> g = g')
    -> (forall x y : B, f x = f y -> x = y).
    intros H x y fxfy.
    unfold compose in *; simpl in *; fg_equal.
    apply (fun H' => H bool (fun b => if b then x else y) (fun _ => y) H' true).
    apply functional_extensionality_dep.
    intro b; destruct b; trivial.
  Qed.

  Lemma EpiSurj A (f : A -> S) :
    (forall C (g g' : S -> C), (compose g f) = (compose g' f) -> g = g')
    -> (forall x : S, exists y : A, f y = x).
    intro H.
    assert (H' := fun x H' => H bool (fun y => if eq_dec x y then true else false) (fun y => true) H').
    clear H.
    unfold compose in *; simpl in *; fg_equal.

    let H'T := type of H' in cut (~~H'T).
    clear H'; intro H.
    contradict H
    cut (~(~H')).
    contradict H'.
    intro x.
    pose (H bool (fun y => if eq_dec_B x y then true else false) (fun y => true)); simpl in *.
    fg_equal.
*)
