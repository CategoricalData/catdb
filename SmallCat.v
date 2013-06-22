Require Import FunctionalExtensionality JMeq ProofIrrelevance.
Require Export Category CategoryIsomorphisms InitialTerminalCategory Functor ComputableCategory.
Require Import Common FEqualDep.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section SmallCat.
  Definition SmallCat := ComputableCategory SUnderlyingCategory.
  Definition LocallySmallCat := ComputableCategory LSUnderlyingCategory.
End SmallCat.

Local Ltac destruct_simple_types :=
  repeat match goal with
           | [ |- context[?T] ] => let T' := type of T in
                                   let T'' := fresh in
                                   match eval hnf in T' with
                                     | unit => set (T'' := T); destruct T''
                                     | _ = _ => set (T'' := T); destruct T''
                                   end
         end.

Section Objects.
  Hint Unfold Morphism Object.

  Local Arguments Object / C : rename.
  Local Arguments Morphism / _ _ _ : rename.

  Hint Extern 1 => destruct_simple_types.
  Hint Extern 3 => destruct_to_empty_set.

  Lemma TerminalCategory_Terminal : IsTerminalObject (C := SmallCat) TerminalCategory.
    repeat intro;
    exists (FunctorToTerminal _).
    abstract (
        repeat intro; functor_eq; eauto
      ).
  Defined.

  Lemma InitialCategory_Initial : IsInitialObject (C := SmallCat) InitialCategory.
    repeat intro;
    exists (FunctorFromInitial _).
    abstract (
        repeat intro; functor_eq; eauto
      ).
  Qed.
End Objects.
