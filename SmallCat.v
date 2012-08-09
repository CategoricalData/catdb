Require Import FunctionalExtensionality JMeq ProofIrrelevance.
Require Export Category DiscreteCategory Functor ComputableCategory.
Require Import Common FEqualDep.

Set Implicit Arguments.

Section SmallCat.
  Definition SmallCat := ComputableCategory _ _ SUnderlyingCategory.
  Definition LocallySmallCat := ComputableCategory _ _ LSUnderlyingCategory.
End SmallCat.

Section Objects.
  Local Transparent Object Morphism.

  Hint Unfold Morphism Object.

  Local Arguments Object / {obj mor} C : rename.
  Local Arguments Morphism / {obj mor} _ _ _.

  Hint Extern 1 (_ = _) => apply functional_extensionality_dep; intro.
  Hint Extern 1 (_ = _) => apply forall_extensionality_dep; intro.
  Hint Extern 1 (JMeq _ _) => apply (@functional_extensionality_dep_JMeq _); intros.
  Hint Extern 1 => subst; simpl in *.
  Hint Extern 1 => apply proof_irrelevance.
  Hint Extern 3 => destruct_type @Empty_set.
  Hint Extern 3 => JMeq_eq.
(*  Hint Extern 3 (_ = _) => destruct_to_empty_set.
  Hint Extern 3 (JMeq _ _) => destruct_to_empty_set. *)

  Lemma TerminalCategory_Terminal : @TerminalObject _ _ SmallCat TerminalCategory.
    unfold TerminalObject, TerminalCategory in *.
    intros; eexists.
    unfold is_unique; intros;
      functor_eq; destruct_type @SpecializedFunctor;
      auto.
    Grab Existential Variables.
    eapply Build_SpecializedFunctor; intros; simpl in *; auto.
    Grab Existential Variables.
    simpl in *; auto.
    simpl in *; auto.
  Qed.

  Lemma InitialCategory_Initial : @InitialObject _ _ SmallCat InitialCategory.
    unfold InitialObject, InitialCategory in *.
    intros; eexists.
    unfold is_unique; intros;
      functor_eq; auto.
    Grab Existential Variables.
    eapply Build_SpecializedFunctor; intros; simpl in *; auto.
    Grab Existential Variables.
    simpl in *; tauto.
    simpl in *; tauto.
  Qed.
End Objects.
