Require Import FunctionalExtensionality JMeq ProofIrrelevance.
Require Export Category CategoryIsomorphisms InitialTerminalCategory Functor ComputableCategory.
Require Import Common FEqualDep.

Set Implicit Arguments.

Section SmallCat.
  Definition SmallCat := ComputableCategory _ SUnderlyingCategory.
  Definition LocallySmallCat := ComputableCategory _ LSUnderlyingCategory.
End SmallCat.

Section Objects.
  Hint Unfold Morphism Object.

  Local Arguments Object / {obj} C : rename.
  Local Arguments Morphism / {obj} _ _ _.

  Hint Extern 1 (_ = _) => apply functional_extensionality_dep; intro.
  Hint Extern 1 (_ = _) => apply forall_extensionality_dep; intro.
  Hint Extern 1 (JMeq _ _) => apply (@functional_extensionality_dep_JMeq _); intros.
  Hint Extern 3 => destruct_to_empty_set.

  Lemma TerminalCategory_Terminal : TerminalObject (C := SmallCat) TerminalCategory.
    unfold TerminalObject in *.
    intros; eexists.
    unfold is_unique; intros;
      functor_eq; eauto.
    Grab Existential Variables.
    hnf; eapply Build_SpecializedFunctor; intros; simpl in *; eauto.
    Grab Existential Variables.
    simpl in *; tauto.
    simpl in *; tauto.
  Qed.

  Lemma InitialCategory_Initial : InitialObject (C := SmallCat) InitialCategory.
    unfold InitialObject in *.
    intros; eexists.
    unfold is_unique; intros;
      functor_eq; eauto.
    Grab Existential Variables.
    hnf; eapply Build_SpecializedFunctor; intros; simpl in *; auto.
    Grab Existential Variables.
    simpl in *; tauto.
    simpl in *; tauto.
  Qed.
End Objects.
