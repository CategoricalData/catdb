Require Import FunctionalExtensionality JMeq.
Require Export Category SmallCategory SmallFunctor DiscreteCategory.
Require Import Common FEqualDep.

Set Implicit Arguments.

Section SmallCat.
  Definition SmallCat : Category.
    refine {| Object := SmallCategory;
      Morphism := @SmallFunctor;
      Compose := @ComposeSmallFunctors;
      Identity := @IdentitySmallFunctor
      |}; abstract sfunctor_eq.
  Defined.
End SmallCat.

Section Objects.
  Hint Extern 1 (_ = _) => apply functional_extensionality_dep; intro.
  Hint Extern 1 (JMeq _ _) => apply (@functional_extensionality_dep_JMeq _); intros.
  Hint Extern 3 (_ = _) => destruct_to_empty_set.
  Hint Extern 3 (JMeq _ _) => destruct_to_empty_set.

  Lemma TerminalCategory_Terminal : @TerminalObject SmallCat TerminalCategory.
    unfold TerminalObject, TerminalCategory in *.
    intros; eexists.
    unfold is_unique; intros;
      sfunctor_eq; simpl; auto.
    Grab Existential Variables.
    eapply Build_SmallFunctor; intros; simpl in *; auto.
    Grab Existential Variables.
    simpl in *; tauto.
    simpl in *; tauto.
  Qed.

  Lemma InitialCategory_Initial : @InitialObject SmallCat InitialCategory.
    unfold InitialObject, InitialCategory in *.
    intros; eexists.
    unfold is_unique; intros;
      sfunctor_eq; auto.
    Grab Existential Variables.
    eapply Build_SmallFunctor; intros; simpl in *; tauto.
    Grab Existential Variables.
    simpl in *; tauto.
    simpl in *; tauto.
  Qed.
End Objects.
