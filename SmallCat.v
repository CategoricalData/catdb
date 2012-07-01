Require Import FunctionalExtensionality JMeq.
Require Export Category SmallCategory.
Require Import Common SmallFunctor FEqualDep.

Set Implicit Arguments.

Section SmallCat.
  Hint Resolve ComposeSmallFunctorsAssociativity LeftIdentitySmallFunctor RightIdentitySmallFunctor.

  Definition SmallCat : Category.
    refine {| Object := SmallCategory;
      Morphism := @SmallFunctor;
      Identity := @IdentitySmallFunctor;
      Compose := @ComposeSmallFunctors
      |}; auto.
  Defined.
End SmallCat.

Section Objects.
  Definition TerminalCategory : SmallCategory.
    refine {| SObject := unit;
      SMorphism := (fun _ _ => unit);
      SCompose := (fun _ _ _ _ _ => tt);
      SIdentity := (fun _ => tt)
    |};
    abstract (
      intros;
        repeat match goal with
                 | [ H : unit |- _ ] => destruct H
               end;
        reflexivity
    ).
  Defined.

  Definition InitialCategory : SmallCategory.
    refine {| SObject := Empty_set;
      SMorphism := (fun s _ => match s with end);
      SCompose := (fun s _ _ _ _ => match s with end);
      SIdentity := (fun o => match o with end)
    |}; abstract tauto.
  Defined.

  Hint Extern 1 (@eq unit ?a ?b) => try destruct a; try destruct b; try reflexivity.
  Hint Extern 1 (@eq Empty_set) => tauto.
  Hint Extern 1 (_ = _) => apply functional_extensionality_dep; intro.

  Lemma TerminalCategory_Terminal : @TerminalObject SmallCat TerminalCategory.
    unfold TerminalObject, TerminalCategory in *.
    intros; eexists.
    unfold is_unique; intros;
      sfunctor_eq; simpl; auto.
    Grab Existential Variables.
    eapply Build_SmallFunctor; intros; simpl in *; auto.
    Grab Existential Variables.
    intros; simpl in *; tauto.
    intros; simpl in *; tauto.
  Qed.

  Lemma InitialCategory_Initial : @InitialObject SmallCat InitialCategory.
    unfold InitialObject, InitialCategory in *.
    intros; eexists.
    unfold is_unique; intros;
      sfunctor_eq;
      try (apply (@functional_extensionality_dep_JMeq _); intros);
        repeat (apply functional_extensionality_dep; intros);
          simpl; eauto; try tauto.
    Grab Existential Variables.
    eapply Build_SmallFunctor; intros; simpl in *; auto; try tauto.
    Grab Existential Variables.
    intros; simpl in *; tauto.
    intros; simpl in *; tauto.
  Qed.
End Objects.
