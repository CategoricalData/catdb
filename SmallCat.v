Require Import FunctionalExtensionality JMeq.
Require Export Category SmallCategory SmallFunctor.
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
  Hint Extern 1 (@eq unit ?a ?b) => try destruct a; try destruct b; try reflexivity.
  Hint Extern 1 (_ = _) => simpl in *; tauto.

  Definition TerminalCategory : SmallCategory.
    refine {| SObject := unit;
      SMorphism := (fun _ _ => unit);
      SCompose := (fun _ _ _ _ _ => tt);
      SIdentity := (fun _ => tt)
    |}; abstract (intros; auto).
  Defined.

  Definition InitialCategory : SmallCategory.
    refine {| SObject := Empty_set;
      SMorphism := (fun s _ => match s with end);
      SCompose := (fun s _ _ _ _ => match s with end);
      SIdentity := (fun o => match o with end)
    |}; abstract (intros; auto).
  Defined.

  Hint Extern 1 (_ = _) => apply functional_extensionality_dep; intro.
  Hint Extern 1 (JMeq _ _) => apply (@functional_extensionality_dep_JMeq _); intros.

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
    apply (@functional_extensionality_dep_JMeq _);
      tauto.
    Grab Existential Variables.
    eapply Build_SmallFunctor; intros; simpl in *; tauto.
    Grab Existential Variables.
    simpl in *; tauto.
    simpl in *; tauto.
  Qed.
End Objects.
