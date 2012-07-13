Require Import FunctionalExtensionality JMeq.
Require Export Category DiscreteCategory Functor.
Require Import Common FEqualDep.

Set Implicit Arguments.

Section SmallCat.
  Definition SmallCat : @SpecializedCategory SmallCategory (fun C D => SpecializedFunctor C D).
    refine (@Build_SpecializedCategory SmallCategory (fun C D => SpecializedFunctor C D)
      (fun o => IdentityFunctor o)
      (fun C D E F G => ComposeFunctors F G)
      _
      _
      _
    );
    abstract functor_eq.
  Defined.

  Definition LocallySmallCat : @SpecializedCategory LocallySmallCategory (fun C D => SpecializedFunctor C D).
    refine (@Build_SpecializedCategory LocallySmallCategory (fun C D => SpecializedFunctor C D)
      (fun o => IdentityFunctor o)
      (fun C D E F G => ComposeFunctors F G)
      _
      _
      _
    );
    abstract functor_eq.
  Defined.
End SmallCat.

Section Objects.
  Hint Extern 1 (_ = _) => apply functional_extensionality_dep; intro.
  Hint Extern 1 (_ = _) => apply forall_extensionality_dep; intro.
  Hint Extern 1 (JMeq _ _) => apply (@functional_extensionality_dep_JMeq _); intros.
  Hint Extern 3 (_ = _) => destruct_to_empty_set.
  Hint Extern 3 (JMeq _ _) => destruct_to_empty_set.

  Lemma TerminalCategory_Terminal : TerminalObject (C := SmallCat) TerminalCategory.
    unfold TerminalObject, TerminalCategory in *.
    intros; eexists.
    unfold is_unique; intros;
      functor_eq; auto.
    Grab Existential Variables.
    eapply Build_SpecializedFunctor; intros; simpl in *; auto.
    Grab Existential Variables.
    simpl in *; tauto.
    simpl in *; tauto.
  Qed.

  Lemma InitialCategory_Initial : InitialObject (C := SmallCat) InitialCategory.
    unfold InitialObject, InitialCategory in *.
    intros; eexists.
    unfold is_unique; intros;
      functor_eq; auto.
    Grab Existential Variables.
    eapply Build_SpecializedFunctor; intros; simpl in *; tauto.
    Grab Existential Variables.
    simpl in *; tauto.
    simpl in *; tauto.
  Qed.
End Objects.
