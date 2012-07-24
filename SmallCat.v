Require Import FunctionalExtensionality JMeq.
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
  Hint Extern 3 (_ = _) => destruct_to_empty_set.
  Hint Extern 3 (JMeq _ _) => destruct_to_empty_set.

  Lemma TerminalCategory_Terminal : @TerminalObject _ _ SmallCat TerminalCategory.
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

  Lemma InitialCategory_Initial : @InitialObject _ _ SmallCat InitialCategory.
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

Section SmallCatOver.
  Variable C : Category.

  Definition SmallCatOver_Object := { C' : SmallCategory & Functor C' C }.
  Definition LocallySmallCatOver_Object := { C' : LocallySmallCategory & Functor C' C }.
  Definition SmallCatOver_Morphism (s d : SmallCatOver_Object) :=
    { F : Functor (projT1 s) (projT1 d) |
      ComposeFunctors (projT2 d) F = (projT2 s) }.
  Definition LocallySmallCatOver_Morphism (s d : LocallySmallCatOver_Object) :=
    { F : Functor (projT1 s) (projT1 d) |
      ComposeFunctors (projT2 d) F = (projT2 s) }.

  Let SmallCatOver_Compose s d d' (m1 : SmallCatOver_Morphism d d') (m2 : SmallCatOver_Morphism s d) : SmallCatOver_Morphism s d'.
    exists (ComposeFunctors (proj1_sig m1) (proj1_sig m2)).
    abstract (
      destruct m1, m2; simpl;
        t_rev_with t';
        rewrite ComposeFunctorsAssociativity; reflexivity
    ).
  Defined.

  Let LocallySmallCatOver_Compose s d d' (m1 : LocallySmallCatOver_Morphism d d') (m2 : LocallySmallCatOver_Morphism s d) : LocallySmallCatOver_Morphism s d'.
    exists (ComposeFunctors (proj1_sig m1) (proj1_sig m2)).
    abstract (
      destruct m1, m2; simpl;
        t_rev_with t';
        rewrite ComposeFunctorsAssociativity; reflexivity
    ).
  Defined.

  Definition SmallCatOver : SpecializedCategory SmallCatOver_Morphism.
    refine (Build_SpecializedCategory SmallCatOver_Morphism
      (fun _ => existT _ (IdentityFunctor _) (RightIdentityFunctor _))
      SmallCatOver_Compose
      _
      _
      _
    );
    abstract (
      subst SmallCatOver_Compose LocallySmallCatOver_Compose;
        simpl in *; intros;
          simpl_eq;
          rewrite ComposeFunctorsAssociativity || rewrite RightIdentityFunctor || rewrite LeftIdentityFunctor;
            reflexivity
    ).
  Defined.

  Definition LocallySmallCatOver : SpecializedCategory LocallySmallCatOver_Morphism.
    refine (Build_SpecializedCategory LocallySmallCatOver_Morphism
      (fun _ => existT _ (IdentityFunctor _) (RightIdentityFunctor _))
      LocallySmallCatOver_Compose
      _
      _
      _
    );
    abstract (
      subst SmallCatOver_Compose LocallySmallCatOver_Compose;
        simpl in *; intros;
          simpl_eq;
          rewrite ComposeFunctorsAssociativity || rewrite RightIdentityFunctor || rewrite LeftIdentityFunctor;
            reflexivity
    ).
  Defined.
End SmallCatOver.
