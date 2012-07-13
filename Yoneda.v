Require Import FunctionalExtensionality.
Require Export Category Functor FunctorCategory Hom FunctorAttributes.
Require Import Common SmallDuals ProductCategory SetCategory.

Set Implicit Arguments.

Local Infix "*" := ProductCategory.
Local Notation "C ^ D" := (FunctorCategory D C).

Local Ltac apply_scommutes_by_transitivity_and_solve_with tac :=
  repeat (apply functional_extensionality_dep; intro);
    match goal with
      | [ a : _, f : _ |- _ ] => let H := fresh in
        assert (H := fg_equal (SCommutes a _ _ f)); simpl in H;
          let fin_tac := (solve [ etransitivity; try apply H; clear H; tac ]) in
            fin_tac || symmetry in H; fin_tac
    end.

Section Yoneda.
  Variable C : SmallCategory.
  Let COp := OppositeSmallCategory C.

  Section Yoneda.
    Definition Yoneda : Functor COp (TypeCat ^ C).
      refine {| ObjectOf := (fun c : COp.(Object) => CovariantHomFunctor C c : TypeCat ^ C);
        MorphismOf := (fun s d (f : SMorphism COp s d) =>
          Build_SmallNaturalTransformation (CovariantHomFunctor C s) (CovariantHomFunctor C d)
          (fun c : C => (fun m => SCompose m f))
          _
        )
      |}; simpl; snt_eq; abstract auto.
      Grab Existential Variables.
      abstract (intros; simpl; apply functional_extensionality_dep; intros; auto).
    Defined.
  End Yoneda.

  Section CoYoneda.
    Definition CoYoneda : Functor C (TypeCat ^ COp).
      refine {| ObjectOf := (fun c : C.(Object) => SmallContravariantHomFunctor C c : TypeCat ^ COp);
        MorphismOf := (fun s d (f : SMorphism C s d) =>
          Build_SmallNaturalTransformation (SmallContravariantHomFunctor C s) (SmallContravariantHomFunctor C d)
          (fun c : C => (fun m => SCompose m f))
          _
        )
      |}; simpl; snt_eq; abstract auto.
      Grab Existential Variables.
      abstract (intros; simpl; apply functional_extensionality_dep; intros; auto).
    Defined.
  End CoYoneda.
End Yoneda.

Section YonedaLemma.
  Variable C : SmallCategory.
  Let COp := OppositeSmallCategory C.

  Definition YonedaLemmaMorphism (c : C) (X : TypeCat ^ C) : Morphism TypeCat (Morphism _ (Yoneda _ c) X) (X c).
    simpl; intro a.
    exact (a c (SIdentity _)).
  Defined.

  Definition YonedaLemmaMorphismInverse (c : C) (X : TypeCat ^ C) : Morphism TypeCat (X c) (Morphism _ (Yoneda _ c) X).
    simpl; intro Xc.
    refine {| SComponentsOf := (fun c' : C => (fun f : SMorphism _ c c' => X.(MorphismOf) f Xc) : Morphism TypeCat (CovariantHomFunctor C c c') (X c')) |}.
    abstract (
      intros; simpl; apply functional_extensionality_dep; intros; eauto;
        pose (FCompositionOf X);
          unfold smallcat2cat in *; simpl in *;
            t_with t'
    ).
  Defined.

  Lemma YonedaLemma (c : C) (X : TypeCat ^ C) : CategoryIsomorphism (@YonedaLemmaMorphism c X).
    exists (@YonedaLemmaMorphismInverse c X).
    unfold YonedaLemmaMorphismInverse, YonedaLemmaMorphism.
    pose (FIdentityOf X).
    pose (FCompositionOf X).
    split; simpl; snt_eq;
      unfold smallcat2cat in *; simpl in *; t_with t'.
    apply_scommutes_by_transitivity_and_solve_with ltac:(t_with t').
  Qed.
End YonedaLemma.

Section CoYonedaLemma.
  Variable C : SmallCategory.
  Let COp := OppositeSmallCategory C.

  Definition CoYonedaLemmaMorphism (c : C) (X : TypeCat ^ COp) : Morphism TypeCat (Morphism _ (CoYoneda _ c) X) (X c).
    simpl; intro a.
    exact (a c (SIdentity _)).
  Defined.

  Definition CoYonedaLemmaMorphismInverse (c : C) (X : TypeCat ^ COp) : Morphism TypeCat (X c) (Morphism _ (CoYoneda _ c) X).
    simpl; intro Xc.
    refine {| SComponentsOf := (fun c' : COp => (fun f : SMorphism COp c c' => X.(MorphismOf) f Xc) : Morphism TypeCat (SmallContravariantHomFunctor C c c') (X c')) |}.
    abstract (
      intros; simpl; apply functional_extensionality_dep; intros; eauto;
        pose (FCompositionOf X);
          unfold smallcat2cat in *; simpl in *;
            t_with t'
    ).
  Defined.

  Lemma CoYonedaLemma (c : C) (X : TypeCat ^ COp) : CategoryIsomorphism (@CoYonedaLemmaMorphism c X).
    exists (@CoYonedaLemmaMorphismInverse c X).
    split; simpl; snt_eq;
      pose (FIdentityOf X);
        pose (FCompositionOf X);
          unfold smallcat2cat in *; simpl in *; t_with t'.
    apply_scommutes_by_transitivity_and_solve_with ltac:(t_with t').
  Qed.
End CoYonedaLemma.

Section FullyFaithful.
  Variable C : SmallCategory.

  Definition YonedaEmbedding : FunctorFullyFaithful (Yoneda C).
    unfold FunctorFullyFaithful.
    intros c c'.
    destruct (@YonedaLemma C c (CovariantHomFunctor C c')) as [ m i ].
    exists (YonedaLemmaMorphism (X := CovariantHomFunctor C c')).
    t_with t'; snt_eq; t_with t'.
    apply_scommutes_by_transitivity_and_solve_with ltac:(t_with t').
  Qed.

  Definition CoYonedaEmbedding : FunctorFullyFaithful (CoYoneda C).
    unfold FunctorFullyFaithful.
    intros c c'.
    destruct (@CoYonedaLemma C c (SmallContravariantHomFunctor C c')) as [ m i ].
    exists (CoYonedaLemmaMorphism (X := SmallContravariantHomFunctor C c')).
    t_with t'; snt_eq; t_with t'.
    apply_scommutes_by_transitivity_and_solve_with ltac:(t_with t').
  Qed.
End FullyFaithful.
