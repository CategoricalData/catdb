Require Import FunctionalExtensionality.
Require Export Category Functor FunctorCategory Hom.
Require Import Common SmallDuals ProductCategory SetCategory.

Set Implicit Arguments.

Local Infix "*" := ProductCategory.
Local Notation "C ^ D" := (FunctorCategory D C).

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
    split; simpl; snt_eq;
      pose (FIdentityOf X);
        pose (FCompositionOf X);
          unfold smallcat2cat in *; simpl in *; t_with t'.
    rename x0 into c'.
    rename x1 into f.
    rename x into a.
    unfold YonedaLemmaMorphism; simpl.
    admit.
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
    rename x0 into c'.
    rename x1 into f.
    rename x into a.
    unfold CoYonedaLemmaMorphism; simpl.
    admit.
  Qed.
End CoYonedaLemma.
