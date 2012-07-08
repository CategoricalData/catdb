Require Import FunctionalExtensionality.
Require Export SpecializedCategory SpecializedFunctor SpecializedFunctorCategory SpecializedHom SpecializedFunctorAttributes.
Require Import Common SpecializedProductCategory SpecializedSetCategory.

Set Implicit Arguments.

Local Infix "*" := ProductSpecializedCategory.
Local Notation "C ^ D" := (SpecializedFunctorCategory D C).

Local Ltac apply_commutes_by_transitivity_and_solve_with tac :=
  repeat (apply functional_extensionality_dep; intro);
    match goal with
      | [ a : _, f : _ |- _ ] => let H := fresh in
        assert (H := fg_equal (Commutes a _ _ f)); simpl in H;
          let fin_tac := (solve [ etransitivity; try apply H; clear H; tac ]) in
            fin_tac || symmetry in H; fin_tac
    end.

Section Yoneda.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Let COp := OppositeSpecializedCategory C.

  Section Yoneda.
    Definition Yoneda : SpecializedFunctor COp (TypeCat ^ C).
      Transparent Morphism Compose Identity.
      refine {| ObjectOf' := (fun c : COp => CovariantHomSpecializedFunctor C c : TypeCat ^ C);
        MorphismOf' := (fun s d (f : COp.(Morphism) s d) =>
          Build_SpecializedNaturalTransformation (CovariantHomSpecializedFunctor C s) (CovariantHomSpecializedFunctor C d)
          (fun c : C => (fun m : C.(Morphism) _ _ => Compose m f))
          _
        )
      |}; simpl; spnt_eq; abstract t.
      Grab Existential Variables.
      abstract (intros; simpl; apply functional_extensionality_dep; t).
    Defined.
  End Yoneda.

  Section CoYoneda.
    Definition CoYoneda : SpecializedFunctor C (TypeCat ^ COp).
      Transparent Morphism Compose Identity.
      refine {| ObjectOf' := (fun c : C => ContravariantHomSpecializedFunctor C c : TypeCat ^ COp);
        MorphismOf' := (fun s d (f : C.(Morphism) s d) =>
          Build_SpecializedNaturalTransformation (ContravariantHomSpecializedFunctor C s) (ContravariantHomSpecializedFunctor C d)
          (fun c : C => (fun m : COp.(Morphism) _ _ => Compose m f))
          _
        )
      |}; simpl; spnt_eq; abstract t.
      Grab Existential Variables.
      abstract (intros; simpl; apply functional_extensionality_dep; t).
    Defined.
  End CoYoneda.
End Yoneda.

Section YonedaLemma.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Let COp := OppositeSpecializedCategory C : SpecializedCategory _.

  (* Note: If we use [Yoneda _ c] instead, we get Universe Inconsistencies.  Hmm... *)
  Definition YonedaLemmaMorphism (c : C) (X : TypeCat ^ C) : Morphism TypeCat (Morphism (TypeCat ^ C) (Yoneda C c) X) (X c).
    Transparent Morphism.
    simpl; intro a.
    exact (a c (Identity _)).
  Defined.

  Definition YonedaLemmaMorphismInverse (c : C) (X : TypeCat ^ C) : Morphism TypeCat (X c) (Morphism (TypeCat ^ C) (Yoneda C c) X).
    simpl; intro Xc.
    refine {| ComponentsOf' := (fun c' : C => (fun f : Morphism _ c c' => X.(MorphismOf) f Xc) : TypeCat.(Morphism) (CovariantHomSpecializedFunctor C c c') (X c')) |}.
    abstract (
      intros; simpl; apply functional_extensionality_dep; intros; eauto;
        pose (FCompositionOf X);
          simpl in *;
            t_with t'
    ).
  Defined.

  Lemma YonedaLemma (c : C) (X : TypeCat ^ C) : CategoryIsomorphism (@YonedaLemmaMorphism c X).
    Transparent Compose Morphism Identity.
    exists (@YonedaLemmaMorphismInverse c X).
    unfold YonedaLemmaMorphismInverse, YonedaLemmaMorphism.
    pose (FIdentityOf X).
    pose (FCompositionOf X).
    split; simpl; spnt_eq;
      simpl in *; t_with t'.
    apply_commutes_by_transitivity_and_solve_with ltac:(t_with t').
  Qed.
End YonedaLemma.

Section CoYonedaLemma.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Let COp := OppositeSpecializedCategory C.

  Definition CoYonedaLemmaMorphism (c : C) (X : TypeCat ^ COp) : Morphism TypeCat (Morphism _ (CoYoneda C c) X) (X c).
    Transparent Morphism.
    simpl; intro a.
    exact (a c (Identity _)).
  Defined.

  Definition CoYonedaLemmaMorphismInverse (c : C) (X : TypeCat ^ COp) : Morphism TypeCat (X c) (Morphism _ (CoYoneda C c) X).
    simpl; intro Xc.
    refine {| ComponentsOf' := (fun c' : COp => (fun f : COp.(Morphism) c c' => X.(MorphismOf) f Xc) : TypeCat.(Morphism) (ContravariantHomSpecializedFunctor C c c') (X c')) |}.
    abstract (
      intros; simpl; apply functional_extensionality_dep; intros; eauto;
        pose (FCompositionOf X);
          simpl in *;
            t_with t'
    ).
  Defined.

  Lemma CoYonedaLemma (c : C) (X : TypeCat ^ COp) : CategoryIsomorphism (@CoYonedaLemmaMorphism c X).
    Transparent Compose Morphism Identity.
    exists (@CoYonedaLemmaMorphismInverse c X).
    split; simpl; spnt_eq;
      pose (FIdentityOf X);
        pose (FCompositionOf X);
          simpl in *; t_with t'.
    apply_commutes_by_transitivity_and_solve_with ltac:(t_with t').
  Qed.
End CoYonedaLemma.

Section FullyFaithful.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Definition YonedaEmbedding : SpecializedFunctorFullyFaithful (Yoneda C).
    Transparent Morphism Compose.
    unfold SpecializedFunctorFullyFaithful.
    intros c c'.
    destruct (@YonedaLemma _ _ C c (CovariantHomSpecializedFunctor C c')) as [ m i ].
    exists (YonedaLemmaMorphism (X := CovariantHomSpecializedFunctor C c')).
    t_with t'; spnt_eq; t_with t'.
    apply_commutes_by_transitivity_and_solve_with ltac:(t_with t').
  Qed.

  Definition CoYonedaEmbedding : SpecializedFunctorFullyFaithful (CoYoneda C).
    Transparent Morphism Compose Identity.
    unfold SpecializedFunctorFullyFaithful.
    intros c c'.
    destruct (@CoYonedaLemma _ _ C c (ContravariantHomSpecializedFunctor C c')) as [ m i ].
    exists (CoYonedaLemmaMorphism (X := ContravariantHomSpecializedFunctor C c')).
    t_with t'; spnt_eq; t_with t'.
    apply_commutes_by_transitivity_and_solve_with ltac:(t_with t').
  Qed.
End FullyFaithful.
