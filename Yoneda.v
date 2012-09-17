Require Import FunctionalExtensionality.
Require Export SpecializedCategory Functor FunctorCategory Hom FunctorAttributes.
Require Import Common ProductCategory SetCategory.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope category_scope.

Local Ltac apply_commutes_by_transitivity_and_solve_with tac :=
  repeat (apply functional_extensionality_dep; intro);
    match goal with
      | [ a : _, f : _ |- _ ] => let H := fresh in
        assert (H := fg_equal (Commutes a _ _ f)); simpl in H;
          let fin_tac := (solve [ etransitivity; try apply H; clear H; tac ]) in
            fin_tac || symmetry in H; fin_tac
    end.

Section Yoneda.
  Context `(C : @SpecializedCategory objC).
  Let COp := OppositeCategory C.

  Section Yoneda.
    Definition Yoneda : SpecializedFunctor COp (TypeCat ^ C).
      match goal with
        | [ |- SpecializedFunctor ?C0 ?D0 ] =>
          refine (Build_SpecializedFunctor C0 D0
            (fun c : COp => CovariantHomFunctor C c : TypeCat ^ C)
            (fun s d (f : COp.(Morphism) s d) =>
              Build_SpecializedNaturalTransformation (CovariantHomFunctor C s) (CovariantHomFunctor C d)
              (fun c : C => (fun m : C.(Morphism) _ _ => Compose m f))
              _
            )
            _
            _
          )
      end;
      simpl; nt_eq; abstract t.
      Grab Existential Variables.
      abstract (intros; simpl; apply functional_extensionality_dep; t).
    Defined.
  End Yoneda.

  Section CoYoneda.
    Definition CoYoneda : SpecializedFunctor C (TypeCat ^ COp).
      match goal with
        | [ |- SpecializedFunctor ?C0 ?D0 ] =>
          refine (Build_SpecializedFunctor C0 D0
            (fun c : C => ContravariantHomFunctor C c : TypeCat ^ COp)
            (fun s d (f : C.(Morphism) s d) =>
              Build_SpecializedNaturalTransformation (ContravariantHomFunctor C s) (ContravariantHomFunctor C d)
              (fun c : C => (fun m : COp.(Morphism) _ _ => Compose m f))
              _
            )
            _
            _
          )
      end;
      simpl; nt_eq; abstract t.
      Grab Existential Variables.
      abstract (intros; simpl; apply functional_extensionality_dep; t).
    Defined.
  End CoYoneda.
End Yoneda.

Section YonedaLemma.
  Context `(C : @SpecializedCategory objC).
  Let COp := OppositeCategory C : SpecializedCategory _.

  (* Note: If we use [Yoneda _ c] instead, we get Universe Inconsistencies.  Hmm... *)
  Definition YonedaLemmaMorphism (c : C) (X : TypeCat ^ C) : Morphism TypeCat (Morphism (TypeCat ^ C) (Yoneda C c) X) (X c).
    simpl; intro a.
    exact (a c (Identity _)).
  Defined.

  Definition YonedaLemmaMorphismInverse (c : C) (X : TypeCat ^ C) : Morphism TypeCat (X c) (Morphism (TypeCat ^ C) (Yoneda C c) X).
    simpl; intro Xc.
    hnf.
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun c' : C => (fun f : Morphism _ c c' => X.(MorphismOf) f Xc))
          _
        )
    end;
    abstract (
      intros; simpl; apply functional_extensionality_dep; intros; eauto;
        pose (FCompositionOf X);
          simpl in *;
            fg_equal;
            t_with t'
    ).
  Defined.

  Hint Rewrite @FIdentityOf.

  Lemma YonedaLemma (c : C) (X : TypeCat ^ C) : IsIsomorphism (@YonedaLemmaMorphism c X).
    exists (@YonedaLemmaMorphismInverse c X).
    unfold YonedaLemmaMorphismInverse, YonedaLemmaMorphism.
    pose (FIdentityOf X).
    pose (FCompositionOf X).
    split; simpl; nt_eq;
      simpl in *; t_with t'.
    apply_commutes_by_transitivity_and_solve_with ltac:(t_with t').
  Qed.
End YonedaLemma.

Section CoYonedaLemma.
  Context `(C : @SpecializedCategory objC).
  Let COp := OppositeCategory C.

  Definition CoYonedaLemmaMorphism (c : C) (X : TypeCat ^ COp) : Morphism TypeCat (Morphism _ (CoYoneda C c) X) (X c).
    simpl; intro a.
    exact (a c (Identity _)).
  Defined.

  Definition CoYonedaLemmaMorphismInverse (c : C) (X : TypeCat ^ COp) : Morphism TypeCat (X c) (Morphism _ (CoYoneda C c) X).
    simpl; intro Xc.
    hnf.
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun c' : COp => (fun f : COp.(Morphism) c c' => X.(MorphismOf) f Xc))
          _
        )
    end;
    abstract (
      intros; simpl; apply functional_extensionality_dep; intros; eauto;
        pose (FCompositionOf X);
          simpl in *;
            fg_equal;
            t_with t'
    ).
  Defined.

  Hint Rewrite @FIdentityOf.

  Lemma CoYonedaLemma (c : C) (X : TypeCat ^ COp) : IsIsomorphism (@CoYonedaLemmaMorphism c X).
    exists (@CoYonedaLemmaMorphismInverse c X).
    split; simpl; nt_eq;
      pose (FIdentityOf X);
        pose (FCompositionOf X);
          simpl in *; t_with t'.
    apply_commutes_by_transitivity_and_solve_with ltac:(t_with t').
    fg_equal.
    t_with t'.
  Qed.
End CoYonedaLemma.

Section FullyFaithful.
  Context `(C : @SpecializedCategory objC).

  Definition YonedaEmbedding : FunctorFullyFaithful (Yoneda C).
    unfold FunctorFullyFaithful.
    intros c c'.
    destruct (@YonedaLemma _ C c (CovariantHomFunctor C c')) as [ m i ].
    exists (YonedaLemmaMorphism (X := CovariantHomFunctor C c')).
    t_with t'; nt_eq; t_with t'.
    apply_commutes_by_transitivity_and_solve_with ltac:(t_with t').
  Qed.

  Definition CoYonedaEmbedding : FunctorFullyFaithful (CoYoneda C).
    unfold FunctorFullyFaithful.
    intros c c'.
    destruct (@CoYonedaLemma _ C c (ContravariantHomFunctor C c')) as [ m i ].
    exists (CoYonedaLemmaMorphism (X := ContravariantHomFunctor C c')).
    t_with t'; nt_eq; t_with t'.
    apply_commutes_by_transitivity_and_solve_with ltac:(t_with t').
  Qed.
End FullyFaithful.
