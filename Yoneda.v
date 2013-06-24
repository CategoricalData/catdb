Require Import FunctionalExtensionality.
Require Export Category Functor FunctorCategory Hom FunctorAttributes.
Require Import Common ProductCategory SetCategory.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

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
  Variable C : Category.
  Let COp := OppositeCategory C.

  Section Yoneda.
    Let Yoneda_NT s d (f : COp.(Morphism) s d) : NaturalTransformation (CovariantHomFunctor C s) (CovariantHomFunctor C d).
      refine (Build_NaturalTransformation
                (CovariantHomFunctor C s)
                (CovariantHomFunctor C d)
                (fun c : C => (fun m : C.(Morphism) _ _ => Compose m f))
                _
             );
      abstract (intros; simpl; apply functional_extensionality_dep; intros; auto with morphism).
    Defined.

    Definition Yoneda : Functor COp (TypeCat ^ C).
      match goal with
        | [ |- Functor ?C0 ?D0 ] =>
          refine (Build_Functor C0 D0
            (fun c : COp => CovariantHomFunctor C c : TypeCat ^ C)
            (fun s d (f : COp.(Morphism) s d) => Yoneda_NT s d f)
            _
            _
          )
      end;
      abstract (simpl; nt_eq; auto with morphism).
    Defined.
  End Yoneda.

  Section CoYoneda.
    Let CoYoneda_NT s d (f : C.(Morphism) s d) : NaturalTransformation (ContravariantHomFunctor C s) (ContravariantHomFunctor C d).
      refine (Build_NaturalTransformation
                (ContravariantHomFunctor C s)
                (ContravariantHomFunctor C d)
                (fun c : C => (fun m : COp.(Morphism) _ _ => Compose m f))
                _
             );
      abstract (intros; simpl; apply functional_extensionality_dep; intros; auto with morphism).
    Defined.

    Definition CoYoneda : Functor C (TypeCat ^ COp).
      match goal with
        | [ |- Functor ?C0 ?D0 ] =>
          refine (Build_Functor C0 D0
            (fun c : C => ContravariantHomFunctor C c : TypeCat ^ COp)
            (fun s d (f : C.(Morphism) s d) => CoYoneda_NT s d f)
            _
            _
          )
      end;
      abstract (simpl; nt_eq; auto with morphism).
    Defined.
  End CoYoneda.
End Yoneda.

Section YonedaLemma.
  Variable C : Category.
  Let COp := OppositeCategory C.

  (* Note: If we use [Yoneda _ c] instead, we get Universe Inconsistencies.  Hmm... *)
  Definition YonedaLemmaMorphism (c : C) (X : TypeCat ^ C) : Morphism TypeCat (Morphism (TypeCat ^ C) (Yoneda C c) X) (X c).
    simpl; intro a.
    exact (a c (Identity _)).
  Defined.

  Definition YonedaLemmaMorphismInverse (c : C) (X : TypeCat ^ C) : Morphism TypeCat (X c) (Morphism (TypeCat ^ C) (Yoneda C c) X).
    simpl; intro Xc.
    hnf.
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
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

  Lemma YonedaLemma (c : C) (X : TypeCat ^ C) : IsIsomorphism (@YonedaLemmaMorphism c X).
    exists (@YonedaLemmaMorphismInverse c X).
    unfold YonedaLemmaMorphismInverse, YonedaLemmaMorphism.
    pose (FIdentityOf X).
    pose (FCompositionOf X).
    split; simpl; nt_eq;
    simpl in *; autorewrite with functor; simpl; trivial;
    apply_commutes_by_transitivity_and_solve_with ltac:(rewrite_hyp; autorewrite with morphism; trivial).
  Qed.
End YonedaLemma.

Section CoYonedaLemma.
  Variable C : Category.
  Let COp := OppositeCategory C.

  Definition CoYonedaLemmaMorphism (c : C) (X : TypeCat ^ COp)
  : Morphism TypeCat (Morphism (TypeCat ^ COp) (CoYoneda C c) X) (X c).
    simpl; intro a.
    exact (a c (Identity _)).
  Defined.

  Definition CoYonedaLemmaMorphismInverse (c : C) (X : TypeCat ^ COp)
  : Morphism TypeCat (X c) (Morphism (TypeCat ^ COp) (CoYoneda C c) X).
    simpl; intro Xc.
    hnf.
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
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

  Lemma CoYonedaLemma (c : C) (X : TypeCat ^ COp) : IsIsomorphism (@CoYonedaLemmaMorphism c X).
    exists (@CoYonedaLemmaMorphismInverse c X).
    split; simpl; nt_eq; clear;
    [ | pose (FIdentityOf X); fg_equal; trivial ];
    pose (FCompositionOf X);
    unfold CoYonedaLemmaMorphism, CoYonedaLemmaMorphismInverse;
    simpl;
    apply_commutes_by_transitivity_and_solve_with ltac:(rewrite_hyp; autorewrite with morphism; trivial).
  Qed.
End CoYonedaLemma.

Section FullyFaithful.
  Variable C : Category.

  Definition YonedaEmbedding : FunctorFullyFaithful (Yoneda C).
    unfold FunctorFullyFaithful.
    intros c c'.
    destruct (YonedaLemma (C := C) c (CovariantHomFunctor C c')) as [ m i ].
    exists (YonedaLemmaMorphism (X := CovariantHomFunctor C c')).
    t_with t'; nt_eq; autorewrite with morphism; trivial.
    apply_commutes_by_transitivity_and_solve_with ltac:(rewrite_hyp; autorewrite with morphism; trivial).
  Qed.

  Definition CoYonedaEmbedding : FunctorFullyFaithful (CoYoneda C).
    unfold FunctorFullyFaithful.
    intros c c'.
    destruct (CoYonedaLemma (C := C) c (ContravariantHomFunctor C c')) as [ m i ].
    exists (CoYonedaLemmaMorphism (X := ContravariantHomFunctor C c')).
    t_with t'; nt_eq; autorewrite with morphism; trivial.
    unfold CoYonedaLemmaMorphism, CoYonedaLemmaMorphismInverse;
      simpl;
      apply_commutes_by_transitivity_and_solve_with ltac:(rewrite_hyp; autorewrite with morphism; trivial).
  Qed.
End FullyFaithful.
