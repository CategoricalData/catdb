Require Import SpecializedCategory Functor NaturalTransformation.
Require Import Notations SumCategory ProductCategory.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Section SimplifiedMorphism.
  Section single_category_definition.
    Context `{C : SpecializedCategory objC}.

    Class > MorphismSimplifiesTo {s d} (m_orig m_simpl : Morphism C s d) :=
      simplified_morphism_ok :> m_orig = m_simpl.
  End single_category_definition.

  Local Ltac t :=
    hnf in *; subst;
    repeat rewrite <- FCompositionOf;
    repeat match goal with
             | [ H : _ |- _ ] => rewrite H
           end;
    repeat rewrite FIdentityOf;
    autorewrite with category;
    auto with category;
    trivial.

  Section single_category_instances.
    Context `{C : SpecializedCategory objC}.

    Global Instance LeftIdentitySimplify
           `(@MorphismSimplifiesTo _ C s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ C _ _ m2_orig (Identity _))
    : MorphismSimplifiesTo (Compose m2_orig m1_orig) m1_simpl | 10.
    t.
    Qed.

    Global Instance RightIdentitySimplify
           `(@MorphismSimplifiesTo _ C s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ C _ _ m2_orig (Identity _))
    : MorphismSimplifiesTo (Compose m1_orig m2_orig) m1_simpl | 10.
    t.
    Qed.

    Global Instance ComposeToIdentitySimplify
           `(@MorphismSimplifiesTo _ C s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ C d s m2_orig m2_simpl)
           `(Compose m2_simpl m1_simpl = Identity _)
    : MorphismSimplifiesTo (Compose m2_orig m1_orig) (Identity _) | 20.
    t.
    Qed.

    Global Instance AssociativitySimplify `(@MorphismSimplifiesTo _ C _ _ (@Compose _ C _ c d m3 (@Compose _ C a b c m2 m1)) m_simpl)
    : MorphismSimplifiesTo (Compose (Compose m3 m2) m1) m_simpl | 1000.
    t.
    Qed.

    Global Instance ComposeSimplify
           `(@MorphismSimplifiesTo _ C s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ C d d' m2_orig m2_simpl)
    : MorphismSimplifiesTo (Compose m2_orig m1_orig) (Compose m2_simpl m1_simpl) | 5000.
    t.
    Qed.

    Global Instance NoSimplify {s d} (m : Morphism C s d)
    : MorphismSimplifiesTo m m | 10000
      := eq_refl.
  End single_category_instances.

  Section sum_prod_category_instances.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.

    Global Instance SumCategorySimplify_inl
           `(@MorphismSimplifiesTo _ C s d m_orig m_simpl)
    : @MorphismSimplifiesTo _ (C + D) (inl s) (inl d) m_orig m_simpl | 100.
    t.
    Qed.

    Global Instance SumCategorySimplify_inr
           `(@MorphismSimplifiesTo _ D s d m_orig m_simpl)
    : @MorphismSimplifiesTo _ (C + D) (inr s) (inr d) m_orig m_simpl | 100.
    t.
    Qed.

    Global Instance SumComposeSimplify_inl
           `(@MorphismSimplifiesTo _ C s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ C d d' m2_orig m2_simpl)
    : MorphismSimplifiesTo (@Compose _ (C + D) (inl s) (inl d) (inl d') m2_orig m1_orig)
                           (@Compose _ (C + D) (inl s) (inl d) (inl d') m2_simpl m1_simpl) | 50.
    t.
    Qed.

    Global Instance SumComposeSimplify_inr
           `(@MorphismSimplifiesTo _ D s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ D d d' m2_orig m2_simpl)
    : MorphismSimplifiesTo (@Compose _ (C + D) (inr s) (inr d) (inr d') m2_orig m1_orig)
                           (@Compose _ (C + D) (inr s) (inr d) (inr d') m2_simpl m1_simpl) | 50.
    t.
    Qed.

    (*Global Instance ProductCategorySimplify
           `(@MorphismSimplifiesTo _ C s d m_orig m_simpl)
           `(@MorphismSimplifiesTo _ D s' d' m'_orig m'_simpl)
    : @MorphismSimplifiesTo _
                            (C * D)
                            (s, s')
                            (d, d')
                            (m_orig, m'_orig)
                            (m_simpl, m'_simpl)
    | 50.
    t.
    Qed.*)
  End sum_prod_category_instances.


  Section functor_instances.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.
    Variable F : SpecializedFunctor C D.

    Global Instance FIdentityOfSimplify `(@MorphismSimplifiesTo _ C x x m_orig (Identity _))
    : MorphismSimplifiesTo (MorphismOf F m_orig) (Identity _) | 30.
    t.
    Qed.

    Global Instance FCompositionOfSimplify
           `(@MorphismSimplifiesTo _ C s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ C d d' m2_orig m2_simpl)
           `(@MorphismSimplifiesTo _ _ _ _ (Compose m2_simpl m1_simpl) m_comp)
           `(@MorphismSimplifiesTo _ _ _ _ (MorphismOf F m_comp) m_Fcomp)
    : MorphismSimplifiesTo (Compose (MorphismOf F m2_orig) (MorphismOf F m1_orig))
                           m_Fcomp | 30.
    t.
    Qed.

    (** TODO(jgross): Remove this kludge *)
    Global Instance FunctorComposeToIdentitySimplify
           `(@MorphismSimplifiesTo _ D (F s) (F d) m1_orig (MorphismOf F m1_simpl))
           `(@MorphismSimplifiesTo _ D (F d) (F s) m2_orig (MorphismOf F m2_simpl))
           `(Compose m2_simpl m1_simpl = Identity _)
    : MorphismSimplifiesTo (Compose m2_orig m1_orig) (Identity _) | 20.
    t.
    Qed.

    Global Instance FunctorNoSimplify
           `(@MorphismSimplifiesTo _ C s d m_orig m_simpl)
    : MorphismSimplifiesTo (MorphismOf F m_orig) (MorphismOf F m_simpl) | 5000.
    t.
    Qed.
  End functor_instances.
End SimplifiedMorphism.

Hint Extern 0 (_ = _) => eassumption : typeclass_instances.

Ltac rsimplify_morphisms_in_all :=
  unfold Object in *;
  simpl in *;
  progress
    repeat match goal with
             | [ H : context[?m] |- _ ] =>
               progress erewrite (simplified_morphism_ok (m_orig := m)) in H by typeclasses eauto
             | [ |- context[?m] ] =>
               progress erewrite (simplified_morphism_ok (m_orig := m)) by typeclasses eauto
           end.

Ltac rsimplify_morphisms :=
  unfold Object in *;
  simpl in *;
  match goal with
    | [ |- @eq (Morphism _ _ _) ?A ?B ] =>
      progress (
          try erewrite (simplified_morphism_ok (m_orig := A));
          try erewrite (simplified_morphism_ok (m_orig := B));
          []
        )
    | [ |- context[?m] ] =>
          match type of m with
            | Morphism _ _ _ => progress (erewrite (simplified_morphism_ok (m_orig := m)); [])
          end
    | _ => erewrite simplified_morphism_ok; []
  end;
  simpl.


(*******************************************************************************)
(**                Goals which aren't yet solved by [rsimplify_morphisms]     **)
(*******************************************************************************)
Section bad1.
  Context `(C : SpecializedCategory objC).
  Context `(D : SpecializedCategory objD).
  Context `(E : SpecializedCategory objE).
  Variable s : SpecializedFunctor D E.
  Variable s8 : SpecializedFunctor C D.
  Variable s6 : SpecializedFunctor D E.
  Variable s7 : SpecializedFunctor C D.
  Variable s4 : SpecializedFunctor D E.
  Variable s5 : SpecializedFunctor C D.
  Variable s2 : SpecializedNaturalTransformation s s6.
  Variable s3 : SpecializedNaturalTransformation s8 s7.
  Variable s0 : SpecializedNaturalTransformation s6 s4.
  Variable s1 : SpecializedNaturalTransformation s7 s5.
  Variable x : objC.

  Goal
    (Compose (MorphismOf s4 (Compose (s1 x) (s3 x)))
             (Compose (s0 (s8 x)) (s2 (s8 x)))) =
  (Compose (MorphismOf s4 (s1 x))
           (Compose (s0 (s7 x)) (Compose (MorphismOf s6 (s3 x)) (s2 (s8 x))))).
  Fail (rsimplify_morphisms; reflexivity).
  repeat erewrite @FCompositionOf by typeclasses eauto;
    repeat try_associativity ltac:(repeat rewrite Commutes;
                                   ((apply f_equal2; reflexivity)
                                      || (apply f_equal2; try reflexivity; [])));
    reflexivity.
  Qed.
End bad1.


Section bad2.
  Context `(C : SpecializedCategory objC).
  Context `(D : SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.
  Variable o1 : objC.
  Variable o2 : objC.
  Variable o : objC.
  Variable o0 : objC.
  Variable m : Morphism C o o1.
  Variable m0 : Morphism C o2 o0.
  Variable x : Morphism C o1 o2.
  Goal MorphismOf F (Compose m0 (Compose x m)) =
  Compose (MorphismOf F m0) (Compose (MorphismOf F x) (MorphismOf F m)).
  Fail (rsimplify_morphisms; reflexivity).
  rsimplify_morphisms; rsimplify_morphisms; reflexivity.
  Qed.
End bad2.
