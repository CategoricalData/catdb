Require Export LtacReifiedSimplification.
Require Import Category Functor NaturalTransformation.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section SimplifiedMorphism.
  Section single_category.
    Context `{C : Category}.

    Class SimplifiedMorphism {s d} (m : Morphism C s d) :=
      SimplifyMorphism { reified_morphism : ReifiedMorphism C s d;
                         reified_morphism_ok : m = ReifiedMorphismDenote reified_morphism }.

    Lemma SimplifyReifiyMorphismOk `(@SimplifiedMorphism s d m)
    : m
      = ReifiedMorphismDenote (ReifiedMorphismSimplify (reified_morphism (m := m))).
      rewrite <- ReifiedMorphismSimplifyOk.
      rewrite <- reified_morphism_ok.
      reflexivity.
    Qed.

    Global Instance unchanged_morphism s d (m : Morphism C s d) : SimplifiedMorphism m | 1000
      := SimplifyMorphism (m := m) (ReifiedGenericMorphism C s d m) eq_refl.

    Global Instance identity_morphism x : SimplifiedMorphism (Identity x) | 10
      := SimplifyMorphism (m := Identity x) (ReifiedIdentityMorphism C x) eq_refl.

    Global Instance composition_morphism s d d'
           `(@SimplifiedMorphism d d' m1) `(@SimplifiedMorphism s d m2)
    : SimplifiedMorphism (Compose m1 m2) | 10
      := SimplifyMorphism (m := Compose m1 m2)
                          (ReifiedComposedMorphism (reified_morphism (m := m1))
                                                   (reified_morphism (m := m2)))
                          (f_equal2 _
                                    reified_morphism_ok
                                    reified_morphism_ok).
  End single_category.

  Section functor.
    Context `{C : Category}.
    Context `{D : Category}.
    Variable F : Functor C D.

    Global Instance functor_morphism `(@SimplifiedMorphism C s d m)
    : SimplifiedMorphism (MorphismOf F m) | 50
      := SimplifyMorphism (m := MorphismOf F m)
                          (ReifiedFunctorMorphism F (reified_morphism (m := m)))
                          (f_equal _ reified_morphism_ok).
  End functor.

  Section natural_transformation.
    Context `{C : Category}.
    Context `{D : Category}.
    Variables F G : Functor C D.
    Variable T : NaturalTransformation F G.

    Global Instance nt_morphism x
    : SimplifiedMorphism (T x) | 50
      := SimplifyMorphism (m := T x) (ReifiedNaturalTransformationMorphism T x) eq_refl.
  End natural_transformation.
End SimplifiedMorphism.

Ltac rsimplify_morphisms :=
  match goal with
    | [ |- @eq (Morphism _ _ _) ?A ?B ] =>
      erewrite (SimplifyReifiyMorphismOk (m := A));
        erewrite (SimplifyReifiyMorphismOk (m := B))
    | _ => erewrite SimplifyReifiyMorphismOk
  end;
  simpl.
