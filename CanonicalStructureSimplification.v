Require Export LtacReifiedSimplification.
Require Import Category Functor NaturalTransformation.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section SimplifiedMorphism.
  Section single_category.
    Context `{C : Category}.

    (* structure for packaging a morphism and its reification *)

    Structure TaggedMorphism s d := Tag { untag :> Morphism C s d }.

    Structure SimplifiedMorphism s d :=
      ReifyMorphism
        {
          morphism_of : TaggedMorphism s d;
          reified_morphism_of : ReifiedMorphism C s d;
          reified_morphism_ok : untag morphism_of = ReifiedMorphismDenote reified_morphism_of
        }.
    Global Arguments ReifyMorphism [s d] morphism_of _ _.

    (* main overloaded lemma for simplification *)

    Lemma rsimplify_morphisms `(r : SimplifiedMorphism s d)
    : untag (morphism_of r) = ReifiedMorphismDenote (ReifiedMorphismSimplify (reified_morphism_of r)).
      rewrite <- ReifiedMorphismSimplifyOk.
      destruct r; assumption.
    Qed.

    (* tags to control the order of application *)


    Definition generic_tag {s d} := Tag s d.
    Definition compose_tag {s d} := @generic_tag s d.
    Definition functor_tag {s d} := @compose_tag s d.
    Definition nt_tag {s d} := @functor_tag s d.
    Canonical Structure identity_tag {s d} m := @nt_tag s d m.
  End single_category.

  (* canonical instances reifying each propositional constructor *)
  (* into a respective value from reified *)

  Local Ltac t := simpl;
                 repeat rewrite <- reified_morphism_ok;
                 reflexivity.

  Section more_single_category.
    Context `{C : Category}.

    Lemma reifyIdentity x : Identity x = ReifiedMorphismDenote (ReifiedIdentityMorphism C x). reflexivity. Qed.
    Canonical Structure reify_identity_morphism x := ReifyMorphism (identity_tag _) _ (reifyIdentity x).

    Lemma reifyCompose s d d'
          `(m1' : @SimplifiedMorphism C d d') `(m2' : @SimplifiedMorphism C s d)
    : Compose (untag (morphism_of m1')) (untag (morphism_of m2'))
      = ReifiedMorphismDenote (ReifiedComposedMorphism (reified_morphism_of m1') (reified_morphism_of m2')).
      t.
    Qed.
    Canonical Structure reify_composition_morphism s d d' m1' m2' := ReifyMorphism (compose_tag _) _ (@reifyCompose s d d' m1' m2').
  End more_single_category.

  Section functor.
    Context `{C : Category}.
    Context `{D : Category}.
    Variable F : Functor C D.

    Lemma reifyFunctor `(m' : @SimplifiedMorphism C s d)
    : MorphismOf F (untag (morphism_of m')) = ReifiedMorphismDenote (ReifiedFunctorMorphism F (reified_morphism_of m')).
      t.
    Qed.
    Canonical Structure reify_functor_morphism s d m' := ReifyMorphism (functor_tag _) _ (@reifyFunctor s d m').
  End functor.

  Section natural_transformation.
    Context `{C : Category}.
    Context `{D : Category}.
    Variables F G : Functor C D.
    Variable T : NaturalTransformation F G.

    Lemma reifyNT (x : C) : T x = ReifiedMorphismDenote (ReifiedNaturalTransformationMorphism T x). reflexivity. Qed.
    Canonical Structure reify_nt_morphism x := ReifyMorphism (nt_tag _) _ (@reifyNT x).
  End natural_transformation.
  Section generic.
    Context `{C : Category}.

    Lemma reifyGeneric s d (m : Morphism C s d) : m = ReifiedMorphismDenote (ReifiedGenericMorphism C s d m). reflexivity. Qed.
    Canonical Structure reify_generic_morphism s d m := ReifyMorphism (generic_tag m) _ (@reifyGeneric s d m).
  End generic.

End SimplifiedMorphism.

Ltac rsimplify_morphisms :=
  simpl;
  (* [refine] uses a unification algorithm compatible with
     ssreflect-style canonical structures; [apply] is not (but
     [apply:] in ssreflect is *)
  etransitivity; [ refine (rsimplify_morphisms _) | ];
  etransitivity; [ | symmetry; refine (rsimplify_morphisms _) ];
  instantiate;
  simpl.
(* Note: Using [lazy] in the above tactic makes ExponentialLaws die on
   OOM after 1-2 GB of RAM and 40 minutes. *)

(*******************************************************************************)
(**                Goals which are solved by [rsimplify_morphisms]            **)
(*******************************************************************************)
Section good_examples.
  Section id.
    Variable C : Category.
    Variable D : Category.
    Variables F G : Functor C D.
    Variable T : NaturalTransformation F G.

    Lemma good_example_00001 (x : C) :Compose (Identity x) (Identity x) = Identity (C := C) x.
      rsimplify_morphisms.
      reflexivity.
    Qed.

    Lemma good_example_00002 s d (m : Morphism C s d)
    : MorphismOf F (Compose m (Identity s)) = MorphismOf F m.
      rsimplify_morphisms.
      reflexivity.
    Qed.

    Lemma good_example_00003 s d (m : Morphism C s d)
    : MorphismOf F (Compose (Identity d) m) = MorphismOf F m.
      rsimplify_morphisms.
      reflexivity.
    Qed.
  End id.
End good_examples.


(***************************************************)
(* Confusing examples that don't quite work *)
Section bad_examples.
  Require Import SumCategory.
  Section bad_example_0001.
    Variable C0 : Category.
    Variable C1 : Category.
    Variable D : Category.

    Variables s d d' : C0.
    Variable m1 : Morphism C0 s d.
    Variable m2 : Morphism C0 d d'.
    Variable F : Functor (C0 + C1) D.

    Goal MorphismOf F (s := inl _) (d := inl _) (Compose m2 m1) = Compose (MorphismOf F (s := inl _) (d := inl _) m2) (MorphismOf F (s := inl _) (d := inl _) m1).
    simpl in *.
    etransitivity; [ refine (rsimplify_morphisms _) | ].
    Fail reflexivity.
    Abort.
  End bad_example_0001.
End bad_examples.
