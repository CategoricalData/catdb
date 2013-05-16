Require Import SpecializedCategory Functor NaturalTransformation.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section SimplifiedMorphism.
  Inductive ReifiedMorphism : forall objC (C : SpecializedCategory objC), C -> C -> Type :=
  | ReifiedIdentityMorphism : forall objC C x, @ReifiedMorphism objC C x x
  | ReifiedComposedMorphism : forall objC C s d d', ReifiedMorphism C d d' -> ReifiedMorphism C s d -> @ReifiedMorphism objC C s d'
  | ReifiedNaturalTransformationMorphism : forall objB (B : SpecializedCategory objB)
                                                  objC (C : SpecializedCategory objC)
                                                  (F G : SpecializedFunctor B C)
                                                  (T : SpecializedNaturalTransformation F G)
                                                  x,
                                             ReifiedMorphism C (F x) (G x)
  | ReifiedFunctorMorphism : forall objB (B : SpecializedCategory objB)
                                    objC (C : SpecializedCategory objC)
                                    (F : SpecializedFunctor B C)
                                    s d,
                               @ReifiedMorphism objB B s d -> @ReifiedMorphism objC C (F s) (F d)
  | ReifiedGenericMorphism : forall objC (C : SpecializedCategory objC) s d, Morphism C s d -> @ReifiedMorphism objC C s d.

  Fixpoint ReifiedMorphismSimplify objC C s d (m : @ReifiedMorphism objC C s d) : ReifiedMorphism C s d
    := match
        m in (ReifiedMorphism C s d) return (ReifiedMorphism C s d)
      with
        | ReifiedComposedMorphism _ _ _ _ _ m1 m2 =>
          match
            ReifiedMorphismSimplify m1
            in (ReifiedMorphism C d d')
            return
            (forall s,
               ReifiedMorphism C s d -> ReifiedMorphism C s d')
          with
            | ReifiedIdentityMorphism _ _ _ => fun _ m2' => m2'
            | m1' => fun _ m2' => match m2'
                                        in (ReifiedMorphism C s d)
                                        return (forall d',
                                                  ReifiedMorphism C d d' -> ReifiedMorphism C s d')
                                  with
                                    | ReifiedIdentityMorphism _ _ _ => fun _ m1'' => m1''
                                    | m2'' => fun _ m1'' => ReifiedComposedMorphism m1'' m2''
                                  end _ m1'
          end _ (ReifiedMorphismSimplify m2)
        | ReifiedFunctorMorphism objB B objC0 C0 F s0 d0 m0 =>
          match
            ReifiedMorphismSimplify m0
            in (ReifiedMorphism C1 o o0)
            return
            (forall F0 : SpecializedFunctor C1 C0,
               ReifiedMorphism C0 (F0 o) (F0 o0))
          with
            | ReifiedIdentityMorphism _ _ x =>
              fun F0 => ReifiedIdentityMorphism _ (F0 x)
            | ReifiedComposedMorphism _ _ _ _ _ m11 m12 =>
              fun F0 =>
                ReifiedComposedMorphism (ReifiedFunctorMorphism F0 m11)
                                        (ReifiedFunctorMorphism F0 m12)
            | m' =>
              fun F0 =>
                ReifiedFunctorMorphism F0 m'
          end F
        | m' => m'
  end.

  Fixpoint ReifiedMorphismDenote objC C s d (m : @ReifiedMorphism objC C s d) : Morphism C s d :=
    match m in @ReifiedMorphism objC C s d return Morphism C s d with
      | ReifiedIdentityMorphism _ _ x => Identity x
      | ReifiedComposedMorphism _ _ _ _ _ m1 m2 => Compose (@ReifiedMorphismDenote _ _ _ _ m1)
                                                           (@ReifiedMorphismDenote _ _ _ _ m2)
      | ReifiedNaturalTransformationMorphism _ _ _ _ _ _ T x => T x
      | ReifiedFunctorMorphism _ _ _ _ F _ _ m => MorphismOf F (@ReifiedMorphismDenote _ _ _ _ m)
      | ReifiedGenericMorphism _ _ _ _ m => m
    end.

  Local Ltac ok_fin_t :=
    simpl;
    repeat rewrite Associativity;
    repeat rewrite FCompositionOf;
    autorewrite with category;
    try reflexivity.

  Lemma ReifiedMorphismSimplifyOk objC C s d (m : @ReifiedMorphism objC C s d)
  : ReifiedMorphismDenote m =
    ReifiedMorphismDenote (ReifiedMorphismSimplify m).
    induction m;
    repeat match goal with
             | _ => progress ok_fin_t
             | [ IH : ReifiedMorphismDenote _ = _ |- _ ] => rewrite IH; clear IH
             | [ |- context[ReifiedMorphismSimplify ?m] ] =>
               let H := fresh in
               set (H := ReifiedMorphismSimplify m);
                 clearbody H;
                 destruct H
             | [ |- context[match ReifiedMorphismSimplify ?m with _ => _ end _ ?m'] ] =>
               (* simply destructing H didn't work, so we need to be more tricky *)
               let H := fresh in
               set (H := ReifiedMorphismSimplify m);
                 clearbody H;
                 match type of H with
                   | ReifiedMorphism _ ?A ?B =>
                     let FH := fresh in
                     let H2 := fresh in
                     (* save the troublesome term, so we can [clearbody] it *)
                     set (FH := m');
                       let FH' := (eval simpl in (ReifiedMorphismDenote FH)) in
                       (* save the value of the term *)
                       assert (H2 : ReifiedMorphismDenote FH = FH') by reflexivity;
                         (* the denoted version shows up, so rewrite with it *)
                         rewrite <- H2;
                         clear H2;
                         clearbody FH;
                         simpl in *;
                         set (A' := A) in *;
                         set (B' := B) in *;
                         clearbody A' B';
                         destruct H
                 end
           end.
  Qed.

  Section single_category.
    Context `{C : SpecializedCategory objC}.

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
    Context `{C : SpecializedCategory objC}.

    Lemma reifyIdentity x : Identity x = ReifiedMorphismDenote (ReifiedIdentityMorphism C x). reflexivity. Qed.
    Canonical Structure reify_identity_morphism x := ReifyMorphism (identity_tag _) _ (reifyIdentity x).

    Lemma reifyCompose s d d'
          `(m1' : @SimplifiedMorphism objC C d d') `(m2' : @SimplifiedMorphism objC C s d)
    : Compose (untag (morphism_of m1')) (untag (morphism_of m2'))
      = ReifiedMorphismDenote (ReifiedComposedMorphism (reified_morphism_of m1') (reified_morphism_of m2')).
      t.
    Qed.
    Canonical Structure reify_composition_morphism s d d' m1' m2' := ReifyMorphism (compose_tag _) _ (@reifyCompose s d d' m1' m2').
  End more_single_category.

  Section functor.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.
    Variable F : SpecializedFunctor C D.

    Lemma reifyFunctor `(m' : @SimplifiedMorphism objC C s d)
    : MorphismOf F (untag (morphism_of m')) = ReifiedMorphismDenote (ReifiedFunctorMorphism F (reified_morphism_of m')).
      t.
    Qed.
    Canonical Structure reify_functor_morphism s d m' := ReifyMorphism (functor_tag _) _ (@reifyFunctor s d m').
  End functor.

  Section natural_transformation.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.
    Variables F G : SpecializedFunctor C D.
    Variable T : SpecializedNaturalTransformation F G.

    Lemma reifyNT (x : C) : T x = ReifiedMorphismDenote (ReifiedNaturalTransformationMorphism T x). reflexivity. Qed.
    Canonical Structure reify_nt_morphism x := ReifyMorphism (nt_tag _) _ (@reifyNT x).
  End natural_transformation.
  Section generic.
    Context `{C : SpecializedCategory objC}.

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

(***************************************************)
(* Confusing examples that don't quite work *)
Section bad_examples.
  Require Import SumCategory.
  Context `(C0 : SpecializedCategory objC0).
  Context `(C1 : SpecializedCategory objC1).
  Context `(D : SpecializedCategory objD).

  Variables s d d' : C0.
  Variable m1 : Morphism C0 s d.
  Variable m2 : Morphism C0 d d'.
  Variable F : SpecializedFunctor (C0 + C1) D.

  Goal MorphismOf F (s := inl _) (d := inl _) (Compose m2 m1) = Compose (MorphismOf F (s := inl _) (d := inl _) m2) (MorphismOf F (s := inl _) (d := inl _) m1).
  simpl in *.
  etransitivity; [ refine (rsimplify_morphisms _) | ].
  Abort.
End bad_examples.
