Require Export LimitFunctorTheorems LaxCommaCategory.
Require Import Common DefinitionSimplification Category Functor NaturalTransformation Duals CanonicalStructureSimplification.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section InducedFunctor.
  (* The components of the functor can be useful even if we don't have
     a category that we're coming from.  So prove them separately, so
     we can use them elsewhere, without assuming a full [HasLimits]. *)
  Variable I : Type.
  Variable Index2Cat : I -> Category.

  Local Coercion Index2Cat : I >-> Category.

  Local Notation "'CAT' ⇑ D" := (@LaxCosliceCategory _ Index2Cat D).
  Local Notation "'CAT' ⇓ D" := (@LaxSliceCategory _ Index2Cat D).

  Variable D : Category.
  Let DOp := OppositeCategory D.

  Section Limit.
    Definition InducedLimitFunctor_MorphismOf (s d : CAT ⇑ D) (limS : Limit (projT2 s)) (limD : Limit (projT2 d))
      (m : Morphism (CAT ⇑ D) s d) :
      Morphism D (LimitObject limS) (LimitObject limD)
      := InducedLimitMap (projT2 m) _ _.

    Lemma InducedLimitFunctor_FCompositionOf (s d d' : CAT ⇑ D) (limS : Limit (projT2 s)) (limD : Limit (projT2 d)) (limD' : Limit (projT2 d'))
      (m1 : Morphism _ s d) (m2 : Morphism _ d d') :
      InducedLimitFunctor_MorphismOf limS limD' (Compose m2 m1) =
      Compose (InducedLimitFunctor_MorphismOf limD limD' m2) (InducedLimitFunctor_MorphismOf limS limD m1).
    Proof.
      unfold InducedLimitFunctor_MorphismOf.
      unfold InducedLimitMap at 1; cbv zeta.
      match goal with
        | [ |- TerminalProperty_Morphism ?a ?b ?c = _ ] => apply (proj2 (TerminalProperty a b c))
      end (* 3 s *).
      nt_eq (* 4 s *).
      rsimplify_morphisms (* 11 s *).
      repeat rewrite Associativity (* 3 s *).
      match goal with
        | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
          eapply (@eq_trans _ _ (Compose a' (Compose _ c)) _);
            try_associativity ltac:(apply f_equal2; try reflexivity)
      end (* 13 s *);
      unfold InducedLimitMap;
      match goal with
        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] =>
          let H := constr:(TerminalProperty a) in
            let H' := fresh in
              pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                simpl in H';
                  unfold Object, Morphism in *;
                    simpl in *;
                      rewrite H';
                        clear H'
      end (* 7 s *);
      simpl;
      rsimplify_morphisms;
      reflexivity (* 6 s since [simpl] *).
    Qed.

    Lemma InducedLimitFunctor_FIdentityOf (x : CAT ⇑ D) (limX : Limit (projT2 x)) :
      InducedLimitFunctor_MorphismOf limX limX (Identity x) =
      Identity (LimitObject limX).
    Proof.
      unfold InducedLimitFunctor_MorphismOf.
      unfold InducedLimitMap at 1; cbv zeta.
      match goal with
        | [ |- TerminalProperty_Morphism ?a ?b ?c = _ ] => apply (proj2 (TerminalProperty a b c))
      end (* 3 s *).
      nt_eq (* 4 s *).
      rsimplify_morphisms;
      reflexivity. (* 2 s *)
    Qed.

    Variable HasLimits : forall C : CAT ⇑ D, Limit (projT2 C).

    Hint Resolve InducedLimitFunctor_FCompositionOf InducedLimitFunctor_FIdentityOf.

    Definition InducedLimitFunctor : Functor (CAT ⇑ D) D.
      match goal with
        | [ |- Functor ?C ?D ] =>
          refine (Build_Functor C D
            (fun x => LimitObject (HasLimits x))
            (fun s d => @InducedLimitFunctor_MorphismOf s d (HasLimits s) (HasLimits d))
            _
            _
          )
      end;
      abstract trivial.
    Defined.
  End Limit.

  Section Colimit.
    Definition InducedColimitFunctor_MorphismOf (s d : CAT ⇓ D) (colimS : Colimit (projT2 s)) (colimD : Colimit (projT2 d))
      (m : Morphism (CAT ⇓ D) s d) :
      Morphism D (ColimitObject colimS) (ColimitObject colimD)
      := InducedColimitMap (projT2 m) _ _.

    Lemma InducedColimitFunctor_FCompositionOf (s d d' : CAT ⇓ D) (colimS : Colimit (projT2 s)) (colimD : Colimit (projT2 d)) (colimD' : Colimit (projT2 d'))
      (m1 : Morphism _ s d) (m2 : Morphism _ d d') :
      InducedColimitFunctor_MorphismOf colimS colimD' (Compose m2 m1) =
      Compose (InducedColimitFunctor_MorphismOf colimD colimD' m2) (InducedColimitFunctor_MorphismOf colimS colimD m1).
    Proof.
      unfold InducedColimitFunctor_MorphismOf.
      unfold InducedColimitMap at 1; cbv zeta.
      match goal with
        | [ |- InitialProperty_Morphism ?a ?b ?c = _ ] => apply (proj2 (InitialProperty a b c))
      end (* 3 s *).
      nt_eq (* 4 s *).
      rsimplify_morphisms (* 8 s *).
      repeat rewrite Associativity (* 3 s *).
      match goal with
        | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
          symmetry; eapply (@eq_trans _ _ (Compose a (Compose _ c')) _);
            try_associativity ltac:(apply f_equal2; try reflexivity)
      end (* 13 s *);
      unfold InducedColimitMap;
      match goal with
        | [ |- appcontext[InitialProperty_Morphism ?a ?b ?c] ] =>
          let H := constr:(InitialProperty a) in
            let H' := fresh in
              pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                simpl in H';
                  unfold Object in *;
                    simpl in *;
                      try (rewrite H'; clear H')
      end (* 7 s *);
      simpl;
      rsimplify_morphisms;
      reflexivity (* 4 s since [simpl] *).
    Qed.

    Lemma InducedColimitFunctor_FIdentityOf (x : CAT ⇓ D) (colimX : Colimit (projT2 x)) :
      InducedColimitFunctor_MorphismOf colimX colimX (Identity x) =
      Identity (ColimitObject colimX).
    Proof.
      unfold InducedColimitFunctor_MorphismOf.
      unfold InducedColimitMap at 1; cbv zeta.
      match goal with
        | [ |- InitialProperty_Morphism ?a ?b ?c = _ ] => apply (proj2 (InitialProperty a b c))
      end (* 3 s *).
      nt_eq (* 4 s *).
      rsimplify_morphisms. (* 1.5 s *)
      reflexivity.
    Qed.

    Variable HasColimits : forall C : CAT ⇓ D, Colimit (projT2 C).

    Hint Resolve InducedColimitFunctor_FCompositionOf InducedColimitFunctor_FIdentityOf.

    Definition InducedColimitFunctor : Functor (CAT ⇓ D) D.
      match goal with
        | [ |- Functor ?C ?D ] =>
          refine (Build_Functor C D
            (fun x => ColimitObject (HasColimits x))
            (fun s d => @InducedColimitFunctor_MorphismOf s d (HasColimits s) (HasColimits d))
            _
            _
          )
      end;
      abstract trivial.
    Defined.
  End Colimit.
End InducedFunctor.
