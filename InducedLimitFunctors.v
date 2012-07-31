Require Export LimitFunctorTheorems SpecializedLaxCommaCategory.
Require Import Common DefinitionSimplification SpecializedCategory Functor NaturalTransformation Duals.

Set Implicit Arguments.

Generalizable All Variables.

Section InducedFunctor.
  Local Transparent Object Morphism.

  Variable I : Type.
  Variable Index2Object : I -> Type.
  Variable Index2Morphism : forall i : I, Index2Object i -> Index2Object i -> Type.
  Variable Index2Cat : forall i : I, SpecializedCategory (@Index2Morphism i).

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Local Notation "'Cat' ⇑ D" := (@LaxCosliceSpecializedCategory _ _ _ Index2Cat _ _ D) (at level 70, no associativity).
  Local Notation "'Cat' ⇓ D" := (@LaxSliceSpecializedCategory _ _ _ Index2Cat _ _ D) (at level 70, no associativity).

  Context `(D : @SpecializedCategory objD morD).
  Let DOp := OppositeCategory D.

  Section Limit.
    Variable HasLimits : forall C : Cat ⇑ D, Limit (projT2 C).

    Let lim (x : Cat ⇑ D) : D
      := LimitObject (HasLimits x).

    Definition InducedLimitFunctor_MorphismOf' (s d : Cat ⇑ D) (m : Morphism _ s d) : Morphism D (lim s) (lim d).
      subst_body; hnf in * |- ; simpl in *.
(*      hnf; change morD with (Morphism D). *)
      apply (InducedLimitMap (G := projT1 m)).
      exact (projT2 m).
    Defined.

    Definition InducedLimitFunctor_MorphismOf'' (s d : Cat ⇑ D) (m : Morphism _ s d) : Morphism D (lim s) (lim d).
      simpl_definition_by_tac_and_exact (@InducedLimitFunctor_MorphismOf' s d m) ltac:(unfold InducedLimitFunctor_MorphismOf' in *).
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedLimitFunctor_MorphismOf (s d : Cat ⇑ D) (m : Morphism _ s d) : Morphism D (lim s) (lim d)
      := Eval cbv beta iota zeta delta [InducedLimitFunctor_MorphismOf''] in @InducedLimitFunctor_MorphismOf'' s d m.

    Definition InducedLimitFunctor : SpecializedFunctor (Cat ⇑ D) D.
      refine {| ObjectOf' := lim;
        MorphismOf' := @InducedLimitFunctor_MorphismOf
      |};
      intros; unfold InducedLimitFunctor_MorphismOf; subst_body;
        abstract (
          present_spcategory;
          unfold InducedLimitMap;
            simpl;
              match goal with
                | [ |- TerminalProperty_Morphism ?a ?b ?c = _ ] => apply (proj2 (TerminalProperty a b c))
              end (* 9 s *);
              nt_eq (* 5 s *);
              repeat rewrite FIdentityOf;
                repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                  try reflexivity;
                    repeat rewrite Associativity; (* 27 s for this past block *)
                      match goal with
                        | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
                          eapply (@eq_trans _ _ (Compose a' (Compose _ c)) _);
                            try_associativity ltac:(apply f_equal2; try reflexivity)
                      end;
                      match goal with
                        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] =>
                          let H := constr:(TerminalProperty a) in
                            let H' := fresh in
                              pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                                simpl in H';
                                  unfold Object, Morphism in *;
                                    simpl in *;
                                      rewrite H'
                      end;
                      simpl;
                        repeat rewrite FIdentityOf;
                          repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                            reflexivity (* 8 s *)
        ).
    Defined.
  End Limit.

  Section Colimit.
    Variable HasColimits : forall C : Cat ⇓ D, Colimit (projT2 C).

    Let colim (x : Cat ⇓ D) : D
      := ColimitObject (HasColimits x).

    Definition InducedColimitFunctor_MorphismOf' (s d : Cat ⇓ D) (m : Morphism _ s d) : Morphism D (colim s) (colim d).
      subst_body; hnf in * |- ; simpl in *.
(*      hnf; change morD with (Morphism D). *)
      apply (InducedColimitMap (G := projT1 m)).
      exact (projT2 m).
    Defined.

    Definition InducedColimitFunctor_MorphismOf'' (s d : Cat ⇓ D) (m : Morphism _ s d) : Morphism D (colim s) (colim d).
      simpl_definition_by_tac_and_exact (@InducedColimitFunctor_MorphismOf' s d m) ltac:(unfold InducedColimitFunctor_MorphismOf' in *).
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedColimitFunctor_MorphismOf (s d : Cat ⇓ D) (m : Morphism _ s d) : Morphism D (colim s) (colim d)
      := Eval cbv beta iota zeta delta [InducedColimitFunctor_MorphismOf''] in @InducedColimitFunctor_MorphismOf'' s d m.

    Definition InducedColimitFunctor : SpecializedFunctor (Cat ⇓ D) D.
      refine {| ObjectOf' := colim;
        MorphismOf' := @InducedColimitFunctor_MorphismOf
      |};
      intros; unfold InducedColimitFunctor_MorphismOf; subst_body;
        abstract (
          present_spcategory;
          unfold InducedColimitMap;
            simpl;
              match goal with
                | [ |- InitialProperty_Morphism ?a ?b ?c = _ ] => apply (proj2 (InitialProperty a b c))
              end (* 2 s *);
              nt_eq (* 4 s *);
              repeat rewrite FIdentityOf;
                repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                  try reflexivity;
                    repeat rewrite Associativity (* 19 s for this past block *);
                      match goal with
                        | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
                          symmetry; eapply (@eq_trans _ _ (Compose a (Compose _ c')) _);
                            try_associativity ltac:(apply f_equal2; try reflexivity)
                      end (* 36 s *);
                      match goal with
                        | [ |- appcontext[InitialProperty_Morphism ?a ?b ?c] ] =>
                          let H := constr:(InitialProperty a) in
                            let H' := fresh in
                              pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                                simpl in H';
                                  unfold Object, Morphism in *;
                                    simpl in *;
                                      rewrite H'
                      end (* 2 s *);
                      simpl;
                        repeat rewrite FIdentityOf;
                          repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                            reflexivity (* 8 s *)
      ).
    Defined.
  End Colimit.
End InducedFunctor.
