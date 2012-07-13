Require Import FunctionalExtensionality.
Require Export Limits.
Require Import Common NaturalTransformation SmallNaturalTransformation FunctorCategory Adjoint AdjointUnit DefinitionSimplification.

Set Implicit Arguments.

Local Notation "C ^ D" := (FunctorCategory D C).

Section HasLimits.
  Variable C : Category.

  Definition HasLimits' (D : SmallCategory) := forall F : Functor D C, exists _ : Limit F, True.
  Definition HasLimits (D : SmallCategory) := forall F : Functor D C, Limit F.

  Definition HasColimits' (D : SmallCategory) := forall F : Functor D C, exists _ : Colimit F, True.
  Definition HasColimits (D : SmallCategory) := forall F : Functor D C, Colimit F.
End HasLimits.

Section LimitFunctors.
  Variable C : Category.
  Variable D : SmallCategory.

  Hypothesis HL : HasLimits C D.
  Hypothesis HC : HasColimits C D.

  Let LimitOf (F : @Object (C ^ D)) := LimitObject (HL F).
  Let ColimitOf (F : @Object (C ^ D)) := ColimitObject (HC F).

  Ltac define_limit_morphism' :=
    clear HL HC;
      intros;
        match goal with
          | [ |- Morphism _ ?a ?b ] => pose a; pose b
        end;
        unfold Colimit, ColimitObject, Limit, LimitObject in *;
          intro_universal_morphisms;
          intro_universal_property_morphisms;
          simpl in *;
            repeat match goal with
                     | [ m : _, t : _ |- _ ] => unique_pose (SNTComposeT m t)
                   end;
            specialized_assumption idtac.

  (* TODO: Perhaps there is a better way to define this, or a more automated way to define this. *)
  Definition LimitFunctor_morphism_of' (F G : @Object (C ^ D)) (m : Morphism (C ^ D) F G) : Morphism C (LimitOf F) (LimitOf G).
    subst LimitOf ColimitOf.
    simpl in *.
    generalize (HL G) (HL F).
    define_limit_morphism'.
  Defined.

  Definition ColimitFunctor_morphism_of' (F G : @Object (C ^ D)) (m : Morphism (C ^ D) F G) : Morphism C (ColimitOf F) (ColimitOf G).
    subst LimitOf ColimitOf.
    simpl in *.
    generalize (HC G) (HC F).
    define_limit_morphism'.
  Defined.

  Definition LimitFunctor_morphism_of'' (F G : @Object (C ^ D)) (m : Morphism (C ^ D) F G) : Morphism C (LimitOf F) (LimitOf G).
    simpl_definition_by_tac_and_exact (LimitFunctor_morphism_of' m) ltac:( unfold LimitFunctor_morphism_of', LimitOf in * ).
  Defined.

  Definition ColimitFunctor_morphism_of'' (F G : @Object (C ^ D)) (m : Morphism (C ^ D) F G) : Morphism C (ColimitOf F) (ColimitOf G).
    simpl_definition_by_tac_and_exact (ColimitFunctor_morphism_of' m) ltac:( unfold ColimitFunctor_morphism_of', ColimitOf in * ).
  Defined.

  (* Then we clean up a bit with reduction. *)
  Let LimitFunctor_morphism_of := Eval cbv beta iota zeta delta [LimitFunctor_morphism_of''] in LimitFunctor_morphism_of''.
  Let ColimitFunctor_morphism_of := Eval cbv beta iota zeta delta [ColimitFunctor_morphism_of''] in ColimitFunctor_morphism_of''.

  (* XXX TODO: Automate this better *)
  Definition LimitFunctor' : Functor (C ^ D) C.
    refine {| ObjectOf := LimitOf;
      MorphismOf := LimitFunctor_morphism_of
    |};
(*    abstract ( *)
      subst LimitOf ColimitOf LimitFunctor_morphism_of ColimitFunctor_morphism_of;
        simpl; intros; autorewrite with core;
          repeat match goal with
                   | [ |- context[HL ?o] ] => generalize (HL o); intro
                 end;
          clear HL HC;
            unfold Limit, LimitObject, Colimit, ColimitObject in *;
              match goal with
                | [ |- TerminalProperty_Morphism ?l0 ?Y ?f = _ ] => let H := fresh in pose (proj2 (TerminalProperty l0 Y f)) as H; simpl in H; apply H; clear H
              end;
              try simpl_do_clear do_rewrite (DiagonalFunctor C D).(FCompositionOf);
                snt_eq;
                try solve [
                  autorewrite with core;
                    try reflexivity
                ];
                repeat rewrite Associativity. (*
    rename s into F0. rename d into G0.  rename d' into H0.
    rename l into F.
    rename l0 into H.
    rename l1 into G.
    Definition Δ {C D} := diagonal_functor_object_of C D.
    Definition ΔMor {C D} o1 o2 := diagonal_functor_morphism_of C D o1 o2.
    Definition limo := TerminalMorphism_Object.
    Definition φ := TerminalMorphism_Morphism.
    Definition unique_m C a b c d := @TerminalProperty_Morphism C a b c d.
    change (diagonal_functor_morphism_of C D) with (@ΔMor C D) in *;
    change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor C D) in *;
    change (ObjectOf (DiagonalFunctor C D)) with (@Δ C D) in *;
    change TerminalMorphism_Object with limo in *;
    change TerminalMorphism_Morphism with φ in *;
    change TerminalProperty_Morphism with unique_m in *. *)
                  match goal with
                    | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
                      eapply (@eq_trans _ _ (Compose a' (Compose _ c)) _);
                        try_associativity_no_evar ltac:(apply f_equal2; try reflexivity)
                  end;
                  intro_universal_properties;
                  unfold unique in *;
                    split_and;
                    repeat match goal with
                             | [ H : forall Y f, @?a Y f = @?b Y f |- _ ] =>
                               let H' := fresh in assert (H' : forall x Y f, a Y f x = b Y f x) by (
                                 let Y := fresh in let H := fresh in intros ? Y f; f_equal; apply (H Y f)
                               ); clear H
                           end;
                    simpl in *;
                      etransitivity; solve [ t_with t' ].
(*    ). *)
(*    rename s into F0. rename d into G0.  rename d' into H0.
    rename l into F.
    rename l0 into H.
    rename l1 into G.
    Definition Δ {C D} := diagonal_functor_object_of C D.
    Definition ΔMor {C D} o1 o2 := diagonal_functor_morphism_of C D o1 o2.
    Definition limo := TerminalMorphism_Object.
    Definition φ := TerminalMorphism_Morphism.
    Definition unique_m C a b c d := @TerminalProperty_Morphism C a b c d.
    change (diagonal_functor_morphism_of C D) with (@ΔMor C D) in *;
    change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor C D) in *;
    change (ObjectOf (DiagonalFunctor C D)) with (@Δ C D) in *;
    change TerminalMorphism_Object with limo in *;
    change TerminalMorphism_Morphism with φ in *;
    change TerminalProperty_Morphism with unique_m in *.*)
  Defined.

  Definition ColimitFunctor' : Functor (C ^ D) C.
    refine {| ObjectOf := ColimitOf;
      MorphismOf := ColimitFunctor_morphism_of
      |};(* abstract ( *)
      subst LimitOf ColimitOf LimitFunctor_morphism_of ColimitFunctor_morphism_of;
        simpl; intros; autorewrite with core;
          repeat match goal with
                   | [ |- context[HC ?o] ] => generalize (HC o); intro
                 end;
          clear HL HC;
            unfold Limit, LimitObject, Colimit, ColimitObject in *;
              match goal with
                | [ |- InitialProperty_Morphism ?l0 ?Y ?f = _ ] => let H := fresh in pose (proj2 (InitialProperty l0 Y f)) as H; simpl in H; apply H; clear H
              end;
              try solve [
                snt_eq;
                autorewrite with core;
                  try reflexivity
              ].
              simpl_do_clear do_rewrite (DiagonalFunctor C D).(FCompositionOf).
              snt_eq.
                repeat rewrite Associativity.
                rename s into F0. rename d into G0.  rename d' into H0.
    rename c into F.
    rename c0 into H.
    rename c1 into G.
                  intro_universal_properties.
    Definition Δ {C D} := diagonal_functor_object_of C D.
    Definition ΔMor {C D} o1 o2 := diagonal_functor_morphism_of C D o1 o2.
    Definition colimo := InitialMorphism_Object.
    Definition φ := InitialMorphism_Morphism.
    Definition unique_m C {a b c d} := @InitialProperty_Morphism C a b c d.
    change (diagonal_functor_morphism_of C D) with (@ΔMor C D) in *;
    change InitialMorphism_Object with colimo in *;
    change InitialMorphism_Morphism with φ in *;
    change InitialProperty_Morphism with unique_m.
                  unfold ΔMor, colimo, φ, unique_m.
    change (diagonal_functor_morphism_of C D) with (@ΔMor C D) in *;
    change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor C D) in *;
    change (ObjectOf (DiagonalFunctor C D)) with (@Δ C D) in *;
    change InitialMorphism_Object with colimo in *;
    change InitialMorphism_Morphism with φ in *;
    change InitialProperty_Morphism with unique_m in *;
                  unfold unique in *;
                    split_and;
                    repeat match goal with
                             | [ H : forall Y f, @?a Y f = @?b Y f |- _ ] =>
                               let H' := fresh in assert (H' : forall x Y f, a Y f x = b Y f x) by (
                                 let Y := fresh in let H := fresh in intros ? Y f; f_equal; apply (H Y f)
                               ); clear H
                           end;
                    simpl in *.
    transitivity (Compose (unique_m (colimo H) (SNTComposeT (φ H) m2)) (Compose

   Compose ((φ H) x)
     (Compose (unique_m H (limo G) (SNTComposeT m2 (φ G)))
        (unique_m G (limo F) (SNTComposeT m1 (φ F)))) =
   Compose (m2 x) (Compose (m1 x) ((φ F) x))

                  match goal with
                    | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
                      eapply (@eq_trans _ _ (Compose a' (Compose _ c)) _);
                        try_associativity_no_evar ltac:(apply f_equal2; try reflexivity)
                  end.
                  etrans


 try apply H2.
                    clear H0 H8.
                    match goal with
                      | [ H : context[ (InitialMorphism_Morphism c0)] |- _] => idtac H; let T := type of H in idtac T
                    end.
                    symmetry; etransitivity. simpl in *.
                    clear H1.
                    specialize (H0 x).
                    apply functional_extensionality_dep.
Set Printing Allapply H0.
                      etransitivity; solve [ t_with t' ].

        unfold ColimitFunctor_morphism_of; subst LimitOf ColimitOf; simpl; intros;
          try rewrite LeftIdentityNaturalTransformation;
            match goal with
              | [ |- projT1 ?x = _ ] => let H := fresh in pose (proj1 (projT2 x)) as H; simpl in H; apply H || symmetry; apply H
            end
      ).
  Defined.
End LimitFunctors.

Definition LimitFunctor := Eval cbv beta iota zeta delta [LimitFunctor'(* LimitFunctor_morphism_of*)] in LimitFunctor'.
Definition ColimitFunctor := Eval cbv beta iota zeta delta [ColimitFunctor'(* ColimitFunctor_morphism_of*)] in ColimitFunctor'.

Section Adjoint.
  Variable C : Category.
  Variable D : SmallCategory.
  Hypothesis HL : HasLimits C D.
  Hypothesis HC : HasColimits C D.

  Let LimitAdjunction_AComponentsOf (c : C) (F : C ^ D)
    : Morphism _ (Hom.HomFunctor _ ((DiagonalFunctor C D) c, F)) (Hom.HomFunctor _ (c, (LimitFunctor HL) F))
    := (fun T : Hom.HomFunctor (C ^ D) ((DiagonalFunctor C D) c, F)
      => proj1_sig (projT2 (projT2 (HL F)) c T) : Hom.HomFunctor C (c, (LimitFunctor HL) F)).

  Definition LimitAdjunction_AComponentsOf_Inverse (c : C) (F : C ^ D)
    : Morphism _ (Hom.HomFunctor _ (c, (LimitFunctor HL) F)) (Hom.HomFunctor _ ((DiagonalFunctor C D) c, F)).
    simpl in *; intro f.
    match goal with
      | [ |- SmallNaturalTransformation ?DF ?F ] =>
        eapply (Build_SmallNaturalTransformation DF F
          (fun d => Compose (projT1 (projT2 (HL F)) d) f)
          _
        )
    end.
    Grab Existential Variables.
    abstract (
      simpl in *; intros; rewrite RightIdentity;
        try_associativity ltac:(apply f_equal2; try reflexivity);
        match goal with
          | [ |- SComponentsOf ?T ?d = Compose _ _ ] => simpl_do do_rewrite_rev (SCommutes T)
        end;
        rewrite RightIdentity;
          reflexivity
    ).
  Defined.

  Definition LimitAdjunction_AIsomorphism (c : C) (F : C ^ D) : CategoryIsomorphism (@LimitAdjunction_AComponentsOf c F).
    exists (LimitAdjunction_AComponentsOf_Inverse _ _).
    abstract (
      subst LimitAdjunction_AComponentsOf; unfold LimitAdjunction_AComponentsOf_Inverse;
        split; simpl in *;
          snt_eq;
          intro_proj2_sig_from_goal; simpl;
            destruct_hypotheses;
            try rewrite_unique;
              intro_fresh_unique;
              t_rev_with t'
    ).
  Defined.

  Definition LimitAdjunction : Adjunction (DiagonalFunctor C D) (LimitFunctor HL).
    refine {| AComponentsOf := LimitAdjunction_AComponentsOf;
      AIsomorphism := LimitAdjunction_AIsomorphism
    |}; abstract (
      intros; simpl in *;
        snt_eq;
        unfold LimitAdjunction_AComponentsOf;
          match goal with
            | [ |- proj1_sig ?x = _ ] => let H := fresh in pose (proj1 (proj2_sig x)) as H; simpl in H; apply H || symmetry; apply H
          end
    ).
  Defined.

  Definition ColimitAdjunction : Adjunction (ColimitFunctor HC) (DiagonalFunctor C D).
    refine {| AComponentsOf := (fun (F : C ^ D) (c : C)
      => fun f : Hom.HomFunctor C (ColimitFunctor HC F, c)
        => Build_SmallNaturalTransformation F (diagonal_functor_object_of C D c)
        (fun d => Compose f (projT1 (projT2 (HC F)) d))
        _
        : Hom.HomFunctor (C ^ D) (F, DiagonalFunctor C D c)
    ) |}; try (
      intros F c; eexists (fun (T : SmallNaturalTransformation F (DiagonalFunctor C D c))
        => proj1_sig (projT2 (projT2 (HC F)) c T)
      )
    );
    intros; repeat split; simpl in *;
      try snt_eq;
        repeat try_associativity ltac:(apply f_equal2; try reflexivity);
          unfold ColimitFunctor_morphism_of;
            intro_proj2_sig_from_goal;
            intro_projT2_from_goal;
            simpl in *; destruct_hypotheses;
              try rewrite_unique;
                intro_fresh_unique;
                t_rev_with t';
                match goal with
                  | [ H : ?a = ?b |- _ ] => assert (forall x, a x = b x) by (rewrite H || rewrite <- H; reflexivity)
                end;
                simpl in *; t_with t'.
    Grab Existential Variables.
    abstract (
      intros; simpl in *; auto; autorewrite with core; simpl;
        try_associativity ltac:(apply f_equal2; try reflexivity);
        match goal with
          | [ |- Compose _ _ = SComponentsOf ?T ?d ] => simpl_do do_rewrite (SCommutes T)
        end;
        autorewrite with core; reflexivity
    ).
  Defined.
End Adjoint.
