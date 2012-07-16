Require Import FunctionalExtensionality.
Require Export Limits.
Require Import Common DefinitionSimplification NaturalTransformation SmallNaturalTransformation FunctorCategory Adjoint Hom SetCategory Duals ProductFunctor.

Set Implicit Arguments.

Local Notation "C ^ D" := (FunctorCategory D C).

Section HasLimits.
  Variable C : Category.
  Variable D : SmallCategory.

  Definition HasLimits' := forall F : Functor D C, exists _ : Limit F, True.
  Definition HasLimits := forall F : Functor D C, Limit F.

  Definition HasColimits' := forall F : Functor D C, exists _ : Colimit F, True.
  Definition HasColimits := forall F : Functor D C, Colimit F.
End HasLimits.

Section LimitFunctors.
  Variable C : Category.
  Variable D : SmallCategory.

  Hypothesis HL : HasLimits C D.
  Hypothesis HC : HasColimits C D.

  Let LimitOf (F : C ^ D) := LimitObject (HL F).
  Let ColimitOf (F : C ^ D) := ColimitObject (HC F).

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
  Definition LimitFunctor_morphism_of' (F G : C ^ D) (m : (C ^ D).(Morphism) F G) : C.(Morphism) (LimitOf F) (LimitOf G).
    subst LimitOf ColimitOf.
    simpl in *.
    generalize (HL G) (HL F).
    define_limit_morphism'.
  Defined.

  Definition ColimitFunctor_morphism_of' (F G : C ^ D) (m : (C ^ D).(Morphism) F G) : C.(Morphism) (ColimitOf F) (ColimitOf G).
    subst LimitOf ColimitOf.
    simpl in *.
    generalize (HC G) (HC F).
    define_limit_morphism'.
  Defined.

  Definition LimitFunctor_morphism_of'' (F G : C ^ D) (m : (C ^ D).(Morphism) F G) : C.(Morphism) (LimitOf F) (LimitOf G).
    simpl_definition_by_tac_and_exact (LimitFunctor_morphism_of' m) ltac:( unfold LimitFunctor_morphism_of', LimitOf in * ).
  Defined.

  Definition ColimitFunctor_morphism_of'' (F G : C ^ D) (m : (C ^ D).(Morphism) F G) : C.(Morphism) (ColimitOf F) (ColimitOf G).
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
    abstract (
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
                repeat rewrite Associativity;
                  match goal with
                    | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
                      eapply (@eq_trans _ _ (Compose a' (Compose _ c)) _);
                        try_associativity ltac:(apply f_equal2; try reflexivity)
                  end;
                  intro_universal_properties;
                  unfold unique in *;
                    split_and;
                    repeat match goal with
                             | [ H : forall Y f, @?a Y f = @?b Y f |- _ ] =>
                               let H' := fresh in assert (H' := (fun x Y f => f_equal (fun T => T.(SComponentsOf) x) (H Y f))); simpl in H'; clear H
                           end;
                    etransitivity; solve [ t_with t' ]
    ).
 (*
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
    change (MorphismOf (DiagonalSpecializedFunctor C D)) with (@ΔMor C D) in *;
    change (ObjectOf (DiagonalSpecializedFunctor C D)) with (@Δ C D) in *;
    change TerminalMorphism_Object with limo in *;
    change TerminalMorphism_Morphism with φ in *;
    change TerminalProperty_Morphism with unique_m in *. *)
  Defined.

  Definition ColimitFunctor' : Functor (C ^ D) C.
    refine {| ObjectOf := ColimitOf;
      MorphismOf := ColimitFunctor_morphism_of
    |};
    abstract (
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
              try simpl_do_clear do_rewrite (DiagonalFunctor C D).(FCompositionOf);
                snt_eq;
                try solve [
                  autorewrite with core;
                    try reflexivity
                ];
                repeat rewrite Associativity;
                  intro_universal_properties;
                  unfold unique in *;
                    split_and;
                    repeat match goal with
                             | [ H : forall Y f, @?a Y f = @?b Y f |- _ ] =>
                               let H' := fresh in assert (H' := (fun x Y f => f_equal (fun T => T.(SComponentsOf) x) (H Y f))); simpl in H'; clear H
                           end;
                    match goal with
                      | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
                        eapply (@eq_trans _ _ (Compose a (Compose _ c')) _);
                          [ try_associativity ltac:(apply f_equal2; try reflexivity) |
                            repeat rewrite <- AssociativityNoEvar by noEvar ]
                    end;
                    etransitivity; solve [ t_with t' ]
    ).
    (*    rename s into F0; rename d into G0;  rename d' into H0;
    rename c into F;
      rename c0 into H;
        rename c1 into G.
    Definition Δ {C D} := @diagonal_functor_object_of C D.
    Definition ΔMor {C D} o1 o2 := @diagonal_functor_morphism_of C D o1 o2.
    Definition colimo := InitialMorphism_Object.
    Definition φ := InitialMorphism_Morphism.
    Definition unique_m C {a b c d} := @InitialProperty_Morphism C a b c d.

    change (diagonal_functor_morphism_of C D) with (@ΔMor C D) in *;
    change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor C D) in *;
    change (ObjectOf (DiagonalFunctor C D)) with (@Δ C D) in *;
    change InitialMorphism_Object with colimo in *;
    change InitialMorphism_Morphism with φ in *;
    change @InitialProperty_Morphism with @unique_m in *. *)
  Defined.
End LimitFunctors.

Definition LimitFunctor := Eval cbv beta iota zeta delta [LimitFunctor'(* LimitFunctor_morphism_of*)] in LimitFunctor'.
Definition ColimitFunctor := Eval cbv beta iota zeta delta [ColimitFunctor'(* ColimitFunctor_morphism_of*)] in ColimitFunctor'.

Section Adjoint.
  Variable C : Category.
  Variable D : SmallCategory.
  Hypothesis HL : HasLimits C D.
  Hypothesis HC : HasColimits C D.

  Let LimitOf (F : C ^ D) := LimitObject (HL F).
  Let ColimitOf (F : C ^ D) := ColimitObject (HC F).

  Let Δ := DiagonalFunctor C D.

  Definition LimitAdjunction_AComponentsOf (c : C) (F : C ^ D) :
    Morphism TypeCat
    (HomFunctor (C ^ D) ((DiagonalFunctor C D) c, F))
    (HomFunctor C (c, (LimitFunctor HL) F))
    := (fun T => LimitProperty_Morphism (HL F) T).

  Definition LimitAdjunction_AComponentsOf_Inverse (c : C) (F : C ^ D)
    : TypeCat.(Morphism) (HomFunctor C (c, (LimitFunctor HL) F)) (HomFunctor (C ^ D) ((DiagonalFunctor C D) c, F)).
    simpl in *; intro f; hnf; simpl.
    match goal with
      | [ |- SmallNaturalTransformation ?DF ?F ] =>
        eapply (Build_SmallNaturalTransformation DF F
          (fun d => Compose (LimitMorphism (HL F) d) f)
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

  Lemma LimitAdjunction_AIsomorphism' (c : C) (F : C ^ D) :
    InverseOf (@LimitAdjunction_AComponentsOf c F) (@LimitAdjunction_AComponentsOf_Inverse c F).
    unfold LimitAdjunction_AComponentsOf, LimitAdjunction_AComponentsOf_Inverse;
      unfold LimitMorphism, LimitProperty_Morphism, LimitObject, Limit in *;
        split; simpl in *;
          repeat (apply functional_extensionality_dep; intro);
            repeat match goal with
                     | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => let H0 := fresh in let H1 := fresh in
                       destruct (TerminalProperty a b c) as [ H0 H1 ]; apply H0 || apply H1; clear H0 H1
                   end;
              snt_eq;
              intro_universal_properties;
              intro_universal_morphisms;
              specialize_all_ways;
              destruct_hypotheses;
              match goal with
                       | [ T : _ |- _ ] => apply (f_equal (@SComponentsOf _ _ _ _)) in T
                     end; fg_equal;
              try specialized_assumption idtac.
  Qed.

  Definition LimitAdjunction_AIsomorphism (c : C) (F : C ^ D) : CategoryIsomorphism (@LimitAdjunction_AComponentsOf c F).
    exists (LimitAdjunction_AComponentsOf_Inverse _ _).
    exact (@LimitAdjunction_AIsomorphism' _ _).
  Defined.

  Lemma LimitAdjunction_ACommutes (c : C) (F : C ^ D) (c' : C) (F' : C ^ D)
    (m : Morphism C c' c) (m' : Morphism (C ^ D) F F') :
    (Compose (@LimitAdjunction_AComponentsOf c' F')
      (@MorphismOf _ _ (HomFunctor (C ^ D)) (_, F) (_, F') ((DiagonalFunctor C D).(MorphismOf) m, m'))) =
    (Compose
      (@MorphismOf _ _ (HomFunctor C) (c, _) (c', _) (m, (LimitFunctor HL).(MorphismOf) m'))
      (@LimitAdjunction_AComponentsOf c F)).
  Proof.
    Local Opaque FunctorCategory.
    repeat match goal with
             | [ |- context[@MorphismOf _ _ (HomFunctor ?C) ?s ?d ?m] ] => rewrite (@SplitHom C s d m)
           end;
    repeat rewrite Associativity;
      match goal with
        | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
          eapply (@eq_trans _ _ (Compose a' (@Compose TypeCat _ _ _ (TerminalProperty_Morphism _ _) c)) _);
              try_associativity ltac:(apply f_equal2; try reflexivity)
      end;
      simpl; unfold LimitAdjunction_AComponentsOf, LimitProperty_Morphism, LimitObject;
        apply functional_extensionality_dep; intro;
        repeat match goal with
                 | [ |- appcontext[@SNTComposeT ?D ?C ?F ?G ?H ?T ?U] ] => change (@SNTComposeT D C F G H T U) with (@Compose (C ^ D) F G H T U) in *
               end;
          repeat match goal with
                   | [ |- context[TerminalProperty_Morphism ?a ?b ?c] ] => let H := constr:(TerminalProperty a b c) in
                     first [ apply H | symmetry; apply H; symmetry ];
                       repeat rewrite FCompositionOf; repeat rewrite <- Associativity;
                         simpl; f_equal
                   | [ |- context[TerminalProperty_Morphism ?a ?b ?c] ] => let H := constr:(TerminalProperty a b c) in
                     first [ simpl_do_clear do_rewrite (proj1 H) | simpl_do_clear do_rewrite (proj2 H) ];
                         repeat rewrite FCompositionOf; repeat rewrite Associativity;
                           simpl; f_equal
                 end.
    Local Transparent FunctorCategory.
  Qed.

  Definition LimitAdjunction : Adjunction (DiagonalFunctor C D) (LimitFunctor HL).
    refine {| AComponentsOf := LimitAdjunction_AComponentsOf;
      AIsomorphism := LimitAdjunction_AIsomorphism;
      ACommutes := LimitAdjunction_ACommutes
    |}.
  Defined.


  Definition ColimitAdjunction_AComponentsOf_Inverse (F : C ^ D) (c : C) :
    Morphism TypeCat
    (HomFunctor (C ^ D) (F, (DiagonalFunctor C D) c))
    (HomFunctor C ((ColimitFunctor HC) F, c))
    := (fun T => ColimitProperty_Morphism (HC F) T).

  Definition ColimitAdjunction_AComponentsOf (F : C ^ D) (c : C) :
    Morphism TypeCat
    (HomFunctor C ((ColimitFunctor HC) F, c))
    (HomFunctor (C ^ D) (F, (DiagonalFunctor C D) c)).
    simpl in *; intro f; hnf; simpl.
    match goal with
      | [ |- SmallNaturalTransformation ?F ?DF ] =>
        eapply (Build_SmallNaturalTransformation F DF
          (fun d => Compose f (ColimitMorphism (HC F) d))
          _
        )
    end.
    Grab Existential Variables.
    abstract (
      simpl in *; intros; rewrite LeftIdentity;
        try_associativity ltac:(apply f_equal2; try reflexivity);
        match goal with
          | [ |- Compose _ _ = SComponentsOf ?T ?d ] => simpl_do do_rewrite (SCommutes T)
        end;
        rewrite LeftIdentity;
          reflexivity
    ).
  Defined.

  Lemma ColimitAdjunction_AIsomorphism' (F : C ^ D) (c : C) :
    InverseOf (@ColimitAdjunction_AComponentsOf F c) (@ColimitAdjunction_AComponentsOf_Inverse F c).
    unfold ColimitAdjunction_AComponentsOf, ColimitAdjunction_AComponentsOf_Inverse;
      unfold ColimitMorphism, ColimitProperty_Morphism, ColimitObject, Colimit in *;
        split; simpl in *;
          repeat (apply functional_extensionality_dep; intro);
            repeat match goal with
                     | [ |- appcontext[InitialProperty_Morphism ?a ?b ?c] ] => let H := constr:(InitialProperty a b c) in
                       apply (proj1 H) || apply (proj2 H)
                   end;
            snt_eq;
            intro_universal_properties;
            intro_universal_morphisms;
            specialize_all_ways;
            destruct_hypotheses;
            match goal with
              | [ T : _ |- _ ] => apply (f_equal (@SComponentsOf _ _ _ _)) in T
            end; fg_equal;
            try specialized_assumption idtac.
  Qed.

  Definition ColimitAdjunction_AIsomorphism (F : C ^ D) (c : C) : CategoryIsomorphism (@ColimitAdjunction_AComponentsOf F c).
    exists (@ColimitAdjunction_AComponentsOf_Inverse _ _).
    exact (@ColimitAdjunction_AIsomorphism' _ _).
  Defined.

  Check @ACommutes_Inverse _ _ (ColimitFunctor HC) (DiagonalFunctor C D).

  Lemma ColimitAdjunction_ACommutes_Inverse (F : C ^ D) (c : C) (F' : C ^ D) (c' : C)
    (m' : Morphism (C ^ D) F' F) (m : Morphism C c c') :
    (Compose
      (@MorphismOf _ _ (HomFunctor C) (_, c) (_, c') ((ColimitFunctor HC).(MorphismOf) m', m))
      (@ColimitAdjunction_AComponentsOf_Inverse F c)) =
    (Compose (@ColimitAdjunction_AComponentsOf_Inverse F' c')
      (@MorphismOf _ _ (HomFunctor (C ^ D)) (F, _) (F', _) (m', (DiagonalFunctor C D).(MorphismOf) m))).
  Proof.
    Local Opaque FunctorCategory.
    repeat match goal with
             | [ |- context[@MorphismOf _ _ (HomFunctor ?C) ?s ?d ?m] ] => rewrite (@SplitHom C s d m)
           end;
    repeat rewrite Associativity.
      match goal with
        | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
          eapply (@eq_trans _ _ (Compose a (@Compose TypeCat _ _ _ (InitialProperty_Morphism _ _) c')) _);
              try_associativity ltac:(apply f_equal2; try reflexivity)
      end;
      simpl; unfold ColimitAdjunction_AComponentsOf_Inverse, ColimitProperty_Morphism, ColimitObject;
        apply functional_extensionality_dep; intro;
        repeat match goal with
                 | [ |- appcontext[@SNTComposeT ?D ?C ?F ?G ?H ?T ?U] ] => change (@SNTComposeT D C F G H T U) with (@Compose (C ^ D) F G H T U) in *
               end;
          repeat match goal with
                   | [ |- context[InitialProperty_Morphism ?a ?b ?c] ] => let H := constr:(InitialProperty a b c) in
                     first [ apply H | symmetry; apply H; symmetry ];
                       repeat rewrite FCompositionOf; repeat rewrite Associativity;
                         simpl; f_equal
                   | [ |- context[InitialProperty_Morphism ?a ?b ?c] ] => let H := constr:(InitialProperty a b c) in
                     first [ simpl_do_clear do_rewrite (proj1 H) | simpl_do_clear do_rewrite (proj2 H) ];
                         repeat rewrite FCompositionOf; repeat rewrite <- Associativity;
                           simpl; f_equal
                 end.
    Local Transparent FunctorCategory.
  Qed.

  Lemma ColimitAdjunction_ACommutes (F : C ^ D) (c : C) (F' : C ^ D) (c' : C)
    (m' : Morphism (C ^ D) F' F) (m : Morphism C c c'):
    (Compose (@ColimitAdjunction_AComponentsOf F' c')
      (@MorphismOf _ _ (HomFunctor C) (_, c) (_, c') ((ColimitFunctor HC).(MorphismOf) m', m))) =
    (Compose
      (@MorphismOf _ _ (HomFunctor (C ^ D)) (F, _) (F', _) (m', (DiagonalFunctor C D).(MorphismOf) m))
      (@ColimitAdjunction_AComponentsOf F c)).
  Proof.
    Local Opaque FunctorCategory TypeCat HomFunctor.
    pose (@ColimitAdjunction_AComponentsOf_Inverse F c).
    pose (@ColimitAdjunction_AComponentsOf_Inverse F' c').
    pose (@ColimitAdjunction_AIsomorphism' F c).
    pose (@ColimitAdjunction_AIsomorphism' F' c').
    unfold InverseOf in *; destruct_hypotheses.
    pre_compose_to_identity; post_compose_to_identity.
    apply ColimitAdjunction_ACommutes_Inverse.
  Qed.

  Definition ColimitAdjunction : Adjunction (ColimitFunctor HC) (DiagonalFunctor C D) .
    refine {| AComponentsOf := ColimitAdjunction_AComponentsOf;
      AIsomorphism := ColimitAdjunction_AIsomorphism;
      ACommutes := ColimitAdjunction_ACommutes
    |}.
  Defined.
End Adjoint.
