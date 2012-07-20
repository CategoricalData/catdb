Require Import FunctionalExtensionality.
Require Export Limits.
Require Import Common DefinitionSimplification NaturalTransformation FunctorCategory Adjoint Hom SetCategory Duals ProductFunctor.

Set Implicit Arguments.

Local Notation "C ^ D" := (FunctorCategory D C).

Section HasLimits.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.

  Definition HasLimits' := forall F : SpecializedFunctor D C, exists _ : Limit F, True.
  Definition HasLimits := forall F : SpecializedFunctor D C, Limit F.

  Definition HasColimits' := forall F : SpecializedFunctor D C, exists _ : Colimit F, True.
  Definition HasColimits := forall F : SpecializedFunctor D C, Colimit F.
End HasLimits.

Section LimitFunctors.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.

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
                     | [ m : _, t : _ |- _ ] => unique_pose (NTComposeT m t)
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
  Definition LimitFunctor' : SpecializedFunctor (C ^ D) C.
    Transparent Object Morphism Compose Identity.
    refine {| ObjectOf' := LimitOf;
      MorphismOf' := LimitFunctor_morphism_of
    |};
    abstract (
      subst LimitOf ColimitOf LimitFunctor_morphism_of ColimitFunctor_morphism_of; present_spnt;
        simpl; intros; autorewrite with core;
          repeat match goal with
                   | [ |- context[HL ?o] ] => generalize (HL o); intro
                 end;
          clear HL HC;
            unfold Limit, LimitObject, Colimit, ColimitObject in *;
              match goal with
                | [ |- TerminalProperty_Morphism ?l0 ?Y ?f = _ ] => let H := fresh in pose (proj2 (TerminalProperty l0 Y f)) as H; simpl in H; apply H; clear H
              end;
              nt_eq;
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
                             let H' := fresh in assert (H' := (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (H Y f))); simpl in H'; clear H
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

  Definition ColimitFunctor' : SpecializedFunctor (C ^ D) C.
    refine {| ObjectOf' := ColimitOf;
      MorphismOf' := ColimitFunctor_morphism_of
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
              nt_eq;
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
                             let H' := fresh in assert (H' := (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (H Y f))); simpl in H'; clear H
                         end;
                  match goal with
                    | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
                      eapply (@eq_trans _ _ (Compose a (Compose _ c')) _);
                        symmetry; (* I'm confused why I need this.  But if I don't have it, [rewrite <- AssociativityNoEvar at 2] fails *)
                          [ try_associativity ltac:(apply f_equal2; try reflexivity) |
                            repeat rewrite <- AssociativityNoEvar by noEvar ]
                  end;
                  etransitivity; solve [ t_with t' ]
    ).
(*    transitivity (Compose (unique_m (colimo H) (SPNTComposeT (φ H) m2)) (Compose ((φ G) x) (m1 x)));
      try_associativity ltac:(apply PreComposeMorphisms || apply PostComposeMorphisms; try reflexivity).*)
(*      ).*)
(*    rename s into F0; rename d into G0;  rename d' into H0;
    rename c into F;
      rename c0 into H;
        rename c1 into G.*)
(*    Definition Δ {objC morC objD morD C D} := @diagonal_functor_object_of objC morC objD morD C D.
    Definition ΔMor {objC morC objD morD C D} o1 o2 := @diagonal_functor_morphism_of objC morC objD morD C D o1 o2.
    Definition colimo := InitialMorphism_Object.
    Definition φ := InitialMorphism_Morphism.
    Definition unique_m {objC morC objD morD} C {a b c d} := @InitialProperty_Morphism objC morC objD morD C a b c d.

    change (diagonal_functor_morphism_of C D) with (@ΔMor _ _ _ _ C D) in *;
    change (MorphismOf (DiagonalSpecializedFunctor C D)) with (@ΔMor _ _ _ _ C D) in *;
    change (ObjectOf (DiagonalSpecializedFunctor C D)) with (@Δ _ _ _ _ C D) in *;
    change InitialMorphism_Object with colimo in *;
    change InitialMorphism_Morphism with φ in *;
    change @InitialProperty_Morphism with @unique_m in *.*)
  Defined.
End LimitFunctors.

Definition LimitFunctor := Eval cbv beta iota zeta delta [LimitFunctor'(* LimitFunctor_morphism_of*)] in LimitFunctor'.
Definition ColimitFunctor := Eval cbv beta iota zeta delta [ColimitFunctor'(* ColimitFunctor_morphism_of*)] in ColimitFunctor'.

Section Adjoint.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Hypothesis HL : HasLimits C D.
  Hypothesis HC : HasColimits C D.

  Let LimitOf (F : C ^ D) := LimitObject (HL F).
  Let ColimitOf (F : C ^ D) := ColimitObject (HC F).

  Definition LimitAdjunction_AComponentsOf (c : C) (F : C ^ D) :
    Morphism TypeCat
    (HomFunctor (C ^ D) ((DiagonalFunctor C D) c, F))
    (HomFunctor C (c, (LimitFunctor HL) F))
    := (fun T => LimitProperty_Morphism (HL F) T).

  Definition LimitAdjunction_AComponentsOf_Inverse (c : C) (F : C ^ D)
    : TypeCat.(Morphism) (HomFunctor C (c, (LimitFunctor HL) F)) (HomFunctor (C ^ D) ((DiagonalFunctor C D) c, F)).
    Transparent Morphism.
    simpl in *; intro f; hnf; simpl.
    match goal with
      | [ |- SpecializedNaturalTransformation ?DF ?F ] =>
        eapply (Build_SpecializedNaturalTransformation DF F
          (fun d => Compose (LimitMorphism (HL F) d) f)
          _
        )
    end.
    Grab Existential Variables.
    abstract (
      simpl in *; intros; rewrite RightIdentity;
        try_associativity ltac:(apply f_equal2; try reflexivity);
        match goal with
          | [ |- ComponentsOf ?T ?d = Compose _ _ ] => simpl_do do_rewrite_rev (Commutes T)
        end;
        rewrite RightIdentity;
          reflexivity
    ).
  Defined.

  Lemma LimitAdjunction_AIsomorphism' (c : C) (F : C ^ D) :
    InverseOf (@LimitAdjunction_AComponentsOf c F) (@LimitAdjunction_AComponentsOf_Inverse c F).
    Transparent Compose.
    unfold LimitAdjunction_AComponentsOf, LimitAdjunction_AComponentsOf_Inverse;
      unfold LimitMorphism, LimitProperty_Morphism, LimitObject, Limit in *;
        split; simpl in *;
          repeat (apply functional_extensionality_dep; intro);
            repeat match goal with
                     | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => let H0 := fresh in let H1 := fresh in
                       destruct (TerminalProperty a b c) as [ H0 H1 ]; apply H0 || apply H1; clear H0 H1
                   end;
              nt_eq;
              intro_universal_properties;
              intro_universal_morphisms;
              specialize_all_ways;
              destruct_hypotheses;
              match goal with
                | [ T : _ |- _ ] => apply (f_equal ComponentsOf) in T
              end; fg_equal;
              try specialized_assumption idtac.
  Qed.

  Definition LimitAdjunction_AIsomorphism (c : C) (F : C ^ D) : CategoryIsomorphism (@LimitAdjunction_AComponentsOf c F).
    exists (LimitAdjunction_AComponentsOf_Inverse _).
    exact (@LimitAdjunction_AIsomorphism' _ _).
  Defined.

  Lemma LimitAdjunction_ACommutes (c : C) (F : C ^ D) (c' : C) (F' : C ^ D)
    (m : Morphism C c' c) (m' : Morphism (C ^ D) F F') :
    (Compose (@LimitAdjunction_AComponentsOf c' F')
      (MorphismOf (HomFunctor (C ^ D)) (s := (_, F)) (d := (_, F')) ((DiagonalFunctor C D).(MorphismOf) m, m'))) =
    (Compose
      (MorphismOf (HomFunctor C) (s := (c, _)) (d := (c', _)) (m, (LimitFunctor HL).(MorphismOf) m'))
      (@LimitAdjunction_AComponentsOf c F)).
  Proof.
    Local Opaque FunctorCategory.
    repeat match goal with
             | [ |- context G [@MorphismOf _ _ _ _ _ _ (HomFunctor ?C) ?s ?d ?m] ] =>
               let H := constr:(@SplitHom _ _ C s d m) in
                 let HT := type of H in
                   match HT with
                     | ?x = ?y => let G' := context G[x] in let G'' := context G[y] in
                       cut G'; [ let H' := fresh in intro H'; simpl in H' |- *; exact H' | ];
                         cut G''; [ let H' := fresh in intro H'; etransitivity; try apply H'; rewrite H; reflexivity
                           |
                         ]
                   end
           end;
    repeat rewrite Associativity.
(*     conv_rewrite (@SplitHom _ _ (C ^ D) ((DiagonalFunctor C D) c, F) ((DiagonalFunctor C D) c', F') (MorphismOf (DiagonalFunctor C D) m, m')).

     simpl in H.
     simpl.*)
    unfold fst, snd.
    match goal with
      | [ |- @eq ?T _ _ ] => let T' := fresh in pose T as T';
        hnf in T'; simpl in T';
          change T with T';
            subst T'
    end.
    present_spcategory.
    Implicit Arguments MorphismOf [objC morC objD morD C D].
    Print Compose.
    Opaque DiagonalFunctor.
    Eval simpl in ((CovariantHomFunctor (C ^ D) ((DiagonalFunctor C D) c)) F').
(*    eapply (@eq_trans _ _
      (MorphismOf (ContravariantHomFunctor C ((LimitFunctor HL) F')) c c' m)
      (@Compose _ _ TypeCat _ _ _ _
        (MorphismOf (CovariantHomFunctor (C ^ D) ((DiagonalFunctor C D) c)) F
          F' m'))).*)
      match goal with
        | [ |- @Compose _ _ _ ?s ?d ?e ?a (@Compose _ _ _ ?f ?g ?h ?b ?c) = @Compose _ _ _ ?s' ?d' ?e' ?a' (@Compose _ _ _ ?f' ?g' ?h' ?b' ?c') ] =>
          let m := fresh in evar (m : @Morphism _ _ TypeCat g d');
          eapply (@eq_trans _ _ (@Compose _ _ TypeCat f d' e' a' (@Compose _ _ TypeCat f g d' m c)) _ );
(*          eapply (@eq_trans _ _ (Compose a' (@Compose _ _ TypeCat _ _ _ (TerminalProperty_Morphism _ _) c)) _)*)
            try_associativity ltac:(apply f_equal2; try reflexivity)
      end.
      hnf in H; simpl in H.
      pose TerminalProperty_Morphism as H'.
      specialize (H' (OppositeCategory (C ^ D))).
      specialize (H' (OppositeCategory C)).
      specialize (H' (OppositeFunctor (DiagonalFunctor C D))).
      simpl in H'.
      specialize (H' ((DiagonalFunctor C D) c)).
      unfold LimitObject in H.
      specialize (H' (HL F')).
      pose ((fun M => H' M F')).
      apply TerminalProperty_Morphism in H.
      simpl; unfold LimitAdjunction_AComponentsOf, LimitProperty_Morphism, LimitObject;
        apply functional_extensionality_dep; intro;



  Check @AMateOf _ _ _ _ _ _ (DiagonalFunctor C D) (LimitFunctor HL).
  Eval simpl in SpecializedNaturalTransformation
         (ComposeFunctors (HomFunctor (C ^ D))
            (ProductFunctor
               (OppositeFunctor (DiagonalFunctor C D))
               (IdentityFunctor (C ^ D))))
         (ComposeFunctors (HomFunctor C)
            (ProductFunctor
               (IdentityFunctor (OppositeCategory C))
               (LimitFunctor HL))).
  Definition LimitAdjunction_AMateOf : SpecializedNaturalTransformation
    (ComposeFunctors (HomFunctor (C ^ D))
      (ProductFunctor
        (OppositeFunctor (DiagonalFunctor C D))
        (IdentityFunctor _)))
    (ComposeFunctors (HomFunctor C)
      (ProductFunctor
        (IdentityFunctor _)
        (LimitFunctor HL))).
    exists (fun (cF : C * (C ^ D)) => @LimitAdjunction_AComponentsOf (fst cF) (snd cF)).
    subst LimitOf ColimitOf.
    clear HC.
    intros s d m;
      present_spnt.
(*    pose (@LimitAdjunction_AIsomorphism' (fst s) (snd s)).
    pose (@LimitAdjunction_AIsomorphism' (fst d) (snd d)).
    pose (@LimitAdjunction_AComponentsOf_Inverse (fst s) (snd s)).
    pose (@LimitAdjunction_AComponentsOf_Inverse (fst d) (snd d)).*)
    Opaque Compose ObjectOf MorphismOf.
    destruct_hypotheses.
    unfold LimitAdjunction_AComponentsOf, LimitAdjunction_AComponentsOf_Inverse, LimitObject, LimitProperty_Morphism in *.
    sanitize_spcategory.
    match goal with
      | [ |- @eq ?T _ _ ] => pose T as T'; change T with T'
    end.
    Transparent Object Morphism Compose Identity ObjectOf MorphismOf.
    Opaque DiagonalFunctor.
    hnf in T'; simpl in T'.
    change (@Morphism ?obj ?mor (C ^ D)) with mor in *.
    subst T'.
    Opaque Object Morphism Compose Identity ObjectOf MorphismOf.
    Opaque HomFunctor.
    Transparent MorphismOf.
    simpl.
    change (diagonal_functor_morphism_of C D) with (@MorphismOf _ _ _ _ _ _ (DiagonalFunctor C D)).
    Opaque MorphismOf.
    Transparent ProductCategory Morphism.
    Print MorphismOf.
    Implicit Arguments MorphismOf [objC morC objD morD].
    Check @MorphismOf _ _ _ _ _ _ (HomFunctor C).
    match goal with
      | [ |- context[@MorphismOf _ _ _ _ _ _ (HomFunctor ?C) ?X ?Y ?gh] ] => let H := fresh in pose (@SplitHom _ _ C X Y gh) as H; simpl in H;
        let x := constr:(@MorphismOf _ _ _ _ _ _ (HomFunctor C) X Y gh) in let x' := fresh in
          pose x as x'; change x with x' in H |- *
    end.
    change (MorphismOf (HomFunctor (C ^ D))
        (MorphismOf (DiagonalFunctor C D) m, s0)) with H0 in H.
    Implicit Arguments MorphismOf.
    rewrite H.
     "MorphismOf (HomFunctor (C ^ D))
                             ((ProductFunctor
                                 (OppositeFunctor (DiagonalFunctor C D))
                                 (IdentityFunctor (C ^ D)))
                                (o0, s))
                             ((ProductFunctor
                                 (OppositeFunctor (DiagonalFunctor C D))
                                 (IdentityFunctor (C ^ D)))
                                (o, s1))
                             (MorphismOf (DiagonalFunctor C D) o o0 m, s0)"
    Set Printing All.
    rewrite H.
    simpl in *.
    rewrite H.
    rewrite SplitHom; simpl; symmetry.
    Implicit Arguments MorphismOf [objC morC].
    Check (@SplitHom objC morC C).
    rewrite SplitHom; simpl; symmetry.
    rewrite SplitHom; simpl; symmetry.
    Transparent ObjectOf.
    Opaque DiagonalFunctor.
    simpl.
    Opaque ObjectOf.
    repeat rewrite Associativity.
    sanitize_spcategory.
    match goal with
      | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
        eapply (@eq_trans _ _ (Compose a' (Compose _ c)) _);
          try_associativity ltac:(apply f_equal2; try reflexivity)
    end;
    unfold LimitObject.
    intro_universal_properties.
    Transparent HomFunctor MorphismOf.
    Opaque DiagonalFunctor.
    simpl.
    Opaque HomFunctor MorphismOf FunctorCategory.
    Transparent Compose.
    simpl.
    Opaque Compose.
    Transparent TypeCat Morphism Compose MorphismOf.
    simpl in *.
    apply functional_extensionality_dep; intro.
    repeat rewrite LeftIdentity.
    match goal with
      | [ |- TerminalProperty_Morphism ?a ?b ?c = _ ] => pose (TerminalProperty a b c); destruct_hypotheses
    end.
    move H1 at bottom.
    rename s into F; rename s1 into F'; rename o0 into c; rename o into c'; rename m into f; rename s0 into a.
    Focus 2.
    Transparent HomFunctor MorphismOf.
    Opaque DiagonalFunctor TypeCat Morphism Compose.
    simpl.
    Transparent Morphism TypeCat.
    simpl.
    repeat match goal with
             | [ |- context G [fun g : ?T => Compose ?a (Compose g (Identity ?b))] ]
               => let H := fresh in let G' := context G[fun g : T => Compose a g] in
                 cut G'; [
                   intro H; rewrite H; apply f_equal2; try reflexivity;
                     apply functional_extensionality_dep; intro; rewrite RightIdentity; reflexivity
                   | ]
           end.
    Check Morphism TypeCat.
    symmetry.

(****** HERE ******)
    Transparent Compose Morphism TypeCat
    unfold Compose at 2.
    match goal with
      | [ |- context G [fun g : ?T => Compose ?a (Compose g (Identity ?b))] ]
        => let G' := context G[fun g : T => Compose a g] in
          cut G'
    end.
    intro H'.
    rewrite H'.
    apply f_equal2; try reflexivity.
    simpl.
    Transparent Morphism TypeCat.
    apply functional_extensionality_dep; intro. rewrite RightIdentity; reflexivity.
    apply functional_extensionality_dep; intro rewrite RightIdentity; reflexivity.

    [ | apply functional_extensionality_dep; intro; rewrite RightIdentity; reflexivity ].
    let x := constr:((fun g : Morphism C o0 (TerminalMorphism_Object (HL s)) =>
      Compose
        (TerminalProperty_Morphism (HL s1) (TerminalMorphism_Object (HL s))
           (NTComposeT s0 (TerminalMorphism_Morphism (HL s))))
        (Compose g (Identity o0)))) in
    match x with
      | context[fun g : ?T => Compose ?a (Compose g (Identity ?b))] => replace (fun g : T => Compose a (Compose g (Identity b))) with (fun g : T => Compose a g)
    end.
    replace (fun g : Morphism C o0 (TerminalMorphism_Object (HL s)) =>
      Compose
        (TerminalProperty_Morphism (HL s1) (TerminalMorphism_Object (HL s))
           (NTComposeT s0 (TerminalMorphism_Morphism (HL s))))
        (Compose g (Identity o0))) with (fun g : Morphism C o0 (TerminalMorphism_Object (HL s)) =>
      Compose
        (TerminalProperty_Morphism (HL s1) (TerminalMorphism_Object (HL s))
           (NTComposeT s0 (TerminalMorphism_Morphism (HL s))))
        g); [ | apply functional_extensionality_dep; intro; rewrite RightIdentity; reflexivity ].
    Check (fun g : Morphism C o0 (TerminalMorphism_Object (HL s)) =>
      Compose
        (TerminalProperty_Morphism (HL s1) (TerminalMorphism_Object (HL s))
           (NTComposeT s0 (TerminalMorphism_Morphism (HL s))))
        (Compose g (Identity o0))).
    Check (fun g : Morphism C o0 (TerminalMorphism_Object (HL s)) =>
      Compose
        (TerminalProperty_Morphism (HL s1) (TerminalMorphism_Object (HL s))
           (NTComposeT s0 (TerminalMorphism_Morphism (HL s))))
        (Compose g (Identity o0))).
    Opaque HomFunctor MorphismOf FunctorCategory.
    Transparent Compose.
    simpl.
    Opaque Compose.
    Transparent TypeCat Morphism Compose MorphismOf.
    simpl in *.
    apply functional_extensionality_dep; intro.
    repeat rewrite RightIdentity.




    match goal with
      | [ |- @eq ?T _ _ ] => pose T as T'
    end.

    apply functional_extensionality_dep; intro.
    unfold Compose at 1.
    Opaque Compose.
    simpl.

    rewrite LeftIdentity.
    destruct_hypotheses.
    rewrite ( (HomFunctor (C ^ D))).
    Transparent Object Morphism Compose Identity ObjectOf MorphismOf HomFunctor.
    Set Printing All.
    do 2 match goal with
           | [ |- appcontext[@Compose _ _ _ ?x] ] => let x'' := fresh in let x''' := fresh in pose x as x''; pose x as x'''; hnf in x'''; simpl in x''';
             let x' := fresh in progress (pose x as x'; change x with x'; hnf in x'; simpl in x'; subst x')
         end.
    match goal with
      | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
        eapply (@eq_trans _ _ (Compose a (Compose _ c')) _)
    end.



    unfold LimitObject.
    intro_universal_properties.
    destruct_hypotheses.
    do 3 match goal with
           | [ H : _ = _ |- _ ] => move H at bottom
         end.
    rename s into F; rename s1 into F'; rename o0 into c; rename o into c'; rename m into f; rename s0 into a.
    pose (TerminalProperty_Morphism (HL F') c') as Mc'F'.
    Ltac change_in_all from to :=
      repeat match goal with
               | [ H : _ |- _ ] => progress change from with to in H |- *
             end.
    change_in_all (TerminalProperty_Morphism (HL F') c') Mc'F'.
    pose (TerminalProperty_Morphism (HL F) c) as McF.
    change_in_all (TerminalProperty_Morphism (HL F) c) McF.
    Definition Δ {objC morC C objD morD D} := @diagonal_functor_object_of objC morC C objD morD D.
    Definition Δ' {objC morC objD morD C D} := @DiagonalFunctor objC morC objD morD C D.
    Definition ΔMor {objC morC C objD morD D} {o1 o2} := @diagonal_functor_morphism_of objC morC C objD morD D o1 o2.
    Definition limo F := TerminalMorphism_Object (HL F).
    Definition φ := TerminalMorphism_Morphism.
    Definition unique_m {objC morC} C {objD morD} D := @TerminalProperty_Morphism objC morC C objD morD D.
    change (diagonal_functor_morphism_of C D) with (@ΔMor _ _ _ _ C D) in *;
    change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor _ _ _ _ C D) in *;
    change (ObjectOf (DiagonalFunctor C D)) with (@Δ _ _ _ _ C D) in *.
    change (TerminalMorphism_Object (HL ?F)) with (limo F) in *;
    change TerminalMorphism_Morphism with φ in *;
    change TerminalProperty_Morphism with @unique_m in *.
    Local Notation "F ** G" := (ProductFunctor F G) (at level 70).
    Local Notation "F *" := (OppositeFunctor F) (at level 70).
    Definition IdF := IdentityFunctor.
    Arguments IdF {objC morC C}.
    change @IdentityFunctor with @IdF in *.
    (*Transparent Compose ObjectOf MorphismOf Identity Morphism Object.
    simpl.
    apply functional_extensionality_dep; intro.
    simpl.
    unfold hom_functor_morphism_of.
    unfold LimitObject in *.*)
    Arguments Identity {obj mor} [C o].
    Local Notation "$$ m" := (MorphismOf _ m) (at level 70).
    Local Notation "$ m" := (ObjectOf _ m) (at level 70).




    Print SpecializedFunctor.
    Print FCompositionOf.
    rewrite SplitHom at 1 2.
    simpl.


(****** here ******)



    replace (@MorphismOf _ _ _ _ _ _ (HomFunctor (C ^ D)) (_, F) (_, F') (ΔMor f, a)) with
      (@MorphismOf _ _ _ _ _ _ (HomFunctor (C ^ D)) (_, F) (_, F') (@Compose _ _ (C ^ D) _ _ _ (ΔMor f) (IdentityNaturalTransformation _), @Compose _ _ (C ^ D) _ _ _ a (IdentityNaturalTransformation _))).
    match goal with
      | [ |- context[MorphismOf (HomFunctor ?C) (?a, ?b)] ] => replace (MorphismOf (HomFunctor C) (a, b)) with
    (Compose (MorphismOf (HomFunctor C) (IdentityFunctor _, b)) (MorphismOf (HomFunctor C) (a, IdentityFunctor _)))
    end.
    Transparent MorphismOf.
    unfold MorphismOf at 1 2.
    Opaque MorphismOf.
    Transparent HomFunctor.
    simpl.
    unfold hom_functor_morphism_of.
    Transparent ObjectOf.
    Opaque DiagonalFunctor.
    simpl.
    Transparent Object Compose Morphism.
    simpl.
    Opaque Object Compose Morphism.
    apply functional_extensionality_dep; intro.


    apply functional_
    Transparent ObjectOf.
    Transparent LimitFunctor.
    simpl.
    Opaque ObjectOf.


    change (diagonal_functor_morphism_of C D) with (@ΔMor _ _ _ _ C D) in *;
    change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor _ _ _ _ C D) in *;
    change (ObjectOf (DiagonalFunctor C D)) with (@Δ _ _ _ _ C D) in *;
    change (TerminalMorphism_Object (HL ?F)) with (limo F) in *;
    change TerminalMorphism_Morphism with φ in *;
    change TerminalProperty_Morphism with @unique_m in *.
    change (DiagonalFunctor C D) with (@Δ' _ _ _ _ C D) in *.
    Local Notation "C ~~~~> D" := (SpecializedFunctor C D) (at level 70).
    Local Notation "F ====> G" := (SpecializedNaturalTransformation F G) (at level 70).
    Local Notation "x ----> y" := (Morphism _ x y) (at level 70).
    Local Notation "x >------ ( F ) ------> y >------ ( G ) ------> z" := (@Compose x y z G F) (at level 75).
    Local Notation "x >~~~~~~ ( F ) ~~~~~~> y >~~~~~~ ( G ) ~~~~~~> z" := (@ComposeFunctors _ _ _ _ _ _ x y z G F) (at level 75).
    Local Notation "x >====== ( F ) ======> y >====== ( G ) ======> z" := (@NTComposeT _ _ _ _ _ _ x y z G F) (at level 75).
    Local Notation "F ** G" := (ProductFunctor F G) (at level 70).
    Local Notation "F *" := (OppositeFunctor F) (at level 70).
    pose (fun s d : Type => s -> d) as Fun; change (fun s d : Type => s -> d) with Fun.
    Definition ΔFunctor obj := @Build_SpecializedFunctor _ _ D _ _ C
         (fun _ : objD => obj)
         (fun (s d : objD) (_ : morD s d) =>
                        Identity obj)
         (diagonal_functor_object_of_subproof morD C
                              obj)
         (diagonal_functor_object_of_subproof0 C obj).
    change {|
         ObjectOf' := fun _ : objD => limo (HL F);
         MorphismOf' := fun (s d : objD) (_ : morD s d) =>
                        Identity (limo (HL F));
         FCompositionOf' := diagonal_functor_object_of_subproof morD C
                              (limo (HL F));
         FIdentityOf' := diagonal_functor_object_of_subproof0 C (limo (HL F)) |} with (ΔFunctor (limo (HL F))) in *.
    change {|
      ObjectOf' := fun _ : objD => c;
      MorphismOf' := fun (s d : objD) (_ : morD s d) => Identity c;
      FCompositionOf' := diagonal_functor_object_of_subproof morD C c;
      FIdentityOf' := diagonal_functor_object_of_subproof0 C c |} with (ΔFunctor c) in *.
    change
      {|
      ObjectOf' := fun _ : objD => c';
      MorphismOf' := fun (s d : objD) (_ : morD s d) => Identity c';
      FCompositionOf' := diagonal_functor_object_of_subproof morD C c';
      FIdentityOf' := diagonal_functor_object_of_subproof0 C c' |} with (ΔFunctor c') in *.
    simpl.
    Opaque MorphismOf.
    simpl.
    Transparent MorphismOf.


    Local Notation "C ~~~~> D" := (SpecializedFunctor C D) (at level 70).
    Local Notation "F ----> G" := (SpecializedNaturalTransformation F G) (at level 70).
    Local Notation "x ~~> y" := (Morphism _ x y) (at level 70).
    Local Notation "x >------ F ------> y >------ G ------> z" := (@Compose x y z G F) (at level 75).
    Local Notation "x >~~~~~~ F ~~~~~~> y >~~~~~~ G ~~~~~~> z" := (@ComposeFunctors _ _ _ _ _ _ x y z G F) (at level 75).
    Local Notation "F ** G" := (ProductFunctor F G) (at level 70).
    Local Notation "F *" := (OppositeFunctor F) (at level 70).
    pose (OppositeCategory C) as COp; change (OppositeCategory C) with COp.
    Print IdentityFunctor.
    Definition IdF := IdentityFunctor.
    Arguments IdF {objC morC C}.
    change @IdentityFunctor with @IdF in *.
    Definition Δ {objC morC objD morD C D} := @diagonal_functor_object_of objC morC objD morD C D.
    Definition ΔMor {objC morC objD morD C D} o1 o2 := @diagonal_functor_morphism_of objC morC objD morD C D o1 o2.
    change (diagonal_functor_morphism_of C D) with (@ΔMor _ _ _ _ C D) in *;
    change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor _ _ _ _ C D) in *;
    change (ObjectOf (DiagonalFunctor C D)) with (@Δ _ _ _ _ C D) in *.
    Definition Δ' {objC morC objD morD C D} := @DiagonalFunctor objC morC objD morD C D.
    change (DiagonalFunctor C D) with (@Δ' _ _ _ _ C D) in *.

Definition limo := TerminalMorphism_Object.
    Definition φ := TerminalMorphism_Morphism.
    Definition unique_m {objC morC objD morD} C {a b c} d := @TerminalProperty_Morphism objC morC objD morD C a b c d.

    Arguments IdentityFunctor
    pose IdentityFunctor as
    simpl.

    pre_compose_to_identity.


unfold CategoryIsomorphism, IsCategoryIsomorphism, InverseOf in *. hnf; simpl;
    hnf. simpl. unfold InverseOf. simpl.


 simpl. intro; split.
    eapply iso_is_epi.
    match goal with
      | [ |- @eq (?a -> ?b) _ _ ] => change (a -> b) with (Morphism TypeCat a b)
    end.
    destruct (@LimitAdjunction_AIsomorphism' (fst s) (snd s)) as [ H0 H1 ].
    eapply (@iso_is_epi _ _ TypeCat _ _ (@LimitAdjunction_AComponentsOf_Inverse (fst s) (snd s))).
    exists (@LimitAdjunction_AComponentsOf _ _); split; auto.
    Ltac try_associativity_quick tac := try_rewrite Associativity tac.
    repeat rewrite Associativity.
    symmetry.
    simpl in *.
    apply functional_extensionality_dep; intro.
    fg_equal.
    Transparent Object Morphism Compose Identity.
    simpl in *.
    specialize (H1 x).
    unfold
    conv_rewrite H1.
(*    unfold Object in *; simpl; rewrite H1.*)
    match goal with
      | [ H1 : ?a' = ?x |- Compose _ (Compose ?a _) = _ ] => assert (a = x)
    end.
    clear H0.
    generalize H1.
    repeat match goal with
             | [ H := _ |- _ ] => subst H
             | [ H : _ |- _ ] => clear H || subst H
           end.
    generalize LimitAdjunction_AComponentsOf.
    generalize LimitAdjunction_AComponentsOf_Inverse.
    generalize dependent s.
    generalize (DiagonalFunctor C D).
    generalize dependent HL.
    simpl.
    generalize (@LimitObject objC morC objD morD C D).
    simpl.
    unfold Morphism; simpl.
    intros; generalize dependent H1.
    repeat match goal with
             | [ H := _ |- _ ] => subst H
             | [ H : _ |- _ ] => clear H || subst H
           end.
    generalize dependent m0.
    generalize dependent m.
    generalize dependent s.
    generalize dependent s0.
    generalize dependent HL0.
    generalize dependent o.
    unfold HasLimits.
    generalize (@Limit objC morC objD morD C D).
    intros; generalize dependent H1.
    generalize dependent (@SpecializedFunctorCategory objD morD objC morC D C).
    intro.
    generalize dependent (@SpecializedNaturalTransformation objD morD objC morC D C).
    generalize dependent (@SpecializedFunctor objD morD objC morC D C).
    intros; generalize dependent H1.
    repeat match goal with
             | [ H := _ |- _ ] => subst H
             | [ H : _ |- _ ] => clear H || subst H
           end.
    change (@Object objC morC C) with objC in *.
    generalize dependent objC.
    generalize dependent T.
    repeat match goal with
             | [ H := _ |- _ ] => subst H
             | [ H : _ |- _ ] => clear H || subst H
           end.
    intros; generalize dependent H1.
    generalize dependent s1.
    Set Printing All.
    Goal forall A (a a' : A), id a = id a' -> a = a'.
      intros A a a' H.
      Opaque id.
      match type of H with
        | ?a = _ => match goal with
                      | [ |- appcontext[?a'] ] => change a' with a; rewrite H
                    end
      end.
      replace a with (@id A a).
      exact H.
      rewrite H.

    generalize dependent (@SpecializedFunctor objC morC).
    generalize dependent
    intros; rewrite H1.
    generalize dependent (@fst objC T s0).
    simpl; intros; rewrite H1.
    simpl; intros; rewrite H1.
    clear s.
    generalize dependent
    intros; rewrite H1.
    generalize dependent (T F).
    intros; rewrite H1.
    Print HasLimits.
    generalize dependent (fst s0).
    intros; rewrite H1.
    generalize (LimitFunctor HL).
    generalize (((HomFunctor C) (c, (LimitFunctor HL) F))).
    simpl.
    intros; rewrite H1.

    generalize dependent x.
    generalize dependent s.
    generalize (SpecializedFunctor D C).

    Set Printing All.

    Lemma foo (A : Type) (B : A -> Type) (a : A) (b b' : B a) (H : @eq (B a) b b') : @eq (id (B (id a))) b b'.
      Opaque id.
      rewrite H
    Goal forall a : Set, @eq Type a a -> @eq Set a a.
      intros a H.
    exact H1.
    rewrite H1.
    etransitivity; exact H1 || reflexivity.
    rewrite H1.
    match type of H1 with
      | ?a = ?b => pose a as a'; simpl in *; change a with a'
    end.
    simultaneous_rewrite H1
    rewrite H1.
    Implicit Arguments  LimitAdjunction_AComponentsOf [].
    Implicit Arguments  LimitAdjunction_AComponentsOf_Inverse [].
    Implicit Arguments Compose [].
    Implicit Arguments eq [].
    Definition eq' := eq. change eq with eq' in *.
    Implicit Arguments eq' [].
    Set Printing All.
    rewrite H1.
    assert (LimitAdjunction_AComponentsOf (fst s) (snd s)
      (LimitAdjunction_AComponentsOf_Inverse (fst s) (snd s) x) = LimitAdjunction_AComponentsOf (fst s) (snd s)
      (LimitAdjunction_AComponentsOf_Inverse (fst s) (snd s) x)).
    rewrite H1.
    rewrite (H1 x).
 (rewrite H0 || rewrite H1).
    try_associativity ltac:(t_with t'). || eauto; try rewrite RightIdentity.
    auto.
    unfold LimitAdjunction_AIsomorphism in H.

    intros; split.
    pose (LimitAdjunction_AIsomorphism).
    unfold CategoryIsomorphism, CategoryIsomorphism' in *.
    eapply iso_is_epi; eauto.
    exact (c _ _).
    pre_compose_to_identity.
    eapply (@iso_is_epi _ _ TypeCat).
    specialize (e _ _ TypeCat).
    unfold Epimorphism in e.
    eapply e.
    repeat match goal with
             | [ _ : appcontext[fun x => ?f x] |- _ ] => change (fun x => f x) with f in *
             | [ |- appcontext[fun x => ?f x] ] => change (fun x => f x) with f in *
           end.
    Opaque Compose.
    destruct s as [c F], d as [c' F'].
    destruct m as [f a].
    Opaque MorphismOf.
    simpl.
    Check (LimitProperty_Morphism (HL F') (Y:=c')).
    unfold HomFunctor.
    unfold ComposeFunctors.
    simpl.
    Transparent MorphismOf.
    unfold MorphismOf at 1.
    Opaque MorphismOf.
    simpl.
    Transparent MorphismOf.
    unfold MorphismOf at 1.
    Opaque MorphismOf.
    simpl.
    Transparent Object Morphism Identity.
    simpl.
    eapply iso_is_mono.
    (*
    simpl in *.*)
    unfold LimitProperty_Morphism, LimitObject.
(*    apply functional_extensionality_dep; intro.
    Transparent Morphism.
    hnf in x.*)
    (*intro_universal_objects.
    intro_universal_properties.
    intro_universal_morphisms.*)
    pose ((LimitFunctor HL).(MorphismOf') _ _ a).
    present_spnt.
    specialize_all_ways.
(*    do 3 match goal with
           | [ H : unique _ _ |- _ ] => move H at bottom
         end.*)
    destruct_hypotheses.
(*    specialize_all_ways.
    do 3 match goal with
           | [ H : unique _ _ |- _ ] => move H at bottom
         end.
    destruct_hypotheses.
    t_with t'.
    t_with t'.*)
    pose (TerminalProperty_Morphism (HL F') c') as Mc'F'.
    change (TerminalProperty_Morphism (HL F') c') with Mc'F'.
    pose (TerminalProperty_Morphism (HL F) c) as McF.
    change (TerminalProperty_Morphism (HL F) c) with McF.
    Definition Δ {objC morC objD morD C D} := @diagonal_functor_object_of objC morC objD morD C D.
    Definition ΔMor {objC morC objD morD C D} o1 o2 := @diagonal_functor_morphism_of objC morC objD morD C D o1 o2.
    Definition limo := TerminalMorphism_Object.
    Definition φ := TerminalMorphism_Morphism.
    Definition unique_m {objC morC objD morD} C {a b c} d := @TerminalProperty_Morphism objC morC objD morD C a b c d.
    change (diagonal_functor_morphism_of C D) with (@ΔMor _ _ _ _ C D) in *;
    change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor _ _ _ _ C D) in *;
    change (ObjectOf (DiagonalFunctor C D)) with (@Δ _ _ _ _ C D) in *;
    change TerminalMorphism_Object with limo in *;
    change TerminalMorphism_Morphism with φ in *;
    change TerminalProperty_Morphism with @unique_m in *.
    Opaque MorphismOf.
    simpl.
    Transparent MorphismOf.

    simpl.
    unfold MorphismOf, MorphismOf'.
    simpl
    unfold MorphismOf, MorphismOf'. simpl.
    Check Commutes.
    simpl
    present_obj_mor @Identity' @Identity; present_obj_mor @Compose' @Compose.
    match goal with
             | [ C : @SpecializedCategory ?obj ?mor |- _ ] => idtac C (*
               match goal with
(*                 | [ _ : appcontext[mor ?s ?d] |- _ ] => progress change (mor s d) with (@Morphism _ mor C s d) in * *)
                 | [ |- context[mor ?s ?d] ] => idtac mor; idtac s; idtac d; change (mor s d) with (@Morphism _ mor C s d) in *
               end*)
           end.
    Ltac present_mor_all mor_fun cat :=
      repeat match goal with
               | [ _ : appcontext[mor_fun ?s ?d] |- _ ] => progress change (mor_fun s d) with (@Morphism _ mor_fun cat s d) in *
               | [ |- appcontext[mor_fun ?s ?d] ] => progress change (mor_fun s d) with (@Morphism _ mor_fun cat s d) in *
             end.

    Ltac present_spcategory :=
      repeat match goal with
               | [ C : @SpecializedCategory ?obj ?mor |- _ ] => progress present_mor mor C
             end.
    Set Printing All.


    present_spcategory.
    present_spnt.
    simpl; intros s d m.
    destruct s as [c F], d as [c' F'].
    destruct m as [f a].
    simpl in *.
    unfold LimitProperty_Morphism, LimitObject.
    apply functional_extensionality_dep; intro.
    Transparent Morphism.
    hnf in x.
    (*intro_universal_objects.
    intro_universal_properties.
    intro_universal_morphisms.*)
    pose ((LimitFunctor HL).(MorphismOf') _ _ a).
    present_spnt.
    specialize_all_ways.
(*    do 3 match goal with
           | [ H : unique _ _ |- _ ] => move H at bottom
         end.*)
    destruct_hypotheses.
(*    specialize_all_ways.
    do 3 match goal with
           | [ H : unique _ _ |- _ ] => move H at bottom
         end.
    destruct_hypotheses.
    t_with t'.
    t_with t'.*)
    pose (TerminalProperty_Morphism (HL F') c') as Mc'F'.
    change (TerminalProperty_Morphism (HL F') c') with Mc'F'.
    pose (TerminalProperty_Morphism (HL F) c) as McF.
    change (TerminalProperty_Morphism (HL F) c) with McF.
    Definition Δ {objC morC objD morD C D} := @diagonal_functor_object_of objC morC objD morD C D.
    Definition ΔMor {objC morC objD morD C D} o1 o2 := @diagonal_functor_morphism_of objC morC objD morD C D o1 o2.
    Definition limo := TerminalMorphism_Object.
    Definition φ := TerminalMorphism_Morphism.
    Definition unique_m {objC morC objD morD} C {a b c} d := @TerminalProperty_Morphism objC morC objD morD C a b c d.
    change (diagonal_functor_morphism_of C D) with (@ΔMor _ _ _ _ C D) in *;
    change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor _ _ _ _ C D) in *;
    change (ObjectOf (DiagonalFunctor C D)) with (@Δ _ _ _ _ C D) in *;
    change TerminalMorphism_Object with limo in *;
    change TerminalMorphism_Morphism with φ in *;
    change TerminalProperty_Morphism with @unique_m in *.
    Set Printing All
    specialize_all_ways.
    do 3 match goal with
           | [ H : unique _ _ |- _ ] => move H at bottom
         end.
    destruct_hypotheses.
    pose (
    match goal with


    pose (TerminalProperty_Morphism (HL F') c') as Mc'F'.
    change (TerminalProperty_Morphism (HL F') c') with Mc'F'.
    pose (TerminalProperty_Morphism (HL F) c) as McF.
    change (TerminalProperty_Morphism (HL F) c) with McF.


    destruct s, d, m.
    simpl in *.
    unfold_SpecializedFunctorCategory.
    present_spnt.
    unfold LimitProperty_Morphism, LimitObject.
    simpl.
    intro_universal_objects.
    intro_universal_morphisms.
    intro_universal_properties.
    specialize_all_ways.
    do 3 match goal with
           | [ H : unique _ _ |- _ ] => move H at bottom
         end.
    destruct_hypotheses.
    pose (TerminalProperty (HL s) o x).
    destruct (TerminalProperty (HL s0) o0
     (SPNTComposeT s1
        (SPNTComposeT x (diagonal_functor_morphism_of C D o0 o m)))).
    clear H16.
    simpl in H15.
    s
    Definition LimitAdjunction_AComponentsOf_Inverse (c : C) (F : C ^ D)
    : TypeCat.(Morphism) (HomFunctor C (c, (LimitFunctor HL) F)) (HomFunctor (C ^ D) ((DiagonalFunctor C D) c, F)).
    Transparent Morphism.
    simpl in *; intro f; hnf; simpl.
    match goal with
      | [ |- SpecializedNaturalTransformation ?DF ?F ] =>
        eapply (Build_SpecializedNaturalTransformation DF F
          (fun d => Compose (LimitMorphism (HL F) d) f)
          _
        )
    end.
    Grab Existential Variables.
    simpl in *.
        match goal with
          | [ |- ComponentsOf ?T ?d = Compose _ _ ] => simpl_do do_rewrite_rev (Commutes T)
        end.
    unfold_Funct
    Transparent Morphism
    destruct

  Goal SpecializedAdjunction (DiagonalFunctor C D) (LimitFunctor HL).
    Print Build_SpecializedAdjunction.
    Check @AMateOf _ _ _ _ _ _ (DiagonalFunctor C D) (LimitFunctor HL).
    Eval simpl in SpecializedNaturalTransformation
         (ComposeFunctors (HomFunctor C)
            (ProductFunctor
               (IdentityFunctor _)
               (LimitFunctor HL)))
         (ComposeFunctors (HomFunctor (C ^ D))
            (ProductFunctor
               (OppositeFunctor (DiagonalFunctor C D))
               (IdentityFunctor _))).
  Print AMateOf


  Let LimitAdjunction_AComponentsOf (c : C) (F : C ^ D)
    : TypeCat.(Morphism) (HomFunctor (C ^ D) ((DiagonalFunctor C D) c, F)) (HomFunctor C (c, (LimitFunctor HL) F))
    := (fun T : HomFunctor (C ^ D) ((DiagonalFunctor C D) c, F)
      => LimitProperty_Morphism (HL F) T : HomFunctor C (c, (LimitFunctor HL) F)).

  Definition LimitAdjunction_AComponentsOf_Inverse (c : C) (F : C ^ D)
    : TypeCat.(Morphism) (HomFunctor C (c, (LimitFunctor HL) F)) (HomFunctor (C ^ D) ((DiagonalFunctor C D) c, F)).
    Transparent Morphism.
    simpl in *; intro f; hnf; simpl.
    match goal with
      | [ |- SpecializedNaturalTransformation ?DF ?F ] =>
        eapply (Build_SpecializedNaturalTransformation DF F
          (fun d => Compose (LimitMorphism (HL F) d) f)
          _
        )
    end.
    Grab Existential Variables.
    abstract (
      simpl in *; intros; rewrite RightIdentity;
        try_associativity ltac:(apply f_equal2; try reflexivity);
        match goal with
          | [ |- ComponentsOf ?T ?d = Compose _ _ ] => simpl_do do_rewrite_rev (Commutes T)
        end;
        rewrite RightIdentity;
          reflexivity
    ).
  Defined.

  Definition LimitAdjunction_AIsomorphism (c : C) (F : C ^ D) : CategoryIsomorphism (@LimitAdjunction_AComponentsOf c F).
    Transparent Object Morphism Compose Identity.
    unfold CategoryIsomorphism, CategoryIsomorphism'.
    exists (LimitAdjunction_AComponentsOf_Inverse _).
(*    abstract ( *)
      subst LimitAdjunction_AComponentsOf; unfold LimitAdjunction_AComponentsOf_Inverse;
        unfold LimitMorphism, LimitProperty_Morphism, LimitObject, Limit in *;
          split; simpl in *;
            spnt_eq;
            unfold LimitMorphism, LimitProperty_Morphism, LimitObject, Limit in *;
            intro_universal_properties;
            intro_universal_morphisms;
            destruct_hypotheses;
            specialize_all_ways;
            destruct_hypotheses;
            specialize_all_ways;
            destruct_hypotheses;
            repeat match goal with
                     | [ H : _ |- _ ] => apply (f_equal ComponentsOf) in H
                   end; fg_equal;
            destruct_hypotheses;
            try specialized_assumption idtac.
      unfold_SpecializedFunctorCategory.
            intro_universal_properties;
            intro_universal_morphisms;
            destruct_hypotheses;
            specialize_all_ways;
            destruct_hypotheses;
            specialize_all_ways;
            destruct_hypotheses;
            repeat match goal with
                     | [ H : _ |- _ ] => apply (f_equal ComponentsOf) in H
                   end; fg_equal;
            destruct_hypotheses.
            match goal with
              | [ |- TerminalProperty_Morphism ?M ?a ?b = _ ] => destruct (TerminalProperty M a b) as [ H10 ]
            end.
            move H10 at bottom.
            simpl in H10.
            apply (f_equal ComponentsOf) in H10; fg_equal.
            (*** HERE ***)
            specialize (H10 c).
            etransitivity; try apply H9.
            unfold diagonl_functor_morphism_of in H9
            destruct H8.

            specialize (H8
      Check TerminalProperty_Morphism (HL F) c
      change (@Object (@SpecializedFunctor objD morD objC morC D C)
                       (@SpecializedNaturalTransformation objD morD objC morC
                          D C) with (@SpecializedFunctor objD morD objC morC D C)
                       (@SpecializedNaturalTransformation objD morD objC morC
                          D C)
      apply functional_extensionality_dep.
            t_with t'.
      unfold_SpecializedFunctorCategory.
      match goal with
      (*     | [ _ : appcontext[@Object ?obj ?mor (?C ^ ?D)] |- _ ] => unfold_SpecializedFunctorCategory_of obj mor C
           | [ _ : appcontext[@Morphism ?obj ?mor (?C ^ ?D)] |- _ ] => unfold_SpecializedFunctorCategory_of obj mor C
           | [ _ : appcontext[@Identity ?obj ?mor (?C ^ ?D)] |- _ ] => unfold_SpecializedFunctorCategory_of obj mor C
           | [ _ : appcontext[@Compose ?obj ?mor (?C ^ ?D)] |- _ ] => unfold_SpecializedFunctorCategory_of obj mor C
           | [ |- appcontext[@Object ?obj ?mor (?C ^ ?D)] ] => unfold_SpecializedFunctorCategory_of obj mor C*)
           | [ |- appcontext[@Morphism ?obj ?mor (?C ^ ?D)] ] => idtac C; idtac D(*; unfold_SpecializedFunctorCategory_of obj mor C*)(*
           | [ |- appcontext[@Identity ?obj ?mor (?C ^ ?D)] ] => unfold_SpecializedFunctorCategory_of obj mor C
           | [ |- appcontext[@Compose ?obj ?mor (?C ^ ?D)] ] => unfold_SpecializedFunctorCategory_of obj mor C*)
         end.
      auto.
            t_with t'.
      match goal with
        | [ |- TerminalProperty_Morphism ?M ?a ?b = _ ] => pose (TerminalProperty M a b)
      end.
      destruct_hypotheses.
      specialize_all_ways.
            repeat match goal with
                     | [ H : _ |- _ ] => apply (f_equal ComponentsOf) in H
                   end; fg_equal.
            simpl in *.
            eapply H6.
            rewrite <- H8 at 2

              try rewrite_unique;
                intro_fresh_unique; simpl.
              try rewrite_unique.

            intro_proj2_sig_from_goal; simpl;
              destruct_hypotheses;
              try rewrite_unique;
                intro_fresh_unique; simpl.
      hnf in *.
      unfold TerminalProperty_Morphism.
      intro_proj2_sig_from_goal; simpl;
              destruct_hypotheses;
              try rewrite_unique;
                intro_fresh_unique; simpl.
      unfold Morphism in *; simpl in *.
      unfold CommaSpecializedCategory_Morphism in *.
      repeat match goal with
               | [ H : _ |- _ ] => clear H
             end.
      intro_proj2_sig_from_goal; simpl;
              destruct_hypotheses;
              try rewrite_unique;
                intro_fresh_unique; simpl.

 . simpl.
            intro_proj2_sig_from_goal; simpl.

                t_rev_with t'.
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
      => fun f : HomFunctor C (ColimitFunctor HC F, c)
        => Build_SpecializedNaturalTransformation F (diagonal_functor_object_of C D c)
        (fun d => Compose f (projT1 (projT2 (HC F)) d))
        _
        : HomFunctor (C ^ D) (F, DiagonalFunctor C D c)
    ) |}; try (
      intros F c; eexists (fun (T : SpecializedNaturalTransformation F (DiagonalFunctor C D c))
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
*)
