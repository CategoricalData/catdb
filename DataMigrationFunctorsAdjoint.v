Require Import FunctionalExtensionality.
Require Export Adjoint DataMigrationFunctors.
Require Import Common Notations FunctorCategory LimitFunctors AdjointUnit CommaCategory InducedLimitFunctors CommaCategoryFunctors (* NaturalTransformation Hom Duals CommaCategoryFunctors SetLimits SetColimits LimitFunctors LimitFunctorTheorems InducedLimitFunctors DefinitionSimplification FEqualDep CommaCategoryFunctorProperties*).

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.
(*
Section coslice_initial.
  (* TODO(jgross): This should go elsewhere *)
  Definition CosliceCategory_InitialObject C D (F : Functor C D) x :
    { o : _ & @InitialObject _ (CosliceCategory (F x) F) o }.
    unfold Object; simpl;
    match goal with
      | [ |- { o : CommaCategory_Object ?A ?B & _ } ] =>
        (exists (existT _ (tt, _) (@Identity D _) : CommaCategory_ObjectT A B))
    end;
    simpl.
    intro o'; hnf; simpl.
    destruct o' as [ [ [ ? o' ] m' ] ]; simpl in *.
    evar (T : Type); evar (t : T); subst T.
    eexists (Build_CommaCategory_Morphism _ _ _).
    instantiate (1 := t); simpl in *.

    {αβ : unit * objC & Morphism D (F x) (F (snd αβ))}
    instantiate (1 := t).
    simpl in t.
    evar_exists.
    eexists.
    hnf.
    intro o'.


End coslice_initial.
*)
Section DataMigrationFunctorsAdjoint.
  Variables C D : Category.
  Variables S : Category.

  Variable F : Functor C D.

  Let Δ_F := PullbackAlong C D S F.

  Section ΔΠ.
    (*Variable HasLimits' : forall (F : Functor C D), Limit F.
    Goal forall F (M := TerminalMorphism_Morphism (HasLimits' F)), True.
    intros.
    hnf in M.


                           Limit (RightPushforwardAlong_pre_Functor C D S F g d).*)
    Variable HasLimits : forall (g : FunctorCategory C S) (d : D),
                           Limit (RightPushforwardAlong_pre_Functor C D S F g d).
    Let Π_F := RightPushforwardAlong HasLimits.

    Definition Pullback_RightPushforward_AdjunctionCounit_NaturalTransformation_ComponentsOf_ComponentsOf (G : S ^ C) (c : C) :
      Morphism S ((ComposeFunctors (RightPushforwardAlong_ObjectOf HasLimits G) F) c) (G c)
      := (TerminalMorphism_Morphism (HasLimits G (F c))
                                    (existT
                                       _
                                       (tt, c)
                                       (Identity (F c)) :
                                       CommaCategory_ObjectT (SliceCategory_Functor D (F c)) F)).
    (* simpl in *.
      unfold Limit, LimitObject in *;
        intro_from_universal_objects;
        intro_universal_morphisms;
        simpl in *.
      match goal with
        | [ m : NaturalTransformation _ _ |- _ ] =>
          let X := constr:(ComponentsOf m) in
          match type of X with
            | forall _ : ?T, _ => match eval hnf in T with
                                    | CommaCategory_Object ?A ?B =>
                                      let x := constr:(CommaCategory_ObjectT A B) in
                                      match eval hnf in x with
                                        | @sigT (?A' * ?B') ?C' =>
                                          let a := fresh in
                                          let b := fresh in
                                          let c := fresh in
                                          match A' with | unit => pose tt as a | _ => evar (a : A') end;
                                          match B' with | unit => pose tt as b | _ => evar (b : B') end;
                                          evar (c : C' (a, b));
                                          let X' := fresh in
                                          pose (X ((@existT _ _ (a, b) c) : CommaCategory_ObjectT A B)) as X';
                                            subst a b c;
                                            simpl in X';
                                            apply X'
                                      end
                                  end
          end
      end.
      Grab Existential Variables.
      apply Identity.
    Defined. *)

    Eval cbv beta iota zeta delta [Pullback_RightPushforward_AdjunctionCounit_NaturalTransformation_ComponentsOf_ComponentsOf] in Pullback_RightPushforward_AdjunctionCounit_NaturalTransformation_ComponentsOf_ComponentsOf.

    Definition Pullback_RightPushforward_AdjunctionCounit_NaturalTransformation_ComponentsOf (G : S ^ C) :
      Morphism (S ^ C) ((ComposeFunctors Δ_F Π_F) G) ((IdentityFunctor _) G).
      exists (Pullback_RightPushforward_AdjunctionCounit_NaturalTransformation_ComponentsOf_ComponentsOf G).
      unfold Pullback_RightPushforward_AdjunctionCounit_NaturalTransformation_ComponentsOf_ComponentsOf;
        simpl;
        intros.
      unfold RightPushforwardAlong_ObjectOf_MorphismOf, InducedLimitFunctor_MorphismOf, InducedLimitMap, InducedLimitMapNT, LimitObject; simpl.
      (* nt_hideProofs. *)
      unfold ComposeFunctorsAssociator1; simpl. (* ; nt_hideProofs. *)
      unfold NTComposeT, NTComposeF; simpl. (* ; nt_hideProofs. *)
      nt_hideProofs.
      simpl in *.
      (* setoid_rewrite FIdentityOf. (* fails with "Error: build_signature: no constraint can apply on a dependent argument" *) *)
      match goal with
        | [ |- ?A = _ ] =>
          match A with
            | context A'[@Build_NaturalTransformation ?objC ?C ?objD ?D ?F ?G ?CO _] =>
              (* make evars for ComponentsOf, Commutes *)
              let ComT := fresh in
              let Com' := fresh in
              let COT := fresh in
              let CO' := fresh in
              evar (COT : Type); evar (CO' : COT); evar (ComT : Type); evar (Com' : ComT); subst COT ComT;
              (* assert equality of ComponentsOf parts *)
              let H := fresh in
              assert (H : forall x, CO x = CO' x);
                [ subst CO'; intro;
                  (* kill the identity terms *)
                  repeat rewrite FIdentityOf;
                  repeat rewrite LeftIdentity;
                  repeat rewrite RightIdentity;
                  reflexivity
                | ];
                (* do transitivity with the evar'd components *)
                let A'' := context A'[@Build_NaturalTransformation C D F G CO' Com'] in
                transitivity A''; subst Com' CO'
          end
      end.
      apply f_equal.
      apply f_equal.
      nt_eq.
      simpl in *.
      match goal with
        | [ H : _ |- _ ] => apply H
      end.
      clear.
      nt_hideProofs.
      clear e.
      simpl in *.
      present_spfunctor.
      present_spcategory.
      Print CommaCategory_Object.
      Check fun (g : (S ^ C)%functor) (d : D) =>
              (RightPushforwardAlong_pre_Functor C D S F g d).
      match goal with
        | [ |- Compose ?a ?b = Compose ?c ?d ] => pose a; pose b; pose c; pose d; simpl in *
      end.
      pose ((HasLimits G (F d))); simpl in *.
      rename s into c, d into c'.
      pose (TerminalProperty_Morphism (HasLimits G (F c')) (TerminalMorphism_Object (HasLimits G (F c)))).
      clear m1; revert e0.
      match goal with
        | [ |- context[{| ComponentsOf' := ?x |}] ] => let x' := fresh in set (x' := x)
      end.
      intro e0.
      setoid_rewrite LeftIdentity in e0.
      unfold RightPushforwardAlong_pre_Functor in *; simpl in *.
      pose (fun (g : (S ^ C)%functor) (d : D) =>
              (CosliceCategoryProjection d F)).
      intro_universal_properties.
      unfold unique in *; simpl in *.
      split_and.
      match goal with
        | [ |- _ = Compose _ ?X ] => let x := fresh in pose X as x; move x at bottom; simpl in x
      end.

      pose @TerminalProperty_Morphism.
      Set Printing All.
      pose ((TerminalMorphism_Morphism (HasLimits G (F c)))
        (existT (fun αβ : unit * LSObject C => Morphism D (F c) (F (snd αβ)))
           (tt, c) (Identity (F c)))).
      pose ((RightPushforwardAlong_pre_Functor C D S F G (F d))); simpl in *.
      match goal with
        | [ |- Compose ?a ?b = Compose ?c ?d ] => pose a; pose
      pose (RightPushforwardAlong_pre_Functor C D S F G (F d)) as x.
      simpl in x.
      hnf in x; simpl in x.
      rename m0 into M0.
      match goal with
        | [ |- Compose ?a ?b = _ ] => pose a as m0
      end.
      simpl in m0.
      pose (TerminalMorphism_Morphism (HasLimits G (F d)))
          (existT
             (fun αβ : unit * LSObject C => Morphism D (F d) (F (snd αβ)))
             (tt, d) (Identity (F d)))
      assert True.
      -
        unfold CosliceCategory, CommaCategory, Object in x; simpl in x.
        unfold Object in x.
      asser
      Check (TerminalMorphism_Morphism (HasLimits G (F d)) (existT (fun αβ : unit * LSObject C => Morphism D (F d) (F (snd αβ)))
           (tt, d) (Identity (F d)))).
      match goal with
        | [ |- context G[@Build_CommaCategory_Object ?objA ?A ?objB ?C ?objC ?C
      Set Printing All.
      assert (Compose
     ((TerminalMorphism_Morphism (HasLimits G (F d)))
        (existT (fun αβ : unit * LSObject C => Morphism D (F d) (F (snd αβ)))
           (tt, d) (Identity (F d))))
     (TerminalProperty_Morphism (HasLimits G (F d))
        (TerminalMorphism_Object (HasLimits G (F s)))
        {|
        ComponentsOf' := fun x : CosliceCategory (F d) F =>
                         (TerminalMorphism_Morphism (HasLimits G (F s)))
                           (existT
                                                  (fun αβ : unit * LSObject C =>
                                                  Morphism D
                                                  (F s)
                                                  (F (snd αβ))) (projT1 x)
                                                  (Compose
                                                  (projT2 x)
                                                  (MorphismOf F m)));
        Commutes' := e0 |}) =
   Compose (MorphismOf G m)
     ((TerminalMorphism_Morphism (HasLimits G (F s))))).
      intro_universal_properties.
      Check TerminalProperty_Morphism (HasLimits G (F d)).
      hnf in *.
      split_and.
      apply H3.
      t with
      expand.
      match goal with
        | [ |- @eq (@NaturalTransformation ?objC ?C ?objD ?D ?F ?G) _ _ ] =>
          apply (@NaturalTransformation_eq C D F G)
      end.
      nt_eq.
      assumption.
rewrite <- H3.

      apply f_equal5.
      f_equal.
      reflexivity.
              (* assert equality of the Components

      etransitivity.
      mat
      - do 3 match goal with
               | [ |- @Build_NaturalTransformation ?objC ?C ?objD ?D ?F ?G _ _ = _ ] => (apply (@NaturalTransformation_eq C D F G); simpl) || fail 1 "Cannot apply NaturalTransformation_eq"
               | [ |- appcontext[Build_NaturalTransformation] ] => apply f_equal2 || apply f_equal || fail 1 "Cannot apply f_equal"
               | _ => reflexivity
             end.
        instantiate (1 := (fun x : CosliceCategory (F d) F =>
    (TerminalMorphism_Morphism (HasLimits G (F s)))
      {|
      CommaCategory_Object_Member := existT
                                                  (fun αβ : unit * LSObject C =>
                                                  Morphism D
                                                  (F s)
                                                  (F (snd αβ)))
                                                  (projT1 x)
                                                  (Compose
                                                  (projT2 x)
                                                  (MorphismOf F m)) |})).
        apply functional_extensionality_dep; intro.
        clear.
        clear e.
        repeat rewrite FIdentityOf;
          repeat rewrite LeftIdentity; repeat rewrite RightIdentity.
        Show Existentials.
        revert x.
        match goal with
          | [ |- forall x : ?T, @?A x = @?B x ] => cut (A = B); change (fun x => ?f x) with f;
                                                   [ let H := fresh in intro H; rewrite <- H; simpl; reflexivity | ]
        end.
        Show Existentials.
        instantiate (1 := (fun x : CosliceCategory (F d) F =>
    (TerminalMorphism_Morphism (HasLimits G (F s)))
      {|
      CommaCategory_Object_Member := existT
                                                  (fun αβ : unit * LSObject C =>
                                                  Morphism D
                                                  (F s)
                                                  (F (snd αβ)))
                                                  (projT1 x)
                                                  (Compose
                                                  (projT2 x)
                                                  (MorphismOf F m)) |})).

        match goal with
          | [
        etransitivity.
        Focus 2.
        instantiate (1 := (fun x => (TerminalMorphism_Morphism (HasLimits G (F s)))
     {|
     CommaCategory_Object_Member := existT
                                                 (fun αβ : unit * LSObject C =>
                                                  Morphism D
                                                  (F s)
                                                  (F (snd αβ)))
                                                 (projT1 x)
                                                 (Compose
                                                  (projT2 x)
                                                  (MorphismOf F m)) |})).
        match goal with
          | [ |- forall x : ?T, @?A x = @?B x ] => instantiate (1 := fun x => A x)
        end.
        clear e.
        reflexivity.
        subst_body.
        instantiate (1 := (fun x => _)).
        reflexivity.
        pattern x.
        reflexivity.
        setoid_rewrite FIdentityOf.



        match goal with
          | [ |- appcontext[Build_NaturalTransformation] ] => try apply f_equal2

        end.

      match goal with
        | [ |- appcontext[@Build_NaturalTransformation ?objC ?C ?objD ?D ?F ?G ?CO ?Com] ] =>
          let A := fresh in
          let H := fresh in
          set (A := CO);
            match CO with
              | context CO'[MorphismOf ?G (Identity _)] => let CO'' := context CO'[Identity (G x)] in
                                                            assert (H : A = CO'')
            end;
            simpl in *
      end.
      match
      setoid_rewrite FIdentityOf in H0.
      Require Import Setoid.
      present_spnt.
      setoid_rewrite FIdentityOf in H0.
      clear.
      revert e2.
      nt_hideProofs.

      intros.

      clear.

      match goal with
        | [ |- appcontext[@Build_NaturalTransformation _ ?C _ ?D ?F ?G ?CO ?Com] ] =>
          assert (forall com, @Build_NaturalTransformation _ C _ D F G CO com = @Build_NaturalTransformation _ C _ D F G CO com)
                 by reflexivity
      end.
      assert True.
      - clear e3 e2 e1 e0 e.
        revert H.
        functor_hideProofs.
        present_spcategory.
        match goal with
          | [ |- ?A -> True ] => assert A
        end.
        intro.
        match goal with
          | [ |- ?A = ?B ] => assert (forall x, ComponentsOf A x = ComponentsOf B x)
        end; simpl.
        intro.
        + repeat rewrite FIdentityOf.
          repeat rewrite LeftIdentity.
          repeat rewrite FIdentityOf.
          repeat rewrite RightIdentity.
          reflexivity.
        rewrite
        intro.
        setoid_rewrite FIdentityOf.
        pose (fun c => Compose
                           (Compose
                              (Compose
                                 (Compose
                                    (MorphismOf G (Identity (snd (projT1 c))))
                                    (Identity (G (snd (projT1 c)))))
                                 (Identity (G (snd (projT1 c)))))
                              (Compose
                                 (MorphismOf G (Identity (snd (projT1 c))))
                                 ((TerminalMorphism_Morphism
                                     (HasLimits G (F s)))
                                    {|
                                    CommaCategory_Object_Member := existT
                                                  (fun αβ : unit * LSObject C =>
                                                  Morphism D
                                                  (F s)
                                                  (F (snd αβ))) (projT1 c)
                                                  (Compose
                                                  (projT2 c)
                                                  (MorphismOf F m)) |})))
                           (Identity
                              (TerminalMorphism_Object (HasLimits G (F s))))).
      pose


      functor_hideProofs.
      Implicit Arguments existT [].
      assert (
          forall e2 e2',
{|
        ComponentsOf' := fun c : CosliceCategory (F d) F =>
                         Compose
                           (Compose
                              (Compose
                                 (Compose
                                    (MorphismOf G (Identity (snd (projT1 c))))
                                    (Identity (G (snd (projT1 c)))))
                                 (Identity (G (snd (projT1 c)))))
                              (Compose
                                 (MorphismOf G (Identity (snd (projT1 c))))
                                 ((TerminalMorphism_Morphism
                                     (HasLimits G (F s)))
                                    {|
                                    CommaCategory_Object_Member := @existT
                                                  (unit * LSObject C)
                                                  (fun αβ : unit * LSObject C =>
                                                  Morphism D
                                                  (F s)
                                                  (F (snd αβ))) (projT1 c)
                                                  (Compose
                                                  (projT2 c)
                                                  (MorphismOf F m)) |})))
                           (Identity
                              (TerminalMorphism_Object (HasLimits G (F s))));
        Commutes' := e2 |}
=
{|
        ComponentsOf' := fun c : CosliceCategory (F d) F =>
                         Compose
                           (Compose
                              (Compose
                                 (Compose
                                    (MorphismOf G (Identity (snd (projT1 c))))
                                    (Identity (G (snd (projT1 c)))))
                                 (Identity (G (snd (projT1 c)))))
                              (Compose
                                 (MorphismOf G (Identity (snd (projT1 c))))
                                 ((TerminalMorphism_Morphism
                                     (HasLimits G (F s)))
                                    {|
                                    CommaCategory_Object_Member := @existT
                                                  (unit * LSObject C)
                                                  (fun αβ : unit * LSObject C =>
                                                  Morphism D
                                                  (F s)
                                                  (F (snd αβ))) (projT1 c)
                                                  (Compose
                                                  (projT2 c)
                                                  (MorphismOf F m)) |})))
                           (Identity
                              (TerminalMorphism_Object (HasLimits G (F s))));
        Commutes' := e2 |}).
            {|
              ComponentsOf' := fun c : CosliceCategory (F d) F =>
                                 Compose
                                   (Compose
                                      (Compose
                                         (Compose
                                            (MorphismOf G (Identity (snd (projT1 c))))
                                            (Identity (G (snd (projT1 c)))))
                                         (Identity (G (snd (projT1 c)))))
                                      (Compose
                                         (MorphismOf G (Identity (snd (projT1 c))))
                                         ((TerminalMorphism_Morphism
                                             (HasLimits G (F s)))
                                            {|
                                              CommaCategory_Object_Member := existT
                                                                                          (fun αβ : unit * LSObject C =>
                                                                                             Morphism D
                                                                                                      (F s)
                                                                                                      (F (snd αβ))) (projT1 c)
                                                                                          (Compose
                                                                                             (projT2 c)
                                                                                             (MorphismOf F m)) |})))
                                   (Identity
                                      (TerminalMorphism_Object (HasLimits G (F s))));
              Commutes' := e2 |} =
            {|
              ComponentsOf' := fun c : CosliceCategory (F d) F =>
                                 Compose
                                   (Compose
                                      (Compose
                                         (Compose
                                            (MorphismOf G (Identity (snd (projT1 c))))
                                            (Identity (G (snd (projT1 c)))))
                                         (Identity (G (snd (projT1 c)))))
                                      (Compose
                                         (MorphismOf G (Identity (snd (projT1 c))))
                                         ((TerminalMorphism_Morphism
                                             (HasLimits G (F s)))
                                            {|
                                              CommaCategory_Object_Member := existT
                                                                                          (fun αβ : unit * LSObject C =>
                                                                                             Morphism D
                                                                                                      (F s)
                                                                                                      (F (snd αβ))) (projT1 c)
                                                                                          (Compose
                                                                                             (projT2 c)
                                                                                             (MorphismOf F m)) |})))
                                   (Identity
                                      (TerminalMorphism_Object (HasLimits G (F s))));
              Commutes' := e2' |}).
      revert e2; nt_hideProofs; functor_hideProofs.
      revert dependent e.
      revert dependent e0.
      revert dependent e1.
      nt_hideProofs.
      revert e.
      setoid_rewrite FIdentityOf.
      autorewrite with category.
      rewrite LeftIdentityNaturalTransformation.

      Implicit Arguments Compose [].
      Compose
        (CObject S)
        S
        (LimitObject (HasLimits G (F s)))
        (LimitObject (HasLimits G (F d)))
        (G d)
        ((TerminalMorphism_Morphism (HasLimits G (F d)))
           (existT (fun αβ : unit * LSObject C => Morphism D (F d) (F (snd αβ)))
                   (tt, d) (Identity (F d))))
        (RightPushforwardAlong_ObjectOf_MorphismOf HasLimits G
                                                   (F s) (F d) (MorphismOf F m))
      unfold Compose.
      expand.
      Check TerminalMorphism_Morphism.
      fold @LimitObject in *.
      subst_body.
      unfold Limit in *; simpl in *.
      intro_universal_properties.
      hnf in G; simpl in *.
      Check @ComponentsOf _ _ _ _ (ComposeFunctors (RightPushforwardAlong_ObjectOf HasLimits G) F) G.
    Definition Pullback_RightPushforward_AdjunctionUnit : AdjunctionCounit Δ_F Π_F.
      hnf.
      Definition Pullback_RightPushforward_AdjunctionCounit_NaturalTransformation :
        NaturalTransformation (ComposeFunctors Δ_F Π_F) (IdentityFunctor _).
        Check @ComponentsOf _ _ _ _ (ComposeFunctors Δ_F Π_F)
              (IdentityFunctor (S ^ C)%functor).

      let t := type of H1 in
      pose ((@existT _ _ (H, H0) H1) : CommaCategory_ObjectT (SliceCategory_Functor D (F c)) F) as H2.
      Set Printing All.

      Print CommaCategory_Object.
      unfold
      apply X.
      intro_universal_properties.
      intro_universal_
      simpl in *.
      intro_universal_property_morphisms.
      simpl


      assert (NaturalTransformation (IdentityFunctor (S ^ D)%functor)
       (ComposeFunctors Π_F Δ_F)).
      assert (forall c : (S ^ D)%functor,
       Morphism (S ^ D)%functor ((IdentityFunctor (S ^ D)%functor) c)
         ((ComposeFunctors Π_F Δ_F) c)).
      intro G; hnf in G.
      simpl in *.
      assert (forall c : D,
       Morphism S (G c)
         ((RightPushforwardAlong_ObjectOf HasLimits (ComposeFunctors G F)) c)).
      intro c.
      simpl in *.
      Check @ComponentsOf _ _ _ _ c
     (RightPushforwardAlong_ObjectOf HasLimits (ComposeFunctors c F)).
      Check @ComponentsOf _ _ _ _ (IdentityFunctor (S ^ D)%functor)
       (ComposeFunctors Π_F Δ_F).
      hnf.

      Definition
    Print AdjunctionUnit.

    Definition Pullback_RightPushforward_HomAdjunction_AComponentsOf :
      forall A A', Morphism (S ^ C) (Δ_F A) A' -> Morphism (S ^ D) A (Π_F A').
      intros; hnf in *.
      destruct X.
      assert (forall c : D, Morphism S (A c) ((Π_F A') c)).
      intro.
      clear Commutes'.
      present_spfunctor.
      subst_body; simpl in *.
      Check @ComponentsOf _ _ _ _ A (Π_F A').


    Definition Pullback_RightPushforward_HomAdjunction : HomAdjunction Δ_F Π_F.
      Eval hnf in HomAdjunction Δ_F Π_F.
      Check @AComponentsOf' _ _
         _ _ Δ_F Π_F.
      Check @AComponentsOf _ _ _ _ Δ_F Π_F.


  End ΔΠ.

  Section Δ.
    Definition PullbackAlong : Functor (S ^ D) (S ^ C).
  End Δ.

  Section Π.
    Local Notation "A ↓ F" := (CosliceCategory A F).
    (*Local Notation "C / c" := (@SliceCategoryOver _ _ C c).*)

    (** Quoting David Spivak in "Functorial Data Migration":
       Definition 2.1.2. Let [F : C -> D] be a morphism of schemas and
       [Δ_F : D–Set -> C–Set] be the associated data pull-back functor
       (see Definition 1.3.1). There exists a right adjoint to [Δ_F]
       called the right push-forward functor associated to [F], denoted
       [Π_F : C–Set -> D–Set], and defined as follows.
       Given an object [ɣ : C -> Set] in [C–Set] define [Π_F ɣ] on an
       object [d : D] as
       [[
         Π_F ɣ(d) := lim_{d ↓ F} (ɣ ○ (π^F d))
       ]]
       This is simply the limit of the functor
       [[
         (d ↓ F) --- (π^F d) ---> C --- ɣ ---> Set
       ]]
       Given a map [h : d -> d'] in D one obtains a map
       [Π_F ɣ(h) : Π_F ɣ(d) -> Π_F ɣ(d')] by the universal property of
       limits.
       The idea is this. We have some [C-set] [ɣ] and we want a [D-set]
       [Π_F ɣ]. To each object in [d] we look at the objects in [C]
       which are sent to the right of [d] (i.e. those equipped with a
       chosen morphism from [d]). Each has been assigned by [ɣ]some
       set of rows; we take the limit of all these sets and assign
       that to [Π_F ɣ(d)].
       *)

    (* Define [ɣ ○ (π^F d)] *)
    Definition RightPushforwardAlong_pre_Functor (g : S ^ C) (d : D) : Functor (d ↓ F) S
      := ComposeFunctors g (projT2 (CosliceCategoryProjectionFunctor C D F d)).

    Variable HasLimits : forall g d, Limit (RightPushforwardAlong_pre_Functor g d).

    Let Index2Cat d := d ↓ F.

    Local Notation "'CAT' ⇑ D" := (@LaxCosliceCategory _ _ Index2Cat _ D).

    Let RightPushforwardAlong_ObjectOf_ObjectOf (g : S ^ C) d := LimitObject (HasLimits g d).

    Let RightPushforwardAlong_ObjectOf_MorphismOf_Pre' (g : S ^ C) s d (m : Morphism D s d) :
      {F0 : unit * Functor (d ↓ F) (s ↓ F) &
        NaturalTransformation
        (ComposeFunctors (RightPushforwardAlong_pre_Functor g s) (snd F0))
        (RightPushforwardAlong_pre_Functor g d) }.
      exists (tt, fst (proj1_sig (MorphismOf (CosliceCategoryProjectionFunctor C D F) m))).
      unfold RightPushforwardAlong_pre_Functor;
        hnf;
          simpl;
            unfold Object, Morphism, GeneralizeFunctor.
      match goal with
        | [ |- NaturalTransformation (ComposeFunctors (ComposeFunctors ?g ?h) ?i) _ ] =>
          eapply (NTComposeT _ (ComposeFunctorsAssociator1 g h i))
      end.
      Grab Existential Variables.
      eapply (NTComposeF (IdentityNaturalTransformation g) _).
      Grab Existential Variables.
      match goal with
        | [ C : _ |- NaturalTransformation ?F ?G ] =>
          refine (Build_NaturalTransformation F G
            (fun _ => Identity (C := C) _)
            _
          )
      end;
      abstract (
        simpl; intros ? ? m0;
          destruct m0 as [ [ m0 ] ]; simpl;
            rewrite LeftIdentity; rewrite RightIdentity;
              reflexivity
      ).
    Defined.

    Let RightPushforwardAlong_ObjectOf_MorphismOf_Pre'' (g : S ^ C) s d (m : Morphism D s d) :
      Morphism (CAT ⇑ S)
      (existT _ (tt, s) (RightPushforwardAlong_pre_Functor g s) : @LaxCosliceCategory_ObjectT _ _ Index2Cat _ _)
      (existT _ (tt, d) (RightPushforwardAlong_pre_Functor g d) : @LaxCosliceCategory_ObjectT _ _ Index2Cat _ _).
    Proof.
      hnf.
      match goal with
        | [ |- LaxCosliceCategory_Morphism ?a ?b ] =>
          exact (RightPushforwardAlong_ObjectOf_MorphismOf_Pre' g _ _ m : @LaxCosliceCategory_MorphismT _ _ _ _ _ a b)
      end.
    Defined.

    Definition RightPushforwardAlong_ObjectOf_MorphismOf_Pre (g : S ^ C) s d (m : Morphism D s d) :
      Morphism (CAT ⇑ S)
      (existT _ (tt, s) (RightPushforwardAlong_pre_Functor g s) : @LaxCosliceCategory_ObjectT _ _ Index2Cat _ _)
      (existT _ (tt, d) (RightPushforwardAlong_pre_Functor g d) : @LaxCosliceCategory_ObjectT _ _ Index2Cat _ _)
      := Eval cbv beta iota zeta delta [RightPushforwardAlong_ObjectOf_MorphismOf_Pre' RightPushforwardAlong_ObjectOf_MorphismOf_Pre'' RightPushforwardAlong_ObjectOf_ObjectOf Index2Cat] in
        @RightPushforwardAlong_ObjectOf_MorphismOf_Pre'' g s d m.

    (* TODO(jgross): Check if [simpl in *] would make this faster. *)
    Ltac step := clear; subst_body;
                 ((abstract (autorewrite with category; reflexivity))
                    || (abstract apply SliceCategoryInducedFunctor_FIdentityOf)
                    || (abstract apply CosliceCategoryInducedFunctor_FIdentityOf)
                    || (abstract apply SliceCategoryInducedFunctor_FCompositionOf)
                    || (abstract apply CosliceCategoryInducedFunctor_FCompositionOf)
                    || apply CommaCategory_Morphism_eq
                    || apply f_equal
                    || (apply f_equal2; try reflexivity; [])
                    || apply sigT_eq (* simpl_eq *)
                    || (progress nt_eq)
                    || (progress functor_eq)); simpl; trivial.

    Ltac anihilate := repeat step.

    Local Ltac pre_anihilate :=
      simpl;
      subst_body;
      clear;
      nt_hideProofs;
      unfold NTComposeF, NTComposeT; simpl;
      nt_hideProofs;
      clear; simpl in *.


    Lemma RightPushforwardAlong_ObjectOf_FCompositionOf_Pre (g : S ^ C) s d d' (m1 : Morphism D s d) (m2 : Morphism D d d') :
      RightPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ (Compose m2 m1) =
      Compose (C := LaxCosliceCategory _ _) (RightPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ m2) (RightPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ m1).
    Proof.
      (* For speed temporarily *)
    Admitted. (*
      unfold RightPushforwardAlong_ObjectOf_MorphismOf_Pre.
Time pre_anihilate.
      Time (anihilate). (* 85 s *)
    Qed. *)

    Lemma RightPushforwardAlong_ObjectOf_FIdentityOf_Pre (g : S ^ C) x :
      RightPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ (Identity x) =
      Identity (C := LaxCosliceCategory _ _) _.
    Proof.
      unfold RightPushforwardAlong_ObjectOf_MorphismOf_Pre.
      Time pre_anihilate.
      Time anihilate. (* 12 s *)
    Qed.

    Definition RightPushforwardAlong_ObjectOf_MorphismOf (g : S ^ C) s d (m : Morphism D s d) :
      Morphism S (RightPushforwardAlong_ObjectOf_ObjectOf g s) (RightPushforwardAlong_ObjectOf_ObjectOf g d).
      subst RightPushforwardAlong_ObjectOf_ObjectOf RightPushforwardAlong_ObjectOf_MorphismOf_Pre' RightPushforwardAlong_ObjectOf_MorphismOf_Pre''; simpl.
      apply (InducedLimitFunctor_MorphismOf (Index2Cat := Index2Cat) (D := S)
        (s := existT _ (tt, s) (RightPushforwardAlong_pre_Functor g s) : LaxCosliceCategory_ObjectT _ _)
        (d := existT _ (tt, d) (RightPushforwardAlong_pre_Functor g d) : LaxCosliceCategory_ObjectT _ _)
        (HasLimits g s)
        (HasLimits g d)
      ); simpl in *.
      apply RightPushforwardAlong_ObjectOf_MorphismOf_Pre; assumption.
    Defined.

    Hint Resolve RightPushforwardAlong_ObjectOf_FIdentityOf_Pre RightPushforwardAlong_ObjectOf_FCompositionOf_Pre.

    Definition RightPushforwardAlong_ObjectOf (g : S ^ C) : S ^ D.
      pose proof (InducedLimitFunctor (Index2Cat := Index2Cat) (D := S)).
      hnf.
      unfold Object in X.
      simpl in X.
(*      Set Printing All. *)
      refine (Build_Functor D S
        (@RightPushforwardAlong_ObjectOf_ObjectOf g)
        (@RightPushforwardAlong_ObjectOf_MorphismOf g)
        _
        _
      );
      unfold RightPushforwardAlong_ObjectOf_MorphismOf;
        subst RightPushforwardAlong_ObjectOf_MorphismOf_Pre'' RightPushforwardAlong_ObjectOf_MorphismOf_Pre' RightPushforwardAlong_ObjectOf_ObjectOf;
          simpl;
            present_spcategory;
            abstract (
              present_spcategory;
              first [
                intros s d d' m1 m2;
                  etransitivity;
                  try apply (InducedLimitFunctor_FCompositionOf (Index2Cat := Index2Cat) (D := S)
                    (s := existT _ (tt, s) (RightPushforwardAlong_pre_Functor g s) : LaxCosliceCategory_ObjectT _ _)
                    (d := existT _ (tt, d) (RightPushforwardAlong_pre_Functor g d) : LaxCosliceCategory_ObjectT _ _)
                    (d' := existT _ (tt, d') (RightPushforwardAlong_pre_Functor g d') : LaxCosliceCategory_ObjectT _ _)
                    (HasLimits g s)
                    (HasLimits g d)
                    (HasLimits g d')
                    (RightPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ m1)
                    (RightPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ m2)
                  ); []
                |
                  intros x;
                    etransitivity;
                    try apply (InducedLimitFunctor_FIdentityOf (Index2Cat := Index2Cat) (D := S)
                      (existT _ (tt, x) (RightPushforwardAlong_pre_Functor g x) : LaxCosliceCategory_ObjectT _ _)
                      (HasLimits g x)
                    ); []
              ];
              apply f_equal;
                trivial
            ).
    Defined.

    Definition RightPushforwardAlong_MorphismOf_ComponentsOf_Pre (s d : S ^ C) (m : NaturalTransformation s d) (c : D) :
      NaturalTransformation
      (ComposeFunctors (RightPushforwardAlong_pre_Functor s c) (IdentityFunctor _))
      (RightPushforwardAlong_pre_Functor d c).
    Proof.
      eapply (NTComposeT (ComposeFunctorsAssociator1 _ _ _) _).
      Grab Existential Variables.
      match goal with
        | [ |- NaturalTransformation ?F ?G ] =>
          refine (Build_NaturalTransformation F G
            (fun x => m (snd (projT1 x)))
            _
          )
      end;
      abstract (
        repeat (let H := fresh in intro H; destruct H as [ [ [ ] ] ]; simpl in *);
          match goal with
            | [ H : _ |- _ ] => rewrite RightIdentity in H
            | [ H : _ |- _ ] => rewrite LeftIdentity in H
          end;
          subst;
            apply Commutes
      ).
    Defined.

    Definition RightPushforwardAlong_MorphismOf_ComponentsOf (s d : S ^ C) (m : NaturalTransformation s d) (c : D) :
      Morphism S ((RightPushforwardAlong_ObjectOf s) c) ((RightPushforwardAlong_ObjectOf d) c).
    Proof.
      simpl; subst_body; simpl.
      apply (InducedLimitMap (G := IdentityFunctor _)).
      exact (@RightPushforwardAlong_MorphismOf_ComponentsOf_Pre s d m c).
    Defined.

    Definition RightPushforwardAlong_MorphismOf (s d : S ^ C) (m : NaturalTransformation s d) :
      NaturalTransformation (RightPushforwardAlong_ObjectOf s) (RightPushforwardAlong_ObjectOf d).
    Proof.
      exists (@RightPushforwardAlong_MorphismOf_ComponentsOf s d m).
      present_spnt.
      unfold RightPushforwardAlong_MorphismOf_ComponentsOf, RightPushforwardAlong_MorphismOf_ComponentsOf_Pre;
        subst_body; clear.
      intros.
      Time pre_anihilate.
      simpl.

      simpl; intros; subst_body; simpl in *.
      hnf in s, d.
      unfold RightPushforwardAlong_MorphismOf_ComponentsOf; simpl in *.
      unfold InducedLimitMap, LimitObject; simpl.
      unfold RightPushforwardAlong_ObjectOf_MorphismOf.
      simpl.
      unfold InducedLimitMap.
      subst_body; simpl.
      unfold RightPushforwardAlong_MorphismOf_ComponentsOf_Pre.
      unfold LimitObject.

      admit.

      (*
      Definition Δ {C D} := @diagonal_functor_object_of C D.
      Definition ΔMor {C D} o1 o2 := @diagonal_functor_morphism_of C D o1 o2.
      Definition limo F x := TerminalMorphism_Object (HasLimits F x).
      Definition φ := TerminalMorphism_Morphism.
      Definition unique_m := @TerminalProperty_Morphism.
      Print unique_m.
      Arguments unique_m [C D U X] [M] Y f.

      change (diagonal_functor_morphism_of C D) with (@ΔMor _ C _ D) in *;
      change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor _ C _ D) in *;
      change (ObjectOf (DiagonalFunctor C D)) with (@Δ _ C _ D) in *;
      change (TerminalMorphism_Object (HasLimits ?a ?b)) with (limo a b) in *;
      change TerminalMorphism_Morphism with φ in *;
      change @TerminalProperty_Morphism with @unique_m in *.

      unfold RightPushforwardAlong_pre_Functor  in *.


      change (diagonal_functor_morphism_of C D) with (@ΔMor _ C _ D) in *;
        change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor _ C _ D) in *;
          change (ObjectOf (DiagonalFunctor C D)) with (@Δ _ C _ D) in *;
            change TerminalMorphism_Object with limo in *;
              change TerminalMorphism_Morphism with φ in *;
                change TerminalProperty_Morphism with unique_m in *.


*)

(*    transitivity (Compose (unique_m (colimo H) (SPNTComposeT (φ H) m2)) (Compose ((φ G) x) (m1 x)));
      try_associativity ltac:(apply PreComposeMorphisms || apply PostComposeMorphisms; try reflexivity).*)
(*      ).*)
(*    rename s into F0; rename d into G0;  rename d' into H0;
    rename c into F;
      rename c0 into H;
        rename c1 into G.*)
(*

    change (diagonal_functor_morphism_of C D) with (@ΔMor _ _ _ _ C D) in *;
    change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor _ _ _ _ C D) in *;
    change (ObjectOf (DiagonalFunctor C D)) with (@Δ _ _ _ _ C D) in *;
    change InitialMorphism_Object with colimo in *;
    change InitialMorphism_Morphism with φ in *;
    change @InitialProperty_Morphism with @unique_m in *.*)



(*
      match goal with
        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => pose proof (proj2 (TerminalProperty a b c)); simpl in *
      end (* 9 s *).
      simpl in *.
      pose proof (fun x' => H x'
      erewrite H.

      unfold RightPushforwardAlong_MorphismOf_ComponentsOf.
      unfold InducedLimitMap.
      unfold LimitObject, Limit in *.
      subst RightPushforwardAlong_ObjectOf_MorphismOf; simpl.
      unfold InducedLimitMap, LimitObject; simpl.
      unfold RightPushforwardAlong_MorphismOf_ComponentsOf_Pre; simpl.
      match goal with
        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => pose proof (proj2 (TerminalProperty a b c))
      end (* 9 s *).
      erewrite H.
      match goal with
        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => pose proof (proj2 (TerminalProperty a b c))
      end (* 9 s *).
      erewrite H0.
      Focus 2.
      nt_eq.
      repeat rewrite FIdentityOf;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity.
      clear H H0.


      simpl
      subst_body.
      simpl.
      apply Commutes.
      symmetry.
      simpl.
      unfold RightPushforwardAlong_ObjectOf_MorphismOf at 1.
      unfold InducedLimitMap at 1.
      simpl.
      unfold LimitObject, Limit in *; simpl in *.


      match goal with
        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] =>
          let H := constr:(TerminalProperty a) in
            let H' := fresh in
              pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                simpl in H';
                  unfold Object, Morphism in *;
                    simpl in *
      end.
      subst_body.

      Focus 2.
      simpl in *.
      nt_eq.
      repeat rewrite FIdentityOf;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity.
      clear H.
      hnf in x.
      destruct x as [ [ [ [] x ] Hx ] ]; simpl in *.
      simpl.

      Time match goal with
        | [ |- appcontext[TerminalMorphism_Morphism ?a] ] =>
          let H := constr:(TerminalProperty a) in
            let H' := fresh in
              pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                simpl in H'
      end (* 7 s *).
      erewrite H.

      etransitivity; try apply Commutes.
      Focus 2.
      symmetry; apply (Commutes m ().
      etransitivity; [ rewrite H0 | ].
      rewrite H0.


      match goal with
        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => pose proof (proj2 (TerminalProperty a b c))
      end (* 9 s *).
      unfold Object, Morphism in *.
      simpl in *.
      unfold Limit, LimitObject in *.
      fg_equal.


      subst_body

      simpl.
      unfold LimitObject.
      unfold InducedLimitMap.
      simpl.
      symmetry.

      match goal with
        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => pose proof (proj2 (TerminalProperty a b c))
      end (* 9 s *).


      Time match goal with
        | [ |- appcontext[TerminalMorphism_Morphism ?a] ] =>
          let H := constr:(TerminalProperty a) in
            let H' := fresh in
              pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                simpl in H'
      end (* 7 s *).

      present_spcategory;
      unfold InducedLimitMap;
        simpl.
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
                            reflexivity (* 8 s *).

      auto.
      simpl.
      apply (NTComposeF
      exists (ComponentsOf' m).
      assert (forall
         c0 : CommaCategory_Object
                (SliceCategory_Functor D c) F,
       CMorphism S
         (ObjectOf
            (ComposeFunctors (RightPushforwardAlong_pre_Functor s c)
               (IdentityFunctor (c ↓ F))) c0)
         (ObjectOf (RightPushforwardAlong_pre_Functor d c) c0)).
      present_spnt.
      intro c0; destruct c0 as [ [ [ [] c0 ] cm ] ]; simpl in *.
      match goal with
        | [ |- NaturalTransformation ?F ?G ] =>
          refine (Build_NaturalTransformation F G
            (fun _ => Identity _)
            _
          )
      end.












      Set Printing All.
      Check LaxCosliceCategory_Object LSObject LSMorphism
                LSUnderlyingCategory S.
      specialize (s0 (fun c => (HasLimits (projT2 c)))).
      specialize

      simpl in *.
      S ^ D.
      refine (Build_Functor D S
        (@RightPushforwardAlong_ObjectOf_ObjectOf g)
        (@RightPushforwardAlong_ObjectOf_MorphismOf g)
        _
        _
      );


     Definition RightPushforwardAlong : Functor (S ^ C) (S ^ D).
       Check @MorphismOf' _ _ (S ^ C) _ _ (S ^ D) _.

       refine {| ObjectOf := (fun
*)
(*
 & Adjunction PushforwardAlong PullbackAlong }.
      eexists; try reflexivity.
      refine {| AComponentsOf' := (fun A A' => (fun _ : HomFunctor _ (_, _) => _ )) |};
        intros; simpl in *; repeat (apply functional_extensionality_dep; intro; try snt_eq; simpl in *)(*; try reflexivity.
      unfold CategoryIsomorphism; simpl.
      eexists (fun _ => Build_SmallNaturalTransformation _ _ _ _); try reflexivity.
      split; simpl in *; repeat (apply functional_extensionality_dep; intro); try reflexivity.
      snt_eq.
      symmetry.
      symmetry.

      apply SmallNaturalTransformations_Equal
      snt_eq
      destruct x; try reflexivity.

      assert (forall (C : Category) D (F G : Functor C D) (T : SmallNaturalTransformation F G), T = {| SComponentsOf := SComponentsOf T; SCommutes := SCommutes T |}).
      let T := fresh in intros ? ? ? ? T; destruct T; simpl; reflexivity.
      symmetry.
      rewrite (H .
      apply SmallNaturalTransformations_Equal.

      destruct_type @SmallNaturalTransformation.
      try solve [ destruct_type SmallNaturalTransformation; snt_eq ].
*)
    Defined.

    Definition RightPushforwardAlong : Functor (S ^ C) (S ^ D).
      match goal with
          | [ |- Functor ?C ?D ] =>
            refine (Build_Functor
                      C D
                      RightPushforwardAlong_ObjectOf
                      RightPushforwardAlong_MorphismOf
                      _
                      _
                   )
      end.
      Focus 2.
      present_spcategory.
      intro.
      simpl.
      Time pre_anihilate.
      Time step.
      simpl.
      unfold RightPushforwardAlong_MorphismOf_ComponentsOf.
      apply functional_extensionality_dep.
      intro.
      Time step.
      pose (fun I Index2Object Index2Cat D C => @FIdentityOf _ _ _ _ (@InducedLimitFunctor I Index2Object Index2Cat D C)) as a.
      unfold InducedLimitFunctor, InducedLimitFunctor_MorphismOf in a; simpl in a.
      unfold RightPushforwardAlong_MorphismOf.
      admit.
      admit.
    Defined.
  End Π.

  Section Σ.
    Local Notation "F ↓ A" := (SliceCategory A F).
    (*Local Notation "C / c" := (@SliceCategoryOver _ _ C c).*)

    (** Quoting David Spivak in "Functorial Data Migration":
       Definition 2.1.3. Let [F : C -> D] be a morphism of schemas and
       [Δ_F : D–Set -> C–Set] be the associated data pull-back functor
       (see Definition 1.3.1). There exists a left adjoint to [Δ_F]
       called the left push-forward functor associated to [F], denoted
       [Σ_F : C–Set -> D–Set], and defined as follows.
       Given an object [ɣ : C -> Set] in [C–Set] define [Σ_F ɣ] on an
       object [d : D] as
       [[
         Σ_F ɣ(d) := colim_{F ↓ d} (ɣ ○ (π_F d))
       ]]
       This is simply the limit of the functor
       [[
         (F ↓ d) --- (π_F d) ---> C --- ɣ ---> Set
       ]]
       Given a map [h : d -> d'] in D one obtains a map
       [Σ_F ɣ(h) : Σ_F ɣ(d) -> Σ_F ɣ(d')] by the universal property of
       colimits.

       Here, we have some [C-set] [ɣ] and we want a [D-set] [Σ_F ɣ].
       To each object in [d] we look at the objects in [C] which are
       sent to the left of [d] (i.e. those equipped with a chosen
       morphism to [d]). Each has been assigned by [ɣ] some set of
       rows; we take the colimit of all these sets and assign that to
       [Σ_F ɣ(d)].
       *)

    (* Define [ɣ ○ (π_F d)] *)
    Definition LeftPushforwardAlong_pre_Functor (g : S ^ C) (d : D) : Functor (F ↓ d) S
      := ComposeFunctors g (projT2 (SliceCategoryProjectionFunctor C D F d)).

    Variable HasColimits : forall g d, Colimit (LeftPushforwardAlong_pre_Functor g d).

    Let Index2Cat d := F ↓ d.

    Local Notation "'CAT' ⇓ D" := (@LaxSliceCategory _ _ Index2Cat _ D).

    Let LeftPushforwardAlong_ObjectOf_ObjectOf (g : S ^ C) d := ColimitObject (HasColimits g d).

    Let LeftPushforwardAlong_ObjectOf_MorphismOf_Pre' (g : S ^ C) s d (m : Morphism D s d) :
      {F0 : Functor (F ↓ s) (F ↓ d) * unit &
        NaturalTransformation
        (LeftPushforwardAlong_pre_Functor g s)
        (ComposeFunctors (LeftPushforwardAlong_pre_Functor g d) (fst F0)) }.
      exists (fst (proj1_sig (MorphismOf (SliceCategoryProjectionFunctor C D F) m)), tt).
      unfold LeftPushforwardAlong_pre_Functor;
        hnf;
          simpl;
            unfold Object, Morphism, GeneralizeFunctor.
      match goal with
        | [ |- NaturalTransformation _ (ComposeFunctors (ComposeFunctors ?g ?h) ?i) ] =>
          eapply (NTComposeT (ComposeFunctorsAssociator2 g h i) _)
      end.
      Grab Existential Variables.
      eapply (NTComposeF (IdentityNaturalTransformation g) _).
      Grab Existential Variables.
      match goal with
        | [ C : _ |- NaturalTransformation ?F ?G ] =>
          refine (Build_NaturalTransformation F G
            (fun _ => Identity (C := C) _)
            _
          )
      end;
      abstract (
        simpl; intros ? ? m0;
          destruct m0 as [ [ m0 ] ]; simpl;
            rewrite LeftIdentity; rewrite RightIdentity;
              reflexivity
      ).
    Defined.

    Let LeftPushforwardAlong_ObjectOf_MorphismOf_Pre'' (g : S ^ C) s d (m : Morphism D s d) :
      Morphism (CAT ⇓ S)
      (existT _ (s, tt) (LeftPushforwardAlong_pre_Functor g s) : @LaxSliceCategory_ObjectT _ _ Index2Cat _ _)
      (existT _ (d, tt) (LeftPushforwardAlong_pre_Functor g d) : @LaxSliceCategory_ObjectT _ _ Index2Cat _ _).
    Proof.
      hnf.
      match goal with
        | [ |- LaxSliceCategory_Morphism ?a ?b ] =>
          exact (LeftPushforwardAlong_ObjectOf_MorphismOf_Pre' g _ _ m : @LaxSliceCategory_MorphismT _ _ _ _ _ a b)
      end.
    Defined.

    Definition LeftPushforwardAlong_ObjectOf_MorphismOf_Pre (g : S ^ C) s d (m : Morphism D s d) :
      Morphism (CAT ⇓ S)
      (existT _ (s, tt) (LeftPushforwardAlong_pre_Functor g s) : @LaxSliceCategory_ObjectT _ _ Index2Cat _ _)
      (existT _ (d, tt) (LeftPushforwardAlong_pre_Functor g d) : @LaxSliceCategory_ObjectT _ _ Index2Cat _ _)
      := Eval cbv beta iota zeta delta [LeftPushforwardAlong_ObjectOf_MorphismOf_Pre' LeftPushforwardAlong_ObjectOf_MorphismOf_Pre'' LeftPushforwardAlong_ObjectOf_ObjectOf Index2Cat] in
        @LeftPushforwardAlong_ObjectOf_MorphismOf_Pre'' g s d m.

    (* TODO(jgross): Check if [simpl in *] would make this faster. *)
    Ltac step := clear; subst_body;
                 ((abstract (autorewrite with category; reflexivity))
                    || (abstract apply SliceCategoryInducedFunctor_FIdentityOf)
                    || (abstract apply CosliceCategoryInducedFunctor_FIdentityOf)
                    || (abstract apply SliceCategoryInducedFunctor_FCompositionOf)
                    || (abstract apply CosliceCategoryInducedFunctor_FCompositionOf)
                    || apply CommaCategory_Morphism_eq
                    || apply f_equal
                    || (apply f_equal2; try reflexivity; [])
                    || apply sigT_eq (* simpl_eq *)
                    || (progress nt_eq)
                    || (progress functor_eq)); simpl; trivial.

    Ltac anihilate := repeat step.

    Local Ltac pre_anihilate :=
      simpl;
      subst_body;
      clear;
      nt_hideProofs;
      unfold NTComposeF, NTComposeT; simpl;
      nt_hideProofs;
      clear; simpl in *.


    Lemma LeftPushforwardAlong_ObjectOf_FCompositionOf_Pre (g : S ^ C) s d d' (m1 : Morphism D s d) (m2 : Morphism D d d') :
      LeftPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ (Compose m2 m1) =
      Compose (C := LaxSliceCategory _ _ _) (LeftPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ m2) (LeftPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ m1).
    Proof.
      (* For speed temporarily *)
    Admitted. (*
      unfold LeftPushforwardAlong_ObjectOf_MorphismOf_Pre.
      Time pre_anihilate.
      Time (anihilate). (* 85 s *)
    Qed. *)

    Lemma LeftPushforwardAlong_ObjectOf_FIdentityOf_Pre (g : S ^ C) x :
      LeftPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ (Identity x) =
      Identity (C := LaxSliceCategory _ _ _) _.
    Proof.
      unfold LeftPushforwardAlong_ObjectOf_MorphismOf_Pre.
      Time pre_anihilate.
      Time anihilate. (* 12 s *)
    Qed.

    Definition LeftPushforwardAlong_ObjectOf_MorphismOf (g : S ^ C) s d (m : Morphism D s d) :
      Morphism S (LeftPushforwardAlong_ObjectOf_ObjectOf g s) (LeftPushforwardAlong_ObjectOf_ObjectOf g d).
      subst LeftPushforwardAlong_ObjectOf_ObjectOf LeftPushforwardAlong_ObjectOf_MorphismOf_Pre' LeftPushforwardAlong_ObjectOf_MorphismOf_Pre''; simpl.
      apply (InducedColimitFunctor_MorphismOf (Index2Cat := Index2Cat) (D := S)
        (s := existT _ (s, tt) (LeftPushforwardAlong_pre_Functor g s) : LaxSliceCategory_ObjectT _ _ _)
        (d := existT _ (d, tt) (LeftPushforwardAlong_pre_Functor g d) : LaxSliceCategory_ObjectT _ _ _)
        (HasColimits g s)
        (HasColimits g d)
      ); simpl in *.
      apply LeftPushforwardAlong_ObjectOf_MorphismOf_Pre; assumption.
    Defined.

    Hint Resolve LeftPushforwardAlong_ObjectOf_FIdentityOf_Pre LeftPushforwardAlong_ObjectOf_FCompositionOf_Pre.

    Definition LeftPushforwardAlong_ObjectOf (g : S ^ C) : S ^ D.
      refine (Build_Functor
                D
                S
                (@LeftPushforwardAlong_ObjectOf_ObjectOf g)
                (@LeftPushforwardAlong_ObjectOf_MorphismOf g)
                _
                _
             );
        unfold LeftPushforwardAlong_ObjectOf_MorphismOf;
        subst LeftPushforwardAlong_ObjectOf_MorphismOf_Pre''
              LeftPushforwardAlong_ObjectOf_MorphismOf_Pre'
              LeftPushforwardAlong_ObjectOf_ObjectOf;
        simpl;
        present_spcategory;
        abstract (
            first [
                intros s d d' m1 m2;
                etransitivity;
                try apply (InducedColimitFunctor_FCompositionOf
                             (Index2Cat := Index2Cat)
                             (D := S)
                             (s := existT _ (s, tt) (LeftPushforwardAlong_pre_Functor g s) : LaxSliceCategory_ObjectT _ _ _)
                             (d := existT _ (d, tt) (LeftPushforwardAlong_pre_Functor g d) : LaxSliceCategory_ObjectT _ _ _)
                             (d' := existT _ (d', tt) (LeftPushforwardAlong_pre_Functor g d') : LaxSliceCategory_ObjectT _ _ _)
                             (HasColimits g s)
                             (HasColimits g d)
                             (HasColimits g d')
                             (LeftPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ m1)
                             (LeftPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ m2)
                          ); []
              |
              intros x;
                etransitivity;
                try apply (InducedColimitFunctor_FIdentityOf
                             (Index2Cat := Index2Cat)
                             (D := S)
                             (existT _ (x, tt) (LeftPushforwardAlong_pre_Functor g x) : LaxSliceCategory_ObjectT _ _ _)
                             (HasColimits g x)
                          ); []
              ];
            apply f_equal;
            trivial
          ).
    Defined.

    Definition LeftPushforwardAlong_MorphismOf_ComponentsOf_Pre (s d : S ^ C) (m : NaturalTransformation s d) (c : D) :
      NaturalTransformation
        (LeftPushforwardAlong_pre_Functor s c)
        (ComposeFunctors (LeftPushforwardAlong_pre_Functor d c) (IdentityFunctor _)).
    Proof.
      eapply (NTComposeT _ (ComposeFunctorsAssociator2 _ _ _)).
      Grab Existential Variables.
      match goal with
        | [ |- NaturalTransformation ?F ?G ] =>
          refine (Build_NaturalTransformation
                    F
                    G
                    (fun x => m (fst (projT1 x)))
                    _
                 )
      end;
        abstract (
            repeat (let H := fresh in intro H; destruct H as [ [ [ ] ] ]; simpl in * );
            match goal with
              | [ H : _ |- _ ] => rewrite RightIdentity in H
              | [ H : _ |- _ ] => rewrite LeftIdentity in H
            end;
            subst;
            apply Commutes
          ).
    Defined.

    Definition LeftPushforwardAlong_MorphismOf_ComponentsOf (s d : S ^ C) (m : NaturalTransformation s d) (c : D) :
      Morphism S ((LeftPushforwardAlong_ObjectOf s) c) ((LeftPushforwardAlong_ObjectOf d) c).
    Proof.
      simpl; subst_body; simpl.
      apply (InducedColimitMap (G := IdentityFunctor _)).
      exact (@LeftPushforwardAlong_MorphismOf_ComponentsOf_Pre s d m c).
    Defined.

    Definition LeftPushforwardAlong_MorphismOf (s d : S ^ C) (m : NaturalTransformation s d) :
      NaturalTransformation (LeftPushforwardAlong_ObjectOf s) (LeftPushforwardAlong_ObjectOf d).
    Proof.
      exists (@LeftPushforwardAlong_MorphismOf_ComponentsOf s d m).
      present_spnt.
      unfold LeftPushforwardAlong_MorphismOf_ComponentsOf, LeftPushforwardAlong_MorphismOf_ComponentsOf_Pre;
        subst_body; clear.
      intros.
      admit.
    Defined.

    Definition LeftPushforwardAlong : Functor (S ^ C) (S ^ D).
      match goal with
        | [ |- Functor ?C ?D ] =>
          refine (Build_Functor
                    C D
                    LeftPushforwardAlong_ObjectOf
                    LeftPushforwardAlong_MorphismOf
                    _
                    _
                 )
      end.
      Focus 2.
      present_spcategory.
      intro.
      simpl.
      Time pre_anihilate.
      Time step.
      simpl.
      unfold LeftPushforwardAlong_MorphismOf_ComponentsOf.
      apply functional_extensionality_dep.
      intro.
      Time step.
      pose (fun I Index2Object Index2Cat D C => @FIdentityOf _ _ _ _ (@InducedColimitFunctor I Index2Object Index2Cat D C)) as a.
      unfold InducedColimitFunctor, InducedColimitFunctor_MorphismOf in a; simpl in a.
      unfold LeftPushforwardAlong_MorphismOf.
      admit.
      admit.
    Defined.
  End Σ.
End DataMigrationFunctors.
