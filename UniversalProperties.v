Require Export CommaCategory CategoryIsomorphisms.
Require Import Common Notations DefinitionSimplification Eqdep.

Set Implicit Arguments.

Section UniversalMorphism.
  (**
     Quoting Wikipedia:
     Suppose that [U : D -> C] is a functor from a category [D] to a
     category [C], and let [X] be an object of [C].  Consider the
     following dual (opposite) notions:
     *)
  Variables C D : Category.

  Local Ltac intro_t :=
    repeat intro;
    destruct_sig;
    destruct_head_hnf prod;
    destruct_head_hnf unit;
    simpl_eq;
    repeat rewrite @RightIdentity in *;
    repeat rewrite @LeftIdentity in *;
    intuition.

  Section InitialMorphism.
    Local Notation "A ↓ F" := (CosliceCategory A F).
    Variable X : C.
    Variable U : Functor D C.
    (**
       An initial morphism from [X] to [U] is an initial object in the
       category [(X ↓ U)] of morphisms from [X] to [U].  In other
       words, it consists of a pair [(A, φ)] where [A] is an object of
       [D] and [φ: X -> U A] is a morphism in [C], such that the
       following initial property is satisfied:
       (o) Whenever [Y] is an object of [D] and [f : X -> U Y] is a
           morphism in [C], then there exists a unique morphism
           [g : A -> Y] such that the following diagram commutes:
       [[
             φ
         X -----> U A       A
          \        .        .
            \      . U g    . g
           f  \    .        .
               ↘  ↓        ↓
                 U Y        Y

       ]]
       *)
    Definition InitialMorphism := { Aφ : (X ↓ U) & InitialObject Aφ }.

    Section IntroductionAbstractionBarrier.
      Definition Build_InitialMorphism'
                 (UniversalProperty : { A : D & { φ : Morphism C X (U A) &
                                              (*UniversalProperty : *)
                                              forall (A' : D) (φ' : Morphism C X (U A')),
                                                { m : Morphism D A A' |
                                                  Compose (MorphismOf U m) φ = φ'
                                                  /\
                                                  forall m' : Morphism D A A',
                                                    Compose (MorphismOf U m') φ = φ'
                                                    -> m' = m } } }) :
        InitialMorphism.
        pose proof (projT2 UniversalProperty) as φUniversalProperty;
        set (A := projT1 UniversalProperty) in *;
        clearbody A; clear UniversalProperty; simpl in *.
        pose proof (projT2 φUniversalProperty) as UniversalProperty;
        set (φ := projT1 φUniversalProperty) in *;
        clearbody φ; clear φUniversalProperty; simpl in *.
        exists (existT _ (tt, A) φ).
        intro o'.
        specialize (UniversalProperty (snd (projT1 o')) (projT2 o')).
        match goal with
          | [ |- { _ : ?T | _ } ] => match eval hnf in T with
                                       | sig ?P => cut (P (@unit_eq _ _, proj1_sig UniversalProperty));
                                                  [ let H := fresh in
                                                    intro H;
                                                      exists (exist _ (@unit_eq _ _, proj1_sig UniversalProperty) H)
                                                  | ]
                                     end
        end;
          abstract intro_t.
      Defined.

      Arguments Build_InitialMorphism' / .
      Local Arguments Object / .
      Local Arguments CommaCategory_Object / .
      Local Arguments CommaCategory_Morphism / .

      Definition Build_InitialMorphism A φ UniversalProperty : InitialMorphism
        := Eval simpl in @Build_InitialMorphism' (existT _ A (existT _ φ UniversalProperty)).
    End IntroductionAbstractionBarrier.

    Section EliminationAbstractionBarrier.
      Variable M : InitialMorphism.

      Definition InitialMorphism_Object : D := snd (projT1 (projT1 M)).
      Definition InitialMorphism_Morphism : C.(Morphism) X (U (InitialMorphism_Object)) := projT2 (projT1 M).
      Definition InitialProperty_Morphism (Y : D) (f : C.(Morphism) X (U Y)) : D.(Morphism) InitialMorphism_Object Y
        := snd (proj1_sig (proj1_sig (projT2 M (existT (fun ttY => C.(Morphism) X (U (snd ttY))) (tt, Y) f)))).
      (* TODO: Automate this better *)
      Lemma InitialProperty (Y : D) (f : C.(Morphism) X (U Y)) :
        unique (fun g => Compose (U.(MorphismOf) g) InitialMorphism_Morphism = f) (InitialProperty_Morphism Y f).
        Hint Unfold Object : category.
        unfold InitialProperty_Morphism, InitialMorphism_Object, InitialMorphism_Morphism in *;
          simpl in *.
        destruct M; clear M.
        unfold InitialObject, is_unique, unique in *; simpl in *; unfold Object in *.
        match goal with
          | [ |- context[?i (existT ?f ?x ?m)] ] => destruct (i (existT f x m)); simpl in *; clear i
        end.
        repeat (autounfold with category in *; simpl in *).
        destruct_all_hypotheses; simpl in *.
        match goal with
          | [ H : _ |- _ ] => revert dependent H; rewrite @RightIdentity; intros
        end.
        split; try (assumption || symmetry; assumption); intros.
        destruct_head @prod;
          destruct_head unit.
        match goal with
          | [ m : _, pf : _, H : forall _, _ |- _ ] =>
            specialize (H (existT _ (eq_refl, m) pf));
              apply eq_sig_fst in H; apply (f_equal (@snd _ _)) in H;
                solve [ intuition ]
        end.
      Qed.
    End EliminationAbstractionBarrier.
  End InitialMorphism.

  Section TerminalMorphism.
    Local Notation "F ↓ A" := (SliceCategory A F).
    Variable U : Functor D C.
    Variable X : C.
    (**
       A terminal morphism from [U] to [X] is a terminal object in the
       comma category [(U ↓ X)] of morphisms from [U] to [X].  In
       other words, it consists of a pair [(A, φ)] where [A] is an
       object of [D] and [φ : U A -> X] is a morphism in [C], such
       that the following terminal property is satisfied:
       (o) Whenever [Y] is an object of [D] and [f : U Y -> X] is a
           morphism in [C], then there exists a unique morphism
           [g : Y -> A] such that the following diagram commutes:
       [[
         Y      U Y
         .       . \
       g .   U g .   \  f
         .       .     \
         ↓       ↓       ↘
         A      U A -----> X
                      φ
       ]]
       *)
    Definition TerminalMorphism := { Aφ : (U ↓ X) & TerminalObject Aφ }.

    Section IntroductionAbstractionBarrier.
      Definition Build_TerminalMorphism'
                 (UniversalProperty : { A : D & { φ : Morphism C (U A) X &
                                                               (*UniversalProperty : *)
                                                               forall (A' : D) (φ' : Morphism C (U A') X),
                                                                 { m : Morphism D A' A |
                                                                   Compose φ (MorphismOf U m) = φ'
                                                                   /\
                                                                   forall m' : Morphism D A' A,
                                                                     Compose φ (MorphismOf U m') = φ'
                                                                     -> m' = m } } }) :
        TerminalMorphism.
        pose proof (projT2 UniversalProperty) as φUniversalProperty;
        set (A := projT1 UniversalProperty) in *;
        clearbody A; clear UniversalProperty; simpl in *.
        pose proof (projT2 φUniversalProperty) as UniversalProperty;
        set (φ := projT1 φUniversalProperty) in *;
        clearbody φ; clear φUniversalProperty; simpl in *.
        exists (existT _ (A, tt) φ).
        intro o'.
        specialize (UniversalProperty (fst (projT1 o')) (projT2 o')).
        match goal with
          | [ |- { _ : ?T | _ } ] => match eval hnf in T with
                                       | sig ?P => cut (P (proj1_sig UniversalProperty, @unit_eq _ _));
                                                  [ let H := fresh in
                                                    intro H;
                                                      exists (exist _ (proj1_sig UniversalProperty, @unit_eq _ _) H)
                                                  | ]
                                     end
        end;
          abstract intro_t.
      Defined.

      Arguments Build_TerminalMorphism' / .
      Local Arguments Object / .
      Local Arguments CommaCategory_Object / .
      Local Arguments CommaCategory_Morphism / .

      Definition Build_TerminalMorphism A φ UniversalProperty : TerminalMorphism
        := Eval simpl in @Build_TerminalMorphism' (existT _ A (existT _ φ UniversalProperty)).
    End IntroductionAbstractionBarrier.

    Section AbstractionBarrier.
      Variable M : TerminalMorphism.

      Definition TerminalMorphism_Object : D := fst (projT1 (projT1 M)).
      Definition TerminalMorphism_Morphism : C.(Morphism) (U (TerminalMorphism_Object)) X := projT2 (projT1 M).
      Definition TerminalProperty_Morphism (Y : D) (f : C.(Morphism) (U Y) X) : D.(Morphism) Y TerminalMorphism_Object
        := fst (proj1_sig (proj1_sig (projT2 M (existT (fun Ytt => C.(Morphism) (U (fst Ytt)) X) (Y, tt) f)))).
      (* TODO: Automate this better *)
      Lemma TerminalProperty (Y : D) (f : C.(Morphism) (U Y) X) :
        unique (fun g => Compose TerminalMorphism_Morphism (U.(MorphismOf) g) = f) (TerminalProperty_Morphism Y f).
        Hint Unfold Object : category.
        unfold TerminalProperty_Morphism, TerminalMorphism_Object, TerminalMorphism_Morphism in *;
          simpl in *.
        destruct M; clear M.
        unfold TerminalObject, is_unique, unique; simpl in *; unfold Object in *.
        match goal with
          | [ |- context[?i (existT ?f ?x ?m)] ] => destruct (i (existT f x m)); simpl in *; clear i
        end.
        repeat (autounfold with category in *; simpl in *).
        match goal with
          | [ H : _ |- _ ] => revert dependent H; rewrite @LeftIdentity; intros
        end.
        destruct_all_hypotheses; unfold is_unique in *.
        split; try (assumption || symmetry; assumption); intros.
        destruct_head @prod;
          destruct_head unit.
        match goal with
          | [ m : _, pf : _, H : forall _, _ |- _ ] =>
            symmetry in pf;
              specialize (H (existT _ (m, eq_refl) pf));
                apply eq_sig_fst in H; apply (f_equal (@fst _ _)) in H;
                  solve [ intuition ]
        end.
      Qed.
    End AbstractionBarrier.
  End TerminalMorphism.

  Section UniversalMorphism.
    Variable U : Functor D C.
    Variable X : C.
    (**
       The term universal morphism refers either to an initial
       morphism or a terminal morphism, and the term universal
       property refers either to an initial property or a terminal
       property.  In each definition, the existence of the morphism
       [g] intuitively expresses the fact that [(A, φ)] is ``general
       enough'', while the uniqueness of the morphism ensures that
       [(A, φ)] is ``not too general''.
       *)
    Definition UniversalMorphism := ((InitialMorphism X U) + (TerminalMorphism U X))%type.

    Section AbstractionBarrier.
      Variable M : UniversalMorphism.

      Definition UniversalMorphism_Object : D :=
        match M with
          | inl M' => InitialMorphism_Object M'
          | inr M' => TerminalMorphism_Object M'
        end.
      Definition UniversalMorphism_Morphism :
        match M with
          | inl _ => Morphism C X (U (UniversalMorphism_Object))
          | inr _ => Morphism C (U (UniversalMorphism_Object)) X
        end.
        unfold UniversalMorphism_Object; destruct M; simpl;
          eapply InitialMorphism_Morphism || eapply TerminalMorphism_Morphism.
      Defined.
      Definition UniversalProperty_Morphism
        (Y : D)
        (f : match M with
               | inl _ => Morphism C X (U Y)
               | inr _ => Morphism C (U Y) X
             end) :
        match M with
          | inl _ => Morphism _ UniversalMorphism_Object Y
          | inr _ => Morphism _ Y UniversalMorphism_Object
        end.
        unfold UniversalMorphism_Object; destruct M; simpl;
          eapply InitialProperty_Morphism || eapply TerminalProperty_Morphism;
            assumption.
      Defined.

      Definition UniversalPropertyT (Y : D) : Type.
        assert (m := UniversalMorphism_Morphism).
        assert (m' := UniversalProperty_Morphism Y).
        destruct M; simpl in *.
        exact (forall f : Morphism C X (U Y),
          unique
          (fun g : Morphism D UniversalMorphism_Object Y =>
            Compose (MorphismOf U g) m = f)
          (m' f)
        ).
        exact (forall f : Morphism C (U Y) X,
          unique
          (fun g : Morphism D Y UniversalMorphism_Object =>
            Compose m (MorphismOf U g) = f)
          (m' f)
        ).
      Defined.

      Definition UniversalProperty'
        (Y : D) : { T : Type & T }.
        destruct M as [ m | m ].
        exact (existT _ _ (InitialProperty m Y)).
        exact (existT _ _ (TerminalProperty m Y)).
      Defined.

      Definition UniversalProperty'' (Y : D) : { A : Type & A }.
        simpl_definition_by_tac_and_exact (UniversalProperty' Y) ltac:( unfold UniversalProperty in * ).
      Defined.

      Definition UniversalProperty (Y : D) := Eval cbv beta iota zeta delta [UniversalProperty' UniversalProperty''] in projT2 (UniversalProperty'' Y).
    End AbstractionBarrier.
  End UniversalMorphism.
End UniversalMorphism.

Arguments Build_InitialMorphism [C D] X U A φ UniversalProperty.
Arguments Build_TerminalMorphism [C D] U X A φ UniversalProperty.

Ltac intro_from_universal_objects :=
  repeat match goal with
           | [ |- appcontext[TerminalMorphism_Object ?x] ] => unique_pose_with_body x
           | [ _ : appcontext[TerminalMorphism_Object ?x] |- _ ] => unique_pose_with_body x
           | [ |- appcontext[InitialMorphism_Object ?x] ] => unique_pose_with_body x
           | [ _ : appcontext[InitialMorphism_Object ?x] |- _ ] => unique_pose_with_body x
           | [ |- appcontext[UniversalMorphism_Object ?x] ] => unique_pose_with_body x
           | [ _ : appcontext[UniversalMorphism_Object ?x] |- _ ] => unique_pose_with_body x
         end.

Ltac intro_universal_objects :=
  repeat match goal with
           | [ m : TerminalMorphism _ _ |- _ ] => unique_pose_with_body (TerminalMorphism_Object m)
           | [ m : InitialMorphism _ _ |- _ ] => unique_pose_with_body (InitialMorphism_Object m)
           | [ m : UniversalMorphism _ _ |- _ ] => unique_pose_with_body (UniversalMorphism_Object m)
         end.

Ltac intro_universal_morphisms := intro_from_universal_objects;
  repeat match goal with
           | [ m : TerminalMorphism _ _ |- _ ] => unique_pose_with_body (TerminalMorphism_Morphism m)
           | [ m : InitialMorphism _ _ |- _ ] => unique_pose_with_body (InitialMorphism_Morphism m)
           | [ m : UniversalMorphism _ _ |- _ ] => unique_pose_with_body (UniversalMorphism_Morphism m)
         end.

Ltac intro_universal_property_morphisms :=
  repeat match goal with
           | [ m : TerminalMorphism _ _ |- _ ] => unique_pose (TerminalProperty_Morphism m)
           | [ m : InitialMorphism _ _ |- _ ] => unique_pose (InitialProperty_Morphism m)
           | [ m : UniversalMorphism _ _ |- _ ] => unique_pose (UniversalProperty_Morphism m)
         end.

Ltac intro_universal_properties :=
  repeat match goal with
           | [ m : TerminalMorphism _ _ |- _ ] => unique_pose (TerminalProperty m)
           | [ m : InitialMorphism _ _ |- _ ] => unique_pose (InitialProperty m)
           | [ m : UniversalMorphism _ _ |- _ ] => unique_pose (UniversalProperty m)

           | [ _ : appcontext[TerminalProperty_Morphism ?a] |- _ ] => unique_pose (TerminalProperty a)
           | [ _ : appcontext[InitialProperty_Morphism ?a] |- _ ] => unique_pose (InitialProperty a)
           | [ _ : appcontext[UniversalProperty_Morphism ?a] |- _ ] => unique_pose (UniversalProperty a)
           | [ |- appcontext[TerminalProperty_Morphism ?a] ] => unique_pose (TerminalProperty a)
           | [ |- appcontext[InitialProperty_Morphism ?a] ] => unique_pose (InitialProperty a)
           | [ |- appcontext[UniversalProperty_Morphism ?a] ] => unique_pose (UniversalProperty a)

           | [ _ : appcontext[TerminalProperty_Morphism ?a ?b] |- _ ] => unique_pose (TerminalProperty a b)
           | [ _ : appcontext[InitialProperty_Morphism ?a ?b] |- _ ] => unique_pose (InitialProperty a b)
           | [ _ : appcontext[UniversalProperty_Morphism ?a ?b] |- _ ] => unique_pose (UniversalProperty a b)
           | [ |- appcontext[TerminalProperty_Morphism ?a ?b] ] => unique_pose (TerminalProperty a b)
           | [ |- appcontext[InitialProperty_Morphism ?a ?b] ] => unique_pose (InitialProperty a b)
           | [ |- appcontext[UniversalProperty_Morphism ?a ?b] ] => unique_pose (UniversalProperty a b)

           | [ _ : appcontext[TerminalProperty_Morphism ?a ?b ?c] |- _ ] => unique_pose (TerminalProperty a b c)
           | [ _ : appcontext[InitialProperty_Morphism ?a ?b ?c] |- _ ] => unique_pose (InitialProperty a b c)
           | [ _ : appcontext[UniversalProperty_Morphism ?a ?b ?c] |- _ ] => unique_pose (UniversalProperty a b c)
           | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => unique_pose (TerminalProperty a b c)
           | [ |- appcontext[InitialProperty_Morphism ?a ?b ?c] ] => unique_pose (InitialProperty a b c)
           | [ |- appcontext[UniversalProperty_Morphism ?a ?b ?c] ] => unique_pose (UniversalProperty a b c)
         end.
