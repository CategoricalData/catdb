Require Export Adjoint UniversalProperties.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section AdjunctionUniversal.
  Context `{C : Category}.
  Context `{D : Category}.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Definition InitialMorphismOfAdjunction (A : Adjunction F G) Y : InitialMorphism Y G.
    pose (projT1 (A : AdjunctionCounit F G)) as ε.
    pose (projT1 (A : AdjunctionUnit F G)) as η.
    apply Build_InitialMorphism'.
    rename η into i, Y into c, G into R, F into L.
    clear ε.
    exists (L c).
    exists (AComponentsOf A c (L c) (Identity (L c))).
    refine (fun d f => exist _ (proj1_sig (AIsomorphism A _ _) f) _).
    abstract (
        let H := fresh in
        pose proof (fun x0 => fg_equal (ACommutes A c (L c) c d (Identity _) x0) (Identity (L c))) as H;
        pose proof (fg_equal (RightInverse (AIsomorphism A c d)));
        pose proof (fg_equal (LeftInverse (AIsomorphism A c d)));
        simpl in *;
          repeat rewrite FIdentityOf in H;
        repeat rewrite LeftIdentity in H;
        repeat rewrite RightIdentity in H;
        split; repeat (intro || apply functional_extensionality_dep);
        subst;
        simpl in *;
          rewrite <- H;
        autorewrite with morphism;
        trivial; symmetry; trivial
      ).
  Defined.

  (* TODO(jgross): Automate this more *)
  Definition TerminalMorphismOfAdjunction (A : Adjunction F G) X : TerminalMorphism F X.
    pose (projT1 (A : AdjunctionCounit F G)) as ε.
    pose (projT1 (A : AdjunctionUnit F G)) as η.
    apply Build_TerminalMorphism'.
    rename ε into i, X into d, G into R, F into L.
    clear η.
    exists (R d).
    exists (proj1_sig (AIsomorphism A (R d) d) (Identity (R d))).
    refine (fun c g => exist _ ((AComponentsOf A _ _) g) _).
    abstract (
        pose proof (fg_equal (RightInverse (AIsomorphism A (R d) d)));
        pose proof (fg_equal (RightInverse (AIsomorphism A c d)));
        pose proof (fg_equal (LeftInverse (AIsomorphism A (R d) d)));
        pose proof (fg_equal (LeftInverse (AIsomorphism A c d)));
        let H := fresh in
        split;
        [ pose proof (let m := (A (c, d) g) in
                      fg_equal (ACommutes_Inverse A (R d) d c d m (Identity _)) (Identity _)) as H
        | intro m';
          pose proof (fg_equal (ACommutes A (R d) _ c d m' (Identity _))
                               (Inverse (NaturalIsomorphism_Isomorphism A (R d, d)) (Identity (R d)))) as H ];
        simpl in *;
          repeat rewrite FIdentityOf in H;
        repeat rewrite LeftIdentity in H;
        repeat rewrite RightIdentity in H;
        repeat (intro || apply functional_extensionality_dep);
        subst;
        simpl in *;
          etransitivity; try (apply H || (symmetry; apply H));
        try match goal with
              | [ H : _ |- _ ] => rewrite H; autorewrite with morphism; solve [ trivial ]
            end
      ).
  Defined.
End AdjunctionUniversal.

Section AdjunctionFromUniversal.
  Context `{C : Category}.
  Context `{D : Category}.

  Local Ltac diagonal_transitivity_pre_then tac :=
    repeat rewrite AssociativityNoEvar by noEvar;
    match goal with
      | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
        eapply (@eq_trans _ _ (Compose a (Compose _ c')) _); tac
      | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
        eapply (@eq_trans _ _ (Compose a' (Compose _ c)) _); tac
    end.

  Local Ltac post_diagonal_transitivity_tac :=
    first [ try_associativity ltac:(apply f_equal2; try reflexivity; [])
          | symmetry; (* I'm confused why I need this.  But if I don't have it, [rewrite <- AssociativityNoEvar at 2] fails *)
            try_associativity ltac:(apply f_equal2; try reflexivity; []) ].

  Local Ltac diagonal_transitivity_then tac :=
    diagonal_transitivity_pre_then ltac:(post_diagonal_transitivity_tac; tac).

  Local Ltac diagonal_transitivity_then_solve_rewrite :=
    diagonal_transitivity_then ltac:(solve [ rewrite_hyp'; reflexivity | rewrite_rev_hyp'; reflexivity ]).

  Local Ltac solve_adjoint_functor UniversalObject :=
    repeat intro;
    repeat match goal with
             | [ |- context[UniversalObject ?o] ] => generalize (UniversalObject o); intro
           end;
    clear UniversalObject;
    intro_universal_properties;
    unfold unique in *;
    split_and;
    apply_hyp';
    repeat rewrite FCompositionOf;
    repeat rewrite FIdentityOf;
    autorewrite with morphism;
    try reflexivity;
    diagonal_transitivity_then_solve_rewrite.

  Section initial.
    Variable G : Functor D C.
    Variable M : forall Y, InitialMorphism Y G.

    Definition AdjointFunctorOfInitialMorphism : Functor C D.
      refine (Build_Functor C D
                                       (fun Y => let ηY := InitialMorphism_Morphism (M Y) in
                                                 let F0Y := InitialMorphism_Object (M Y) in
                                                 F0Y)
                                       (fun Y0 Y1 f => let ηY1 := InitialMorphism_Morphism (M Y1) in
                                                       (InitialProperty_Morphism (M Y0) _ (Compose ηY1 f)))
                                       _
                                       _);
      simpl in *;
      abstract solve_adjoint_functor M.
    Defined.

    Definition AdjunctionOfInitialMorphism : Adjunction AdjointFunctorOfInitialMorphism G.
      refine (_ : AdjunctionUnit AdjointFunctorOfInitialMorphism G).
      exists (Build_NaturalTransformation (IdentityFunctor C)
                                                     (ComposeFunctors G AdjointFunctorOfInitialMorphism)
                                                     (fun x => InitialMorphism_Morphism (M x))
                                                     (fun s d m => eq_sym (proj1 (InitialProperty (M s) _ _)))).
      simpl.
      exact (fun c d f => exist _ (InitialProperty_Morphism (M c) d f) (InitialProperty (M c) d f)).
    Defined.
  End initial.

  Section terminal.
    Variable F : Functor C D.
    Variable M : forall X, TerminalMorphism F X.

    Definition AdjointFunctorOfTerminalMorphism : Functor D C.
      refine (Build_Functor D C
                                       (fun X => let εX := TerminalMorphism_Morphism (M X) in
                                                 let G0X := TerminalMorphism_Object (M X) in
                                                 G0X)
                                       (fun X0 X1 g => let εX0 := TerminalMorphism_Morphism (M X0) in
                                                       let εX1 := TerminalMorphism_Morphism (M X1) in
                                                       (TerminalProperty_Morphism (M X1) _ (Compose g εX0)))
                                       _
                                       _);
      simpl in *;
      abstract solve_adjoint_functor M.
    Defined.

    Definition AdjunctionOfTerminalMorphism : Adjunction F AdjointFunctorOfTerminalMorphism.
      refine (_ : AdjunctionCounit F AdjointFunctorOfTerminalMorphism).
      hnf.
      exists (Build_NaturalTransformation (ComposeFunctors F AdjointFunctorOfTerminalMorphism)
                                                     (IdentityFunctor D)
                                                     (fun x => TerminalMorphism_Morphism (M x))
                                                     (fun s d m => proj1 (TerminalProperty (M d) _ _))).
      simpl.
      exact (fun c d g => exist _ (TerminalProperty_Morphism (M d) c g) (TerminalProperty (M d) c g)).
    Defined.
  End terminal.
End AdjunctionFromUniversal.
