Require Import JMeq ProofIrrelevance FunctionalExtensionality.
Require Export Notations Functor.
Require Import Common StructureEquality FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Section NaturalTransformation.
  Context `(C : Category).
  Context `(D : Category).
  Variables F G : Functor C D.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of functors is known as a natural transformation. Namely, given two functors
     [F : C -> D], [G : C -> D], a natural transformation [T: F -> G] is a collection of maps
     [T A : F A -> G A], one for each object [A] of [C], such that [(T B) ○ (F m) = (G m) ○ (T A)]
     for every map [m : A -> B] of [C]; that is, the following diagram is commutative:

           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    G m     V
     G A --------> G B
     **)
  Record NaturalTransformation :=
    {
      ComponentsOf :> forall c, D.(Morphism) (F c) (G c);
      Commutes : forall s d (m : C.(Morphism) s d),
                   Compose (ComponentsOf d) (F.(MorphismOf) m) = Compose (G.(MorphismOf) m) (ComponentsOf s)
    }.
End NaturalTransformation.

Bind Scope natural_transformation_scope with NaturalTransformation.

Create HintDb natural_transformation discriminated.

Arguments ComponentsOf {C%category D%category F%functor G%functor} T%natural_transformation c%object : rename, simpl nomatch.
Arguments Commutes [C D F G] T _ _ _ : rename.

Hint Resolve @Commutes : category natural_transformation.

Ltac nt_hideProofs :=
  repeat match goal with
             | [ |- context[{|
                               Commutes := ?pf
                             |}] ] =>
               hideProofs pf
         end.

Ltac nt_tac_abstract_trailing_props T tac :=
  let T' := (eval hnf in T) in
  let T'' := (tac T') in
  let H := fresh in
  pose T'' as H;
    hnf in H;
    revert H; clear; intro H; clear H;
    match T'' with
      | @Build_NaturalTransformation ?C
                                                ?D
                                                ?F
                                                ?G
                                                ?CO
                                                ?COM =>
        refine (@Build_NaturalTransformation C D F G
                                                        CO
                                                        _);
          abstract exact COM
    end.
Ltac nt_abstract_trailing_props T := nt_tac_abstract_trailing_props T ltac:(fun T' => T').
Ltac nt_simpl_abstract_trailing_props T := nt_tac_abstract_trailing_props T ltac:(fun T' => let T'' := eval simpl in T' in T'').

Section NaturalTransformations_Equal.
  Lemma NaturalTransformation_contr_eq' C D F G
        (T U : @NaturalTransformation C D F G)
        (D_morphism_proof_irrelevance
         : forall s d (m1 m2 : Morphism D s d) (pf1 pf2 : m1 = m2),
             pf1 = pf2)
  : ComponentsOf T = ComponentsOf U
    -> T = U.
    destruct T, U; simpl; intros; repeat subst;
    f_equal;
    repeat (apply functional_extensionality_dep; intro).
    trivial.
  Qed.

  Lemma NaturalTransformation_contr_eq C D F G
        (T U : @NaturalTransformation C D F G)
        (D_morphism_proof_irrelevance
         : forall s d (m1 m2 : Morphism D s d) (pf1 pf2 : m1 = m2),
             pf1 = pf2)
  : (forall x, ComponentsOf T x = ComponentsOf U x)
    -> T = U.
    intros; apply NaturalTransformation_contr_eq'; try assumption.
    destruct T, U; simpl in *;
    repeat (apply functional_extensionality_dep; intro);
    trivial.
  Qed.

  Lemma NaturalTransformation_eq' C D F G :
    forall (T U : @NaturalTransformation C D F G),
    ComponentsOf T = ComponentsOf U
    -> T = U.
    intros T U.
    apply NaturalTransformation_contr_eq'.
    intros; apply proof_irrelevance.
  Qed.

  Lemma NaturalTransformation_eq C D F G :
    forall (T U : @NaturalTransformation C D F G),
    (forall x, ComponentsOf T x = ComponentsOf U x)
    -> T = U.
    intros T U.
    apply NaturalTransformation_contr_eq.
    intros; apply proof_irrelevance.
  Qed.

  Lemma NaturalTransformation_JMeq' C D C' D' :
    forall F G F' G'
      (T : @NaturalTransformation C D F G) (U : @NaturalTransformation C' D' F' G'),
      C = C'
      -> D = D'
      -> F == F'
      -> G == G'
      -> ComponentsOf T == ComponentsOf U
      -> T == U.
    simpl; intros; intuition; destruct T, U; simpl in *; repeat subst;
      JMeq_eq.
    f_equal; apply proof_irrelevance.
  Qed.
  Lemma NaturalTransformation_JMeq C D C' D' :
    forall F G F' G'
      (T : @NaturalTransformation C D F G) (U : @NaturalTransformation C' D' F' G'),
      C = C'
      -> D = D'
      -> F == F'
      -> G == G'
      -> (forall x x', x == x' -> ComponentsOf T x == ComponentsOf U x')
      -> T == U.
    intros; apply NaturalTransformation_JMeq'; trivial;
    destruct T, U; simpl in *; repeat subst.
    apply functional_extensionality_dep_JMeq; trivial.
    intuition.
  Qed.
End NaturalTransformations_Equal.

Ltac nt_eq_step_with tac :=
  structures_eq_step_with_tac ltac:(apply NaturalTransformation_eq || apply NaturalTransformation_JMeq) tac.

Ltac nt_eq_with tac := repeat nt_eq_step_with tac.

Ltac nt_eq_step := nt_eq_step_with idtac.
Ltac nt_eq := nt_hideProofs; nt_eq_with idtac.


Ltac nt_tac_abstract_trailing_props_with_equality_do tac T thm :=
  let T' := (eval hnf in T) in
  let T'' := (tac T') in
  let H := fresh in
  pose T'' as H;
    hnf in H;
    revert H; clear; intro H; clear H;
    match T'' with
      | @Build_NaturalTransformation ?objC ?C
                                                ?objD ?D
                                                ?F
                                                ?G
                                                ?CO
                                                ?COM =>
        let COM' := fresh in
        let COMT' := type of COM in
        let COMT := (eval simpl in COMT') in
        assert (COM' : COMT) by abstract exact COM;
          exists (@Build_NaturalTransformation C D F G
                                                          CO
                                                          COM');
          expand; abstract (apply thm; reflexivity) || (apply thm; try reflexivity)
    end.
Ltac nt_tac_abstract_trailing_props_with_equality tac :=
  pre_abstract_trailing_props;
  match goal with
    | [ |- { T0 : NaturalTransformation _ _ | T0 = ?T } ] =>
      nt_tac_abstract_trailing_props_with_equality_do tac T @NaturalTransformation_eq'
    | [ |- { T0 : NaturalTransformation _ _ | T0 == ?T } ] =>
      nt_tac_abstract_trailing_props_with_equality_do tac T @NaturalTransformation_JMeq
  end.
Ltac nt_abstract_trailing_props_with_equality := nt_tac_abstract_trailing_props_with_equality ltac:(fun T' => T').
Ltac nt_simpl_abstract_trailing_props_with_equality := nt_tac_abstract_trailing_props_with_equality ltac:(fun T' => let T'' := eval simpl in T' in T'').

Section NaturalTransformationComposition.
  Context `(C : Category).
  Context `(D : Category).
  Context `(E : Category).
  Variables F F' F'' : Functor C D.
  Variables G G' : Functor D E.

  Hint Resolve @Commutes f_equal f_equal2 : natural_transformation.
  Hint Rewrite @Associativity : natural_transformation.

  (*
     We have the diagram
          F
     C -------> D
          |
          |
          | T
          |
          V
     C -------> D
          F'
          |
          | T'
          |
          V
     C ------> D
          F''

     And we want the commutative diagram
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    F' m    V
     F' A -------> F' B
      |            |
      |            |
      | T' A       | T' B
      |            |
      V    F'' m   V
     F'' A ------> F'' B

  *)

  Definition NTComposeT (T' : NaturalTransformation F' F'') (T : NaturalTransformation F F') :
    NaturalTransformation F F''.
    exists (fun c => Compose (T' c) (T c));
    (* XXX TODO: Find a way to get rid of [m] in the transitivity call *)
    abstract (
        intros;
        transitivity (Compose (T' _) (Compose (MorphismOf F' m) (T _)));
        try_associativity ltac:(eauto with natural_transformation)
      ).
  Defined.

  (*
     We have the diagram
          F          G
     C -------> D -------> E
          |          |
          |          |
          | T        | U
          |          |
          V          V
     C -------> D -------> E
          F'         G'

     And we want the commutative diagram
             G (F m)
     G (F A) -------> G (F B)
        |                |
        |                |
        | U (T A)        | U (T B)
        |                |
        V     G' (F' m)  V
     G' (F' A) -----> G' (F' B)

  *)
  (* XXX TODO: Automate this better *)

  Hint Rewrite @Commutes : natural_transformation.
  Hint Resolve f_equal2 : natural_transformation.
  Hint Extern 1 (_ = _) => apply @FCompositionOf : natural_transformation.

  Lemma FCompositionOf2 : forall `(C : Category) `(D : Category)
    (F : Functor C D) x y z u (m1 : C.(Morphism) x z) (m2 : C.(Morphism) y x) (m3 : D.(Morphism) u _),
    Compose (MorphismOf F m1) (Compose (MorphismOf F m2) m3) = Compose (MorphismOf F (Compose m1 m2)) m3.
    intros; symmetry; try_associativity ltac:(eauto with natural_transformation).
  Qed.

  Hint Rewrite @FCompositionOf2 : natural_transformation.

  Definition NTComposeF (U : NaturalTransformation G G') (T : NaturalTransformation F F'):
    NaturalTransformation (ComposeFunctors G F) (ComposeFunctors G' F').
    exists (fun c => Compose (G'.(MorphismOf) (T c)) (U (F c)));
    abstract (
        simpl; intros; autorewrite with category;
        repeat try_associativity ltac:(repeat rewrite <- @Commutes; repeat rewrite <- @FCompositionOf);
        reflexivity
      ).
  Defined.
End NaturalTransformationComposition.

Section IdentityNaturalTransformation.
  Context `(C : Category).
  Context `(D : Category).
  Variable F : Functor C D.

  (* There is an identity natrual transformation. *)
  Definition IdentityNaturalTransformation : NaturalTransformation F F.
    exists (fun c => Identity (F c));
    abstract (intros; autorewrite with morphism; reflexivity).
  Defined.

  Lemma LeftIdentityNaturalTransformation (F' : Functor C D) (T : NaturalTransformation F' F) :
    NTComposeT IdentityNaturalTransformation T = T.
    nt_eq; auto with morphism.
  Qed.

  Lemma RightIdentityNaturalTransformation (F' : Functor C D) (T : NaturalTransformation F F') :
    NTComposeT T IdentityNaturalTransformation = T.
    nt_eq; auto with morphism.
  Qed.
End IdentityNaturalTransformation.

Hint Rewrite @LeftIdentityNaturalTransformation @RightIdentityNaturalTransformation : category.
Hint Rewrite @LeftIdentityNaturalTransformation @RightIdentityNaturalTransformation : natural_transformation.

Section IdentityNaturalTransformationF.
  Context `(C : Category).
  Context `(D : Category).
  Context `(E : Category).
  Variable G : Functor D E.
  Variable F : Functor C D.

  Lemma NTComposeFIdentityNaturalTransformation :
    NTComposeF (IdentityNaturalTransformation G) (IdentityNaturalTransformation F) = IdentityNaturalTransformation (ComposeFunctors G F).
  Proof.
    nt_eq; repeat rewrite FIdentityOf; auto with morphism.
  Qed.
End IdentityNaturalTransformationF.

Hint Rewrite @NTComposeFIdentityNaturalTransformation : category.
Hint Rewrite @NTComposeFIdentityNaturalTransformation : natural_transformation.

Section Associativity.
  Context `(B : Category).
  Context `(C : Category).
  Context `(D : Category).
  Context `(E : Category).
  Variable F : Functor D E.
  Variable G : Functor C D.
  Variable H : Functor B C.

  Let F0 := ComposeFunctors (ComposeFunctors F G) H.
  Let F1 := ComposeFunctors F (ComposeFunctors G H).

  Definition ComposeFunctorsAssociator1 : NaturalTransformation F0 F1.
    refine (Build_NaturalTransformation F0 F1
                                                   (fun _ => Identity (C := E) _)
                                                   _
           );
    abstract (
        simpl; intros;
        autorewrite with morphism; reflexivity
      ).
  Defined.

  Definition ComposeFunctorsAssociator2 : NaturalTransformation F1 F0.
    refine (Build_NaturalTransformation F1 F0
                                                   (fun _ => Identity (C := E) _)
                                                   _
           );
    abstract (
        simpl; intros;
        autorewrite with morphism; reflexivity
      ).
  Defined.
End Associativity.

Section IdentityFunctor.
  Context `(C : Category).
  Context `(D : Category).

  Local Ltac t :=
    repeat match goal with
             | [ |- NaturalTransformation ?F ?G ] =>
               refine (Build_NaturalTransformation F G
                                                              (fun _ => Identity _)
                                                              _)
             | _ => abstract (simpl; intros; autorewrite with morphism; reflexivity)
             | _ => split; nt_eq
           end.

  Section left.
    Variable F : Functor D C.

    Definition LeftIdentityFunctorNaturalTransformation1 : NaturalTransformation (ComposeFunctors (IdentityFunctor _) F) F. t. Defined.
    Definition LeftIdentityFunctorNaturalTransformation2 : NaturalTransformation F (ComposeFunctors (IdentityFunctor _) F). t. Defined.

    Theorem LeftIdentityFunctorNT_Isomorphism
    : NTComposeT LeftIdentityFunctorNaturalTransformation1 LeftIdentityFunctorNaturalTransformation2 = IdentityNaturalTransformation _
      /\ NTComposeT LeftIdentityFunctorNaturalTransformation2 LeftIdentityFunctorNaturalTransformation1 = IdentityNaturalTransformation _.
      t.
    Qed.
  End left.

  Section right.
    Variable F : Functor C D.

    Definition RightIdentityFunctorNaturalTransformation1 : NaturalTransformation (ComposeFunctors F (IdentityFunctor _)) F. t. Defined.
    Definition RightIdentityFunctorNaturalTransformation2 : NaturalTransformation F (ComposeFunctors F (IdentityFunctor _)). t. Defined.

    Theorem RightIdentityFunctorNT_Isomorphism
    : NTComposeT RightIdentityFunctorNaturalTransformation1 RightIdentityFunctorNaturalTransformation2 = IdentityNaturalTransformation _
      /\ NTComposeT RightIdentityFunctorNaturalTransformation2 RightIdentityFunctorNaturalTransformation1 = IdentityNaturalTransformation _.
      t.
    Qed.
  End right.
End IdentityFunctor.

Section NaturalTransformationExchangeLaw.
  Context `(C : Category).
  Context `(D : Category).
  Context `(E : Category).

  Variables F G H : Functor C D.
  Variables F' G' H' : Functor D E.

  Variable T : NaturalTransformation F G.
  Variable U : NaturalTransformation G H.

  Variable T' : NaturalTransformation F' G'.
  Variable U' : NaturalTransformation G' H'.

  Local Ltac t_progress := progress repeat
    match goal with
      | _ => apply f_equal
      | _ => apply f_equal2; try reflexivity; []
      | _ => apply Commutes
      | _ => symmetry; apply Commutes
    end.

  Local Ltac t_exch := repeat
    match goal with
      | _ => repeat rewrite FCompositionOf; repeat rewrite Associativity;
        t_progress
      | _ => repeat rewrite <- FCompositionOf; repeat rewrite <- Associativity;
        t_progress
    end.

  Theorem NaturalTransformationExchangeLaw :
    NTComposeF (NTComposeT U' T') (NTComposeT U T) =
    NTComposeT (NTComposeF U' U) (NTComposeF T' T).
  Proof.
    nt_eq;
    t_exch.
  Qed.
End NaturalTransformationExchangeLaw.

Hint Resolve @NaturalTransformationExchangeLaw : category.
Hint Resolve @NaturalTransformationExchangeLaw : natural_transformation.

Ltac nt_solve_associator' :=
  repeat match goal with
           | _ => exact (ComposeFunctorsAssociator1 _ _ _)
           | _ => exact (ComposeFunctorsAssociator2 _ _ _)
           | [ |- NaturalTransformation (ComposeFunctors ?F _) (ComposeFunctors ?F _) ] =>
             refine (NTComposeF (IdentityNaturalTransformation F) _)
           | [ |- NaturalTransformation (ComposeFunctors _ ?F) (ComposeFunctors _ ?F) ] =>
             refine (NTComposeF _ (IdentityNaturalTransformation F))
         end.
Ltac nt_solve_associator :=
  repeat match goal with
           | _ => refine (NTComposeT (ComposeFunctorsAssociator1 _ _ _) _); progress nt_solve_associator'
           | _ => refine (NTComposeT _ (ComposeFunctorsAssociator1 _ _ _)); progress nt_solve_associator'
           | _ => refine (NTComposeT (ComposeFunctorsAssociator2 _ _ _) _); progress nt_solve_associator'
           | _ => refine (NTComposeT _ (ComposeFunctorsAssociator2 _ _ _)); progress nt_solve_associator'
           | _ => progress nt_solve_associator'
         end.
