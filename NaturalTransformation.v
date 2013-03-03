Require Import JMeq ProofIrrelevance FunctionalExtensionality.
Require Export Notations Functor.
Require Import Common StructureEquality FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Local Infix "==" := JMeq.

Section SpecializedNaturalTransformation.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variables F G : SpecializedFunctor C D.

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
  Record SpecializedNaturalTransformation := {
    ComponentsOf' : forall c, D.(Morphism') (F.(ObjectOf') c) (G.(ObjectOf') c);
    Commutes' : forall s d (m : C.(Morphism') s d),
      D.(Compose') _ _ _ (ComponentsOf' d) (F.(MorphismOf') _ _ m) = D.(Compose') _ _ _ (G.(MorphismOf') _ _ m) (ComponentsOf' s)
  }.
End SpecializedNaturalTransformation.

Bind Scope natural_transformation_scope with SpecializedNaturalTransformation.

Create HintDb natural_transformation discriminated.

Section NaturalTransformationInterface.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variables F G : SpecializedFunctor C D.

  Variable T : SpecializedNaturalTransformation F G.

  Definition ComponentsOf : forall c : C, D.(Morphism) (F c) (G c) := Eval cbv beta delta [ComponentsOf'] in T.(ComponentsOf').
  Definition Commutes : forall (s d : C) (m : C.(Morphism) s d),
    Compose (ComponentsOf d) (F.(MorphismOf) m) = Compose (G.(MorphismOf) m) (ComponentsOf s)
    := T.(Commutes').
End NaturalTransformationInterface.

Arguments ComponentsOf {objC C objD D F G} T c : simpl nomatch.
Global Coercion ComponentsOf : SpecializedNaturalTransformation >-> Funclass.

Section NaturalTransformation.
  Variable C D : Category.
  Variable F G : Functor C D.

  Definition NaturalTransformation := SpecializedNaturalTransformation F G.
End NaturalTransformation.

Bind Scope natural_transformation_scope with NaturalTransformation.

Identity Coercion NaturalTransformation_SpecializedNaturalTransformation_Id : NaturalTransformation >-> SpecializedNaturalTransformation.
Definition GeneralizeNaturalTransformation `(T : @SpecializedNaturalTransformation objC C objD D F G) :
  NaturalTransformation F G := T.
Global Coercion GeneralizeNaturalTransformation : SpecializedNaturalTransformation >-> NaturalTransformation.

Arguments GeneralizeNaturalTransformation [objC C objD D F G] T /.
Hint Extern 0 => unfold GeneralizeNaturalTransformation : category.
Hint Extern 0 => unfold GeneralizeNaturalTransformation : natural_transformation.
Ltac fold_NT :=
  change @SpecializedNaturalTransformation with
    (fun objC (C : SpecializedCategory objC) objD (D : SpecializedCategory objD) => @NaturalTransformation C D) in *; simpl in *.

Arguments Commutes [objC C objD D F G] T _ _ _.

Hint Resolve @Commutes @Commutes' : category.
Hint Resolve @Commutes @Commutes' : natural_transformation.

Ltac present_spnt := present_spcategory; present_spfunctor;
  present_obj_obj @ComponentsOf' @ComponentsOf(*;
  repeat match goal with
           | [ H : appcontext[@ObjectOf (@Object ?obj ?mor ?C)] |- _ ] => change (@Object obj mor C) with obj in H
           | [ H : appcontext[@ObjectOf _ _ (@Object ?obj ?mor ?C)] |- _ ] => change (@Object obj mor C) with obj in H
           | [ |- appcontext[@ObjectOf (@Object ?obj ?mor ?C)] ] => change (@Object obj mor C) with obj
           | [ |- appcontext[@ObjectOf _ _ (@Object ?obj ?mor ?C)] ] => change (@Object obj mor C) with obj
           | [ H : appcontext[@MorphismOf (@Object ?obj ?mor ?C)] |- _ ] => change (@Object obj mor C) with obj in H
           | [ H : appcontext[@MorphismOf _ _ (@Object ?obj ?mor ?C)] |- _ ] => change (@Object obj mor C) with obj in H
           | [ |- appcontext[@MorphismOf (@Object ?obj ?mor ?C)] ] => change (@Object obj mor C) with obj
           | [ |- appcontext[@MorphismOf _ _ (@Object ?obj ?mor ?C)] ] => change (@Object obj mor C) with obj
         end*).

Ltac nt_hideProofs :=
  repeat match goal with
             | [ |- context[{|
                               ComponentsOf' := _;
                               Commutes' := ?pf
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
      | @Build_SpecializedNaturalTransformation ?objC ?C
                                                ?objD ?D
                                                ?F
                                                ?G
                                                ?CO
                                                ?COM =>
        refine (@Build_SpecializedNaturalTransformation objC C objD D F G
                                                        CO
                                                        _);
          abstract exact COM
    end.
Ltac nt_abstract_trailing_props T := nt_tac_abstract_trailing_props T ltac:(fun T' => T').
Ltac nt_simpl_abstract_trailing_props T := nt_tac_abstract_trailing_props T ltac:(fun T' => let T'' := eval simpl in T' in T'').

Section NaturalTransformations_Equal.
  Lemma NaturalTransformation_eq' objC C objD D F G :
    forall (T U : @SpecializedNaturalTransformation objC C objD D F G),
    ComponentsOf T = ComponentsOf U
    -> T = U.
    destruct T, U; simpl; intros; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.

  Lemma NaturalTransformation_eq objC C objD D F G :
    forall (T U : @SpecializedNaturalTransformation objC C objD D F G),
    (forall x, ComponentsOf T x = ComponentsOf U x)
    -> T = U.
    intros; apply NaturalTransformation_eq'; destruct T, U; simpl in *; repeat subst;
    apply functional_extensionality_dep; trivial.
  Qed.

  Lemma NaturalTransformation_JMeq objC C objD D objC' C' objD' D' :
    forall F G F' G'
      (T : @SpecializedNaturalTransformation objC C objD D F G) (U : @SpecializedNaturalTransformation objC' C' objD' D' F' G'),
      objC = objC'
      -> objD = objD'
      -> C == C'
      -> D == D'
      -> F == F'
      -> G == G'
      -> ComponentsOf T == ComponentsOf U
      -> T == U.
    simpl; intros; intuition; destruct T, U; simpl in *; repeat subst;
      JMeq_eq.
    f_equal; apply proof_irrelevance.
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
      | @Build_SpecializedNaturalTransformation ?objC ?C
                                                ?objD ?D
                                                ?F
                                                ?G
                                                ?CO
                                                ?COM =>
        let COM' := fresh in
        let COMT' := type of COM in
        let COMT := (eval simpl in COMT') in
        assert (COM' : COMT) by abstract exact COM;
          exists (@Build_SpecializedNaturalTransformation objC C objD D F G
                                                          CO
                                                          COM');
          expand; abstract (apply thm; reflexivity) || (apply thm; try reflexivity)
    end.
Ltac nt_tac_abstract_trailing_props_with_equality tac :=
  pre_abstract_trailing_props;
  match goal with
    | [ |- { T0 : SpecializedNaturalTransformation _ _ | T0 = ?T } ] =>
      nt_tac_abstract_trailing_props_with_equality_do tac T @NaturalTransformation_eq'
    | [ |- { T0 : SpecializedNaturalTransformation _ _ | T0 == ?T } ] =>
      nt_tac_abstract_trailing_props_with_equality_do tac T @NaturalTransformation_JMeq
  end.
Ltac nt_abstract_trailing_props_with_equality := nt_tac_abstract_trailing_props_with_equality ltac:(fun T' => T').
Ltac nt_simpl_abstract_trailing_props_with_equality := nt_tac_abstract_trailing_props_with_equality ltac:(fun T' => let T'' := eval simpl in T' in T'').

Section NaturalTransformationComposition.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).
  Variables F F' F'' : SpecializedFunctor C D.
  Variables G G' : SpecializedFunctor D E.

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

  Definition NTComposeT (T' : SpecializedNaturalTransformation F' F'') (T : SpecializedNaturalTransformation F F') :
    SpecializedNaturalTransformation F F''.
    exists (fun c => Compose (T' c) (T c));
    (* XXX TODO: Find a way to get rid of [m] in the transitivity call *)
    abstract (
        present_spcategory;
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

  Lemma FCompositionOf2 : forall `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD)
    (F : SpecializedFunctor C D) x y z u (m1 : C.(Morphism) x z) (m2 : C.(Morphism) y x) (m3 : D.(Morphism) u _),
    Compose (MorphismOf F m1) (Compose (MorphismOf F m2) m3) = Compose (MorphismOf F (Compose m1 m2)) m3.
    intros; symmetry; try_associativity ltac:(eauto with natural_transformation).
  Qed.

  Hint Rewrite @FCompositionOf2 : natural_transformation.

  Definition NTComposeF (U : SpecializedNaturalTransformation G G') (T : SpecializedNaturalTransformation F F'):
    SpecializedNaturalTransformation (ComposeFunctors G F) (ComposeFunctors G' F').
    exists (fun c => Compose (G'.(MorphismOf) (T c)) (U (F c)));
    abstract (
        present_spcategory;
        simpl; intros; autorewrite with category;
        repeat try_associativity ltac:(repeat rewrite <- @Commutes; repeat rewrite <- @FCompositionOf);
        reflexivity
      ).
  Defined.
End NaturalTransformationComposition.

Section IdentityNaturalTransformation.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.

  (* There is an identity natrual transformation. *)
  Definition IdentityNaturalTransformation : SpecializedNaturalTransformation F F.
    exists (fun c => Identity (F c));
    abstract (present_spcategory; intros; autorewrite with morphism; reflexivity).
  Defined.

  Lemma LeftIdentityNaturalTransformation (F' : SpecializedFunctor C D) (T : SpecializedNaturalTransformation F' F) :
    NTComposeT IdentityNaturalTransformation T = T.
    nt_eq; auto with morphism.
  Qed.

  Lemma RightIdentityNaturalTransformation (F' : SpecializedFunctor C D) (T : SpecializedNaturalTransformation F F') :
    NTComposeT T IdentityNaturalTransformation = T.
    nt_eq; auto with morphism.
  Qed.
End IdentityNaturalTransformation.

Coercion IdentityNaturalTransformation : SpecializedFunctor >-> SpecializedNaturalTransformation.

Hint Rewrite @LeftIdentityNaturalTransformation @RightIdentityNaturalTransformation : category.
Hint Rewrite @LeftIdentityNaturalTransformation @RightIdentityNaturalTransformation : natural_transformation.

Section IdentityNaturalTransformationF.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).
  Variable G : SpecializedFunctor D E.
  Variable F : SpecializedFunctor C D.

  Lemma NTComposeFIdentityNaturalTransformation :
    NTComposeF (IdentityNaturalTransformation G) (IdentityNaturalTransformation F) = IdentityNaturalTransformation (ComposeFunctors G F).
  Proof.
    nt_eq; repeat rewrite FIdentityOf; auto with morphism.
  Qed.
End IdentityNaturalTransformationF.

Hint Rewrite @NTComposeFIdentityNaturalTransformation : category.
Hint Rewrite @NTComposeFIdentityNaturalTransformation : natural_transformation.

Section Associativity.
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).
  Variable F : SpecializedFunctor D E.
  Variable G : SpecializedFunctor C D.
  Variable H : SpecializedFunctor B C.

  Let F0 := ComposeFunctors (ComposeFunctors F G) H.
  Let F1 := ComposeFunctors F (ComposeFunctors G H).

  Definition ComposeFunctorsAssociator1 : SpecializedNaturalTransformation F0 F1.
    refine (Build_SpecializedNaturalTransformation F0 F1
                                                   (fun _ => Identity (C := E) _)
                                                   _
           );
    abstract (
        present_spcategory;
        simpl; intros;
        autorewrite with morphism; reflexivity
      ).
  Defined.

  Definition ComposeFunctorsAssociator2 : SpecializedNaturalTransformation F1 F0.
    refine (Build_SpecializedNaturalTransformation F1 F0
                                                   (fun _ => Identity (C := E) _)
                                                   _
           );
    abstract (
        present_spcategory;
        simpl; intros;
        autorewrite with morphism; reflexivity
      ).
  Defined.
End Associativity.

Section NaturalTransformationExchangeLaw.
  Context `(C : SpecializedCategory objC).
  Context `(D : SpecializedCategory objD).
  Context `(E : SpecializedCategory objE).

  Variables F G H : SpecializedFunctor C D.
  Variables F' G' H' : SpecializedFunctor D E.

  Variable T : SpecializedNaturalTransformation F G.
  Variable U : SpecializedNaturalTransformation G H.

  Variable T' : SpecializedNaturalTransformation F' G'.
  Variable U' : SpecializedNaturalTransformation G' H'.

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
           | [ |- SpecializedNaturalTransformation (ComposeFunctors ?F _) (ComposeFunctors ?F _) ] =>
             refine (NTComposeF F _)
           | [ |- SpecializedNaturalTransformation (ComposeFunctors _ ?F) (ComposeFunctors _ ?F) ] =>
             refine (NTComposeF _ F)
         end.
Ltac nt_solve_associator :=
  repeat match goal with
           | _ => refine (NTComposeT (ComposeFunctorsAssociator1 _ _ _) _); progress nt_solve_associator'
           | _ => refine (NTComposeT _ (ComposeFunctorsAssociator1 _ _ _)); progress nt_solve_associator'
           | _ => refine (NTComposeT (ComposeFunctorsAssociator2 _ _ _) _); progress nt_solve_associator'
           | _ => refine (NTComposeT _ (ComposeFunctorsAssociator2 _ _ _)); progress nt_solve_associator'
           | _ => progress nt_solve_associator'
         end.
