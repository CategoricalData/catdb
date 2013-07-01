Require Import JMeq ProofIrrelevance FunctionalExtensionality.
Require Export Notations Category.
Require Import Common StructureEquality FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Local Open Scope morphism_scope.

Section Functor.
  Variable C : Category.
  Variable D : Category.

  (** Quoting from the lecture notes for 18.705, Commutative Algebra:

      A map of categories is known as a functor. Namely, given
      categories [C] and [C'], a (covariant) functor [F : C -> C'] is
      a rule that assigns to each object [A] of [C] an object [F A] of
      [C'] and to each map [m : A -> B] of [C] a map [F m : F A -> F
      B] of [C'] preserving composition and identity; that is,

     (1) [F (m' ∘ m) = (F m') ∘ (F m)] for maps [m : A -> B] and [m' :
         B -> C] of [C], and

     (2) [F (id A) = id (F A)] for any object [A] of [C], where [id A]
         is the identity morphism of [A]. **)

  Record Functor :=
    {
      ObjectOf :> C -> D;
      MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d);
      FCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
                          MorphismOf _ _ (m2 ∘ m1) = (MorphismOf _ _ m2) ∘ (MorphismOf _ _ m1);
      FIdentityOf : forall x, MorphismOf _ _ (Identity x) = Identity (ObjectOf x)
    }.
End Functor.

Bind Scope functor_scope with Functor.

Create HintDb functor discriminated.

Arguments Functor C D.
Arguments ObjectOf {C%category D%category} F%functor c%object : rename, simpl nomatch.
Arguments MorphismOf [C%category] [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.

Arguments FCompositionOf [C D] F _ _ _ _ _ : rename.
Arguments FIdentityOf [C D] F _ : rename.

Notation "F ₀ x" := (ObjectOf F x) : object_scope.
Notation "F ₁ m" := (MorphismOf F m) : morphism_scope.

Hint Resolve @FCompositionOf @FIdentityOf : category functor.
Hint Rewrite @FIdentityOf : category.
Hint Rewrite @FIdentityOf : functor.

Ltac functor_hideProofs :=
  repeat match goal with
             | [ |- context[{|
                               FCompositionOf := ?pf0;
                               FIdentityOf := ?pf1
                             |}] ] =>
               hideProofs pf0 pf1
         end.

Ltac functor_tac_abstract_trailing_props F tac :=
  let F' := (eval hnf in F) in
  let F'' := (tac F') in
  let H := fresh in
  pose F'' as H;
    hnf in H;
    revert H; clear; intro H; clear H;
    match F'' with
      | @Build_Functor ?C
                       ?D
                       ?OO
                       ?MO
                       ?FCO
                       ?FIO =>
        refine (@Build_Functor C D
                               OO
                               MO
                               _
                               _);
          [ abstract exact FCO | abstract exact FIO ]
    end.
Ltac functor_abstract_trailing_props F := functor_tac_abstract_trailing_props F ltac:(fun F' => F').
Ltac functor_simpl_abstract_trailing_props F := functor_tac_abstract_trailing_props F ltac:(fun F' => let F'' := eval simpl in F' in F'').

Section Functors_Equal.
  Lemma Functor_contr_eq' C D (F G : Functor C D)
        (D_morphism_proof_irrelevance
         : forall s d (m1 m2 : Morphism D s d) (pf1 pf2 : m1 = m2),
             pf1 = pf2)
  : forall HO : ObjectOf F = ObjectOf G,
      match HO in (_ = f) return forall s d, Morphism C s d -> Morphism D (f s) (f d) with
        | eq_refl => MorphismOf F
      end = MorphismOf G
      -> F = G.
  Proof.
    intros.
    destruct F, G; simpl in *.
    subst.
    f_equal;
      repeat (apply functional_extensionality_dep; intro);
      trivial.
  Qed.

  Lemma Functor_contr_eq C D (F G : Functor C D)
        (D_object_proof_irrelevance
         : forall (x : D) (pf : x = x),
             pf = eq_refl)
        (D_morphism_proof_irrelevance
         : forall s d (m1 m2 : Morphism D s d) (pf1 pf2 : m1 = m2),
             pf1 = pf2)
  : forall HO : (forall x, ObjectOf F x = ObjectOf G x),
      (forall s d (m : Morphism C s d),
         match HO s in (_ = y) return (Morphism D y _) with
           | eq_refl =>
             match HO d in (_ = y) return (Morphism D _ y) with
               | eq_refl => MorphismOf F m
             end
         end = MorphismOf G m)
      -> F = G.
  Proof.
    intros HO HM.
    apply Functor_contr_eq' with (HO := (functional_extensionality_dep F G HO));
      try assumption.
    repeat (apply functional_extensionality_dep; intro).
    rewrite <- HM; clear HM.
    generalize_eq_match.
    destruct F, G; simpl in *; subst.
    subst_eq_refl_dec.
    reflexivity.
  Qed.

  Lemma Functor_eq' C D : forall (F G : Functor C D),
    ObjectOf F = ObjectOf G
    -> MorphismOf F == MorphismOf G
    -> F = G.
  Proof.
    destruct F, G; simpl; intros; specialize_all_ways; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.

  Lemma Functor_eq C D
  : forall (F G : Functor C D),
      (forall x, ObjectOf F x = ObjectOf G x)
      -> (forall s d m, MorphismOf F (s := s) (d := d) m == MorphismOf G (s := s) (d := d) m)
      -> F = G.
  Proof.
    intros; cut (ObjectOf F = ObjectOf G); intros; try apply Functor_eq'; destruct F, G; simpl in *; repeat subst;
    try apply eq_JMeq;
    repeat (apply functional_extensionality_dep; intro); trivial;
    try apply JMeq_eq; trivial.
  Qed.

  Lemma Functor_JMeq C D C' D'
  : forall (F : Functor C D) (G : Functor C' D'),
      C = C'
      -> D = D'
      -> ObjectOf F == ObjectOf G
      -> MorphismOf F == MorphismOf G
      -> F == G.
  Proof.
    intros; destruct F, G; simpl in *; repeat subst.
    apply eq_JMeq.
    f_equal; apply proof_irrelevance.
  Qed.
End Functors_Equal.

Ltac functor_eq_step_with tac :=
  structures_eq_step_with_tac ltac:(apply Functor_eq || apply Functor_JMeq) tac.

Ltac functor_eq_with tac := repeat functor_eq_step_with tac.

Ltac functor_eq_step := functor_eq_step_with idtac.
Ltac functor_eq := functor_hideProofs; functor_eq_with idtac.

Ltac functor_tac_abstract_trailing_props_with_equality_do tac F thm :=
  let F' := (eval hnf in F) in
  let F'' := (tac F') in
  let H := fresh in
  pose F'' as H;
    hnf in H;
    revert H; clear; intro H; clear H;
    match F'' with
      | @Build_Functor ?C
                       ?D
                       ?OO
                       ?MO
                       ?FCO
                       ?FIO =>
        let FCO' := fresh in
        let FIO' := fresh in
        let FCOT' := type of FCO in
        let FIOT' := type of FIO in
        let FCOT := (eval simpl in FCOT') in
        let FIOT := (eval simpl in FIOT') in
        assert (FCO' : FCOT) by abstract exact FCO;
          assert (FIO' : FIOT) by (clear FCO'; abstract exact FIO);
          exists (@Build_Functor C D
                                 OO
                                 MO
                                 FCO'
                                 FIO');
          expand; abstract (apply thm; reflexivity) || (apply thm; try reflexivity)
    end.

Ltac functor_tac_abstract_trailing_props_with_equality tac :=
  pre_abstract_trailing_props;
  match goal with
    | [ |- { F0 : Functor _ _ | F0 = ?F } ] =>
      functor_tac_abstract_trailing_props_with_equality_do tac F @Functor_eq'
    | [ |- { F0 : Functor _ _ | F0 == ?F } ] =>
      functor_tac_abstract_trailing_props_with_equality_do tac F @Functor_JMeq
  end.
Ltac functor_abstract_trailing_props_with_equality := functor_tac_abstract_trailing_props_with_equality ltac:(fun F' => F').
Ltac functor_simpl_abstract_trailing_props_with_equality := functor_tac_abstract_trailing_props_with_equality ltac:(fun F' => let F'' := eval simpl in F' in F'').

Section FunctorComposition.
  Variable B : Category.
  Variable C : Category.
  Variable D : Category.
  Variable E : Category.
  Variable G : Functor D E.
  Variable F : Functor C D.

  Local Notation CObjectOf c := (G (F c)).
  Local Notation CMorphismOf m := (MorphismOf G (MorphismOf F m)).
  (* We use [rewrite <-] because the resulting [match]es look better. *)
  Let ComposeFunctors_FCompositionOf' s d d' (m1 : Morphism C s d) (m2 : Morphism C d d')
  : CMorphismOf (m2 ∘ m1) = CMorphismOf m2 ∘ CMorphismOf m1.
  Proof.
    rewrite <- !FCompositionOf.
    reflexivity.
  Defined.
  Definition ComposeFunctors_FCompositionOf s d d' m1 m2
    := Eval cbv beta iota zeta delta [ComposeFunctors_FCompositionOf' eq_rect eq_ind] in
        @ComposeFunctors_FCompositionOf' s d d' m1 m2.

  Let ComposeFunctors_FIdentityOf' x
  : CMorphismOf (Identity x) = Identity (CObjectOf x).
  Proof.
    rewrite <- !FIdentityOf.
    reflexivity.
  Defined.
  Definition ComposeFunctors_FIdentityOf x
    := Eval cbv beta iota zeta delta [ComposeFunctors_FIdentityOf' eq_rect eq_ind] in
        @ComposeFunctors_FIdentityOf' x.

  Global Opaque ComposeFunctors_FCompositionOf ComposeFunctors_FIdentityOf.

  Definition ComposeFunctors : Functor C E
    := Build_Functor C E
                     (fun c => G (F c))
                     (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
                     ComposeFunctors_FCompositionOf
                     ComposeFunctors_FIdentityOf.
End FunctorComposition.

Infix "∘" := ComposeFunctors : functor_scope.

Section IdentityFunctor.
  (** There is an identity functor.  It does the obvious thing. *)
  Definition IdentityFunctor C : Functor C C
    := Build_Functor C C
                     (fun x => x)
                     (fun _ _ x => x)
                     (fun _ _ _ _ _ => eq_refl)
                     (fun _ => eq_refl).

  (** We define some useful generalizations of the identity functor. *)
  Definition IdentityFunctor'
             objC
             morC
             idC
             compC
             assocC assocC'
             leftIdC leftIdC'
             rightIdC rightIdC'
  : Functor _ _
    := Build_Functor (@Build_Category objC morC idC compC assocC leftIdC rightIdC)
                     (@Build_Category objC morC idC compC assocC' leftIdC' rightIdC')
                     (fun x => x)
                     (fun _ _ x => x)
                     (fun _ _ _ _ _ => eq_refl)
                     (fun _ => eq_refl).

  Definition GeneralizedIdentityFunctor (C D : Category) (H : C = D) : Functor C D.
    refine (Build_Functor C D
                          (fun x => match H with eq_refl => x end)
                          (fun s d m => match H as H in (_ = C) return
                                              Morphism C (match H with eq_refl => s end) (match H with eq_refl => d end)
                                        with
                                          | eq_refl => m
                                        end)
                          _
                          _);
    destruct H; reflexivity.
  Defined.
End IdentityFunctor.

Global Arguments ComposeFunctors_FCompositionOf / .
Global Arguments ComposeFunctors_FIdentityOf / .

Local Ltac functor_t :=
  destruct_head Functor;
  expand; simpl;
  f_equal;
  repeat (apply functional_extensionality_dep; intro);
  destruct_eq_in_match;
  try reflexivity.

Section IdentityFunctorLemmas.
  Variable C : Category.
  Variable D : Category.

  Local Open Scope functor_scope.

  Local Transparent ComposeFunctors_FIdentityOf.
  Local Transparent ComposeFunctors_FCompositionOf.
  Local Arguments ComposeFunctors_FCompositionOf / .
  Local Arguments ComposeFunctors_FIdentityOf / .

  Lemma LeftIdentityFunctor (F : Functor D C) : IdentityFunctor _ ∘ F = F.
    functor_t.
  Qed.

  Lemma RightIdentityFunctor (F : Functor C D) : F ∘ IdentityFunctor _ = F.
    functor_t.
  Qed.
End IdentityFunctorLemmas.

Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor : category.
Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor : functor.
Hint Immediate @LeftIdentityFunctor @RightIdentityFunctor : category functor.

Section FunctorCompositionLemmas.
  Variable B : Category.
  Variable C : Category.
  Variable D : Category.
  Variable E : Category.

  Local Open Scope functor_scope.

  Local Transparent ComposeFunctors_FCompositionOf.
  Local Transparent ComposeFunctors_FIdentityOf.
  Local Arguments ComposeFunctors_FCompositionOf / .
  Local Arguments ComposeFunctors_FIdentityOf / .

  Lemma ComposeFunctorsAssociativity (F : Functor B C) (G : Functor C D) (H : Functor D E)
  : (H ∘ G) ∘ F = H ∘ (G ∘ F).
  Proof.
    functor_t.
  Qed.
End FunctorCompositionLemmas.

Hint Resolve @ComposeFunctorsAssociativity : category functor.
