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
    destruct F, G; simpl; intros; specialize_all_ways; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.

  Lemma Functor_eq C D :
    forall (F G : Functor C D),
      (forall x, ObjectOf F x = ObjectOf G x)
      -> (forall s d m, MorphismOf F (s := s) (d := d) m == MorphismOf G (s := s) (d := d) m)
      -> F = G.
    intros; cut (ObjectOf F = ObjectOf G); intros; try apply Functor_eq'; destruct F, G; simpl in *; repeat subst;
    try apply eq_JMeq;
    repeat (apply functional_extensionality_dep; intro); trivial;
    try apply JMeq_eq; trivial.
  Qed.

  Lemma Functor_JMeq C D C' D' :
    forall (F : Functor C D) (G : Functor C' D'),
      C = C'
      -> D = D'
      -> ObjectOf F == ObjectOf G
      -> MorphismOf F == MorphismOf G
      -> F == G.
    simpl; intros; intuition; repeat subst; destruct F, G; simpl in *;
      repeat subst; JMeq_eq.
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

  Definition ComposeFunctors' : Functor C E
    := Build_Functor C E
                                (fun c => G (F c))
                                (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
                                (fun _ _ _ m1 m2 =>
                                   match FCompositionOf G _ _ _ (MorphismOf F m1) (MorphismOf F m2) with
                                     | eq_refl =>
                                       match
                                         FCompositionOf F _ _ _ m1 m2 in (_ = y)
                                         return
                                         (MorphismOf G (MorphismOf F (Compose m2 m1)) =
                                          MorphismOf G y)
                                       with
                                         | eq_refl => eq_refl
                                       end
                                   end)
                                (fun x =>
                                   match FIdentityOf G (F x) with
                                     | eq_refl =>
                                       match
                                         FIdentityOf F x in (_ = y)
                                         return
                                         (MorphismOf G (MorphismOf F (Identity x)) =
                                          MorphismOf G y)
                                       with
                                         | eq_refl => eq_refl
                                       end
                                   end).

  Hint Rewrite @FCompositionOf : functor.

  Definition ComposeFunctors : Functor C E.
    refine (Build_Functor C E
                                     (fun c => G (F c))
                                     (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
                                     _
                                     _);
    abstract (
        intros; autorewrite with functor; reflexivity
      ).
  Defined.
End FunctorComposition.

Section IdentityFunctor.
  Variable C : Category.

  (** There is an identity functor.  It does the obvious thing. *)
  Definition IdentityFunctor : Functor C C
    := Build_Functor C C
                                (fun x => x)
                                (fun _ _ x => x)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).
End IdentityFunctor.

Section IdentityFunctorLemmas.
  Variable C : Category.
  Variable D : Category.

  Lemma LeftIdentityFunctor (F : Functor D C) : ComposeFunctors (IdentityFunctor _) F = F.
    functor_eq.
  Qed.

  Lemma RightIdentityFunctor (F : Functor C D) : ComposeFunctors F (IdentityFunctor _) = F.
    functor_eq.
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

  Lemma ComposeFunctorsAssociativity (F : Functor B C) (G : Functor C D) (H : Functor D E) :
    ComposeFunctors (ComposeFunctors H G) F = ComposeFunctors H (ComposeFunctors G F).
    functor_eq.
  Qed.
End FunctorCompositionLemmas.

Hint Resolve @ComposeFunctorsAssociativity : category functor.
