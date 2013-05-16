Require Import JMeq ProofIrrelevance FunctionalExtensionality.
Require Export Notations SpecializedCategory Category.
Require Import Common StructureEquality FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Local Infix "==" := JMeq.

Section SpecializedFunctor.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of categories is known as a functor. Namely, given
     categories [C] and [C'], a (covariant) functor [F : C -> C'] is a rule that assigns to
     each object [A] of [C] an object [F A] of [C'] and to each map [m : A -> B] of [C] a map
     [F m : F A -> F B] of [C'] preserving composition and identity; that is,
     (1) [F (m' ○ m) = (F m') ○ (F m)] for maps [m : A -> B] and [m' : B -> C] of [C], and
     (2) [F (id A) = id (F A)] for any object [A] of [C], where [id A] is the identity morphism of [A].
     **)
  Record SpecializedFunctor :=
    {
      ObjectOf :> objC -> objD;
      MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d);
      FCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
                          MorphismOf _ _ (Compose m2 m1) = Compose (MorphismOf _ _ m2) (MorphismOf _ _ m1);
      FIdentityOf : forall x, MorphismOf _ _ (Identity x) = Identity (ObjectOf x)
    }.
End SpecializedFunctor.

Section Functor.
  Variable C : Category.
  Variable D : Category.

  Definition Functor := SpecializedFunctor C D.
End Functor.

Bind Scope functor_scope with SpecializedFunctor.
Bind Scope functor_scope with Functor.

Create HintDb functor discriminated.

Identity Coercion Functor_SpecializedFunctor_Id : Functor >-> SpecializedFunctor.
Definition GeneralizeFunctor objC C objD D (F : @SpecializedFunctor objC C objD D) : Functor C D := F.
Coercion GeneralizeFunctor : SpecializedFunctor >-> Functor.

(* try to always unfold [GeneralizeFunctor]; it's in there
   only for coercions *)
Arguments GeneralizeFunctor [objC C objD D] F /.
Hint Extern 0 => unfold GeneralizeFunctor : category functor.

Arguments SpecializedFunctor {objC} C {objD} D.
Arguments Functor C D.
Arguments ObjectOf {objC%type C%category objD%type D%category} F%functor c%object : rename, simpl nomatch.
Arguments MorphismOf {objC%type} [C%category] {objD%type} [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.

Arguments FCompositionOf [objC C objD D] F _ _ _ _ _ : rename.
Arguments FIdentityOf [objC C objD D] F _ : rename.

Hint Resolve @FCompositionOf @FIdentityOf : category functor.
Hint Rewrite @FIdentityOf : category.
Hint Rewrite @FIdentityOf : functor.

Ltac functor_hideProofs :=
  repeat match goal with
             | [ |- context[{|
                               ObjectOf := _;
                               MorphismOf := _;
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
      | @Build_SpecializedFunctor ?objC ?C
                                  ?objD ?D
                                  ?OO
                                  ?MO
                                  ?FCO
                                  ?FIO =>
        refine (@Build_SpecializedFunctor objC C objD D
                                          OO
                                          MO
                                          _
                                          _);
          [ abstract exact FCO | abstract exact FIO ]
    end.
Ltac functor_abstract_trailing_props F := functor_tac_abstract_trailing_props F ltac:(fun F' => F').
Ltac functor_simpl_abstract_trailing_props F := functor_tac_abstract_trailing_props F ltac:(fun F' => let F'' := eval simpl in F' in F'').

Section Functors_Equal.
  Lemma Functor_contr_eq' objC C objD D (F G : @SpecializedFunctor objC C objD D)
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

  Lemma Functor_contr_eq objC C objD D (F G : @SpecializedFunctor objC C objD D)
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

  Lemma Functor_eq' objC C objD D : forall (F G : @SpecializedFunctor objC C objD D),
    ObjectOf F = ObjectOf G
    -> MorphismOf F == MorphismOf G
    -> F = G.
    destruct F, G; simpl; intros; specialize_all_ways; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.

  Lemma Functor_eq objC C objD D :
    forall (F G : @SpecializedFunctor objC C objD D),
      (forall x, ObjectOf F x = ObjectOf G x)
      -> (forall s d m, MorphismOf F (s := s) (d := d) m == MorphismOf G (s := s) (d := d) m)
      -> F = G.
    intros; cut (ObjectOf F = ObjectOf G); intros; try apply Functor_eq'; destruct F, G; simpl in *; repeat subst;
    try apply eq_JMeq;
    repeat (apply functional_extensionality_dep; intro); trivial;
    try apply JMeq_eq; trivial.
  Qed.

  Lemma Functor_JMeq objC C objD D objC' C' objD' D' :
    forall (F : @SpecializedFunctor objC C objD D) (G : @SpecializedFunctor objC' C' objD' D'),
      objC = objC'
      -> objD = objD'
      -> C == C'
      -> D == D'
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
      | @Build_SpecializedFunctor ?objC ?C
                                  ?objD ?D
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
          exists (@Build_SpecializedFunctor objC C objD D
                                            OO
                                            MO
                                            FCO'
                                            FIO');
          expand; abstract (apply thm; reflexivity) || (apply thm; try reflexivity)
    end.

Ltac functor_tac_abstract_trailing_props_with_equality tac :=
  pre_abstract_trailing_props;
  match goal with
    | [ |- { F0 : SpecializedFunctor _ _ | F0 = ?F } ] =>
      functor_tac_abstract_trailing_props_with_equality_do tac F @Functor_eq'
    | [ |- { F0 : SpecializedFunctor _ _ | F0 == ?F } ] =>
      functor_tac_abstract_trailing_props_with_equality_do tac F @Functor_JMeq
  end.
Ltac functor_abstract_trailing_props_with_equality := functor_tac_abstract_trailing_props_with_equality ltac:(fun F' => F').
Ltac functor_simpl_abstract_trailing_props_with_equality := functor_tac_abstract_trailing_props_with_equality ltac:(fun F' => let F'' := eval simpl in F' in F'').

Section FunctorComposition.
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).

  Hint Rewrite @FCompositionOf : functor.

  Definition ComposeFunctors (G : SpecializedFunctor D E) (F : SpecializedFunctor C D) : SpecializedFunctor C E.
    refine (Build_SpecializedFunctor C E
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
  Context `(C : @SpecializedCategory objC).

  (* There is an identity functor.  It does the obvious thing. *)
  Definition IdentityFunctor : SpecializedFunctor C C.
    refine {| ObjectOf := (fun x => x);
              MorphismOf := (fun _ _ x => x)
           |};
    abstract t.
  Defined.
End IdentityFunctor.

Section IdentityFunctorLemmas.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Lemma LeftIdentityFunctor (F : SpecializedFunctor D C) : ComposeFunctors (IdentityFunctor _) F = F.
    functor_eq.
  Qed.

  Lemma RightIdentityFunctor (F : SpecializedFunctor C D) : ComposeFunctors F (IdentityFunctor _) = F.
    functor_eq.
  Qed.
End IdentityFunctorLemmas.

Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor : category.
Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor : functor.
Hint Immediate @LeftIdentityFunctor @RightIdentityFunctor : category functor.

Section FunctorCompositionLemmas.
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).

  Lemma ComposeFunctorsAssociativity (F : SpecializedFunctor B C) (G : SpecializedFunctor C D) (H : SpecializedFunctor D E) :
    ComposeFunctors (ComposeFunctors H G) F = ComposeFunctors H (ComposeFunctors G F).
    functor_eq.
  Qed.
End FunctorCompositionLemmas.

Hint Resolve @ComposeFunctorsAssociativity : category functor.
