Require Import JMeq ProofIrrelevance.
Require Export Notations.
Require Import Common StructureEquality FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Record Category :=
  Build_Category' {
      Object :> Type;
      Morphism : Object -> Object -> Type;

      Identity : forall x, Morphism x x;
      Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d';

      Associativity : forall o1 o2 o3 o4
                             (m1 : Morphism o1 o2)
                             (m2 : Morphism o2 o3)
                             (m3 : Morphism o3 o4),
                        Compose (Compose m3 m2) m1 = Compose m3 (Compose m2 m1);
      (* ask for [eq_sym (Associativity ...)], so that C^{op}^{op} is convertible with C *)
      Associativity_sym : forall o1 o2 o3 o4
                                 (m1 : Morphism o1 o2)
                                 (m2 : Morphism o2 o3)
                                 (m3 : Morphism o3 o4),
                            Compose m3 (Compose m2 m1) = Compose (Compose m3 m2) m1;
      LeftIdentity : forall a b (f : Morphism a b), Compose (Identity b) f = f;
      RightIdentity : forall a b (f : Morphism a b), Compose f (Identity a) = f
    }.

Bind Scope category_scope with Category.
Bind Scope object_scope with Object.
Bind Scope morphism_scope with Morphism.

Arguments Object C%category : rename.
Arguments Morphism !C%category s d : rename. (* , simpl nomatch. *)
Arguments Identity [!C%category] x%object : rename.
Arguments Compose [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

Section CategoryInterface.
  Definition Build_Category (obj : Type)
             (Morphism : obj -> obj -> Type)
             (Identity' : forall o : obj, Morphism o o)
             (Compose' : forall s d d' : obj, Morphism d d' -> Morphism s d -> Morphism s d')
             (Associativity' : forall (o1 o2 o3 o4 : obj) (m1 : Morphism o1 o2) (m2 : Morphism o2 o3) (m3 : Morphism o3 o4),
                                 Compose' o1 o2 o4 (Compose' o2 o3 o4 m3 m2) m1 = Compose' o1 o3 o4 m3 (Compose' o1 o2 o3 m2 m1))
             (LeftIdentity' : forall (a b : obj) (f : Morphism a b), Compose' a b b (Identity' b) f = f)
             (RightIdentity' : forall (a b : obj) (f : Morphism a b), Compose' a a b f (Identity' a) = f)
  : Category
    := @Build_Category' obj
                                   Morphism
                                   Identity'
                                   Compose'
                                   Associativity'
                                   (fun _ _ _ _ _ _ _ => eq_sym (Associativity' _ _ _ _ _ _ _))
                                   LeftIdentity'
                                   RightIdentity'.
End CategoryInterface.

(* create a hint db for all category theory things *)
Create HintDb category discriminated.
(* create a hint db for morphisms in categories *)
Create HintDb morphism discriminated.

Hint Extern 1 => symmetry : category morphism. (* TODO(jgross): Why do I need this? *)

Ltac spcategory_hideProofs :=
  repeat match goal with
             | [ |- context[{|
                               Associativity := ?pf0;
                               Associativity_sym := ?pf1;
                               LeftIdentity := ?pf2;
                               RightIdentity := ?pf3
                             |}] ] =>
               hideProofs pf0 pf1 pf2 pf3
         end.

Hint Resolve @LeftIdentity @RightIdentity @Associativity : category morphism.
Hint Rewrite @LeftIdentity @RightIdentity : category.
Hint Rewrite @LeftIdentity @RightIdentity : morphism.

Section Categories_Equal.
  Section contr_eq.
    Variables C D : Category.
    Section contr_eq'.
      Hypothesis C_morphism_proof_irrelevance
      : forall s d (m1 m2 : Morphism C s d) (pf1 pf2 : m1 = m2),
          pf1 = pf2.
      Hypothesis HO : Object C = Object D.
      Hypothesis HM : match HO in (_ = y) return (y -> y -> Type) with
                        | eq_refl => Morphism C
                      end = Morphism D.

      Let HIdT : Prop.
        refine (_ = Identity (C := D)).
        case HM; clear HM.
        case HO; clear HO.
        exact (Identity (C := C)).
      Defined.
      Hypothesis HId : HIdT.

      Let HCoT : Prop.
        refine (_ = Compose (C := D)).
        clear HId HIdT.
        case HM; clear HM.
        case HO; clear HO.
        exact (Compose (C := C)).
      Defined.
      Hypothesis HCo : HCoT.

      Lemma Category_contr_eq' : C = D.
      Proof.
        hnf in *.
        destruct C, D.
        subst_body.
        simpl in *.
        repeat subst.
        f_equal;
          repeat (apply functional_extensionality_dep; intro);
          trivial.
      Qed.
    End contr_eq'.

    Section contr_eq.
      Hypothesis C_morphism_proof_irrelevance
      : forall s d (m1 m2 : Morphism C s d) (pf1 pf2 : m1 = m2),
          pf1 = pf2.

      (* presumably this can be proven from the above by univalence,
         and turning equalities into equivalences *)
      Hypothesis C_morphism_type_contr
      : forall s d (pf1 pf2 : Morphism C s d = Morphism C s d),
          pf1 = pf2.

      Hypothesis HO : Object C = Object D.
      Hypothesis HM : forall s d,
                        match HO in (_ = y) return (y -> y -> Type) with
                          | eq_refl => Morphism C
                        end s d = Morphism D s d.

      Let HIdT : forall x : D, Prop.
        intro x.
        refine (_ = Identity x).
        case (HM x x); clear HM.
        revert x; case HO; clear HO; intro x.
        exact (Identity x).
      Defined.
      Hypothesis HId : forall x, HIdT x.

      Let HCoT s d d' (m1 : Morphism D d d') (m2 : Morphism D s d) : Prop.
        refine (_ = Compose m1 m2).
        clear HId HIdT.
        revert m1 m2.
        case (HM s d'), (HM d d'), (HM s d); clear HM.
        revert s d d'.
        case HO; clear HO.
        exact (Compose (C := C)).
      Defined.
      Hypothesis HCo : forall s d d' m1 m2, @HCoT s d d' m1 m2.

      Lemma Category_contr_eq : C = D.
      Proof.
        let f := match type of HM with forall s d, ?f s d = ?f' s d => constr:(f) end in
        let f' := match type of HM with forall s d, ?f s d = ?f' s d => constr:(f') end in
        assert (HM' : f = f')
          by (repeat (apply functional_extensionality_dep; intro); trivial).
        apply (Category_contr_eq' C_morphism_proof_irrelevance HO HM');
          repeat (apply functional_extensionality_dep; intro);
          destruct C, D;
          subst_body;
          simpl in *;
          repeat (subst || intro || apply functional_extensionality_dep);
          etransitivity;
          try match goal with
                | [ H : _ |- _ ] => solve [ apply H ]
              end;
          [|];
          instantiate;
          generalize_eq_match;
          subst_eq_refl_dec;
          trivial.
      Qed.
    End contr_eq.
  End contr_eq.

  Lemma Category_eq `(C : Category) `(D : Category) :
    @Object C = @Object D
    -> @Morphism C == @Morphism D
    -> @Identity C == @Identity D
    -> @Compose C == @Compose D
    -> C = D.
    intros.
    destruct_head @Category;
    simpl in *; repeat subst;
    f_equal; apply proof_irrelevance.
  Qed.
End Categories_Equal.

Ltac spcat_eq_step_with tac :=
  structures_eq_step_with_tac ltac:(apply Category_eq) tac.

Ltac spcat_eq_with tac := repeat spcat_eq_step_with tac.

Ltac spcat_eq_step := spcat_eq_step_with idtac.
Ltac spcat_eq := spcategory_hideProofs; spcat_eq_with idtac.

Ltac solve_for_identity :=
  match goal with
    | [ |- @Compose ?C ?s ?s ?d ?a ?b = ?b ]
      => cut (a = @Identity C s);
        [ try solve [ let H := fresh in intro H; rewrite H; apply LeftIdentity ] | ]
    | [ |- @Compose ?C ?s ?d ?d ?a ?b = ?a ]
      => cut (b = @Identity C d );
        [ try solve [ let H := fresh in intro H; rewrite H; apply RightIdentity ] | ]
  end.

(** * Version of [Associativity] that avoids going off into the weeds in the presence of unification variables *)

Definition NoEvar T (_ : T) := True.

Lemma AssociativityNoEvar `(C : Category) : forall (o1 o2 o3 o4 : C) (m1 : C.(Morphism) o1 o2)
  (m2 : C.(Morphism) o2 o3) (m3 : C.(Morphism) o3 o4),
  NoEvar (m1, m2) \/ NoEvar (m2, m3) \/ NoEvar (m1, m3)
  -> Compose (Compose m3 m2) m1 = Compose m3 (Compose m2 m1).
  intros; apply Associativity.
Qed.

Ltac noEvar := match goal with
                 | [ |- context[NoEvar ?X] ] => (has_evar X; fail 1)
                                                  || cut (NoEvar X); [ intro; tauto | constructor ]
               end.

Hint Rewrite @AssociativityNoEvar using noEvar : category.
Hint Rewrite @AssociativityNoEvar using noEvar : morphism.

Ltac try_associativity_quick tac := try_rewrite Associativity tac.
Ltac try_associativity tac := try_rewrite_by AssociativityNoEvar ltac:(idtac; noEvar) tac.

Ltac find_composition_to_identity :=
  match goal with
    | [ H : @Compose _ _ _ _ ?a ?b = @Identity _ _ |- context[@Compose ?B ?C ?D ?E ?c ?d] ]
      => let H' := fresh in
        assert (H' : b = d /\ a = c) by (split; reflexivity); clear H';
          assert (H' : @Compose B C D E c d = @Identity _ _) by (
            exact H ||
              (unfold Object; simpl in H |- *; exact H || (rewrite H; reflexivity))
          );
          first [
            rewrite H'
            | simpl in H' |- *; rewrite H'
            | let H'T := type of H' in fail 2 "error in rewriting a found identity" H "[" H'T "]"
          ]; clear H'
  end.

(** * Back to the main content.... *)

Section Category.
  Context `(C : Category).

  (* Quoting Wikipedia,
    In category theory, an epimorphism (also called an epic
    morphism or, colloquially, an epi) is a morphism [f : X → Y]
    which is right-cancellative in the sense that, for all
    morphisms [g, g' : Y → Z],
    [g ○ f = g' ○ f -> g = g']

    Epimorphisms are analogues of surjective functions, but they
    are not exactly the same. The dual of an epimorphism is a
    monomorphism (i.e. an epimorphism in a category [C] is a
    monomorphism in the dual category [OppositeCategory C]).
    *)
  Definition IsEpimorphism x y (m : C.(Morphism) x y) : Prop :=
    forall z (m1 m2 : C.(Morphism) y z), Compose m1 m = Compose m2 m ->
      m1 = m2.
  Definition IsMonomorphism x y (m : C.(Morphism) x y) : Prop :=
    forall z (m1 m2 : C.(Morphism) z x), Compose m m1 = Compose m m2 ->
      m1 = m2.

  Section properties.
    Lemma IdentityIsEpimorphism x : IsEpimorphism _ _ (Identity x).
      repeat intro; autorewrite with category in *; trivial.
    Qed.

    Lemma IdentityIsMonomorphism x : IsMonomorphism _ _ (Identity x).
      repeat intro; autorewrite with category in *; trivial.
    Qed.

    Lemma EpimorphismComposition s d d' m0 m1 :
      IsEpimorphism _ _ m0
      -> IsEpimorphism _ _ m1
      -> IsEpimorphism _ _ (Compose (C := C) (s := s) (d := d) (d' := d') m0 m1).
      repeat intro.
      repeat match goal with | [ H : _ |- _ ] => rewrite <- Associativity in H end.
      intuition.
    Qed.

    Lemma MonomorphismComposition s d d' m0 m1 :
      IsMonomorphism _ _ m0
      -> IsMonomorphism _ _ m1
      -> IsMonomorphism _ _ (Compose (C := C) (s := s) (d := d) (d' := d') m0 m1).
      repeat intro.
      repeat match goal with | [ H : _ |- _ ] => rewrite Associativity in H end.
      intuition.
    Qed.
  End properties.
End Category.

Hint Immediate @IdentityIsEpimorphism @IdentityIsMonomorphism @MonomorphismComposition @EpimorphismComposition : category morphism.

Arguments IsEpimorphism [C x y] m.
Arguments IsMonomorphism [C x y] m.

Section AssociativityComposition.
  Context `(C : Category).
  Variables o0 o1 o2 o3 o4 : C.

  Lemma compose4associativity_helper
    (a : Morphism C o3 o4) (b : Morphism C o2 o3)
    (c : Morphism C o1 o2) (d : Morphism C o0 o1) :
    Compose (Compose a b) (Compose c d) = (Compose a (Compose (Compose b c) d)).
    repeat rewrite Associativity; reflexivity.
  Qed.
End AssociativityComposition.

Ltac compose4associativity' a b c d := transitivity (Compose a (Compose (Compose b c) d)); try solve [ apply compose4associativity_helper ].
Ltac compose4associativity :=
  match goal with
    | [ |- Compose (Compose ?a ?b) (Compose ?c ?d) = _ ] => compose4associativity' a b c d
    | [ |- _ = Compose (Compose ?a ?b) (Compose ?c ?d) ] => compose4associativity' a b c d
  end.


(** * The saturation prover: up to some bound on number of steps, consider all ways to extend equivalences with pre- or post-composition. *)

(** The main tactic, which tries a single round of making deductions from hypotheses that exist at the start of the round.
    Only variables in the goal are chosen to compose. *)

Ltac saturate := repeat match goal with
                          | [ H : @eq (Morphism _ _ _) ?M ?N |- _ ] =>
                            let tryIt G :=
                              match goal with
                                | [ _ : G |- _ ] => fail 1
                                | [ |- context[G] ] => fail 1
                                | _ => let H' := fresh "H" in assert (H' : G) by eauto; generalize dependent H'
                              end in
                              repeat match goal with
                                       | [ m : Morphism _ _ _ |- _ ] =>
                                         tryIt (Compose M m = Compose N m)
                                       | [ m : Morphism _ _ _ |- _ ] =>
                                         tryIt (Compose m M = Compose m N)
                                     end; generalize dependent H
                        end; intros; autorewrite with core in *.

(** To be sure that all relevant terms are represented as variables, we use this tactic to create variables for
    all non-[Compose] subterms of a morphism expression. *)

Ltac extractMorphisms G :=
  match G with
    | Compose ?G1 ?G2 =>
      extractMorphisms G1;
      extractMorphisms G2
    | _ =>
      match goal with
        | [ x := G |- _ ] => idtac
        | [ x : _ |- _ ] =>
          match x with
            | G => idtac
          end
        | _ => pose G
      end
  end.

(** This tactic calls the above on two morphisms being compared for equivalence in the goal. *)

Ltac createVariables :=
  match goal with
    | [ |- @eq (Morphism _ _ _) ?X ?Y ] =>
      extractMorphisms X;
      extractMorphisms Y
  end.

(** After we are done with our variable-related hijinks, we can clean up by removing the new variables,
    replacing them by their definitions. *)

Ltac removeVariables :=
  repeat match goal with
           | [ x := _ |- _ ] => subst x
         end.

(** This notation ties it all together, taking as argument the number of [saturate] rounds to run. *)

Tactic Notation "morphisms" integer(numSaturations) :=
  t; createVariables; do numSaturations saturate; removeVariables; eauto 3.
