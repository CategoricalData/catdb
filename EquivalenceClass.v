Require Import Setoid ProofIrrelevance FunctionalExtensionality Ensembles.
Require Import Common Notations.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

(**
   An equivalence class is a non-empty set of all values
   which are all equivalent to some particular value.
*)

Local Ltac apply_proof_irrelevance :=
  match goal with
    | [ |- @eq ?T _ _ ] => let T' := type of T in
                           match eval hnf in T' with
                             | Prop => apply proof_irrelevance
                           end
  end.

Local Ltac specialize_with tac fin_tac :=
  match goal with
    | [ x : ?T, H : forall _ : ?T, _ |- _ ] => specialize (H x); tac; specialize_with tac fin_tac
    | _ => fin_tac
  end.

Section EquivalenceClass.
  Variable value : Type.
  Variable equiv : value -> value -> Prop.
  (* [E] is an equivalence class if it is non-empty and if all it consists
     of all values that are equivalent to some particular value.
     Because the equivalence relation is transitive, we can encode
     this without picking a representative element by requiring that
     for every member of the class, the class consists of exactly the
     values equivalent to that member. *)
  Record EquivalenceClass := {
    InClass : value -> Prop;

    ClassInhabited : exists v, InClass v;

    ClassEquivalent : relation value := equiv;
    ClassEquivalent_refl : Reflexive ClassEquivalent;
    ClassEquivalent_sym : Symmetric ClassEquivalent;
    ClassEquivalent_trans : Transitive ClassEquivalent;

    ClassElementsEquivalent : forall v, InClass v -> forall v', InClass v' -> ClassEquivalent v v';
    ClassContainsEquivalent : forall v, InClass v -> forall v', ClassEquivalent v v' -> InClass v'
  }.
End EquivalenceClass.

Add Parametric Relation value equiv (E : @EquivalenceClass value equiv) : _ (ClassEquivalent E)
  reflexivity proved by (@ClassEquivalent_refl _ _ _)
  symmetry proved by (@ClassEquivalent_sym _ _ _)
  transitivity proved by (@ClassEquivalent_trans _ _ _)
    as ClassEquivalent_rel.

Add Parametric Morphism value equiv (E : @EquivalenceClass value equiv) : (InClass E)
  with signature equiv ==> iff
    as InClass_mor.
  intros x y eqv; split; intro inc;
    eapply ClassContainsEquivalent; eauto; try symmetry; eauto.
Qed.

Section equiv.
  Variable value : Type.
  Variable equiv : value -> value -> Prop.

  Hypothesis equiv_Equivalence : Equivalence equiv.

  Local Add Parametric Relation : _ equiv
    reflexivity proved by (Equivalence.equiv_reflexive _)
    symmetry proved by (Equivalence.equiv_symmetric _)
    transitivity proved by (Equivalence.equiv_transitive _)
      as equiv_equiv_rel.

  Local Infix "~=" := equiv.

  Local Ltac simpl_equiv := hnf; intros; trivial;
    repeat match goal with
             | _ => solve [ reflexivity ]
             | _ => solve [ symmetry; trivial ]
             | _ => solve [ etransitivity; eauto ]
             | _ => solve [ symmetry; etransitivity; eauto ]
             | _ => solve [ etransitivity; eauto; symmetry; eauto ]
             | [ H : equiv _ _ -> False |- _ ] => contradict H; trivial
             | [ H : ~ equiv _ _ |- _ ] => contradict H; trivial
           end.

  (* The equivalence [classOf] a particular [value] is defined by the proposition that
     the elements are equivalent to that [value]. *)
  Definition classOf (v : value) : EquivalenceClass equiv.
    exists (fun v' => v ~= v');
      abstract (
        repeat esplit; unfold InClass in *;
          simpl_equiv
      ).
  Defined.

  Lemma classOf_refl : forall v, InClass (classOf v) v.
    compute; intro; reflexivity.
  Qed.

  (* Two equivalence classes are the same if they share all values *)
  Definition sameClass (C C' : EquivalenceClass equiv) := forall v, (InClass C v <-> InClass C' v).

  Definition disjointClasses (C C' : EquivalenceClass equiv) := forall v, ~InClass C v \/ ~InClass C' v.

  Definition differentClasses (C C' : EquivalenceClass equiv) := exists v,
    (InClass C v /\ ~InClass C' v) \/
    (~InClass C v /\ InClass C' v).

  Definition notDisjointClasses (C C' : EquivalenceClass equiv) := exists v, InClass C v /\ InClass C' v.

  Definition notDisjointClasses' (C C' : EquivalenceClass equiv) := exists v v', InClass C v /\ InClass C' v' /\ equiv v v'.

  Lemma sameClass_refl (C : EquivalenceClass equiv) : sameClass C C.
    clear equiv_Equivalence; firstorder.
  Qed.

  Lemma sameClass_sym (C C' : EquivalenceClass equiv) : sameClass C C' -> sameClass C' C.
    clear equiv_Equivalence; firstorder.
  Qed.

  Lemma sameClass_trans (C C' C'' : EquivalenceClass equiv) : sameClass C C' -> sameClass C' C'' -> sameClass C C''.
    clear equiv_Equivalence; firstorder.
  Qed.

  Lemma sameClass_eq (C C' : EquivalenceClass equiv) : (sameClass C C') -> (C = C').
    clear equiv_Equivalence; intro H.
    cut (InClass C = InClass C');
      destruct C, C'; simpl;
        intros;
          unfold sameClass in *;
            subst;
              split_iff;
              f_equal; try apply_proof_irrelevance;
                apply Extensionality_Ensembles;
                  hnf; split; hnf; simpl;
                    firstorder.
  Qed.

  Lemma eq_sameClass (C C' : EquivalenceClass equiv) : C = C' -> sameClass C C'.
    intro; subst; apply sameClass_refl.
  Qed.

  Global Add Parametric Morphism : classOf
    with signature equiv ==> eq
      as classOf_mor.
    intros x y eqv;
      apply sameClass_eq; compute in *; intros; split; intros; simpl_equiv.
  Qed.

  Lemma classOf_eq x y : classOf x = classOf y <-> equiv x y.
    split; intro H; try apply classOf_mor; trivial.
    pose (classOf_refl x).
    pose (classOf_refl y).
    rewrite H in *;
      compute in *;
        simpl_equiv.
  Qed.

  Lemma disjointClasses_differentClasses (C C' : EquivalenceClass equiv) : (disjointClasses C C') -> (differentClasses C C').
    clear equiv_Equivalence; unfold differentClasses, disjointClasses; intro H.
    pose (ClassInhabited C) as H'; destruct H' as [ x H' ].
    exists x; specialize (H x); tauto.
  Qed.

  Lemma notDisjointClasses_sameClass (C C' : EquivalenceClass equiv) : (notDisjointClasses C C') -> (sameClass C C').
    clear equiv_Equivalence; unfold notDisjointClasses, sameClass; intro H; destruct H as [ x [ H0 H1 ] ]; intro v; split; intros;
      match goal with
        | [ H0 : InClass ?C ?x, H1 : InClass ?C ?y |- InClass ?C' ?x ]
          => let H := fresh in
            assert (H : equiv x y) by (apply (ClassElementsEquivalent C); assumption);
              rewrite H; assumption
      end.
  Qed.

  Lemma notDisjointClasses_eq (C C' : EquivalenceClass equiv) : (notDisjointClasses C C') -> C = C'.
    clear equiv_Equivalence; intro; apply sameClass_eq; apply notDisjointClasses_sameClass; assumption.
  Qed.

  Lemma EquivalenceClass_forall_equiv__eq (C C' : EquivalenceClass equiv) :
    (forall v v', (InClass C v \/ InClass C' v') -> (InClass C v /\ InClass C' v' <-> equiv v v')) ->
    C' = C.
    clear equiv_Equivalence; intro H. apply sameClass_eq; unfold sameClass; intro v.
    assert (equiv v v) by reflexivity; firstorder.
  Qed.

  Lemma EquivalenceClass_forall__eq (C C' : EquivalenceClass equiv) :
    (forall v, InClass C v <-> InClass C' v) ->
    C' = C.
    clear equiv_Equivalence; intro H. apply sameClass_eq; unfold sameClass;
    firstorder.
  Qed.
End equiv.

Add Parametric Relation value equiv : _ (@sameClass value equiv)
  reflexivity proved by (@sameClass_refl _ _)
  symmetry proved by (@sameClass_sym _ _)
  transitivity proved by (@sameClass_trans _ _)
    as sameClass_mor.

Section InClass_classOf.
  Variable value : Type.
  Variable equiv : value -> value -> Prop.
  Variable C : EquivalenceClass equiv.

  Lemma InClass_classOf_eq eqv v : InClass C v -> C = classOf eqv v.
    intro H.
    apply sameClass_eq.
    pose (classOf eqv v).
    pose (classOf_refl eqv v).
    pose (@ClassContainsEquivalent _ equiv).
    pose (@ClassElementsEquivalent _ equiv).
    specialize_all_ways.
    intro; split; intro;
      eauto.
  Qed.

  Let C_Equivalence : Equivalence equiv
    := {| Equivalence_Reflexive := ClassEquivalent_refl C;
          Equivalence_Symmetric := ClassEquivalent_sym C;
          Equivalence_Transitive := ClassEquivalent_trans C |}.

  Definition InClass_classOf_eq' : forall v, InClass C v -> C = classOf C_Equivalence v
    := InClass_classOf_eq C_Equivalence.
End InClass_classOf.

Ltac create_classOf_InClass :=
  repeat match goal with
           | [ H : InClass (@classOf ?v ?e ?eq ?val) _ |- _ ] => unique_pose (@classOf_refl v e eq val)
           | [ |- InClass (@classOf ?v ?e ?eq ?val) _ ] => unique_pose (@classOf_refl v e eq val)
         end.

Ltac replace_InClass := create_classOf_InClass;
  repeat match goal with
           | [ H : InClass ?C ?x, H' : InClass ?C ?x' |- _ ] => unique_pose (ClassElementsEquivalent C _ H _ H');
             try (clear H' || clear H) (* try, in case both appear in the conclusion *)
           | [ H : InClass ?C ?x |- InClass ?C ?x' ] => apply (ClassContainsEquivalent C x H x')
           | [ |- exists v : ?T, @?G v ] =>
             match G with
               | appcontext[InClass ?C ?v] => fail 1 (* [?v] cannot be the same as [v] above, so we fail *)
               | appcontext[InClass ?C _] => (* match an [InClass] expression that references a variable not scoped outside.
                                                This is a kludge to get the correct InClass, which matches the [exists]. *)
                 let v := fresh in let H := fresh in
                   destruct (ClassInhabited C) as [ v H ]; exists v
             end
           | [ |- _ /\ _ ] => split; intros; create_classOf_InClass
         end.

Ltac InClass2classOf eqv :=
  repeat match goal with
           | [ H : InClass ?C ?x |- _ ] =>
             apply (@InClass_classOf_eq _ _ C eqv _) in H
         end.

Ltac InClass2classOf' :=
  repeat match goal with
           | [ H : InClass ?C ?x |- _ ] =>
             apply (@InClass_classOf_eq' _ _ C _) in H
         end.

Hint Extern 1 (@eq (EquivalenceClass _ _) _ _) => apply EquivalenceClass_forall__eq; replace_InClass.

Ltac clear_InClass' :=
  repeat match goal with
           | [ |- context[InClass] ] => fail 1
           | [ H : InClass _ _ |- _ ] => clear H
         end.

Ltac clear_InClass := replace_InClass; clear_InClass'.

Section apply1.
  Variable value0 : Type.
  Variable equiv0 : value0 -> value0 -> Prop.

  Variable value' : Type.
  Variable equiv' : value' -> value' -> Prop.

  Variable f : value0 -> value'.
  Hypothesis f_mor : forall v v', equiv0 v v' -> equiv' (f v) (f v').
  Variable E0 : EquivalenceClass equiv0.

  Local Add Parametric Relation : _ equiv0
    reflexivity proved by (ClassEquivalent_refl E0)
    symmetry proved by (ClassEquivalent_sym E0)
    transitivity proved by (ClassEquivalent_trans E0)
      as apply_equiv_rel.

  Hypothesis equiv'_Equivalence : Equivalence equiv'.

  Local Add Parametric Relation : _ equiv'
    reflexivity proved by (Equivalence.equiv_reflexive _)
    symmetry proved by (Equivalence.equiv_symmetric _)
    transitivity proved by (Equivalence.equiv_transitive _)
      as apply_equiv'_rel.

  Hint Resolve f_mor.

  Definition apply_to_class : EquivalenceClass equiv'.
    refine {| InClass := (fun v => exists v0, InClass E0 v0 /\ equiv' v (f v0)) |};
      abstract (
        intros;
          solve [ reflexivity || (symmetry; assumption) || (etransitivity; eauto) ] ||
            solve [ destruct (ClassInhabited E0) as [ v0 ]; exists (f v0); eexists; split; eauto; apply f_mor; reflexivity ] ||
              solve [
                destruct_hypotheses; repeat esplit; clear_InClass; repeat_subst_mor_of_type value'; try apply f_mor;
                  reflexivity || assumption || etransitivity; eauto
              ]
      ).
  Defined.

  Lemma apply_to_class_f_inj : forall v, InClass E0 v -> InClass apply_to_class (f v).
    compute; firstorder.
  Qed.

  Lemma apply_to_class_f_surj : forall v, InClass apply_to_class v -> exists v', equiv' v (f v') /\ InClass E0 v'.
    compute; firstorder.
  Qed.
End apply1.

Hint Resolve apply_to_class_f_inj.

Lemma apply_to_classOf value0 equiv0 equiv0_eqv value' equiv' equiv'_eqv f f_mor e0 :
  @apply_to_class value0 equiv0 value' equiv' f f_mor
  (@classOf _ _ equiv0_eqv e0)
  equiv'_eqv
  = @classOf _ _ equiv'_eqv (f e0).
Proof.
  apply EquivalenceClass_forall__eq; intros; split; intros;
    hnf in *; destruct_hypotheses; replace_InClass; repeat_subst_mor_of_type value'; eauto; reflexivity.
Qed.

Section apply2.
  Variable value0 : Type.
  Variable equiv0 : value0 -> value0 -> Prop.

  Variable value1 : Type.
  Variable equiv1 : value1 -> value1 -> Prop.

  Variable value' : Type.
  Variable equiv' : value' -> value' -> Prop.

  Hypothesis equiv'_Equivalence : Equivalence equiv'.

  Local Add Parametric Relation : _ equiv'
    reflexivity proved by (Equivalence.equiv_reflexive _)
    symmetry proved by (Equivalence.equiv_symmetric _)
    transitivity proved by (Equivalence.equiv_transitive _)
      as apply2_equiv'_rel.

  Variable f : value0 -> value1 -> value'.
  Hypothesis f_mor : forall v0 v0', equiv0 v0 v0' -> forall v1 v1', equiv1 v1 v1' -> equiv' (f v0 v1) (f v0' v1').

  Variable E0 : EquivalenceClass equiv0.
  Variable E1 : EquivalenceClass equiv1.

  Local Add Parametric Relation : _ equiv0
    reflexivity proved by (@ClassEquivalent_refl _ _ E0)
    symmetry proved by (@ClassEquivalent_sym _ _ E0)
    transitivity proved by (@ClassEquivalent_trans _ _ E0)
      as apply2_equiv0_rel.

  Local Add Parametric Relation : _ equiv1
    reflexivity proved by (@ClassEquivalent_refl _ _ E1)
    symmetry proved by (@ClassEquivalent_sym _ _ E1)
    transitivity proved by (@ClassEquivalent_trans _ _ E1)
      as apply2_equiv1_rel.

  Definition apply2_to_class : EquivalenceClass equiv'.
    refine {| InClass := (fun v => exists v0 v1, InClass E0 v0 /\ InClass E1 v1 /\ equiv' v (f v0 v1)) |};
      abstract (
        intros;
          solve [ reflexivity || (symmetry; assumption) || (etransitivity; eauto) ] ||
            solve [
              destruct (ClassInhabited E0) as [ v0 ], (ClassInhabited E1) as [ v1 ]; exists (f v0 v1); repeat esplit;
              eauto; apply f_mor; reflexivity
            ] ||
            solve [
              destruct_hypotheses; repeat esplit; clear_InClass; repeat_subst_mor_of_type value'; try apply f_mor;
                reflexivity || assumption || etransitivity; eauto
            ]
    ).
  Defined.

  Lemma apply2_to_class_f_inj : forall v0 v1, InClass E0 v0 -> InClass E1 v1 -> InClass apply2_to_class (f v0 v1).
    compute; firstorder.
  Qed.

  Lemma apply2_to_class_f_surj : forall v, InClass apply2_to_class v -> exists v0 v1, equiv' v (f v0 v1) /\ InClass E0 v0 /\ InClass E1 v1.
    compute; firstorder.
  Qed.
End apply2.

Hint Resolve apply2_to_class_f_inj.

Lemma apply2_to_classOf
  value0 equiv0 equiv0_eqv
  value1 equiv1 equiv1_eqv
  value' equiv' equiv'_eqv
  f f_mor e0 e1 :
  @apply2_to_class value0 equiv0 value1 equiv1 value' equiv'
  equiv'_eqv
  f f_mor
  (@classOf _ _ equiv0_eqv e0)
  (@classOf _ _ equiv1_eqv e1)
  = @classOf _ _ equiv'_eqv (f e0 e1).
Proof.
  apply EquivalenceClass_forall__eq; intros; split; intros;
    hnf in *; destruct_hypotheses;
      repeat (clear_InClass; eexists; repeat split);
        clear_InClass;
        repeat_subst_mor_of_type value';
        hnf in *;
          try apply f_mor;
            eauto; reflexivity || (symmetry; assumption).
Qed.

Section description.
  (** Can be imported from Coq.Logic.ClassicalDescription,
      Coq.Logic.ClassicalEpsilon, Coq.Logic.ConstructiveEpsilon,
      Coq.Logic.Epsilon, Coq.Logic.IndefiniteDescription, or, for the
      axiom, Coq.Logic.Description *)

  Hypothesis constructive_definite_description :
    forall (A : Type) (P : A->Prop),
      (exists! x, P x) -> { x : A | P x }.

  Variable T : Type.

  Definition EquivalenceClass_eq_lift
  : EquivalenceClass (@eq T) -> T.
    intro x.
    cut (exists! u, InClass x u).
    - apply constructive_definite_description.
    - destruct (ClassInhabited x) as [u H].
      exists u.
      abstract (
          split; [ exact H
                 | intros; apply (ClassElementsEquivalent x); assumption ]
        ).
  Defined.

  Definition EquivalenceClass_eq_proj
  : T -> EquivalenceClass (@eq T).
    apply classOf; abstract typeclasses eauto.
  Defined.

  Lemma EquivalenceClass_eq_iso1
  : forall x, EquivalenceClass_eq_lift (EquivalenceClass_eq_proj x) = x.
    intros.
    expand.
    match goal with
      | [ |- appcontext[match ?E with _ => _ end] ] => case E
    end.
    intros; subst; reflexivity.
  Qed.

  Lemma EquivalenceClass_eq_iso2
  : forall x, EquivalenceClass_eq_proj (EquivalenceClass_eq_lift x) = x.
    intros.
    apply sameClass_eq; simpl.
    split;
      intros;
      simpl in *;
      subst;
      hnf;
      unfold EquivalenceClass_eq_lift;
      repeat match goal with
               | [ |- appcontext[match ?E with _ => _ end] ] => case E; simpl; intros
             end;
      subst;
      intuition.
    apply (ClassElementsEquivalent x); assumption.
  Qed.
End description.
