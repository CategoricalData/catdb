Require Import Setoid FunctionalExtensionality ProofIrrelevance.
Require Export Schema.
Require Import Common FEqualDep.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Record SmallSchema := {
  SVertex :> Set;
  SEdge : SVertex -> SVertex -> Set;

  SPathsEquivalent : forall s d, relation (path' SEdge s d);
  SPathsEquivalent_Equivalence : forall s d, equivalence _ (@SPathsEquivalent s d);

  SPreCompose : forall s d (E : SEdge s d) d' (p1 p2 : path' _ d d'),
    SPathsEquivalent p1 p2 -> SPathsEquivalent (prepend p1 E) (prepend p2 E);
  SPostCompose : forall s d (p1 p2 : path' _ s d) d' (E : SEdge d d'),
    SPathsEquivalent p1 p2 -> SPathsEquivalent (AddEdge p1 E) (AddEdge p2 E)
}.

Hint Resolve SPreCompose SPostCompose.

Theorem SPreCompose' : forall S s d (E : S.(SEdge) s d) d' (p1 p2 : path' _ d d'),
  SPathsEquivalent _ p1 p2 -> SPathsEquivalent _ (prepend p1 E) (prepend p2 E).
  intros; auto.
Qed.

Theorem SPostCompose' : forall S s d (p1 p2 : path' _ s d) d' (E : S.(SEdge) d d'),
  SPathsEquivalent _ p1 p2
  -> SPathsEquivalent _ (AddEdge p1 E) (AddEdge p2 E).
  intros; auto.
Qed.

Hint Resolve SPreCompose' SPostCompose'.

Add Parametric Relation S s d : _ (@SPathsEquivalent S s d)
  reflexivity proved by (equiv_refl _ _ (@SPathsEquivalent_Equivalence _ _ _))
  symmetry proved by (equiv_sym _ _ (@SPathsEquivalent_Equivalence _ _ _))
  transitivity proved by (equiv_trans _ _ (@SPathsEquivalent_Equivalence _ _ _))
    as spaths_eq.

Hint Resolve spaths_eq_Reflexive spaths_eq_Symmetric.

Definition spath S := path' S.(SEdge).

Section Small2Large.
  Variables S : SmallSchema.

  Hint Resolve SPathsEquivalent SPreCompose SPostCompose prepend_mor.
  Hint Extern 1 => reflexivity.
  Hint Extern 1 => symmetry; assumption.

  (* XXX TODO: Automate this better *)
  Definition SmallSchema2Schema : Schema.
    refine {| Vertex := @SVertex S;
      Edge := @SEdge S;
      PathsEquivalent := @SPathsEquivalent S;
      PathsEquivalent_Equivalence := (fun s d => @Build_equivalence _ _ _ _ _)
    |};
    abstract (
      hnf; simpl; intros;
        eauto; try solve [ etransitivity; eauto ]
    ).
  Defined.
End Small2Large.

Coercion SmallSchema2Schema : SmallSchema >-> Schema.

Lemma SPathsEquivalent_PathsEquivalent (S : SmallSchema) s d (p p' : spath S s d) : SPathsEquivalent S p p' -> PathsEquivalent S p p'.
  simpl; trivial.
Qed.

Lemma PathsEquivalent_SPathsEquivalent (S : SmallSchema) s d (p p' : spath S s d) : PathsEquivalent S p p' -> SPathsEquivalent S p p'.
  simpl; trivial.
Qed.

Add Parametric Morphism S s d d' :
  (@concatenate _ S.(SEdge) s d d')
  with signature (@SPathsEquivalent S _ _) ==> (@SPathsEquivalent S _ _) ==> (@SPathsEquivalent S _ _) as sconcatenate_mor.
  t;
  apply PathsEquivalent_SPathsEquivalent; apply concatenate_mor;
    t.
Qed.

Add Parametric Morphism S s d d' :
  (@AddEdge S _ s d d')
  with signature (@SPathsEquivalent S _ _) ==> (@eq _) ==> (@SPathsEquivalent S _ _) as SAddEdge_mor.
  t.
Qed.

Add Parametric Morphism S s d d' :
  (fun p => @concatenate' S _ s d p d')
  with signature (@SPathsEquivalent S _ _) ==> (@SPathsEquivalent S _ _) ==> (@SPathsEquivalent S _ _) as sconcatenate'_mor.
  t;
  apply PathsEquivalent_SPathsEquivalent; apply concatenate'_mor;
    t.
Qed.

Add Parametric Morphism S s' s d :
  (fun p => @prepend S _ s d p s')
  with signature (@SPathsEquivalent S _ _) ==> (@eq _) ==> (@SPathsEquivalent S _ _) as sprepend_mor.
  t.
Qed.

Hint Resolve sconcatenate_mor SAddEdge_mor sconcatenate'_mor sprepend_mor.

Section GeneralizedSPathEquivalence.
  Variable S : SmallSchema.

  Inductive GeneralizedSPathsEquivalent s d (p : spath S s d) : forall s' d' (p' : spath S s' d'), Prop :=
    | GSPathsEquivalent (p' : spath S s d) : SPathsEquivalent _ p p' -> GeneralizedSPathsEquivalent p p'.

  Lemma GeneralizedSPathsEquivalent_SPathsEquivalent s d (p p' : spath S s d) :
    GeneralizedSPathsEquivalent p p' -> SPathsEquivalent _ p p'.
    intro H; inversion H.
    repeat match goal with
             | [ H : _ |- _ ] => repeat apply inj_pair2 in H
           end.
    repeat subst.
    assumption.
  Qed.

  Lemma GeneralizedSPathsEquivalent_eq s d (p : spath S s d) s' d' (p' : spath S s' d') :
    GeneralizedSPathsEquivalent p p' -> s = s' /\ d = d'.
    intro H; inversion H.
    repeat subst.
    split; trivial.
  Qed.
End GeneralizedSPathEquivalence.

Ltac simpl_GeneralizedSPathsEquivalent := intros;
  repeat match goal with
           | [ H : GeneralizedSPathsEquivalent _ _ |- _ ]
             => destruct (GeneralizedSPathsEquivalent_eq H); repeat subst;
               apply GeneralizedSPathsEquivalent_SPathsEquivalent in H
           | [ |- GeneralizedSPathsEquivalent _ _ ] => apply GSPathsEquivalent
         end.

Section GeneralizedSPathsEquivalenceRelation.
  Variable S : SmallSchema.

  Lemma GeneralizedSPathsEquivalent_refl s d (p : spath S s d) : GeneralizedSPathsEquivalent p p.
    simpl_GeneralizedSPathsEquivalent; reflexivity.
  Qed.

  Lemma GeneralizedSPathsEquivalent_sym s d (p : spath S s d) s' d' (p' : spath S s' d') :
    GeneralizedSPathsEquivalent p p' -> GeneralizedSPathsEquivalent p' p.
    simpl_GeneralizedSPathsEquivalent; symmetry; assumption.
  Qed.

  Lemma GeneralizedSPathsEquivalent_trans s d (p : spath S s d) s' d' (p' : spath S s' d') s'' d'' (p'' : spath S s'' d'') :
    GeneralizedSPathsEquivalent p p' -> GeneralizedSPathsEquivalent p' p'' -> GeneralizedSPathsEquivalent p p''.
    simpl_GeneralizedSPathsEquivalent; transitivity p'; eauto.
  Qed.
End GeneralizedSPathsEquivalenceRelation.

(*
Section Small2LargeId.
  Variables C D : SmallSchema.

  Lemma ss2si_helper (A : Type) (B : A -> Type) (f g : forall x : A, B x) : f = g -> forall x : A, f x = g x.
    intros; subst; reflexivity.
  Qed.

  (* XXX TODO: Automate this better *)
  Lemma SmallSchema2SchemaId :
    SmallSchema2Schema C = SmallSchema2Schema D -> C = D.
    intro H.
    injection H; intros.
    destruct C, D; simpl in *; repeat subst.
    repeat match goal with
             | [ H : _ |- _ ] => apply inj_pair2 in H; simpl in *; repeat subst
           end.
    cut (SPathsEquivalent'0 = SPathsEquivalent'1);
      intros; repeat subst; f_equal; try apply proof_irrelevance.
    repeat (apply functional_extensionality_dep; intro).
    (* Ugh... *)
    Ltac ss2si_helper'' := repeat rewrite spath_roundtrip in *; repeat rewrite spath_roundtrip' in *; try assumption.
    Ltac ss2si_helper' H' H x := assert (H' := @ss2si_helper _ _ _ _ H x); clear H; simpl in H';
      ss2si_helper''.
    Ltac ss2si_helper :=
      match goal with
        | [ H : _ |- ?a ?x ?x0 ?x1 ?x2 = ?b ?x ?x0 ?x1 ?x2 ] => let H' := fresh in
          ss2si_helper' H' H x; ss2si_helper' H H' x0; ss2si_helper' H' H x1; ss2si_helper' H H' x2
      end.
    ss2si_helper.
  Qed.
End Small2LargeId.

Hint Resolve SmallSchema2SchemaId.
*)
