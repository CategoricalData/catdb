Require Import Bool Omega Setoid FunctionalExtensionality ProofIrrelevance.
Require Export Schema.
Require Import Common EquivalenceRelation FEqualDep.

Set Implicit Arguments.

Section spath'.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Inductive spath' (s : V) : V -> Type :=
  | SNoEdges : spath' s s
  | SAddEdge : forall d d', spath' s d -> E d d' -> spath' s d'.

  Fixpoint sprepend s d (p : spath' s d) : forall s', E s' s -> spath' s' d :=
    match p with
      | SNoEdges => fun _ E' => SAddEdge (SNoEdges _) E'
      | SAddEdge _ _ p' E => fun _ E' => SAddEdge (sprepend p' E') E
    end.

  Fixpoint sconcatenate s d d' (p : spath' s d) (p' : spath' d d') : spath' s d' :=
    match p' with
      | SNoEdges => p
      | SAddEdge _ _ p' E => SAddEdge (sconcatenate p p') E
    end.

  Fixpoint sconcatenate' s d (p : spath' s d) : forall d', spath' d d' -> spath' s d' :=
    match p with
      | SNoEdges => fun _ p' => p'
      | SAddEdge _ _ p E => fun _ p' => sconcatenate' p (sprepend p' E)
    end.

  Variable typeOf : V -> Type.
  Variable functionOf : forall s d, E s d -> typeOf s -> typeOf d.

  Fixpoint scompose s d (p : spath' s d) : typeOf s -> typeOf d :=
    match p with
      | SNoEdges => fun x => x
      | SAddEdge _ _ p' E => fun x => functionOf E (scompose p' x)
    end.

  Fixpoint spath'2path' s d (p : spath' s d) : path' E s d :=
    match p with
      | SNoEdges => NoEdges
      | SAddEdge _ _ p' E => AddEdge (spath'2path' p') E
    end.

  Fixpoint path'2spath' s d (p : path' E s d) : spath' s d :=
    match p with
      | NoEdges => SNoEdges _
      | AddEdge _ _ p' E => SAddEdge (path'2spath' p') E
    end.

  Lemma spath_roundtrip s d (p : path' E s d) : spath'2path' (path'2spath' p) = p.
    induction p; t.
  Qed.

  Lemma spath_roundtrip' s d (p : spath' s d) : path'2spath' (spath'2path' p) = p.
    induction p; t.
  Qed.
End spath'.

Implicit Arguments SNoEdges [V E s].
Implicit Arguments SAddEdge [V E s d d'].
Implicit Arguments sprepend [V E s d s'].

Coercion spath'2path' : spath' >-> path'.
Coercion path'2spath' : path' >-> spath'.

Hint Rewrite spath_roundtrip spath_roundtrip'.

Section spath'_Theorems.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Lemma sconcatenate_noedges_p : forall s d (p : spath' E s d), sconcatenate SNoEdges p = p.
    induction p; t.
  Qed.

  Lemma sconcatenate_p_noedges : forall s d (p : spath' E s d), sconcatenate p SNoEdges = p.
    t.
  Qed.

  Lemma sconcatenate'_addedge : forall s d d' d'' (p : spath' E s d) (p' : spath' E d d') (e : E d' d''),
    sconcatenate' p (SAddEdge p' e) = SAddEdge (sconcatenate' p p') e.
    induction p; t.
  Qed.

  Hint Rewrite sconcatenate'_addedge.

  Lemma sconcatenate'_p_noedges : forall s d (p : spath' E s d), sconcatenate' p SNoEdges = p.
    induction p; t.
  Qed.

  Lemma sconcatenate'_noedges_p : forall s d (p : spath' E s d), sconcatenate' SNoEdges p = p.
    t.
  Qed.

  Hint Rewrite sconcatenate'_p_noedges.

  Lemma sconcatenate_addedge : forall s d d'0 d' (p : spath' E s d) (e : E d d'0) (p' : spath' E d'0 d'),
    sconcatenate (SAddEdge p e) p' = sconcatenate' p (sprepend p' e).
    induction p'; t.
  Qed.

  Hint Resolve sconcatenate_noedges_p sconcatenate_addedge.

  Lemma sconcatenate_prepend_equivalent : forall s d d' (p : spath' E s d) (p' : spath' E d d'), sconcatenate p p' = sconcatenate' p p'.
    induction p; t.
  Qed.

  Hint Rewrite sconcatenate_noedges_p sconcatenate_addedge.
  Hint Rewrite <- sconcatenate_prepend_equivalent.

  Lemma sconcatenate_p_addedge : forall s d d' d'' (p : spath' E s d) (p' : spath' E d d') (e : E d' d''),
    sconcatenate p (SAddEdge p' e) = SAddEdge (sconcatenate p p') e.
    induction p; t.
  Qed.

  Lemma sconcatenate_prepend : forall s s' d d' (p1 : spath' E s' d) (p2 : spath' E d d') (e : E s s'),
    (sprepend (sconcatenate p1 p2) e) = (sconcatenate (sprepend p1 e) p2).
    induction p1; t.
  Qed.

  Hint Rewrite sconcatenate_prepend.

  Lemma sconcatenate_associative o1 o2 o3 o4 : forall (p1 : spath' E o1 o2) (p2 : spath' E o2 o3) (p3 : spath' E o3 o4),
    (sconcatenate (sconcatenate p1 p2) p3) = (sconcatenate p1 (sconcatenate p2 p3)).
    induction p1; t.
  Qed.

  Lemma scompose_prepend s' s d (p : spath' E s d) (e : E s' _) typeOf functionOf : forall x, scompose typeOf functionOf (sprepend p e) x = (scompose typeOf functionOf p (functionOf _ _ e x)).
    induction p; t_with t'.
  Qed.
End spath'_Theorems.

Hint Rewrite scompose_prepend.
Hint Rewrite sconcatenate_p_noedges sconcatenate_noedges_p.
Hint Resolve sconcatenate_p_noedges sconcatenate_noedges_p.

Section path_coercion.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Lemma sconcatenate2concatenate : forall s d (p : spath' E s d) d' (p' : spath' E d d'), sconcatenate p p' = concatenate p p'.
   induction p; induction p'; t_with t'.
 Qed.
End path_coercion.

Record SmallSchema := {
  SVertex :> Type;
  SEdge : SVertex -> SVertex -> Type;

  SPathsEquivalent' : forall s d, (spath' SEdge s d) -> (spath' SEdge s d) -> Prop;
  SPathsEquivalent : EquivalenceRelation SPathsEquivalent';

  SPreCompose : forall s d (E : SEdge s d) d' (p1 p2 : spath' _ d d'),
    SPathsEquivalent' p1 p2 -> SPathsEquivalent' (sprepend p1 E) (sprepend p2 E);
  SPostCompose : forall s d (p1 p2 : spath' _ s d) d' (E : SEdge d d'),
    SPathsEquivalent' p1 p2 -> SPathsEquivalent' (SAddEdge p1 E) (SAddEdge p2 E)
}.

Hint Resolve SPreCompose SPostCompose.

Theorem SPreCompose' : forall S s d (E : S.(SEdge) s d) d' (p1 p2 : spath' _ d d'),
  SPathsEquivalent _ _ _ p1 p2 -> SPathsEquivalent _ _ _ (sprepend p1 E) (sprepend p2 E).
  intros; auto.
Qed.

Theorem SPostCompose' : forall S s d (p1 p2 : spath' _ s d) d' (E : S.(SEdge) d d'),
  SPathsEquivalent _ _ _ p1 p2
  -> SPathsEquivalent _ _ _ (SAddEdge p1 E) (SAddEdge p2 E).
  intros; auto.
Qed.

Hint Resolve SPreCompose' SPostCompose'.

Add Parametric Relation S s d : _ (SPathsEquivalent S s d)
  reflexivity proved by (Reflexive _ _ _)
  symmetry proved by (Symmetric _ _ _)
  transitivity proved by (Transitive _ _ _)
    as spaths_eq.

Lemma spaths_equivalence_equivalent S : relations_equivalence_equivalent S.(SPathsEquivalent).
  hnf; trivial.
Qed.

Hint Rewrite spaths_equivalence_equivalent.

(* It's not true that [(p1 = p2 -> p3 = p4) -> (SPathsEquivalent p1 p2 -> SPathsEquivalent p3 p4)]
   Consider a case where p1 = SNoEdges and p2 is a spath containing an edge and its inverse,
   and p3 and p4 are not equivalent spaths.

   So, let's do the relevant theorems again... *)
Section spath'_Equivalence_Theorems.
  Variable S : SmallSchema.

  Lemma saddedge_equivalent : forall s d d' (p p' : spath' _ s d), SPathsEquivalent S _ _ p p'
    -> forall e : SEdge _ d d', SPathsEquivalent S _ _ (SAddEdge p e) (SAddEdge p' e).
    t.
  Qed.

  Lemma sprepend_equivalent : forall s' s d (p p' : spath' _ s d), SPathsEquivalent S _ _ p p'
    -> forall e : SEdge _ s' s, SPathsEquivalent S _ _ (sprepend p e) (sprepend p' e).
    t.
  Qed.

  Hint Rewrite sconcatenate_noedges_p sconcatenate_addedge.
  Hint Rewrite <- sconcatenate_prepend_equivalent.
  Hint Resolve sprepend_equivalent addedge_equivalent.

  Lemma pre_sconcatenate_equivalent : forall s' s d (p1 : spath' _ s' s) (p p' : spath' _ s d),
    SPathsEquivalent S _ _ p p' -> SPathsEquivalent S _ _ (sconcatenate p1 p) (sconcatenate p1 p').
    induction p1; t.
  Qed.

  Lemma post_sconcatenate_equivalent : forall s d d' (p p' : spath' _ s d) (p2 : spath' _ d d'),
    SPathsEquivalent S _ _ p p' -> SPathsEquivalent S _ _ (sconcatenate p p2) (sconcatenate p' p2).
    induction p2; t.
  Qed.

  Hint Resolve pre_sconcatenate_equivalent post_sconcatenate_equivalent.

  Add Parametric Morphism s d d' p:
    (@sconcatenate _ S.(SEdge) s d d' p)
    with signature (SPathsEquivalent S _ _) ==> (SPathsEquivalent S _ _) as sconcatenate_pre_mor.
    t.
  Qed.

  Add Parametric Morphism s d d' p:
    (fun p' => (@sconcatenate _ S.(SEdge) s d d' p' p))
    with signature (SPathsEquivalent S _ _) ==> (SPathsEquivalent S _ _) as sconcatenate_post_mor.
    t.
  Qed.

  Hint Resolve Transitive.

  Lemma sconcatenate_equivalent : forall s d d' (p1 p1' : spath' _ s d) (p2 p2' : spath' _ d d'),
    SPathsEquivalent S _ _ p1 p1' -> SPathsEquivalent S _ _ p2 p2' -> SPathsEquivalent S _ _ (sconcatenate p1 p2) (sconcatenate p1' p2').
    t; eauto.
  Qed.
End spath'_Equivalence_Theorems.

Hint Resolve sconcatenate_equivalent.

Add Parametric Morphism S s d d' :
  (@sconcatenate _ S.(SEdge) s d d')
  with signature (SPathsEquivalent S _ _) ==> (SPathsEquivalent S _ _) ==> (SPathsEquivalent S _ _) as sconcatenate_mor.
  t.
Qed.

Add Parametric Morphism S s d d' :
  (@SAddEdge S _ s d d')
  with signature (SPathsEquivalent S _ _) ==> (@eq _) ==> (SPathsEquivalent S _ _) as SAddEdge_mor.
  t.
Qed.

Add Parametric Morphism S s d d' :
  (fun p => @sconcatenate' S _ s d p d')
  with signature (SPathsEquivalent S _ _) ==> (SPathsEquivalent S _ _) ==> (SPathsEquivalent S _ _) as sconcatenate'_mor.
  intros; repeat rewrite <- sconcatenate_prepend_equivalent; t.
Qed.

Add Parametric Morphism S s' s d :
  (fun p => @sprepend S _ s d p s')
  with signature (SPathsEquivalent S _ _) ==> (@eq _) ==> (SPathsEquivalent S _ _) as sprepend_mor.
  t.
Qed.

Definition spath S := spath' S.(SEdge).


Section Small2Large.
  Variables S : SmallSchema.

  Hint Resolve SPathsEquivalent SPreCompose SPostCompose Reflexive Symmetric Transitive sprepend_mor.

  (* XXX TODO: Automate this better *)
  Definition SmallSchema2Schema : Schema.
    refine {| Vertex := @SVertex S;
      Edge := @SEdge S;
      PathsEquivalent' := @SPathsEquivalent' S;
      PathsEquivalent := Build_EquivalenceRelation _ _ _ _ _
    |}; abstract (
      simpl; intros;
        auto; try assumption ||
          reflexivity ||
            solve [ symmetry; try assumption ] ||
              solve [ etransitivity; eauto; try reflexivity ];
              match goal with
                | [ |- ?Rel (path'2spath' (prepend ?p ?E)) (path'2spath' (prepend ?p' ?E)) ]
                  => cut (SPathsEquivalent _ _ _ (sprepend p E) (sprepend p' E));
                    auto;
                      try (
                        intro;
                          transitivity (sprepend p E);
                            try solve [
                              repeat match goal with
                                       | [ H : context[p] |- _ ] => clear H
                                     end;
                              induction p; simpl; try apply SAddEdge_mor; eauto
                            ];
                            transitivity (sprepend p' E);
                              try solve [
                                repeat match goal with
                                         | [ H : context[p'] |- _ ] => clear H
                                       end;
                                induction p'; simpl; try apply SAddEdge_mor; eauto
                              ];
                              assumption
                      )
              end
    ).
  Defined.
End Small2Large.

Coercion SmallSchema2Schema : SmallSchema >-> Schema.

Section GeneralizedSPathEquivalence.
  Variable S : SmallSchema.

  Inductive GeneralizedSPathsEquivalent s d (p : spath S s d) : forall s' d' (p' : spath S s' d'), Prop :=
    | GSPathsEquivalent (p' : spath S s d) : SPathsEquivalent _ _ _ p p' -> GeneralizedSPathsEquivalent p p'.

  Lemma GeneralizedSPathsEquivalent_SPathsEquivalent s d (p p' : spath S s d) :
    GeneralizedSPathsEquivalent p p' -> SPathsEquivalent _ _ _ p p'.
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
