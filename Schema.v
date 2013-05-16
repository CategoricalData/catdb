Require Import Setoid.
Require Export Relations.
Require Import Common Eqdep.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section path'.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Inductive path' (s : V) : V -> Type :=
  | NoEdges : path' s s
  | AddEdge : forall d d', path' s d -> E d d' -> path' s d'.

  Fixpoint prepend s d (p : path' s d) : forall s', E s' s -> path' s' d :=
    match p with
      | NoEdges => fun _ E' => AddEdge (NoEdges _) E'
      | AddEdge _ _ p' E => fun _ E' => AddEdge (prepend p' E') E
    end.

  Fixpoint concatenate s d d' (p : path' s d) (p' : path' d d') : path' s d' :=
    match p' with
      | NoEdges => p
      | AddEdge _ _ p' E => AddEdge (concatenate p p') E
    end.

  Fixpoint concatenate' s d (p : path' s d) : forall d', path' d d' -> path' s d' :=
    match p with
      | NoEdges => fun _ p' => p'
      | AddEdge _ _ p E => fun _ p' => concatenate' p (prepend p' E)
    end.

  Variable typeOf : V -> Type.
  Variable functionOf : forall s d, E s d -> typeOf s -> typeOf d.

  Fixpoint compose s d (p : path' s d) : typeOf s -> typeOf d :=
    match p with
      | NoEdges => fun x => x
      | AddEdge _ _ p' E => fun x => functionOf E (compose p' x)
    end.
End path'.

Implicit Arguments NoEdges [V E s].
Implicit Arguments AddEdge [V E s d d'].
Implicit Arguments prepend [V E s d s'].

Section path'_Theorems.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Lemma concatenate_noedges_p : forall s d (p : path' E s d), concatenate NoEdges p = p.
    induction p; t.
  Qed.

  Lemma concatenate_p_noedges : forall s d (p : path' E s d), concatenate p NoEdges = p.
    t.
  Qed.

  Lemma concatenate'_addedge : forall s d d' d'' (p : path' E s d) (p' : path' E d d') (e : E d' d''),
    concatenate' p (AddEdge p' e) = AddEdge (concatenate' p p') e.
    induction p; t.
  Qed.

  Hint Rewrite concatenate'_addedge.

  Lemma concatenate'_p_noedges : forall s d (p : path' E s d), concatenate' p NoEdges = p.
    induction p; t.
  Qed.

  Lemma concatenate'_noedges_p : forall s d (p : path' E s d), concatenate' NoEdges p = p.
    t.
  Qed.

  Hint Rewrite concatenate'_p_noedges.

  Lemma concatenate_addedge : forall s d d'0 d' (p : path' E s d) (e : E d d'0) (p' : path' E d'0 d'),
    concatenate (AddEdge p e) p' = concatenate' p (prepend p' e).
    induction p'; t.
  Qed.

  Hint Resolve concatenate_noedges_p concatenate_addedge.

  Lemma concatenate_prepend_equivalent : forall s d d' (p : path' E s d) (p' : path' E d d'), concatenate p p' = concatenate' p p'.
    induction p; t.
  Qed.

  Hint Rewrite concatenate_noedges_p concatenate_addedge.
  Hint Rewrite <- concatenate_prepend_equivalent.

  Lemma concatenate_p_addedge : forall s d d' d'' (p : path' E s d) (p' : path' E d d') (e : E d' d''),
    concatenate p (AddEdge p' e) = AddEdge (concatenate p p') e.
    induction p; t.
  Qed.

  Lemma concatenate_prepend : forall s s' d d' (p1 : path' E s' d) (p2 : path' E d d') (e : E s s'),
    (prepend (concatenate p1 p2) e) = (concatenate (prepend p1 e) p2).
    induction p1; t.
  Qed.

  Hint Rewrite concatenate_prepend.

  Lemma concatenate_associative o1 o2 o3 o4 : forall (p1 : path' E o1 o2) (p2 : path' E o2 o3) (p3 : path' E o3 o4),
    (concatenate (concatenate p1 p2) p3) = (concatenate p1 (concatenate p2 p3)).
    induction p1; t.
  Qed.

  Lemma compose_prepend s' s d (p : path' E s d) (e : E s' _) typeOf functionOf : forall x, compose typeOf functionOf (prepend p e) x = (compose typeOf functionOf p (functionOf _ _ e x)).
    induction p; t_with t'.
  Qed.
End path'_Theorems.

Hint Rewrite compose_prepend.
Hint Rewrite concatenate_p_noedges concatenate_noedges_p.
Hint Resolve concatenate_p_noedges concatenate_noedges_p.

Record Schema := {
  Vertex :> Type;
  Edge : Vertex -> Vertex -> Type;

  PathsEquivalent : forall s d, relation (path' Edge s d);
  PathsEquivalent_Equivalence : forall s d, equivalence _ (@PathsEquivalent s d);

  PreCompose : forall s d (E : Edge s d) d' (p1 p2 : path' _ d d'),
    PathsEquivalent p1 p2 -> PathsEquivalent (prepend p1 E) (prepend p2 E);
  PostCompose : forall s d (p1 p2 : path' _ s d) d' (E : Edge d d'),
    PathsEquivalent p1 p2 -> PathsEquivalent (AddEdge p1 E) (AddEdge p2 E)
}.

Hint Resolve PreCompose PostCompose.

Theorem PreCompose' : forall S s d (E : S.(Edge) s d) d' (p1 p2 : path' _ d d'),
  PathsEquivalent _ p1 p2 -> PathsEquivalent _ (prepend p1 E) (prepend p2 E).
  intros; auto.
Qed.

Theorem PostCompose' : forall S s d (p1 p2 : path' _ s d) d' (E : S.(Edge) d d'),
  PathsEquivalent _ p1 p2
  -> PathsEquivalent _ (AddEdge p1 E) (AddEdge p2 E).
  intros; auto.
Qed.

Hint Resolve PreCompose' PostCompose'.

Add Parametric Relation S s d : _ (@PathsEquivalent S s d)
  reflexivity proved by (equiv_refl _ _ (@PathsEquivalent_Equivalence _ _ _))
  symmetry proved by (equiv_sym _ _ (@PathsEquivalent_Equivalence _ _ _))
  transitivity proved by (equiv_trans _ _ (@PathsEquivalent_Equivalence _ _ _))
    as paths_eq.

Hint Resolve paths_eq_Reflexive paths_eq_Symmetric.

(* It's not true that [(p1 = p2 -> p3 = p4) -> (PathsEquivalent p1 p2 -> PathsEquivalent p3 p4)]
   Consider a case where p1 = NoEdges and p2 is a path containing an edge and its inverse,
   and p3 and p4 are not equivalent paths.

   So, let's do the relevant theorems again... *)
Section path'_Equivalence_Theorems.
  Variable S : Schema.

  Lemma addedge_equivalent : forall s d d' (p p' : path' _ s d), PathsEquivalent S p p'
    -> forall e : Edge _ d d', PathsEquivalent S (AddEdge p e) (AddEdge p' e).
    t.
  Qed.

  Lemma prepend_equivalent : forall s' s d (p p' : path' _ s d), PathsEquivalent S p p'
    -> forall e : Edge _ s' s, PathsEquivalent S (prepend p e) (prepend p' e).
    t.
  Qed.

  Hint Rewrite concatenate_noedges_p concatenate_addedge.
  Hint Rewrite <- concatenate_prepend_equivalent.
  Hint Resolve prepend_equivalent addedge_equivalent.

  Lemma pre_concatenate_equivalent : forall s' s d (p1 : path' _ s' s) (p p' : path' _ s d),
    PathsEquivalent S p p' -> PathsEquivalent S (concatenate p1 p) (concatenate p1 p').
    induction p1; t.
  Qed.

  Lemma post_concatenate_equivalent : forall s d d' (p p' : path' _ s d) (p2 : path' _ d d'),
    PathsEquivalent S p p' -> PathsEquivalent S (concatenate p p2) (concatenate p' p2).
    induction p2; t.
  Qed.

  Hint Resolve pre_concatenate_equivalent post_concatenate_equivalent.

  Add Parametric Morphism s d d' p:
    (@concatenate _ S.(Edge) s d d' p)
    with signature (@PathsEquivalent S _ _) ==> (@PathsEquivalent S _ _) as concatenate_pre_mor.
    t.
  Qed.

  Add Parametric Morphism s d d' p:
    (fun p' => (@concatenate _ S.(Edge) s d d' p' p))
    with signature (@PathsEquivalent S _ _) ==> (@PathsEquivalent S _ _) as concatenate_post_mor.
    t.
  Qed.

  Lemma concatenate_equivalent : forall s d d' (p1 p1' : path' _ s d) (p2 p2' : path' _ d d'),
    PathsEquivalent S p1 p1' -> PathsEquivalent S p2 p2' -> PathsEquivalent S (concatenate p1 p2) (concatenate p1' p2').
    t; etransitivity; eauto.
  Qed.
End path'_Equivalence_Theorems.

Hint Resolve concatenate_equivalent.

Add Parametric Morphism S s d d' :
  (@concatenate _ S.(Edge) s d d')
  with signature (@PathsEquivalent S _ _) ==> (@PathsEquivalent S _ _) ==> (@PathsEquivalent S _ _) as concatenate_mor.
  t.
Qed.

Add Parametric Morphism S s d d' :
  (@AddEdge S _ s d d')
  with signature (@PathsEquivalent S _ _) ==> (@eq _) ==> (@PathsEquivalent S _ _) as AddEdge_mor.
  t.
Qed.

Add Parametric Morphism S s d d' :
  (fun p => @concatenate' S _ s d p d')
  with signature (@PathsEquivalent S _ _) ==> (@PathsEquivalent S _ _) ==> (@PathsEquivalent S _ _) as concatenate'_mor.
  intros; repeat rewrite <- concatenate_prepend_equivalent; t.
Qed.

Add Parametric Morphism S s' s d :
  (fun p => @prepend S _ s d p s')
  with signature (@PathsEquivalent S _ _) ==> (@eq _) ==> (@PathsEquivalent S _ _) as prepend_mor.
  t.
Qed.

Definition path S := path' S.(Edge).

Section Schema.
  Variable C : Schema.

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
  Definition SEpimorphism x y (p : path C x y) : Prop :=
    forall z (p1 p2 : path C y z), PathsEquivalent _ (concatenate p p1) (concatenate p p2) ->
      PathsEquivalent _ p1 p2.
  Definition SMonomorphism x y (p : path C x y) : Prop :=
    forall z (p1 p2 : path C z x), PathsEquivalent _ (concatenate p1 p) (concatenate p2 p) ->
      PathsEquivalent _ p1 p2.

  (* [m'] is the inverse of [m] if both compositions are
     equivalent to the relevant identity morphisms. *)
  Definition SInverseOf s d (p : path C s d) (p' : path C d s) : Prop :=
    PathsEquivalent _ (concatenate p p') NoEdges /\
    PathsEquivalent _ (concatenate p' p) NoEdges.

  Lemma SInverseOf_sym s d m m' : @SInverseOf s d m m' -> @SInverseOf d s m' m.
    firstorder.
  Qed.

  (* A morphism is an isomorphism if it has an inverse *)
  Definition SchemaIsomorphism' s d (p : path C s d) : Prop :=
    exists p', SInverseOf p p'.

  Definition SchemaIsomorphism s d (p : path C s d) := { p' | SInverseOf p p' }.

  Hint Unfold SInverseOf SchemaIsomorphism' SchemaIsomorphism.

  Lemma SInverseOf1 : forall (s d : C) (p : _ s d) p', SInverseOf p p'
    -> PathsEquivalent _ (concatenate p p') NoEdges.
    firstorder.
  Qed.

  Lemma SInverseOf2 : forall (s d : C) (p : _ s d) p', SInverseOf p p'
    -> PathsEquivalent _ (concatenate p p') NoEdges.
    firstorder.
  Qed.

  Lemma SchemaIsomorphism2Isomorphism' s d (p : path C s d) : SchemaIsomorphism p -> SchemaIsomorphism' p.
    firstorder.
  Qed.

  Hint Rewrite <- SInverseOf1 SInverseOf2 using assumption.

  (* XXX TODO: Automate this better. *)
  Lemma s_iso_is_epi s d (p : path C s d) : SchemaIsomorphism p -> SEpimorphism p.
    destruct 1 as [ x [ i0 i1 ] ]; intros z p1 p2 e.
    transitivity (concatenate (concatenate x p) p1). t_con @PathsEquivalent.
    transitivity (concatenate (concatenate x p) p2); repeat rewrite concatenate_associative; t_con @PathsEquivalent;
      repeat rewrite <- concatenate_associative; t_con @PathsEquivalent.
  Qed.

  Lemma SInverseOf1' : forall x y z (p : path C x y) (p' : path C y x) (p'' : path C z _),
    SInverseOf p p'
    -> PathsEquivalent _ (concatenate (concatenate p'' p) p') p''.
    unfold SInverseOf; intros; destruct_hypotheses; repeat rewrite concatenate_associative; t_con @PathsEquivalent.
  Qed.

  Hint Rewrite SInverseOf1' using assumption.

  (* XXX TODO: Automate this better. *)
  Lemma s_iso_is_mono s d (p : path C s d) : SchemaIsomorphism p -> SMonomorphism p.
    destruct 1 as [ x [ i0 i1 ] ]; intros z p1 p2 e.
    transitivity (concatenate p1 (concatenate p x)). t_con @PathsEquivalent.
    transitivity (concatenate p2 (concatenate p x)); solve [ repeat rewrite <- concatenate_associative; t_con @PathsEquivalent ] || t_con @PathsEquivalent.
  Qed.

  Theorem SchemaIdentityInverse (o : C) : SInverseOf (@NoEdges _ _ o) (@NoEdges _ _ o).
    hnf; t.
  Qed.

  Hint Resolve SchemaIdentityInverse.

  Theorem SchemaIdentityIsomorphism (o : C) : SchemaIsomorphism (@NoEdges _ _ o).
    eauto.
  Qed.
End Schema.

Hint Resolve SchemaIsomorphism2Isomorphism'.

Ltac concatenate4associativity' a b c d := transitivity (concatenate a (concatenate (concatenate b c) d));
  try solve [ repeat rewrite concatenate_associative; reflexivity ].
Ltac concatenate4associativity :=
  match goal with
    | [ |- ?Rel (concatenate (concatenate ?a ?b) (concatenate ?c ?d)) _ ] => concatenate4associativity' a b c d
    | [ |- ?Rel _ (concatenate (concatenate ?a ?b) (concatenate ?c ?d)) ] => concatenate4associativity' a b c d
  end.

Section SchemaIsomorphismEquivalenceRelation.
  Variable C : Schema.
  Variable s d d' : C.

  Theorem SchemaIsomorphismComposition (p : path C s d) (p' : path C d d') :
    SchemaIsomorphism p -> SchemaIsomorphism p' -> SchemaIsomorphism (concatenate p p').
    repeat destruct 1; unfold SInverseOf in *; destruct_hypotheses.
      match goal with
        | [ m : path _ _ _, m' : path _ _ _ |- _ ] => exists (concatenate m m')
      end;
      split;
        concatenate4associativity; t_con @PathsEquivalent.
  Qed.
End SchemaIsomorphismEquivalenceRelation.

Definition path_unique (A : Schema) s d (x : path A s d) := forall x' : path A s d, PathsEquivalent _ x' x.

Section GeneralizedPathEquivalence.
  Variable S : Schema.

  Inductive GeneralizedPathsEquivalent s d (p : path S s d) : forall s' d' (p' : path S s' d'), Prop :=
    | GPathsEquivalent (p' : path S s d) : PathsEquivalent _ p p' -> GeneralizedPathsEquivalent p p'.

  Lemma GeneralizedPathsEquivalent_PathsEquivalent s d (p p' : path S s d) :
    GeneralizedPathsEquivalent p p' -> PathsEquivalent _ p p'.
    intro H; inversion H.
    repeat match goal with
             | [ H : _ |- _ ] => apply inj_pair2 in H
           end.
    repeat subst.
    assumption.
  Qed.

  Lemma GeneralizedPathsEquivalent_eq s d (p : path S s d) s' d' (p' : path S s' d') :
    GeneralizedPathsEquivalent p p' -> s = s' /\ d = d'.
    intro H; inversion H.
    repeat subst.
    split; trivial.
  Qed.
End GeneralizedPathEquivalence.

Ltac simpl_GeneralizedPathsEquivalent := intros;
  repeat match goal with
           | [ H : GeneralizedPathsEquivalent _ _ |- _ ]
             => destruct (GeneralizedPathsEquivalent_eq H); repeat subst;
               apply GeneralizedPathsEquivalent_PathsEquivalent in H
           | [ |- GeneralizedPathsEquivalent _ _ ] => apply GPathsEquivalent
         end.

Section GeneralizedPathsEquivalenceRelation.
  Variable S : Schema.

  Lemma GeneralizedPathsEquivalent_refl s d (p : path S s d) : GeneralizedPathsEquivalent p p.
    simpl_GeneralizedPathsEquivalent; reflexivity.
  Qed.

  Lemma GeneralizedPathsEquivalent_sym s d (p : path S s d) s' d' (p' : path S s' d') :
    GeneralizedPathsEquivalent p p' -> GeneralizedPathsEquivalent p' p.
    simpl_GeneralizedPathsEquivalent; symmetry; assumption.
  Qed.

  Lemma GeneralizedPathsEquivalent_trans s d (p : path S s d) s' d' (p' : path S s' d') s'' d'' (p'' : path S s'' d'') :
    GeneralizedPathsEquivalent p p' -> GeneralizedPathsEquivalent p' p'' -> GeneralizedPathsEquivalent p p''.
    simpl_GeneralizedPathsEquivalent; transitivity p'; eauto.
  Qed.
End GeneralizedPathsEquivalenceRelation.

(*
Section SchemaObjects1.
  Variable C : Schema.

  Definition UniqueUpToUniqueIsomorphism' (P : C.(Object) -> Prop) : Prop :=
    forall o, P o -> forall o', P o' -> exists m : C.(Morphism) o o', SchemaIsomorphism' m /\ is_unique m.

  Definition UniqueUpToUniqueIsomorphism (P : C.(Object) -> Type) :=
    forall o, P o -> forall o', P o' -> { m : C.(Morphism) o o' | SchemaIsomorphism' m & is_unique m }.

  (* A terminal object is an object with a unique morphism from every other object. *)
  Definition TerminalObject' (o : C) : Prop :=
    forall o', exists! m : C.(Morphism) o' o, True.

  Definition TerminalObject (o : C) :=
    forall o', { m : C.(Morphism) o' o | is_unique m }.

  (* An initial object is an object with a unique morphism from every other object. *)
  Definition InitialObject' (o : C) : Prop :=
    forall o', exists! m : C.(Morphism) o o', True.

  Definition InitialObject (o : C) :=
    forall o', { m : C.(Morphism) o o' | is_unique m }.
End SchemaObjects1.

Implicit Arguments UniqueUpToUniqueIsomorphism' [C].
Implicit Arguments UniqueUpToUniqueIsomorphism [C].
Implicit Arguments InitialObject' [C].
Implicit Arguments InitialObject [C].
Implicit Arguments TerminalObject' [C].
Implicit Arguments TerminalObject [C].

Section SchemaObjects2.
  Variable C : Schema.

  Hint Unfold TerminalObject InitialObject InverseOf.

  Ltac unique := intros o Ho o' Ho'; destruct (Ho o); destruct (Ho o'); destruct (Ho' o); destruct (Ho' o');
    unfold is_unique, unique, uniqueness in *;
      repeat (destruct 1);
      repeat match goal with
               | [ x : _ |- _ ] => exists x
             end; eauto; try split; try solve [ etransitivity; eauto ].

  (* The terminal object is unique up to unique isomorphism. *)
  Theorem TerminalObjectUnique : UniqueUpToUniqueIsomorphism (@TerminalObject C).
    unique.
  Qed.

  (* The initial object is unique up to unique isomorphism. *)
  Theorem InitialObjectUnique : UniqueUpToUniqueIsomorphism (@InitialObject C).
    unique.
  Qed.
End SchemaObjects2.
*)
