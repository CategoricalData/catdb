Require Import Bool Omega Setoid Datatypes.
Require Import Common EquivalenceRelation.

Set Implicit Arguments.

Record Category := {
  Object :> Type;
  Morphism : Object -> Object -> Type;

  MorphismsEquivalent' : forall o1 o2, Morphism o1 o2 -> Morphism o1 o2 -> Prop;
  MorphismsEquivalent : EquivalenceRelation MorphismsEquivalent';

  Identity : forall o, Morphism o o;
  Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d';

  PreComposeMorphisms : forall s d d' (m : Morphism d d') (m1 m2 : Morphism s d),
    MorphismsEquivalent' m1 m2 -> MorphismsEquivalent' (Compose m m1) (Compose m m2);
  PostComposeMorphisms : forall s d d' (m1 m2 : Morphism d d') (m : Morphism s d),
    MorphismsEquivalent' m1 m2 -> MorphismsEquivalent' (Compose m1 m) (Compose m2 m);

  Associativity : forall o1 o2 o3 o4 (m1 : Morphism o1 o2) (m2 : Morphism o2 o3) (m3 : Morphism o3 o4),
    MorphismsEquivalent' (Compose (Compose m3 m2) m1) (Compose m3 (Compose m2 m1));
  LeftIdentity : forall a b (f : Morphism a b), MorphismsEquivalent' (Compose (Identity b) f) f;
  RightIdentity : forall a b (f : Morphism a b), MorphismsEquivalent' (Compose f (Identity a)) f
}.

Lemma PreComposeMorphisms' : forall C s d d' (m : C.(Morphism) d d') (m1 m2 : C.(Morphism) s d),
  MorphismsEquivalent _ _ _ m1 m2 -> MorphismsEquivalent _ _ _ (Compose _ _ _ _ m m1) (Compose _ _ _ _ m m2).
  intros; apply PreComposeMorphisms; auto.
Qed.

Lemma PostComposeMorphisms' : forall C s d d' (m1 m2 : C.(Morphism) d d') (m : C.(Morphism) s d),
  MorphismsEquivalent _ _ _ m1 m2 -> MorphismsEquivalent _ _ _ (Compose _ _ _ _ m1 m) (Compose _ _ _ _ m2 m).
  intros; apply PostComposeMorphisms; auto.
Qed.

Lemma Associativity' : forall C o1 o2 o3 o4 (m1 : C.(Morphism) o1 o2) (m2 : C.(Morphism) o2 o3) (m3 : C.(Morphism) o3 o4),
  MorphismsEquivalent _ _ _ (Compose _ _ _ _ (Compose _ _ _ _ m3 m2) m1) (Compose _ _ _ _ m3 (Compose _ _ _ _ m2 m1)).
  intros; apply Associativity; auto.
Qed.

Lemma LeftIdentity' : forall C a b (f : C.(Morphism) a b), MorphismsEquivalent _ _ _ (Compose _ _ _ _ (Identity _ b) f) f.
  intros; apply LeftIdentity; auto.
Qed.

Lemma RightIdentity' : forall S a b (f : S.(Morphism) a b), MorphismsEquivalent _ _ _ (Compose _ _ _ _ f (Identity _ a)) f.
  intros; apply RightIdentity; auto.
Qed.

Implicit Arguments Compose [c s d d'].
Implicit Arguments Identity [c].
Implicit Arguments MorphismsEquivalent' [c o1 o2].

(* XXX TODO: I should look at what hints exist for @eq, and make relavent hints for MorphismsEquivalent *)
Hint Rewrite LeftIdentity' RightIdentity'.
Hint Resolve PreComposeMorphisms' PostComposeMorphisms'.

Hint Extern 1 (@RelationsEquivalent _ _ _ _ _ _ (Compose (Compose ?M _) _) (Compose ?M _)) => repeat (rewrite Associativity); apply PreComposeMorphisms'.
Hint Extern 1 (@RelationsEquivalent _ _ _ _ _ _ (Compose (Compose ?M _) _) (Compose (Compose ?M _) _)) => repeat (rewrite Associativity); apply PreComposeMorphisms'.
Hint Extern 1 (@RelationsEquivalent _ _ _ _ _ _ (Compose _ (Compose _ ?M)) (Compose _ (Compose _ ?M))) => repeat (rewrite <- Associativity); apply PostComposeMorphisms'.

Add Parametric Relation C s d : _ (MorphismsEquivalent C s d)
  reflexivity proved by (Reflexive _ _ _)
  symmetry proved by (Symmetric _ _ _)
  transitivity proved by (Transitive _ _ _)
    as morphisms_eq.

Lemma morphisms_equivalence_equivalent C : relations_equivalence_equivalent C.(MorphismsEquivalent).
  unfold relations_equivalence_equivalent; trivial.
Qed.

Hint Rewrite morphisms_equivalence_equivalent.

Section Morphism_Equivalence_Theorems.
  Variable C : Category.

  Lemma compose_morphisms_equivalent o1 o2 o3 : forall (m1 m1' : Morphism C o1 o2) (m2 m2' : Morphism C o2 o3),
    MorphismsEquivalent _ _ _ m1 m1' -> MorphismsEquivalent _ _ _ m2 m2' -> MorphismsEquivalent _ _ _ (Compose m2 m1) (Compose m2' m1').
    intros; transitivity (Compose m2' m1); t.
  Qed.
End Morphism_Equivalence_Theorems.

Add Parametric Morphism C s d d' :
  (@Compose C s d d')
  with signature (MorphismsEquivalent C _ _) ==> (MorphismsEquivalent C _ _) ==> (MorphismsEquivalent C _ _) as morphism_eq_mor.
  t; apply compose_morphisms_equivalent; t.
Qed.

(* XXX Can we make this a Hint?  If so, I think we want to specify that it can't be nested
   because otherwise it make the identity_unique proof run forever *)
Ltac identity_transitvity :=
  match goal with
    | [ |- (RelationsEquivalent _ _ _ _ (Compose ?M _) ?M) ] => transitivity (Compose M (Identity _));
      apply PreComposeMorphisms' || apply RightIdentity; trivial
    | [ |- (RelationsEquivalent _ _ _ _ (Compose _ ?M) ?M) ] => transitivity (Compose (Identity _) M);
      apply PostComposeMorphisms' || apply LeftIdentity; trivial
    | [ |- (RelationsEquivalent _ _ _ _ ?M (Compose ?M _)) ] => symmetry; identity_transitvity
    | [ |- (RelationsEquivalent _ _ _ _ ?M (Compose _ ?M)) ] => symmetry; identity_transitvity
  end.

(* These [Ltac]s all seem somewhat slow.  I wonder if there's a way to speed them up. *)
(* I kludge with [?MorphismsEquivalent] because I can't actually match on it, because
   the patten is complicated and involves lets.  *)
Ltac pre_compose_to_identity :=
  match goal with
    | [
      H0 : (?MorphismsEquivalent _ _ _ (Identity _) (Compose ?M ?Mi)),
      H1 : (?MorphismsEquivalent _ _ _ (Compose ?Mi ?m1) (Compose ?Mi ?m2))
      |- (?MorphismsEquivalent _ _ _ ?m1 ?m2)
    ] => transitivity (Compose (Compose M Mi) m1);
    ((rewrite <- H0; rewrite LeftIdentity; reflexivity) ||
      (transitivity (Compose (Compose M Mi) m2)); (
        (repeat (rewrite Associativity); apply PreComposeMorphisms; apply H1) ||
          (rewrite <- H0; rewrite LeftIdentity; reflexivity)))
  end.

Ltac post_compose_to_identity :=
  match goal with
    | [
      H0 : (?MorphismsEquivalent _ _ _ (Identity _) (Compose ?M ?Mi)),
      H1 : (?MorphismsEquivalent _ _ _ (Compose ?m1 ?M) (Compose ?m2 ?M))
      |- (?MorphismsEquivalent _ _ _ ?m1 ?m2)
    ] => transitivity (Compose m1 (Compose M Mi));
    ((rewrite <- H0; rewrite RightIdentity; reflexivity) ||
      (transitivity (Compose m2 (Compose M Mi))); (
        (repeat (rewrite <- Associativity); apply PostComposeMorphisms; apply H1) ||
          (rewrite <- H0; rewrite RightIdentity; reflexivity)))
  end.

Ltac rewrite_to_identity' :=
  match goal with
    | [
      H : (?MorphismsEquivalent _ _ _ (Identity _) (Compose ?M ?Mi))
      |- (?MorphismsEquivalent _ _ _ ?m1 ?m2)
    ] => rewrite <- H; (rewrite LeftIdentity || rewrite RightIdentity)
  end.
Ltac rewrite_to_identity :=
  repeat (rewrite Associativity); repeat rewrite_to_identity';
    repeat (rewrite <- Associativity); repeat rewrite_to_identity'.

Section Category.
  Variable C : Category.

  Hint Extern 1 (RelationsEquivalent _ _ _ _ ?M1 ?M2) => identity_transitvity.

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
  Definition Epimorphism x y (m : C.(Morphism) x y) : Prop :=
    forall z (m1 m2 : C.(Morphism) y z), MorphismsEquivalent _ _ _ (Compose m1 m) (Compose m2 m) ->
      MorphismsEquivalent _ _ _ m1 m2.
  Definition Monomorphism x y (m : C.(Morphism) x y) : Prop :=
    forall z (m1 m2 : C.(Morphism) z x), MorphismsEquivalent _ _ _ (Compose m m1) (Compose m m2) ->
      MorphismsEquivalent _ _ _ m1 m2.

  (* [m'] is the inverse of [m] if both compositions are
     equivalent to the relevant identity morphisms. *)
  Definition InverseOf s d (m : C.(Morphism) s d) (m' : C.(Morphism) d s) : Prop :=
    MorphismsEquivalent _ _ _ (Identity s) (Compose m' m) /\
    MorphismsEquivalent _ _ _ (Identity d) (Compose m m').

  Implicit Arguments InverseOf [s d].

  (* A morphism is an isomorphism if it has an inverse *)
  Definition CategoryIsomorphism' s d (m : C.(Morphism) s d) : Prop :=
    exists m', InverseOf m m'.

  (* As per David's comment, everything is better when we supply a witness rather
     than an assertion.  (In particular the [exists m' -> m'] transformation requires
     the axiom of choice.) *)
  Definition CategoryIsomorphism s d (m : C.(Morphism) s d) := { m' | InverseOf m m' }.

  Hint Unfold InverseOf CategoryIsomorphism' CategoryIsomorphism.

  Lemma CategoryIsomorphism2Isomorphism' s d m : CategoryIsomorphism s d m -> CategoryIsomorphism' _ _ m.
    autounfold with *; firstorder.
  Qed.

  Lemma iso_is_epi s d m : CategoryIsomorphism s d m -> Epimorphism s d m.
    unfold CategoryIsomorphism; unfold Epimorphism; unfold InverseOf;
    firstorder;
    post_compose_to_identity.
  Qed.

  Lemma iso_is_mono s d m : CategoryIsomorphism s d m -> Monomorphism s d m.
    unfold CategoryIsomorphism; unfold Monomorphism; unfold InverseOf;
    firstorder;
    pre_compose_to_identity.
  Qed.

  Theorem CategoryIdentityInverse (o : C.(Object)) : InverseOf (Identity o) (Identity o).
    unfold InverseOf; t.
  Qed.

  Theorem CategoryIdentityIsomorphism (o : C.(Object)) : CategoryIsomorphism _ _ (Identity o).
    exists (Identity o); intuition; apply CategoryIdentityInverse.
  Qed.
End Category.

Implicit Arguments CategoryIsomorphism' [C s d].
Implicit Arguments CategoryIsomorphism [C s d].
Implicit Arguments InverseOf [C s d].

Hint Resolve CategoryIsomorphism2Isomorphism'.

Section CategoryIsomorphismEquivalenceRelation.
  Variable C : Category.
  Variable s d d' : C.

  Ltac remove_middle_identity :=
    match goal with
      | [
        H : (?MorphismsEquivalent _ _ _ _ (Identity _) (Compose ?b ?c))
        |- ?MorphismsEquivalent _ _ _ _ _ (Compose (Compose ?a ?b) (Compose ?c ?d))
      ] => transitivity (Compose (Compose a (Compose b c)) d); (
          (repeat (rewrite Associativity); reflexivity) ||
            rewrite <- H; rewrite RightIdentity; try assumption
      )
    end.

  Theorem CategoryIsomorphismComposition (m : C.(Morphism) s d) (m' : C.(Morphism) d d') :
    CategoryIsomorphism m -> CategoryIsomorphism m' -> CategoryIsomorphism (Compose m' m).
    unfold CategoryIsomorphism. firstorder.
    match goal with
      | [
        mi : C.(Morphism) d s,
        m'i : C.(Morphism) d' d
        |- _
        ] => exists (Compose mi m'i)
    end.
    firstorder; remove_middle_identity.
  Qed.
End CategoryIsomorphismEquivalenceRelation.

(* XXX TODO: Figure out if I can replace the nested [cut]s with [lapply] *)
Ltac post_compose_epi e := match goal with
                             | [ |- (RelationsEquivalent _ _ _ _ ?M1 ?M2) ] =>
                               cut (MorphismsEquivalent _ _ _ (Compose M1 e) (Compose M2 e));
                                 try match goal with
                                       | [ |- _ -> _ ] => cut (Epimorphism _ _ _ e); intuition
                                     end
                           end.
Ltac pre_compose_mono m := match goal with
                             | [ |- (RelationsEquivalent _ _ _ _ ?M1 ?M2) ] =>
                               cut (MorphismsEquivalent _ _ _ (Compose m M1) (Compose m M2));
                                 try match goal with
                                       | [ |- _ -> _ ] => cut (Monomorphism _ _ _ m); intuition
                                     end
                           end.

Section OppositeCategory.
  Variable C : Category.

  Definition OppositeCategory : Category.
    refine {| Object := C.(Object);
      Morphism := (fun s d => C.(Morphism) d s);
      MorphismsEquivalent' := (fun _ _ m m' => @MorphismsEquivalent' C _ _ m m');
      Identity := @Identity C;
      Compose := (fun s d d' m1 m2 => @Compose C d' d s m2 m1)
      |}; abstract (t; t;
        simpl_transitivity || (rewrite Associativity; t)).
  Defined.

End OppositeCategory.

Section CategoryObjects1.
  Variable C : Category.

  Definition MorphismUnique s d (m : C.(Morphism) s d) : Prop :=
    forall m', MorphismsEquivalent _ _ _ m m'.

  Implicit Arguments MorphismUnique [s d].

  (* A terminal object is an object with a unique morphism from every other object *)
  Definition TerminalObject' (o : C) : Prop :=
    forall o', exists m : C.(Morphism) o' o, MorphismUnique m.

  Definition TerminalObject (o : C) :=
    forall o', { m : C.(Morphism) o' o | MorphismUnique m }.

  (* An initial object is an object with a unique morphism from every other object *)
  Definition InitialObject' (o : C) : Prop :=
    forall o', exists m : C.(Morphism) o o', MorphismUnique m.

  Definition InitialObject (o : C) :=
    forall o', { m : C.(Morphism) o o' | MorphismUnique m }.
End CategoryObjects1.

Implicit Arguments MorphismUnique [C s d].
Implicit Arguments InitialObject' [C].
Implicit Arguments InitialObject [C].
Implicit Arguments TerminalObject' [C].
Implicit Arguments TerminalObject [C].

Section CategoryObjects2.
  Variable C : Category.

  Ltac solve_uniqueness :=
    match goal with
      | [ X : forall o, { _ : Morphism ?C o ?o' | MorphismUnique _ } |- ?MorphismsEquivalent _ ?o' ?o' _ _ ] =>
        transitivity (proj1_sig (X o'));
          apply (proj2_sig (X o')) ||
            (symmetry; apply (proj2_sig (X o')))
      | [ X : forall o, { _ : Morphism ?C ?o' o | MorphismUnique _ } |- ?MorphismsEquivalent _ ?o' ?o' _ _ ] =>
        transitivity (proj1_sig (X o'));
          apply (proj2_sig (X o')) ||
            (symmetry; apply (proj2_sig (X o')))
    end.

  Ltac uniqueness_exists_sig :=
    match goal with
      | [ X : forall o', { _ : Morphism ?C o' ?o | _ } |- (@sig (Morphism ?C ?o' ?o) _) ] =>
        exists (proj1_sig (X o')); try apply (proj2_sig (X o'))
      | [ X : forall o', { _ : Morphism ?C o' ?o | _ } |- (@sig2 (Morphism ?C ?o' ?o) _ _) ] =>
        exists (proj1_sig (X o')); try apply (proj2_sig (X o'))
      | [ X : forall o', { _ : Morphism ?C ?o o' | _ } |- (@sig (Morphism ?C ?o ?o') _) ] =>
        exists (proj1_sig (X o')); try apply (proj2_sig (X o'))
      | [ X : forall o', { _ : Morphism ?C ?o o' | _ } |- (@sig2 (Morphism ?C ?o ?o') _ _) ] =>
        exists (proj1_sig (X o')); try apply (proj2_sig (X o'))
      | [ X : forall o', { _ : Morphism ?C o' ?o | _ } |- exists _ : Morphism ?C ?o' ?o, _ ] =>
        exists (proj1_sig (X o'))
      | [ X : forall o', { _ : Morphism ?C ?o o' | _ } |- exists _ : Morphism ?C ?o ?o', _ ] =>
        exists (proj1_sig (X o'))
    end.

  Lemma initial_opposite_terminal (o : C) :
    InitialObject o -> @TerminalObject (OppositeCategory C) o.
    t.
  Qed.

  Lemma terminal_opposite_initial (o : C) :
    TerminalObject o -> @InitialObject (OppositeCategory C) o.
    t.
  Qed.

  (* The terminal object is unique up to unique isomorphism *)
  Theorem TerminalObjectUnique o : TerminalObject o ->
    forall o', TerminalObject o' -> { m : C.(Morphism) o' o | CategoryIsomorphism' m & MorphismUnique m }.
    unfold TerminalObject; intros.
    uniqueness_exists_sig.
    unfold CategoryIsomorphism'.
    uniqueness_exists_sig.
    unfold InverseOf; intuition; solve_uniqueness.
  Qed.

  (* The initial object is unique up to unique isomorphism *)
  Theorem InitialObjectUnique o : InitialObject o ->
    forall o', InitialObject o' -> { m : C.(Morphism) o' o | CategoryIsomorphism' m & MorphismUnique m }.
    unfold InitialObject; intros.
    uniqueness_exists_sig.
    unfold CategoryIsomorphism'.
    uniqueness_exists_sig.
    unfold InverseOf; intuition; solve_uniqueness.
  Qed.

End CategoryObjects.