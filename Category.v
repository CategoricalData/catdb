Require Import Bool Omega.
Require Import Common.

Set Implicit Arguments.

Record Category := {
  Object :> Type;
  Morphism : Object -> Object -> Type;

  Identity : forall o, Morphism o o;
  Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d';

  Associativity : forall o1 o2 o3 o4 (m1 : Morphism o1 o2) (m2 : Morphism o2 o3) (m3 : Morphism o3 o4),
    Compose (Compose m3 m2) m1 = Compose m3 (Compose m2 m1);
  LeftIdentity : forall a b (f : Morphism a b), (Compose (Identity b) f) = f;
  RightIdentity : forall a b (f : Morphism a b), (Compose f (Identity a)) = f
}.

Implicit Arguments Compose [c s d d'].
Implicit Arguments Identity [c].

Hint Rewrite LeftIdentity RightIdentity.

Ltac try_associativity tac := try_rewrite Associativity tac.

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


(** * Version of [Associativity] that avoids going off into the weeds in the presence of unification variables *)

Definition NoEvar T (_ : T) := True.

Lemma AssociativityNoEvar : forall (c : Category) (o1 o2 o3 o4 : c) (m1 : Morphism c o1 o2)
  (m2 : Morphism c o2 o3) (m3 : Morphism c o3 o4),
  NoEvar (m1, m2, m3)
  -> Compose (Compose m3 m2) m1 = Compose m3 (Compose m2 m1).
  intros; apply Associativity.
Qed.

Ltac noEvar := match goal with
                 | [ |- NoEvar ?X ] => (has_evar X; fail 1) || constructor
               end.

Hint Rewrite AssociativityNoEvar using noEvar.


(** * Back to the main content.... *)

Section Category.
  Variable C : Category.

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
    forall z (m1 m2 : C.(Morphism) y z), Compose m1 m = Compose m2 m ->
      m1 = m2.
  Definition Monomorphism x y (m : C.(Morphism) x y) : Prop :=
    forall z (m1 m2 : C.(Morphism) z x), Compose m m1 = Compose m m2 ->
      m1 = m2.

  (* [m'] is the inverse of [m] if both compositions are
     equivalent to the relevant identity morphisms. *)
  Definition InverseOf s d (m : C.(Morphism) s d) (m' : C.(Morphism) d s) : Prop :=
    Compose m' m = Identity s /\
    Compose m m' = Identity d.

  Implicit Arguments InverseOf [s d].

  Lemma InverseOf_sym s d m m' : @InverseOf s d m m' -> @InverseOf d s m' m.
    firstorder.
  Qed.

  (* A morphism is an isomorphism if it has an inverse *)
  Definition CategoryIsomorphism' s d (m : C.(Morphism) s d) : Prop :=
    exists m', InverseOf m m'.

  (* As per David's comment, everything is better when we supply a witness rather
     than an assertion.  (In particular the [exists m' -> m'] transformation is only
     permissible for [m' : Prop].  Trying it on other with
       refine match H with
                | ex_intro x x0 => _ x x0
              end
     gives
       Error:
       Incorrect elimination of "H" in the inductive type "ex":
       the return type has sort "Type" while it should be "Prop".
       Elimination of an inductive object of sort Prop
       is not allowed on a predicate in sort Type
       because proofs can be eliminated only to build proofs.
     ) *)
  Definition CategoryIsomorphism s d (m : C.(Morphism) s d) := { m' | InverseOf m m' }.

  Hint Unfold InverseOf CategoryIsomorphism' CategoryIsomorphism.

  Lemma InverseOf1 : forall (s d : C) (m : _ s d) m', InverseOf m m'
    -> Compose m' m = Identity s.
    firstorder.
  Qed.

  Lemma InverseOf2 : forall (s d : C) (m : _ s d) m', InverseOf m m'
    -> Compose m m' = Identity d.
    firstorder.
  Qed.

  Lemma CategoryIsomorphism2Isomorphism' s d m : CategoryIsomorphism s d m -> CategoryIsomorphism' _ _ m.
    firstorder.
  Qed.

  Hint Rewrite <- InverseOf1 InverseOf2 using assumption.

  (* XXX TODO: Automate this better. *)
  Lemma iso_is_epi s d m : CategoryIsomorphism s d m -> Epimorphism s d m.
    destruct 1 as [ x [ i0 i1 ] ]; intros z m1 m2 e.
    transitivity (Compose m1 (Compose m x)). t.
    transitivity (Compose m2 (Compose m x)); repeat (rewrite <- Associativity); t.
  Qed.

  Lemma InverseOf1' : forall x y z (m : C.(Morphism) x y) (m' : C.(Morphism) y x) (m'' : C.(Morphism) z _),
    InverseOf m m'
    -> Compose m' (Compose m m'') = m''.
    unfold InverseOf; intros; destruct_hypotheses; repeat rewrite <- Associativity; t.
  Qed.

  Hint Rewrite InverseOf1' using assumption.

  (* XXX TODO: Automate this better. *)
  Lemma iso_is_mono s d m : CategoryIsomorphism s d m -> Monomorphism s d m.
    destruct 1 as [ x [ i0 i1 ] ]; intros z m1 m2 e.
    transitivity (Compose (Compose x m) m1). t_with t'.
    transitivity (Compose (Compose x m) m2); solve [ repeat (rewrite Associativity); t_with t' ] || t_with t'.
  Qed.

  Theorem CategoryIdentityInverse (o : C.(Object)) : InverseOf (Identity o) (Identity o).
    hnf; t.
  Qed.

  Hint Resolve CategoryIdentityInverse.

  Theorem CategoryIdentityIsomorphism (o : C.(Object)) : CategoryIsomorphism _ _ (Identity o).
    eauto.
  Qed.
End Category.

Implicit Arguments CategoryIsomorphism' [C s d].
Implicit Arguments CategoryIsomorphism [C s d].
Implicit Arguments Epimorphism [C x y].
Implicit Arguments Monomorphism [C x y].
Implicit Arguments InverseOf [C s d].

Hint Resolve CategoryIsomorphism2Isomorphism'.

Ltac compose4associativity :=
  match goal with
    | [ |- Compose (Compose ?a ?b) (Compose ?c ?d) = _ ] => transitivity (Compose a (Compose (Compose b c) d));
      try solve [ repeat (rewrite <- Associativity); reflexivity ]
  end.

Section CategoryIsomorphismEquivalenceRelation.
  Variable C : Category.
  Variable s d d' : C.

  Theorem CategoryIsomorphismComposition (m : C.(Morphism) s d) (m' : C.(Morphism) d d') :
    CategoryIsomorphism m -> CategoryIsomorphism m' -> CategoryIsomorphism (Compose m' m).
    repeat (destruct 1);
      match goal with
        | [ m : Morphism _ _ _, m' : Morphism _ _ _ |- _ ] => exists (Compose m m')
      end;
      firstorder;
        compose4associativity;
        repeat match goal with
                 | [ H : _ |- _ ] => rewrite H
               end; t.
  Qed.
End CategoryIsomorphismEquivalenceRelation.

Definition is_unique (A : Type) (x : A) := forall x' : A, x' = x.
Implicit Arguments is_unique [A].

Section CategoryObjects1.
  Variable C : Category.

  Definition UniqueUpToUniqueIsomorphism' (P : C.(Object) -> Prop) : Prop :=
    forall o, P o -> forall o', P o' -> exists m : C.(Morphism) o o', CategoryIsomorphism' m /\ is_unique m.

  Definition UniqueUpToUniqueIsomorphism (P : C.(Object) -> Type) :=
    forall o, P o -> forall o', P o' -> { m : C.(Morphism) o o' | CategoryIsomorphism' m & is_unique m }.

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
End CategoryObjects1.

Implicit Arguments UniqueUpToUniqueIsomorphism' [C].
Implicit Arguments UniqueUpToUniqueIsomorphism [C].
Implicit Arguments InitialObject' [C].
Implicit Arguments InitialObject [C].
Implicit Arguments TerminalObject' [C].
Implicit Arguments TerminalObject [C].

Section CategoryObjects2.
  Variable C : Category.

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
End CategoryObjects2.
