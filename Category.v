Require Import Bool Omega Setoid.
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

(* XXX TODO: I should look at what hints exist for @eq, and make relevant hints for MorphismsEquivalent *)
Hint Rewrite LeftIdentity' RightIdentity'.
Hint Resolve PreComposeMorphisms' PostComposeMorphisms'.

Hint Extern 1 (@RelationsEquivalent _ _ _ _ _ _ (Compose _ _) (Compose _ _)) =>
  repeat rewrite Associativity; apply PreComposeMorphisms' || apply PreComposeMorphisms' || apply PostComposeMorphisms'.
Hint Extern 1 (@RelationsEquivalent _ _ _ _ _ _ (Compose _ _) (Compose _ _)) =>
  repeat rewrite <- Associativity; apply PostComposeMorphisms'.

Add Parametric Relation C s d : _ (MorphismsEquivalent C s d)
  reflexivity proved by (Reflexive _ _ _)
  symmetry proved by (Symmetric _ _ _)
  transitivity proved by (Transitive _ _ _)
    as morphisms_eq.

Lemma morphisms_equivalence_equivalent : MorphismsEquivalent' = MorphismsEquivalent.
  hnf; trivial.
Qed.

Hint Rewrite morphisms_equivalence_equivalent.
Hint Extern 1 (MorphismsEquivalent' _ _) => reflexivity.
Hint Extern 1 (MorphismsEquivalent _ _) => reflexivity.

Section Morphism_Equivalence_Theorems.
  Variable C : Category.

  Hint Resolve Transitive.

  Lemma compose_morphisms_equivalent o1 o2 o3 : forall (m1 m1' : Morphism C o1 o2) (m2 m2' : Morphism C o2 o3),
    MorphismsEquivalent _ _ _ m1 m1' -> MorphismsEquivalent _ _ _ m2 m2' -> MorphismsEquivalent _ _ _ (Compose m2 m1) (Compose m2' m1').
    eauto.
  Qed.
End Morphism_Equivalence_Theorems.

Hint Resolve compose_morphisms_equivalent.

Add Parametric Morphism C s d d' :
  (@Compose C s d d')
  with signature (MorphismsEquivalent C _ _) ==> (MorphismsEquivalent C _ _) ==> (MorphismsEquivalent C _ _) as morphism_eq_mor.
  t.
Qed.


(** * The saturation prover: up to some bound on number of steps, consider all ways to extend equivalences with pre- or post-composition. *)

(** The main tactic, which tries a single round of making deductions from hypotheses that exist at the start of the round.
    Only variables in the goal are chosen to compose. *)

Ltac saturate := repeat match goal with
                          | [ H : RelationsEquivalent _ _ _ _ ?M ?N |- _ ] =>
                            let tryIt G :=
                              match goal with
                                | [ _ : G |- _ ] => fail 1
                                | [ |- context[G] ] => fail 1
                                | _ => let H' := fresh "H" in assert (H' : G) by eauto; generalize dependent H'
                              end in
                              repeat match goal with
                                       | [ m : Morphism _ _ _ |- _ ] =>
                                         tryIt (MorphismsEquivalent _ _ _ (Compose M m) (Compose N m))
                                       | [ m : Morphism _ _ _ |- _ ] =>
                                         tryIt (MorphismsEquivalent _ _ _ (Compose m M) (Compose m N))
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
    | [ |- RelationsEquivalent _ _ _ _ ?X ?Y ] =>
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
  -> MorphismsEquivalent' (Compose (Compose m3 m2) m1) (Compose m3 (Compose m2 m1)).
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
    -> MorphismsEquivalent _ _ _ (Identity s) (Compose m' m).
    firstorder.
  Qed.

  Lemma InverseOf2 : forall (s d : C) (m : _ s d) m', InverseOf m m'
    -> MorphismsEquivalent _ _ _ (Identity d) (Compose m m').
    firstorder.
  Qed.

  Lemma CategoryIsomorphism2Isomorphism' s d m : CategoryIsomorphism s d m -> CategoryIsomorphism' _ _ m.
    firstorder.
  Qed.

  Hint Rewrite <- InverseOf1 InverseOf2 using assumption.

  Lemma iso_is_epi s d m : CategoryIsomorphism s d m -> Epimorphism s d m.
    destruct 1; hnf; morphisms 1.
  Qed.

  Lemma InverseOf1' : forall x y z (m : C.(Morphism) x y) (m' : C.(Morphism) y x) (m'' : C.(Morphism) z _),
    InverseOf m m'
    -> MorphismsEquivalent _ _ _ (Compose m' (Compose m m'')) m''.
    intros; repeat rewrite <- Associativity; repeat rewrite <- InverseOf1; t.
  Qed.

  Hint Rewrite InverseOf1' using assumption.

  Lemma iso_is_mono s d m : CategoryIsomorphism s d m -> Monomorphism s d m.
    destruct 1; hnf; morphisms 1.
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

Section CategoryIsomorphismEquivalenceRelation.
  Variable C : Category.
  Variable s d d' : C.

  Hint Resolve Transitive.

  Theorem CategoryIsomorphismComposition (m : C.(Morphism) s d) (m' : C.(Morphism) d d') :
    CategoryIsomorphism m -> CategoryIsomorphism m' -> CategoryIsomorphism (Compose m' m).
    repeat (destruct 1);
      match goal with
        | [ m : Morphism _ _ _, m' : Morphism _ _ _ |- _ ] => exists (Compose m m')
      end;
      firstorder; morphisms 1.
  Qed.
End CategoryIsomorphismEquivalenceRelation.

Section CategoryObjects1.
  Variable C : Category.

  Definition MorphismUnique s d (m : C.(Morphism) s d) : Prop :=
    forall m', MorphismsEquivalent _ _ _ m m'.

  Implicit Arguments MorphismUnique [s d].

  Definition UniqueUpToUniqueIsomorphism' (P : C.(Object) -> Prop) : Prop :=
    forall o, P o -> forall o', P o' -> exists m : C.(Morphism) o o', CategoryIsomorphism' m /\ MorphismUnique m.

  Definition UniqueUpToUniqueIsomorphism (P : C.(Object) -> Type) :=
    forall o, P o -> forall o', P o' -> { m : C.(Morphism) o o' | CategoryIsomorphism' m & MorphismUnique m }.

  (* A terminal object is an object with a unique morphism from every other object. *)
  Definition TerminalObject' (o : C) : Prop :=
    forall o', exists m : C.(Morphism) o' o, MorphismUnique m.

  Definition TerminalObject (o : C) :=
    forall o', { m : C.(Morphism) o' o | MorphismUnique m }.

  (* An initial object is an object with a unique morphism from every other object. *)
  Definition InitialObject' (o : C) : Prop :=
    forall o', exists m : C.(Morphism) o o', MorphismUnique m.

  Definition InitialObject (o : C) :=
    forall o', { m : C.(Morphism) o o' | MorphismUnique m }.
End CategoryObjects1.

Implicit Arguments MorphismUnique [C s d].
Implicit Arguments UniqueUpToUniqueIsomorphism' [C].
Implicit Arguments UniqueUpToUniqueIsomorphism [C].
Implicit Arguments InitialObject' [C].
Implicit Arguments InitialObject [C].
Implicit Arguments TerminalObject' [C].
Implicit Arguments TerminalObject [C].

Section CategoryObjects2.
  Variable C : Category.

  Hint Unfold TerminalObject InitialObject InverseOf.

  Hint Resolve Transitive.
  Hint Immediate Symmetric.

  Ltac unique := intros o Ho o' Ho'; destruct (Ho o); destruct (Ho o'); destruct (Ho' o); destruct (Ho' o');
    repeat match goal with
             | [ x : _ |- _ ] => exists x
           end; eauto.

  (* The terminal object is unique up to unique isomorphism. *)
  Theorem TerminalObjectUnique : UniqueUpToUniqueIsomorphism (@TerminalObject C).
    unique.
  Qed.

  (* The initial object is unique up to unique isomorphism. *)
  Theorem InitialObjectUnique : UniqueUpToUniqueIsomorphism (@InitialObject C).
    unique.
  Qed.
End CategoryObjects2.
