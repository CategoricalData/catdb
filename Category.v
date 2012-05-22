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

Hint Rewrite LeftIdentity' RightIdentity'.

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
  
  Hint Resolve PreComposeMorphisms' PostComposeMorphisms'.

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

Ltac identity_transitvity :=
  match goal with
    | [ |- (RelationsEquivalent _ _ _ _ (Compose ?M _) ?M) ] => transitivity (Compose M (Identity _));
      match goal with
        | [ |- (RelationsEquivalent _ _ _ _ (Compose ?M (Identity _)) ?M) ] => apply RightIdentity
        | [ |- (RelationsEquivalent _ _ _ _ (Compose ?M _) (Compose ?M (Identity _))) ] => apply PreComposeMorphisms
      end
    | [ |- (RelationsEquivalent _ _ _ _ (Compose _ ?M) ?M) ] => transitivity (Compose (Identity _) M);
      match goal with
        | [ |- (RelationsEquivalent _ _ _ _ (Compose (Identity _) ?M) ?M) ] => apply LeftIdentity
        | [ |- (RelationsEquivalent _ _ _ _ (Compose _ ?M) (Compose (Identity _) ?M)) ] => apply PostComposeMorphisms
      end
    | [ |- (RelationsEquivalent _ _ _ _ ?M (Compose ?M _)) ] => symmetry; intuition
    | [ |- (RelationsEquivalent _ _ _ _ ?M (Compose _ ?M)) ] => symmetry; intuition
  end.

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

  Lemma CategoryIsomorphism2Isomorphism' s d m : CategoryIsomorphism s d m -> CategoryIsomorphism' _ _ m.
    unfold CategoryIsomorphism; unfold CategoryIsomorphism'; auto.
  Qed.

  Hint Resolve PreComposeMorphisms PostComposeMorphisms.

  Lemma iso_is_epi s d m : CategoryIsomorphism s d m -> Epimorphism s d m.
    unfold CategoryIsomorphism; unfold Epimorphism; unfold InverseOf; repeat (destruct 1); intros.
    transitivity (Compose m1 (Compose m x)); t.
    transitivity (Compose m2 (Compose m x)); t.
    repeat (rewrite <- Associativity); t.
  Qed.

  Lemma iso_is_mono s d m : CategoryIsomorphism s d m -> Monomorphism s d m.
    unfold CategoryIsomorphism; unfold Monomorphism; unfold InverseOf; repeat (destruct 1); intros.
    transitivity (Compose (Compose x m) m1); t.
    transitivity (Compose (Compose x m) m2); t.
    repeat (rewrite Associativity); t.
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

Ltac post_compose_epi e := match goal with
                             | [ |- (RelationsEquivalent _ _ _ _ (?M1 : Morphism _ _ _) (?M2 : Morphism _ _ _)) ] =>
                               cut (MorphismsEquivalent _ _ _ (Compose M1 e) (Compose M2 e)); 
                                 try match goal with
                                       | [ |- _ -> _ ] => cut (Epimorphism _ _ _ e); intuition
                                     end
                           end.
Ltac pre_compose_mono m := match goal with
                             | [ |- (RelationsEquivalent _ _ _ _ (?M1 : Morphism _ _ _) (?M2 : Morphism _ _ _)) ] =>
                               cut (MorphismsEquivalent _ _ _ (Compose m M1) (Compose m M2)); 
                                 try match goal with
                                       | [ |- _ -> _ ] => cut (Monomorphism _ _ _ m); intuition
                                     end
                           end.