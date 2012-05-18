Require Import Bool Omega Setoid.
Require Import EquivalenceRelation.

Set Implicit Arguments.

Ltac t' := simpl; intuition.

Ltac t := t';
  repeat (match goal with
            | [ H : context[@eq] |- _ ] => rewrite H
            | _ => progress autorewrite with core in *
          end; t').

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

Section Categories.
  Variable C D : Category.
  
  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of categories is known as a functor. Namely, given 
     categories [C] and [C'], a (covariant) functor [F : C -> C'] is a rule that assigns to
     each object [A] of [C] an object [F A] of [C'] and to each map [m : A -> B] of [C] a map
     [F m : F A -> F B] of [C'] preserving composition and identity; that is,
     (1) [F (m' ○ m) = (F m') ○ (F m)] for maps [m : A -> B] and [m' : B -> C] of [C], and
     (2) [F (id A) = id (F A)] for any object [A] of [C], where [id A] is the identity morphism of [A].

     Since we are using [MorhpismsEquivalent] rather than [=], we must additionally require
     that [F] preserves [MorphismsEquivalent].
     **)
  Record Functor := {
    ObjectOf :> C -> D;
    MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d);
    FEquivalenceOf : forall s d (m1 m2 : C.(Morphism) s d),
      MorphismsEquivalent _ _ _ m1 m2
      -> MorphismsEquivalent _ _ _ (MorphismOf _ _ m1) (MorphismOf _ _ m2);
    FCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
      MorphismsEquivalent _ _ _ (MorphismOf _ _ (Compose m2 m1))
      (Compose (MorphismOf _ _ m2) (MorphismOf _ _ m1));
    FIdentityOf : forall o, MorphismsEquivalent _ _ _ (MorphismOf _ _ (Identity o)) (Identity (ObjectOf o))
  }.
  
End Categories.

Implicit Arguments MorphismOf [C D s d].

Section Category.
  Variable C : Category.

  (* There is an identity functor.  It does the obvious thing. *)
  Definition IdentityFunctor : Functor C C.
    refine {| ObjectOf := (fun x => x);
      MorphismOf := (fun _ _ x => x)
    |};
    t.
  Defined.

  (* [m'] is the inverse of [m] if both compositions are
     equivalent to the relevant identity morphisms. *)
  Definition InverseOf s d (m : C.(Morphism) s d) (m' : C.(Morphism) d s) : Prop :=
    MorphismsEquivalent _ _ _ (Identity s) (Compose m' m) /\
    MorphismsEquivalent _ _ _ (Identity d) (Compose m m').

  (* A morphism is an isomorphism if it has an inverse *)
  Definition CategoryIsomorphism s d (m : C.(Morphism) s d) : Prop :=
    exists m', InverseOf _ _ m m'.

  Theorem CategoryIdentityInverse (o : C.(Object)) : InverseOf _ _ (Identity o) (Identity o).
    unfold InverseOf; t.
  Qed.

  Theorem CategoryIdentityIsomorphism (o : C.(Object)) : CategoryIsomorphism _ _ (Identity o).
    exists (Identity o); intuition; apply CategoryIdentityInverse.
  Qed.
End Category.

Implicit Arguments CategoryIsomorphism [C s d].

Section Categories_NaturalTransformation.
  Variable C D : Category.
  Variable F G : Functor C D.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:
     
     A map of functors is known as a natural transformation. Namely, given two functors
     [F : C -> C'], [F' : C -> C'], a natural transformation [T: F -> F'] is a collection of maps
     [T A : F A -> F' A], one for each object [A] of [C], such that [(T B) ○ (F m) = (F' m) ○ (T A)]
     for every map [m : A -> B] of [C]; that is, the following diagram is commutative:
     
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    F' m    V
     F' A ------> F' B
     **)
  Record NaturalTransformation := {
    ComponentsOf :> forall c : C.(Object), Morphism _ (F c) (G c);
    Commutes : forall s d (m : Morphism C s d),
      MorphismsEquivalent _ _ _
      (Compose (ComponentsOf d) (F.(MorphismOf) m))
      (Compose (G.(MorphismOf) m) (ComponentsOf s))
  }.

  Definition NaturalEquivalence (T : NaturalTransformation) : Prop :=
    forall x : C.(Object), CategoryIsomorphism (T.(ComponentsOf) x).
End Categories_NaturalTransformation.

Section IdentityNaturalTransformation.
  Variable C : Category.
  Variable F : Functor C C.

  (* There is an identity natrual transformation. *)
  Definition IdentityNaturalTransformation : NaturalTransformation F F.
    refine {| ComponentsOf := (fun c => Identity (F c))
      |};
    abstract t.
  Defined.


   Theorem IdentityNaturalEquivalence : NaturalEquivalence IdentityNaturalTransformation.
     unfold NaturalEquivalence. intros.
     exists (Identity _).
     unfold InverseOf.
     t.
   Qed.
End IdentityNaturalTransformation.
