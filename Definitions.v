Require Import Bool Omega.

Set Implicit Arguments.

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

Ltac t' := simpl; intuition.

Ltac t := t';
  repeat (match goal with
            | [ H : _ |- _ ] => rewrite H
            | _ => progress autorewrite with core in *
          end; t').

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

  Lemma addedge_equal : forall s d d' (p p' : path' E s d), p = p' -> forall e : E d d', AddEdge p e = AddEdge p' e.
    t.
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
End path'_Theorems.


Section EquivalenceRelation.
  Variable Object : Type.
  Variable Relation : Object -> Object -> Type.
  Variable RelationsEquivalent' : forall o1 o2, Relation o1 o2 -> Relation o1 o2 -> Prop.

  Implicit Arguments RelationsEquivalent' [o1 o2].

  Record EquivalenceRelation := {
    RelationsEquivalent :> forall o1 o2, Relation o1 o2 -> Relation o1 o2 -> Prop := RelationsEquivalent';
    Reflexive : forall o1 o2 (r : Relation o1 o2),
      RelationsEquivalent r r;
    Symmetric : forall o1 o2 (r1 r2 : Relation o1 o2),
      RelationsEquivalent r1 r2 -> RelationsEquivalent r2 r1;
    Transitive : forall o1 o2 (r1 r2 r3 : Relation o1 o2),
      RelationsEquivalent r1 r2 -> RelationsEquivalent r2 r3 -> RelationsEquivalent r1 r3
  }.
End EquivalenceRelation.

Implicit Arguments EquivalenceRelation [Object Relation].
Implicit Arguments RelationsEquivalent [Object Relation o1 o2].
Implicit Arguments Reflexive [Object Relation RelationsEquivalent' o1 o2].
Implicit Arguments Symmetric [Object Relation RelationsEquivalent' o1 o2].
Implicit Arguments Transitive [Object Relation RelationsEquivalent' o1 o2].

Record Category := {
  Vertex :> Type;
  Edge : Vertex -> Vertex -> Type;

  PathsEquivalent : forall s d, (path' Edge s d) -> (path' Edge s d) -> Prop;
  PathsEquivalence : EquivalenceRelation PathsEquivalent;

  PreCompose : forall s d (E : Edge s d) d' (p1 p2 : path' _ d d'),
    PathsEquivalent p1 p2 -> PathsEquivalent (prepend p1 E) (prepend p2 E);
  PostCompose : forall s d (p1 p2 : path' _ s d) d' (E : Edge d d'),
    PathsEquivalent p1 p2 -> PathsEquivalent (AddEdge p1 E) (AddEdge p2 E)
}.

Section Category.
  Variable C : Category.

  Definition path := path' C.(Edge).

  Record Instance := {
    TypeOf :> C -> Type;
    FunctionOf : forall s d (E : C.(Edge) s d), TypeOf s -> TypeOf d;
    EquivalenceOf : forall s d (p1 p2 : path s d), C.(PathsEquivalent) p1 p2
      -> forall x, compose TypeOf FunctionOf p1 x = compose TypeOf FunctionOf p2 x
  }.

  Record NaturalTransformation (I J : Instance) := {
    ComponentsOf :> forall c : C, I c -> J c;
    Commutes : forall s d (p : path s d),
      forall x, ComponentsOf d (compose I I.(FunctionOf) p x)
        = compose J J.(FunctionOf) p (ComponentsOf s x)
  }.
End Category.

Section Categories.
  Variables C D : Category.

  Section transferPath.
    Variable vertexOf : C -> D.
    Variable pathOf : forall s d, C.(Edge) s d -> path D (vertexOf s) (vertexOf d).

    Fixpoint transferPath s d (p : path C s d) : path D (vertexOf s) (vertexOf d) :=
      match p with
        | NoEdges => NoEdges
        | AddEdge _ _ p' E => concatenate (transferPath p') (pathOf _ _ E)
      end.
  End transferPath.

  Record Functor := {
    VertexOf :> C -> D;
    PathOf : forall s d, C.(Edge) s d -> path D (VertexOf s) (VertexOf d);
    FEquivalenceOf : forall s d (p1 p2 : path C s d),
      PathsEquivalent C p1 p2
      -> PathsEquivalent D (transferPath VertexOf PathOf p1) (transferPath VertexOf PathOf p2)
  }.
End Categories.

Record SaturatedCategory := {
  Object :> Type;
  Morphism : Object -> Object -> Type;

  MorphismsEquivalent : forall o1 o2, Morphism o1 o2 -> Morphism o1 o2 -> Prop;
  MorphismsEquivalence : EquivalenceRelation MorphismsEquivalent;

  Identity : forall o, Morphism o o;
  Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d';

  PreComposeMorphisms : forall s d d' (m : Morphism d d') (m1 m2 : Morphism s d),
    MorphismsEquivalent m1 m2 -> MorphismsEquivalent (Compose m m1) (Compose m m2);
  PostComposeMorphisms : forall s d d' (m1 m2 : Morphism d d') (m : Morphism s d),
    MorphismsEquivalent m1 m2 -> MorphismsEquivalent (Compose m1 m) (Compose m2 m);

  Associativity : forall o1 o2 o3 o4 (m1 : Morphism o1 o2) (m2 : Morphism o2 o3) (m3 : Morphism o3 o4),
    MorphismsEquivalent (Compose (Compose m3 m2) m1) (Compose m3 (Compose m2 m1));
  LeftIdentity : forall a b (f : Morphism a b), MorphismsEquivalent (Compose (Identity b) f) f;
  RightIdentity : forall a b (f : Morphism a b), MorphismsEquivalent (Compose f (Identity a)) f
}.

Implicit Arguments Compose [s s0 d d'].
Implicit Arguments Identity [s].
Implicit Arguments MorphismsEquivalent [s o1 o2].

Hint Resolve PostCompose PreCompose PathsEquivalence.
Hint Extern 1 (PathsEquivalent _ _ _) => apply Reflexive.

Section SaturatedCategories.
  Variable C D : SaturatedCategory.
  
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
  Record SaturatedFunctor := {
    ObjectOf :> C -> D;
    MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d);
    SFEquivalenceOf : forall s d (m1 m2 : C.(Morphism) s d),
      MorphismsEquivalent m1 m2
      -> MorphismsEquivalent (MorphismOf _ _ m1) (MorphismOf _ _ m2);
    SFCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
      MorphismsEquivalent (MorphismOf _ _ (Compose m2 m1))
      (Compose (MorphismOf _ _ m2) (MorphismOf _ _ m1));
    SFIdentityOf : forall o, MorphismsEquivalent (MorphismOf _ _ (Identity o)) (Identity (ObjectOf o))
  }.
  
End SaturatedCategories.

Implicit Arguments MorphismOf [C D s0 d].

Section SaturatedCategory.
  Variable C : SaturatedCategory.

  (* There is an identity functor.  It does the obvious thing. *)
  Definition IdentitySaturatedFunctor : SaturatedFunctor C C.
    refine {| ObjectOf := (fun x => x);
      MorphismOf := (fun _ _ x => x)
    |};
    intuition; apply Reflexive; apply MorphismsEquivalence.
  Defined.

  (* [m'] is the inverse of [m] if both compositions are
     equivalent to the relevant identity morphisms. *)
  Definition InverseOf s d (m : C.(Morphism) s d) (m' : C.(Morphism) d s) : Prop :=
    MorphismsEquivalent (Identity s) (Compose m' m) /\
    MorphismsEquivalent (Identity d) (Compose m m').

  (* A morphism is an isomorphism if it has an inverse *)
  Definition SaturatedCategoryIsomorphism s d (m : C.(Morphism) s d) : Prop :=
    exists m', InverseOf _ _ m m'.

  Theorem SaturatedCategoryIdentityInverse (o : C.(Object)) : InverseOf _ _ (Identity o) (Identity o).
    unfold InverseOf; intuition;
      apply C.(MorphismsEquivalence).(Symmetric). apply LeftIdentity. apply RightIdentity.
  Qed.

  Theorem SaturatedCategoryIdentityIsomorphism (o : C.(Object)) : SaturatedCategoryIsomorphism _ _ (Identity o).
    exists (Identity o); intuition; apply SaturatedCategoryIdentityInverse.
  Qed.
End SaturatedCategory.

Implicit Arguments SaturatedCategoryIsomorphism [C s d].

Section SaturatedCategories_NaturalTransformation.
  Variable C D : SaturatedCategory.
  Variable F G : SaturatedFunctor C D.

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
  Record SaturatedNaturalTransformation := {
    SComponentsOf :> forall c : C.(Object), Morphism _ (F c) (G c);
    SCommutes : forall s d (m : Morphism C s d),
      MorphismsEquivalent
      (Compose (SComponentsOf d) (F.(MorphismOf) m))
      (Compose (G.(MorphismOf) m) (SComponentsOf s))
  }.


  Definition SaturatedNaturalEquivalence (S : SaturatedNaturalTransformation) : Prop :=
    forall x : C.(Object), SaturatedCategoryIsomorphism (S.(SComponentsOf) x).
End SaturatedCategories_NaturalTransformation.

Section IdentitySaturatedNaturalTransformation.
  Variable C : SaturatedCategory.
  Variable F : SaturatedFunctor C C.

  (* There is an identity natrual transformation. *)
(*
  Definition IdentitySaturatedNaturalTransformation : SaturatedNaturalTransformation F F.
    refine {| SComponentsOf := (fun c => Identity (F c))
      |}.
    intros; intuition.
    assert (H0 : (forall (s d : C) (m : C.(Morphism) s d), MorphismsEquivalent (Compose (Identity d) m) (Compose m (Identity s)))).
    assert (H1 : (forall (s d : C) (m : C.(Morphism) s d), MorphismsEquivalent (Compose (Identity d) m) m)).
    apply IdentityAxiom.
    assert (H2 : (forall (s d : C) (m : C.(Morphism) s d), MorphismsEquivalent m (Compose m (Identity s)))).
    intuition; apply C.(MorphismsEquivalence).(Symmetric).
    apply IdentityAxiom.
    intuition.
    
    assert C.(MorphismsEquivalence).(Transitive).
   Qed.*)

End IdentitySaturatedNaturalTransformation.

Section Category_SaturatedCategory_Equivalence.
  Variable C : Category.
  Variable S : SaturatedCategory.

  Hint Rewrite concatenate_noedges_p concatenate_addedge.
  Hint Rewrite <- concatenate_prepend_equivalent.

  Definition saturate : SaturatedCategory.
    refine {| Object := C;
      Morphism := path C;
      MorphismsEquivalence := C.(PathsEquivalence);
      Identity := (fun _ => NoEdges);
      Compose := (fun _ _ _ m1 m2 => concatenate m2 m1)
      |}; abstract (intros; solve [ t | match goal with
                                          | [ p : path _ _ _ |- _ ] => solve [ induction p; t ]
                                        end ]).
  Defined.

  Fixpoint compose_morphism_path s d (p : path' S.(Morphism) s d) : Morphism _ s d :=
    match p with
      | NoEdges => Identity s
      | AddEdge _ _ p' E => Compose E (compose_morphism_path p')
    end.

  Lemma MorphismsEquivalent_symm : forall s o1 o2 x y,
    MorphismsEquivalent y x
    -> MorphismsEquivalent (s := s) (o1 := o1) (o2 := o2) x y.
    intros; eapply (Symmetric (MorphismsEquivalence s)); eassumption.
  Qed.

  Lemma MorphismsEquivalent_trans : forall s o1 o2 x y z,
    MorphismsEquivalent x z
    -> MorphismsEquivalent z y
    -> MorphismsEquivalent (s := s) (o1 := o1) (o2 := o2) x y.
    intros; eapply (Transitive (MorphismsEquivalence s)); eassumption.
  Qed.

  Hint Resolve MorphismsEquivalent_symm MorphismsEquivalent_trans.
  Hint Resolve Associativity LeftIdentity RightIdentity PreComposeMorphisms PostComposeMorphisms.

  Lemma compose_morphism_path_alt : forall s d d' (E : Morphism S s d) (p : path' _ d d'),
    MorphismsEquivalent (compose_morphism_path (prepend p E)) (Compose (compose_morphism_path p) E).
    induction p; t; eauto.
  Qed.    

  Hint Resolve compose_morphism_path_alt.

  Definition unsaturate : Category.
    refine {| Vertex := S;
      Edge := S.(Morphism);
      PathsEquivalent := (fun _ _ p p' => MorphismsEquivalent (compose_morphism_path p) (compose_morphism_path p'))
    |}; abstract (t; eauto).
  Defined.
End Category_SaturatedCategory_Equivalence.
