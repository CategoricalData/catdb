Require Import Setoid Program.
Require Import Common EquivalenceRelation Category Functor.

Section Categories_NaturalTransformation.
  Variable C D : Category.
  Variable F G : Functor C D.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of functors is known as a natural transformation. Namely, given two functors
     [F : C -> D], [G : C -> D], a natural transformation [T: F -> G] is a collection of maps
     [T A : F A -> G A], one for each object [A] of [C], such that [(T B) ○ (F m) = (G m) ○ (T A)]
     for every map [m : A -> B] of [C]; that is, the following diagram is commutative:

           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    G m     V
     G A --------> G B
     **)
  Record NaturalTransformation := {
    ComponentsOf :> forall c : C.(Object), Morphism _ (F c) (G c);
    Commutes : forall s d (m : Morphism C s d),
      MorphismsEquivalent _ _ _
      (Compose (ComponentsOf d) (F.(MorphismOf) m))
      (Compose (G.(MorphismOf) m) (ComponentsOf s))
  }.

  Definition NaturalTransformationsEquivalent (T U : NaturalTransformation) :=
    forall o, MorphismsEquivalent _ _ _ (T.(ComponentsOf) o) (U.(ComponentsOf) o).
End Categories_NaturalTransformation.

Implicit Arguments NaturalTransformation [C D].
Implicit Arguments ComponentsOf [C D F G].
Implicit Arguments Commutes [C D F G].
Implicit Arguments NaturalTransformationsEquivalent [C D F G].

Section NaturalTransformationsEquivalenceRelation.
  Variable C D : Category.
  Variable F G H : Functor C D.

  Lemma NTeq_refl (T : NaturalTransformation F G) : NaturalTransformationsEquivalent T T.
    unfold NaturalTransformationsEquivalent; t.
  Qed.

  Lemma NTeq_sym (T U : NaturalTransformation F G) :
    NaturalTransformationsEquivalent T U -> NaturalTransformationsEquivalent U T.
    unfold NaturalTransformationsEquivalent; intros; symmetry; t.
  Qed.

  Lemma NTeq_trans (T U V: NaturalTransformation F G) :
    NaturalTransformationsEquivalent T U -> NaturalTransformationsEquivalent U V -> NaturalTransformationsEquivalent T V.
    unfold NaturalTransformationsEquivalent; intros H0 H1 o; specialize (H0 o); specialize (H1 o); simpl_transitivity.
  Qed.
End NaturalTransformationsEquivalenceRelation.

Add Parametric Relation C D F G : _ (@NaturalTransformationsEquivalent C D F G)
  reflexivity proved by (NTeq_refl _ _ _ _)
  symmetry proved by (NTeq_sym _ _ _ _)
  transitivity proved by (NTeq_trans _ _ _ _)
    as natural_transformation_eq.

Section NaturalTransformationComposition.
  Variable C D E : Category.
  Variable F F' F'' : Functor C D.
  Variable G G' : Functor D E.

  Hint Resolve Commutes.

  (*
     We have the diagram
          F
     C -------> D
          |
          |
          | T
          |
          V
     C -------> D
          F'
          |
          | T'
          |
          V
     C ------> D
          F''

     And we want the commutative diagram
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    F' m    V
     F' A -------> F' B
      |            |
      |            |
      | T' A       | T' B
      |            |
      V    F'' m   V
     F'' A ------> F'' B

  *)

  Definition NTComposeT (T' : NaturalTransformation F' F'') (T : NaturalTransformation F F') :
    NaturalTransformation F F''.
    refine {| ComponentsOf := (fun c => Compose (T' c) (T c)) |};
      (* XXX TODO: Find a way to get rid of [m] in the transitivity call *)
      abstract (intros; transitivity (Compose (T' _) (Compose (MorphismOf F' m) (T _))); eauto).
  Defined.

  (*
     We have the diagram
          F          G
     C -------> D -------> E
          |          |
          |          |
          | T        | U
          |          |
          V          V
     C -------> D -------> E
          F'         G'

     And we want the commutative diagram
             G (F m)
     G (F A) -------> G (F B)
        |                |
        |                |
        | U (T A)        | U (T B)
        |                |
        V     G' (F' m)  V
     G' (F' A) -----> G' (F' B)

  *)
  (* XXX TODO: Automate this better *)

  Hint Rewrite Commutes.
  Hint Rewrite <- FCompositionOf.
  Hint Resolve FEquivalenceOf.

  Lemma FCompositionOf2 : forall C D (F : Functor C D) x y z u (m1 : C.(Morphism) x z) (m2 : C.(Morphism) y x) (m3 : D.(Morphism) u _),
    MorphismsEquivalent _ _ _ (Compose (MorphismOf F m1) (Compose (MorphismOf F m2) m3)) (Compose (MorphismOf F (Compose m1 m2)) m3).
    intros; repeat rewrite <- Associative; rewrite FCompositionOf; t.
  Qed.

  Hint Rewrite FCompositionOf2.

  Definition NTComposeF (U : NaturalTransformation G G') (T : NaturalTransformation F F'):
    NaturalTransformation (ComposeFunctors G F) (ComposeFunctors G' F').
    refine (Build_NaturalTransformation _ _ (ComposeFunctors G F) (ComposeFunctors G' F')
      (fun c => Compose (G'.(MorphismOf) (T.(ComponentsOf) c)) (U.(ComponentsOf) (F c)))
      _); abstract t.
  Defined.
End NaturalTransformationComposition.

Implicit Arguments NTComposeT [C D F F' F''].
Implicit Arguments NTComposeF [C D E F F' G G'].

Add Parametric Morphism C D F F' F'' :
  (@NTComposeT C D F F' F'')
  with signature (@NaturalTransformationsEquivalent _ _ _ _) ==> (@NaturalTransformationsEquivalent _ _ _ _) ==> (@NaturalTransformationsEquivalent _ _ _ _)
    as nt_compose_t_eq_mor.
  unfold NTComposeT; unfold NaturalTransformationsEquivalent; t.
Qed.

Add Parametric Morphism C D E F F' G G' :
  (@NTComposeF C D E F F' G G')
  with signature (@NaturalTransformationsEquivalent _ _ _ _) ==> (@NaturalTransformationsEquivalent _ _ _ _) ==> (@NaturalTransformationsEquivalent _ _ _ _)
    as nt_compose_f_eq_mor.
  Hint Resolve FEquivalenceOf.
  unfold NTComposeF; unfold NaturalTransformationsEquivalent; t.
Qed.

Section IdentityNaturalTransformation.
  Variable C D : Category.
  Variable F : Functor C D.

  (* There is an identity natrual transformation. *)
  Definition IdentityNaturalTransformation : NaturalTransformation F F.
    refine {| ComponentsOf := (fun c => Identity (F c))
      |};
    abstract t.
  Defined.
End IdentityNaturalTransformation.

Implicit Arguments IdentityNaturalTransformation [C D].

Section FunctorEquivalence.
  Variable C D : Category.

  Definition equiv_natural_trans_components_of (F F' G G' : Functor C D) (FeF : @ObjectOf _ _ F' = @ObjectOf _ _ F) (FeG : @ObjectOf _ _ G' = @ObjectOf _ _ G) :
    NaturalTransformation F G -> (forall c : C, Morphism D (F' c) (G' c)).
    firstorder; t.
  Defined.

  Hint Unfold equiv_natural_trans_components_of.
  Hint Resolve @functional_extensionality_dep.

  Lemma equiv_natural_trans_components_of_id (F G : Functor C D) (FeF : @ObjectOf _ _ F = @ObjectOf _ _ F) (FeG : @ObjectOf _ _ G = @ObjectOf _ _ G)
    (T : NaturalTransformation F G) :
    equiv_natural_trans_components_of _ _ _ _ FeF FeG T = T.(ComponentsOf).
    eq2eq_refl; destruct T; t.
  Qed.

  Hint Unfold equiv_natural_trans_components_of.

  Definition Build_EquivalentNaturalTransformation' (F F' G G' : Functor C D) (FeF : @ObjectOf _ _ F' = @ObjectOf _ _ F) (FeG : @ObjectOf _ _ G' = @ObjectOf _ _ G) :
    FunctorsEquivalent F F' -> FunctorsEquivalent G G' -> NaturalTransformation F G -> NaturalTransformation F' G'.
    intros FeF' FeG' T.
    refine {| ComponentsOf := equiv_natural_trans_components_of _ _ _ _ FeF FeG T |}.
    abstract (
      unfold FunctorsEquivalent in *;
        destruct_hypotheses;
        unfold ObjectOf, MorphismOf in *;
          destruct T; subst;
            unfold ObjectOf, MorphismOf in *; simpl;
              eq2eq_refl;
              unfold eq_rect_r, eq_sym; repeat (rewrite <- eq_rect_eq);
                t;
                repeat match goal with
                         | [ H : _ |- _ ] => rewrite <- H; t
                       end
    ).
  Defined.

  Definition Build_EquivalentNaturalTransformation (F F' G G' : Functor C D) : FunctorsEquivalent F F' -> FunctorsEquivalent G G' ->
    NaturalTransformation F G -> NaturalTransformation F' G'.
    intros FeF FeG T.
    unfold FunctorsEquivalent in *.
    assert (@ObjectOf _ _ F' = @ObjectOf _ _ F /\ @ObjectOf _ _ G' = @ObjectOf _ _ G);
      destruct_hypotheses; t.
    match goal with
      | [ H0 : _, H1 : _ |- _ ] =>
        exact (Build_EquivalentNaturalTransformation' _ _ _ _ H0 H1 FeF FeG T)
    end.
  Defined.

  Definition Build_EquivalentNaturalTransformation_id' (F G : Functor C D) (FeF : FunctorsEquivalent F F) (FeG : FunctorsEquivalent G G)
    (T : NaturalTransformation F G) : (Build_EquivalentNaturalTransformation F F G G FeF FeG T).(ComponentsOf) = T.(ComponentsOf).
    apply functional_extensionality_dep; intros.
    destruct T, FeF, FeG.
    destruct_hypotheses.
    subst; simpl;
      unfold eq_rect_r;
        repeat (rewrite <- eq_rect_eq); reflexivity.
  Qed.

  Hint Resolve f_equal Build_EquivalentNaturalTransformation_id'.

  Definition Build_EquivalentNaturalTransformation_id (F G : Functor C D) (FeF : FunctorsEquivalent F F) (FeG : FunctorsEquivalent G G)
    (T : NaturalTransformation F G) : Build_EquivalentNaturalTransformation F F G G FeF FeG T = T.
    match goal with
      | [ |- ?a = ?b ] =>
        assert (ComponentsOf a = ComponentsOf b) by t;
        destruct a; destruct b
    end;
    unfold ComponentsOf in *; subst; apply f_equal; apply proof_irrelevance.
  Qed.

End FunctorEquivalence.

Implicit Arguments Build_EquivalentNaturalTransformation [C D F F' G G'].
Implicit Arguments Build_EquivalentNaturalTransformation' [C D F F' G G'].
Implicit Arguments Build_EquivalentNaturalTransformation_id [C D F G].

Hint Rewrite Build_EquivalentNaturalTransformation_id.
