Require Import FunctionalExtensionality ProofIrrelevance.
Require Export SmallCategory Functor NaturalTransformation FEqualDep.
Require Import Common.

Set Implicit Arguments.

Section Categories_NaturalTransformation.
  Variable C : SmallCategory.
  Variable D : Category.
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
  Record SmallNaturalTransformation := {
    SComponentsOf :> forall c : C.(SObject), Morphism _ (F c) (G c);
    SCommutes : forall s d (m : Morphism C s d),
      Compose (SComponentsOf d) (F.(MorphismOf) m) = Compose (G.(MorphismOf) m) (SComponentsOf s)
  }.
End Categories_NaturalTransformation.

Section Small2Large.
  Variable C : SmallCategory.
  Variable D : Category.
  Variable F G : Functor C D.

  Definition SmallNaturalTransformation2NaturalTransformation (T : SmallNaturalTransformation F G) : NaturalTransformation F G.
    refine {| ComponentsOf := (fun c : C.(Object) => T.(SComponentsOf) c); Commutes := T.(SCommutes) |}.
  Defined.
End Small2Large.

Coercion SmallNaturalTransformation2NaturalTransformation : SmallNaturalTransformation >-> NaturalTransformation.

Section Small2LargeId.
  Variable C : SmallCategory.
  Variable D : Category.
  Variable F G : Functor C D.

  Lemma SmallNaturalTransformation2NaturalTransformationId (T T' : SmallNaturalTransformation F G) :
    SmallNaturalTransformation2NaturalTransformation T = SmallNaturalTransformation2NaturalTransformation T' -> T = T'.
    intro H.
    assert (forall x, ComponentsOf T x = ComponentsOf T' x) by (rewrite H; reflexivity).
    unfold SmallNaturalTransformation2NaturalTransformation in *; simpl in *.
    assert (SComponentsOf T = SComponentsOf T') by (apply functional_extensionality_dep; assumption).
    destruct T, T'; simpl in *; repeat subst; f_equal; apply proof_irrelevance.
  Qed.
End Small2LargeId.

Hint Resolve SmallNaturalTransformation2NaturalTransformationId.

Ltac snt_eq_step_with tac := try apply SmallNaturalTransformation2NaturalTransformationId;
  nt_eq_step_with ltac:(try apply SmallNaturalTransformation2NaturalTransformationId; tac).

Ltac snt_eq_with tac := repeat snt_eq_step_with tac.

Ltac snt_eq_step := snt_eq_step_with idtac.
Ltac snt_eq := snt_eq_with idtac.


Section NaturalTransformationCompositionT.
  Variable C : SmallCategory.
  Variable D : Category.
  Variables F F' F'' : Functor C D.

  Hint Resolve SCommutes f_equal f_equal2.
  Hint Rewrite Associativity.

  Definition SNTComposeT (T' : SmallNaturalTransformation F' F'') (T : SmallNaturalTransformation F F') :
    SmallNaturalTransformation F F''.
    refine {| SComponentsOf := (fun c => Compose (T' c) (T c)) |};
      (* XXX TODO: Find a way to get rid of [m] in the transitivity call *)
      abstract (intros; transitivity (Compose (T' _) (Compose (MorphismOf F' m) (T _))); try_associativity eauto).
  Defined.
End NaturalTransformationCompositionT.

Section NaturalTransformationCompositionF.
  Variables C D : SmallCategory.
  Variable E : Category.
  Variable F F' : Functor C D.
  Variable G G' : Functor D E.

  Definition SNTComposeF (U : SmallNaturalTransformation G G') (T : SmallNaturalTransformation F F'):
    SmallNaturalTransformation (ComposeFunctors G F) (ComposeFunctors G' F').
    refine (Build_SmallNaturalTransformation (ComposeFunctors G F) (ComposeFunctors G' F')
      (fun c => Compose (G'.(MorphismOf) (T.(SComponentsOf) c)) (U.(SComponentsOf) (F c)))
      _);
    abstract (simpl; intros; repeat try_associativity ltac:(repeat rewrite SCommutes; repeat rewrite <- FCompositionOf); reflexivity).
  Defined.
End NaturalTransformationCompositionF.

Section IdentityNaturalTransformation.
  Variable C : SmallCategory.
  Variable D : Category.
  Variable F : Functor C D.

  (* There is an identity natrual transformation. *)
  Definition IdentitySmallNaturalTransformation : SmallNaturalTransformation F F.
    refine {| SComponentsOf := (fun c => Identity (F c))
      |};
    abstract t.
  Defined.

  Hint Resolve LeftIdentity RightIdentity.

  Lemma LeftIdentitySmallNaturalTransformation (F' : Functor C D) (T : SmallNaturalTransformation F' F) :
    SNTComposeT IdentitySmallNaturalTransformation T = T.
    snt_eq; auto.
  Qed.

  Lemma RightIdentitySmallNaturalTransformation (F' : Functor C D) (T : SmallNaturalTransformation F F') :
    SNTComposeT T IdentitySmallNaturalTransformation = T.
    snt_eq; auto.
  Qed.
End IdentityNaturalTransformation.

Hint Rewrite LeftIdentitySmallNaturalTransformation RightIdentitySmallNaturalTransformation.
