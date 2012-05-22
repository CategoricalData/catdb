Require Import Setoid.
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

  Definition NaturalEquivalence (T : NaturalTransformation) :=
    forall x : C.(Object), CategoryIsomorphism (T.(ComponentsOf) x).

End Categories_NaturalTransformation.

Implicit Arguments NaturalTransformation [C D].
Implicit Arguments NaturalEquivalence [C D F G].

Section NaturalTransformationInverse.
  Variable C D : Category.
  Variable F G : Functor C D.
  Variable T : NaturalTransformation F G.

(*
  Definition NaturalEquivalenceInverse : (NaturalEquivalence T) -> (NaturalTransformation G F).
    unfold NaturalEquivalence; unfold CategoryIsomorphism; intros.
    refine {| ComponentsOf := (fun c => match (X c) with
                                          | _ => _
                                            end)
    |}.
    intros.
    Check Commutes.
    assert (H : forall s d m m' m'', InverseOf (T d) m' -> InverseOf (T s) m'' -> MorphismsEquivalent _ (G s) (F d) (Compose m' (MorphismOf G m)) (Compose (MorphismOf F m) m'')).
    unfold InverseOf.
    repeat (destruct 1).
    intros.
    t.
    pre_compose_mono (T d0).
    unfold Monomorphism.
    repeat (destruct 1); intros.
    transitivity (Compose (Compose m' (T d0)) m1); t.
    transitivity (Compose (Compose m' (T d0)) m2); t.
    repeat (rewrite Associativity); t.
    apply PreComposeMorphisms; t.

    repeat (rewrite <- Associativity).
    transitivity (Compose (Identity (G d0)) (G.(MorphismOf) m0)); t.
    
    post_compose_epi (T s0).
    unfold Epimorphism.
    repeat (destruct 1); intros.
    transitivity (Compose m1 (Compose (T s0) m'')); t.
    transitivity (Compose m2 (Compose (T s0) m'')); t.
    repeat (rewrite <- Associativity); t.
    apply PostComposeMorphisms; t.
    
    repeat (rewrite Associativity).
    transitivity (Compose (T d0) (Compose (MorphismOf F m0) (Identity (F s0))));
      try (repeat (rewrite Associativity); repeat (apply PreComposeMorphisms); t).
    symmetry.
    apply (@Commutes C D F G T s0 d0 _).
  Defined.
*)
End NaturalTransformationInverse.

Section NaturalTransformationComposition.
  Variable C D D' : Category.
  Variable F F' : Functor C D.
  Variable G G' : Functor D D'.
(*
  Definition NTComposeC (T : NaturalTransformation F F') (T' : NaturalTransformation G G') :
    NaturalTransformation (Compose .
    
*)

End NaturalTransformationComposition.

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
