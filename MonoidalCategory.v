Require Import ProofIrrelevance.
Require Export Category Functor ProductCategory FunctorProduct NaturalTransformation NaturalEquivalence.
Require Import Common Notations StructureEquality DefinitionSimplification.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section PreMonoidalCategory.
  (* It's too hard to implement it all inside a record, so first we
     define everything, then we put it in a record *)

  (** Quoting Wikipedia:
     A  monoidal category is a category [C] equipped with
     *)
  Variable C : Category.
  (**
     - a bifunctor [ ⊗ : C × C -> C] called the tensor product or
         monoidal product,
    *)
  Variable TensorProduct : Functor (C * C) C.

  Let src {s d} (_ : Morphism C s d) := s.
  Let dst {s d} (_ : Morphism C s d) := d.

  Local Notation "A ⊗ B" := (TensorProduct (A, B)).
  Local Notation "A ⊗m B" := (TensorProduct.(MorphismOf) (s := (@src _ _ A, @src _ _ B)) (d := (@dst _ _ A, @dst _ _ B)) (A, B)%morphism).

  Let TriMonoidalProductL_ObjectOf (abc : C * C * C) : C :=
    (fst (fst abc) ⊗ snd (fst abc)) ⊗ snd abc.

  Let TriMonoidalProductR_ObjectOf (abc : C * C * C) : C :=
    fst (fst abc) ⊗ (snd (fst abc) ⊗ snd abc).

  Let TriMonoidalProductL_MorphismOf' (s d : C * C * C) (m : Morphism (C * C * C) s d) :
    Morphism C (TriMonoidalProductL_ObjectOf s) (TriMonoidalProductL_ObjectOf d).
    destruct m as [[ma mb] mc].
    apply (MorphismOf TensorProduct).
    split; try assumption.
    apply (MorphismOf TensorProduct).
    split; try assumption.
  Defined.

  Let TriMonoidalProductR_MorphismOf' (s d : C * C * C) (m : Morphism (C * C * C) s d) :
    Morphism C (TriMonoidalProductR_ObjectOf s) (TriMonoidalProductR_ObjectOf d).
    destruct m as [[ma mb] mc].
    apply (MorphismOf TensorProduct).
    split; try assumption.
    apply (MorphismOf TensorProduct).
    split; try assumption.
  Defined.

  Let TriMonoidalProductL_MorphismOf'' (s d : C * C * C) (m : Morphism (C * C * C) s d) :
    Morphism C (TriMonoidalProductL_ObjectOf s) (TriMonoidalProductL_ObjectOf d).
    simpl_definition_by_tac_and_exact (@TriMonoidalProductL_MorphismOf' s d m) ltac:(subst_body;
      rewrite (prod_eta m) in *;
      try rewrite (prod_eta (fst m)) in *;
        try rewrite (prod_eta (snd m)) in *
    ). (*
  assert (Hf : focus (@TriMonoidalProductL_MorphismOf' s d m)) by constructor.
  subst_body.
  simpl in Hf.
  repeat match type of Hf with
               | context[match ?E with existT2 _ _ _ => _ end] => rewrite (sigT2_eta E) in Hf; simpl in Hf
               | context[match ?E with exist2 _ _ _ => _ end] => rewrite (sig2_eta E) in Hf; simpl in Hf
               | context[match ?E with existT _ _ => _ end] => rewrite (sigT_eta E) in Hf; simpl in Hf
               | context[match ?E with exist _ _ => _ end] => rewrite (sig_eta E) in Hf; simpl in Hf
               | context[match ?E with pair _ _ => _ end] => rewrite (prod_eta E) in Hf; simpl in Hf
             end.
  unfold Morphism, Object in Hf.
  simpl in Hf.
  assert False.
  revert Hf.
  generalize (MorphismOf TensorProduct).
  generalize (ObjectOf TensorProduct).
  simpl in *.
  clear TensorProduct.
  unfold ProductCategory.
  unfold Object in *;
  unfold Morphism in *.
  simpl in *.
  repeat match goal with
           [ H : _ |- _ ] => clear H
         end.
  revert dependent objC.
  repeat match goal with
           [ H : _ |- _ ] => clear H
         end.
  intros ? ? ? ? ? ? ? Hf.
  (**** HERE ****)
  (*match type of Hf with
    | context[match ?E with pair _ _ => _ end] => rewrite (prod_eta E) in Hf; simpl in Hf
  end.*) (* fails *)
  let t := type of Hf in assert (t -> False); [ clear Hf; intro Hf | ].
  (*match type of Hf with
    | context[match ?E with pair _ _ => _ end] => rewrite (prod_eta E) in Hf; simpl in Hf
  end.*) (* fails *)
  Set Printing All.
  (* by copy and paste *)
  Unset Printing All.
  let t := constr:(  )
  in assert (t -> False); [ clear Hf; intro Hf | ].
  match type of Hf with
    | context[match ?E with pair _ _ => _ end] => rewrite (prod_eta E) in Hf; simpl in Hf
  end. (* succeeds o.O *)
  (*
  clear H
  intros.
  rewrite (prod_eta m) in Hf.
  simpl in Hf.
  rewrite (prod_eta (fst m)) in Hf.*)*)
  Defined.

  Let TriMonoidalProductR_MorphismOf'' (s d : C * C * C) (m : Morphism (C * C * C) s d) :
    Morphism C (TriMonoidalProductR_ObjectOf s) (TriMonoidalProductR_ObjectOf d).
    simpl_definition_by_tac_and_exact (@TriMonoidalProductR_MorphismOf' s d m) ltac:(subst_body;
      rewrite (prod_eta m) in *;
      try rewrite (prod_eta (fst m)) in *;
        try rewrite (prod_eta (snd m)) in *
    ).
  Defined.

  Let TriMonoidalProductL_MorphismOf (s d : C * C * C) (m : Morphism (C * C * C) s d) :
    Morphism C (TriMonoidalProductL_ObjectOf s) (TriMonoidalProductL_ObjectOf d)
    := Eval cbv beta iota zeta delta [TriMonoidalProductL_MorphismOf''] in @TriMonoidalProductL_MorphismOf'' s d m.

  Let TriMonoidalProductR_MorphismOf (s d : C * C * C) (m : Morphism (C * C * C) s d) :
    Morphism C (TriMonoidalProductR_ObjectOf s) (TriMonoidalProductR_ObjectOf d)
    := Eval cbv beta iota zeta delta [TriMonoidalProductR_MorphismOf''] in @TriMonoidalProductR_MorphismOf'' s d m.

  Definition TriMonoidalProductL' : Functor (C * C * C) C.
    refine (Build_Functor (C * C * C) C
      TriMonoidalProductL_ObjectOf
      TriMonoidalProductL_MorphismOf
      _
      _
    );
    subst_body;
    abstract (
      intros; destruct_hypotheses; simpl;
        repeat (rewrite <- FCompositionOf; unfold ProductCategory; simpl);
          repeat rewrite FIdentityOf;
            reflexivity
    ).
  Defined.

  Definition TriMonoidalProductR' : Functor (C * C * C) C.
    refine (Build_Functor (C * C * C) C
      TriMonoidalProductR_ObjectOf
      TriMonoidalProductR_MorphismOf
      _
      _
    );
    subst_body;
    abstract (
      intros; destruct_hypotheses; simpl;
        repeat (rewrite <- FCompositionOf; unfold ProductCategory; simpl);
          repeat rewrite FIdentityOf;
            reflexivity
    ).
  Defined.

  Definition TriMonoidalProductL'' : Functor (C * C * C) C.
    simpl_definition_by_tac_and_exact TriMonoidalProductL' ltac:(idtac; subst_body).
  Defined.

  Definition TriMonoidalProductR'' : Functor (C * C * C) C.
    simpl_definition_by_tac_and_exact TriMonoidalProductR' ltac:(idtac; subst_body).
  Defined.

  (* Then we clean up a bit with reduction. *)
  Definition TriMonoidalProductL := Eval cbv beta iota zeta delta [TriMonoidalProductL''] in TriMonoidalProductL''.
  Definition TriMonoidalProductR := Eval cbv beta iota zeta delta [TriMonoidalProductR''] in TriMonoidalProductR''.

  (**
     - an object [I] called the unit object or identity object,
   *)
  Variable UnitObject : C.
  Let I := UnitObject.
  (**
     - three natural isomorphisms subject to certain coherence
         conditions expressing the fact that the tensor operation
       + is associative: there is a natural isomorphism [α], called
           associator, with components [α_{A,B,C} : (A ⊗ B) ⊗ C ~= A ⊗ (B ⊗ C)],
    *)
  Variable Associator : NaturalIsomorphism TriMonoidalProductL TriMonoidalProductR.
  Let α := Associator.
  (**
       + has [I] as left and right identity: there are two natural
           isomorphisms [λ] and [ρ], respectively called left and
           right unitor, with components
           [λ A : I ⊗ A ~= A] and [ρ A : A ⊗ I ~= A].
     *)
  Definition LeftUnitorFunctor : Functor C C.
    clear TriMonoidalProductL_MorphismOf TriMonoidalProductR_MorphismOf
      TriMonoidalProductL_MorphismOf' TriMonoidalProductR_MorphismOf'
      TriMonoidalProductL_MorphismOf'' TriMonoidalProductR_MorphismOf''
      TriMonoidalProductL_ObjectOf TriMonoidalProductR_ObjectOf.
    refine {| ObjectOf := (fun A => I ⊗ A);
      MorphismOf := (fun s d (m : Morphism C s d) => Identity (C := C) I ⊗m m)
    |}; subst_body;
    abstract (
      intros; simpl;
        etransitivity; try (apply FCompositionOf || apply FIdentityOf);
          f_equal;
          unfold ProductCategory; simpl;
            try rewrite RightIdentity;
              reflexivity
    ).
  Defined.

  Definition RightUnitorFunctor : Functor C C.
    clear TriMonoidalProductL_MorphismOf TriMonoidalProductR_MorphismOf
      TriMonoidalProductL_MorphismOf' TriMonoidalProductR_MorphismOf'
      TriMonoidalProductL_MorphismOf'' TriMonoidalProductR_MorphismOf''
      TriMonoidalProductL_ObjectOf TriMonoidalProductR_ObjectOf.
    refine {| ObjectOf := (fun A => A ⊗ I);
      MorphismOf := (fun s d (m : Morphism C s d) => m ⊗m Identity (C := C) I)
    |}; subst_body;
    abstract (
      intros; simpl;
        etransitivity; try (apply FCompositionOf || apply FIdentityOf);
          f_equal;
          unfold ProductCategory; simpl;
            try rewrite RightIdentity;
              reflexivity
    ).
  Defined.

  Variable LeftUnitor : NaturalIsomorphism LeftUnitorFunctor (IdentityFunctor _).
  Variable RightUnitor : NaturalIsomorphism RightUnitorFunctor (IdentityFunctor _).
  Let λ := LeftUnitor.
  Let ρ := RightUnitor.

  (**
     The coherence conditions for these natural transformations are:
     - for all [A], [B], [C] and [D] in [C], the pentagon diagram
     [[
                           α_{A,B,C} ⊗ D                          α_{A,B⊗C,D}
       ((A ⊗ B) ⊗ C) ⊗ D -----------------> (A ⊗ (B ⊗ C)) ⊗ D -----------------> A ⊗ ((B ⊗ C) ⊗ D)
               |                                                                         |
               |                                                                         |
               | α_{A⊗B,C,D}                                                             | A ⊗ α_{B,C,D}
               |                                                                         |
               |                                                                         |
               V                                                                         V
       (A ⊗ B) ⊗ (C ⊗ D) ------------------------------------------------------> A ⊗ (B ⊗ (C ⊗ D))
                                           α_{A,B,C⊗D}
     ]]
     commutes
     *)

  Section AssociatorCoherenceCondition.
    Variables a b c d : C.

    (* going from top-left *)
    Let AssociatorCoherenceConditionT0 : Morphism C (((a ⊗ b) ⊗ c) ⊗ d) ((a ⊗ (b ⊗ c)) ⊗ d)
      := α (a, b, c) ⊗m Identity (C := C) d.
    Let AssociatorCoherenceConditionT1 : Morphism C ((a ⊗ (b ⊗ c)) ⊗ d) (a ⊗ ((b ⊗ c) ⊗ d))
      := α (a, b ⊗ c, d).
    Let AssociatorCoherenceConditionT2 : Morphism C (a ⊗ ((b ⊗ c) ⊗ d)) (a ⊗ (b ⊗ (c ⊗ d)))
      := Identity (C := C) a ⊗m α (b, c, d).
    Let AssociatorCoherenceConditionB0 : Morphism C (((a ⊗ b) ⊗ c) ⊗ d) ((a ⊗ b) ⊗ (c ⊗ d))
      := α (a ⊗ b, c, d).
    Let AssociatorCoherenceConditionB1 : Morphism C ((a ⊗ b) ⊗ (c ⊗ d)) (a ⊗ (b ⊗ (c ⊗ d)))
      := α (a, b, c ⊗ d).

    Definition AssociatorCoherenceCondition' :=
      Compose AssociatorCoherenceConditionT2 (Compose AssociatorCoherenceConditionT1 AssociatorCoherenceConditionT0)
      = Compose AssociatorCoherenceConditionB1 AssociatorCoherenceConditionB0.
  End AssociatorCoherenceCondition.

  Definition AssociatorCoherenceCondition := Eval unfold AssociatorCoherenceCondition' in
    forall a b c d : C, AssociatorCoherenceCondition' a b c d.

  (**
     - for all [A] and [B] in [C], the triangle diagram
     [[
                   α_{A,I,B}
     (A ⊗ I) ⊗ B -------------> A ⊗ (I ⊗ B)
         \                         /
           \                     /
             \                 /
       ρ_A ⊗ B \             / A ⊗ λ_B
                 \         /
                   \     /
                     ↘ ↙
                    A ⊗ B
     ]]
     commutes;
     *)
  Definition UnitorCoherenceCondition := forall A B : C,
    Compose ((Identity (C := C) A) ⊗m (λ B)) (α (A, I, B))
    = (ρ A) ⊗m (Identity (C := C) B).
End PreMonoidalCategory.

Section MonoidalCategory.
  (** Quoting Wikipedia:
     A  monoidal category is a category [C] equipped with
     - a bifunctor [ ⊗ : C × C -> C] called the tensor product or
         monoidal product,
     - an object [I] called the unit object or identity object,
     - three natural isomorphisms subject to certain coherence
         conditions expressing the fact that the tensor operation
       + is associative: there is a natural isomorphism [α], called
           associator, with components [α_{A,B,C} : (A ⊗ B) ⊗ C ~= A ⊗ (B ⊗ C)],
       + has [I] as left and right identity: there are two natural
           isomorphisms [λ] and [ρ], respectively called left and
           right unitor, with components
           [λ A : I ⊗ A ~= A] and [ρ A : A ⊗ I ~= A].
     The coherence conditions for these natural transformations are:
     - for all [A], [B], [C] and [D] in [C], the pentagon diagram
     [[
                           α_{A,B,C} ⊗ D                          α_{A,B⊗C,D}
       ((A ⊗ B) ⊗ C) ⊗ D -----------------> (A ⊗ (B ⊗ C)) ⊗ D -----------------> A ⊗ ((B ⊗ C) ⊗ D)
               |                                                                         |
               |                                                                         |
               | α_{A⊗B,C,D}                                                             | A ⊗ α_{B,C,D}
               |                                                                         |
               |                                                                         |
               V                                                                         V
       (A ⊗ B) ⊗ (C ⊗ D) ------------------------------------------------------> A ⊗ (B ⊗ (C ⊗ D))
                                           α_{A,B,C⊗D}
     ]]
     commutes
     - for all [A] and [B] in [C], the triangle diagram
     [[
                   α_{A,I,B}
     (A ⊗ I) ⊗ B -------------> A ⊗ (I ⊗ B)
         \                         /
           \                     /
             \                 /
       ρ_A ⊗ B \             / A ⊗ λ_B
                 \         /
                   \     /
                     ↘ ↙
                    A ⊗ B
     ]]
     commutes;

     It follows from these three conditions that any such diagram
     (i.e. a diagram whose morphisms are built using [α], [λ], [ρ],
     identities and tensor product) commutes: this is Mac Lane's
     "coherence theorem".

     A strict monoidal category is one for which the natural
     isomorphisms α, λ and ρ are identities. Every monoidal category
     is monoidally equivalent to a strict monoidal category.
     *)
  Local Reserved Notation "'I'".
  Local Reserved Notation "'α'".
  Local Reserved Notation "'λ'".
  Local Reserved Notation "'ρ'".

  Let src (C : Category) {s d} (_ : Morphism C s d) := s.
  Let dst (C : Category) s d (_ : Morphism C s d) := d.

  Let AssociatorCoherenceCondition' := Eval unfold AssociatorCoherenceCondition in @AssociatorCoherenceCondition.
  Let UnitorCoherenceCondition' := Eval unfold UnitorCoherenceCondition in @UnitorCoherenceCondition.

  Record MonoidalCategory := {
    MonoidalUnderlyingCategory :> Category;
    TensorProduct : Functor (MonoidalUnderlyingCategory * MonoidalUnderlyingCategory) MonoidalUnderlyingCategory
      where "A ⊗ B" := (TensorProduct (A, B)) and "A ⊗m B" := (TensorProduct.(MorphismOf) (s := (@src _ _ _ A, @src _ _ _ B)) (d := (@dst _ _ _ A, @dst _ _ _ B)) (A, B)%morphism);

    IdentityObject : MonoidalUnderlyingCategory where "'I'" := IdentityObject;

    Associator : NaturalIsomorphism (TriMonoidalProductL TensorProduct) (TriMonoidalProductR TensorProduct) where "'α'" := Associator;
    LeftUnitor : NaturalIsomorphism (LeftUnitorFunctor TensorProduct I)  (IdentityFunctor _) where "'λ'" := LeftUnitor;
    RightUnitor : NaturalIsomorphism (RightUnitorFunctor TensorProduct I) (IdentityFunctor _) where "'ρ'" := RightUnitor;

    (*
     [[
                           α_{A,B,C} ⊗ D                        α_{A,B,C} ⊗ D
       ((A ⊗ B) ⊗ C) ⊗ D -----------------> (A ⊗ (B ⊗ C)) ⊗ D -----------------> A ⊗ ((B ⊗ C) ⊗ D)
               |                                                                         |
               |                                                                         |
               | α_{A⊗B,C,D}                                                             | A ⊗ α_{B,C,D}
               |                                                                         |
               |                                                                         |
               V                                                                         V
       (A ⊗ B) ⊗ (C ⊗ D) ------------------------------------------------------> A ⊗ (B ⊗ (C ⊗ D))
                                           α_{A,B,C⊗D}
     ]]
     *)
    AssociatorCoherent : AssociatorCoherenceCondition' α;
    UnitorCoherent : UnitorCoherenceCondition' α λ ρ
  }.
End MonoidalCategory.
