Require Import Setoid FunctionalExtensionality.
Require Export Category Functor AdjointUnit.
Require Import Common Hom SetCategory.

Set Implicit Arguments.

Section Adjunction.
  Variables C D : Category.
  Variable F : Functor C D.
  Variable G : Functor D C.

  (**
     Quoting the 18.705 Lecture Notes:
     Let [C] and [D] be categories, [F : C -> D] and [G : D -> C]
     functors. We call [(F, G)] an adjoint pair, [F] the left adjoint of [G], and [G] the
     right adjoint of [F] if, for each object [A : C] and object [A' : D], there is a natural
     bijection
     [Hom_D (F A) A' ~= Hom_C A (G A')]
     Here natural means that maps [B -> A] and [A' -> B'] induce a commutative
     diagram:
     [[
       Hom_D (F A) A' ~= Hom_C A (G A')
             |                  |
             |                  |
             |                  |
             |                  |
             V                  V
       Hom_D (F B) B' ~= Hom_C B (G B')
     ]]
     *)
  Record Adjunction := {
    AComponentsOf : forall A A', Morphism _ (HomFunctor D (F A, A')) (HomFunctor C (A, G A'));
    AIsomorphism : forall A A', CategoryIsomorphism (AComponentsOf A A');
    ACommutes : forall A A' B B' (m : C.(Morphism) B A) (m' : D.(Morphism) A' B'),
      Compose (AComponentsOf B B') (@MorphismOf _ _ (HomFunctor D) (F A, A') (F B, B') (F.(MorphismOf) m, m')) =
      Compose (@MorphismOf _ _ (HomFunctor C) (A, G A') (B, G B') (m, G.(MorphismOf) m')) (AComponentsOf A A')
  }.

  Lemma ACommutes_Inverse (T : Adjunction) :
    forall A A' B B' (m : C.(Morphism) B A) (m' : D.(Morphism) A' B'),
      Compose (@MorphismOf _ _ (HomFunctor D) (F A, A') (F B, B') (F.(MorphismOf) m, m')) (proj1_sig (T.(AIsomorphism) A A')) =
      Compose (proj1_sig (T.(AIsomorphism) B B')) (@MorphismOf _ _ (HomFunctor C) (A, G A') (B, G B') (m, G.(MorphismOf) m')).
    Opaque TypeCat HomFunctor.
    intros.
    pose (T.(AIsomorphism) B B').
    pose (T.(AIsomorphism) A A').
    repeat match goal with
             | [ |- appcontext[proj1_sig ?x] ] => unique_pose (proj2_sig x)
           end; unfold InverseOf in *; destruct_hypotheses;
    pre_compose_to_identity; post_compose_to_identity;
    apply ACommutes.
  Qed.
End Adjunction.

Section AdjunctionEquivalences.
  Variables C D : Category.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Hint Rewrite FIdentityOf.

  Lemma adjunction_naturality (A : Adjunction F G) c d d' (f : Morphism _ (F c) d) (g : Morphism _ d d') :
    @Compose _ c _ _ (G.(MorphismOf) g) (A.(AComponentsOf) _ _ f) = (* we need to help with the explicit [c], or else we get a complicated expression *)
    A.(AComponentsOf) _ _ (Compose g f).
    assert (H := fg_equal (A.(ACommutes) _ _ _ _ (Identity c) g) f).
    simpl in *; autorewrite with core in *.
    auto.
  Qed.

  Lemma adjunction_naturality'' (A : Adjunction F G) c' c d (f : Morphism _ c (G d)) (h : Morphism _ c' c) :
    Compose (proj1_sig (A.(AIsomorphism) _ _) f) (F.(MorphismOf) h) =
    proj1_sig (A.(AIsomorphism) _ _) (Compose f h).
    simpl.
    assert (H := fg_equal (ACommutes_Inverse A _ _ _ _ h (Identity d)) f).
    simpl in *; autorewrite with core in *.
    auto.
  Qed.

  Section typeof.
    Let typeof (A : Type) (a : A) := A.
    Let adjunction_naturality''T := Eval simpl in typeof adjunction_naturality''.
    Let adjunction_naturality''T' := Eval cbv beta iota delta [typeof adjunction_naturality''T] zeta in adjunction_naturality''T.
    Definition adjunction_naturality' : adjunction_naturality''T' := adjunction_naturality''.
  End typeof.

  (**
     Quoting from Awody's "Category Theory",
     Proposition 9.4. Given categories and functors,
     [F : C <-> D : G]
     the following conditions are equivalent:
     1. [F] is left adjoint to [G]; that is, there is a natural transformation
       [η : 1_C -> G ○ F]
       that has the UMP of the unit:
       For any [c : C], [d : D] and [f : c -> G d] there exists a unique
       [g : F c -> d] such that
       [f = G g ○ η c].
     2. For any [c : C] and [d : D] there is an isomorphism,
       [ϕ : Hom_D (F c, d) ~= Hom_C (c, G d)]
       that is natural in both [c] and [d].
     Moreover, the two conditions are related by the formulas
     [ϕ g = G g ○ η c]
     [η c = ϕ(1_{F c})]
     *)
  Definition UnitOf (A : Adjunction F G) : AdjunctionUnit F G.
    eexists (Build_NaturalTransformation (IdentityFunctor C) (ComposeFunctors G F) (fun c => A.(AComponentsOf) c (F c) (Identity _)) _).
    simpl.
    intros c d f.
    exists (proj1_sig (A.(AIsomorphism) c d) f).
    abstract (
      destruct (proj2_sig (A.(AIsomorphism) c d)); simpl in *; fg_equal;
        repeat split; intros;
          t_with t';
          repeat rewrite adjunction_naturality, RightIdentity;
            auto
    ).
    Grab Existential Variables.
    abstract (
      intros s d m; simpl in *;
        repeat rewrite adjunction_naturality, RightIdentity;
          let H := fresh in assert (H := fg_equal (A.(ACommutes) d (F d) s (F d) m (Identity _)) (Identity _));
            simpl in *;
              autorewrite with core in *;
                auto
    ).
  Defined.


  Definition CounitOf (A : Adjunction F G) : AdjunctionCounit F G.
    eexists (Build_NaturalTransformation (ComposeFunctors F G) (IdentityFunctor D) (fun d => proj1_sig (A.(AIsomorphism) (G d) d) (Identity _)) _).
    simpl.
    intros c d f.
    exists (A.(AComponentsOf) c d f).
    abstract (
      split; intros;
        t_with t';
        repeat rewrite (adjunction_naturality' A), LeftIdentity;
          match goal with
            | [ |- appcontext[proj1_sig ?x] ] => let H := fresh in assert (H := proj2_sig x)
          end; unfold InverseOf in *; simpl in *; destruct_hypotheses; fg_equal; auto
    ).
    Grab Existential Variables.
    abstract (
      intros s d m; simpl in *;
        rewrite (adjunction_naturality' A);
          let H := fresh in assert (H := fg_equal (ACommutes_Inverse A (G s) s (G s) d (Identity (G s)) m) (Identity _));
            simpl in *;
              autorewrite with core in *;
                auto
    ).
  Defined.

  Definition AdjunctionOfUnit (T : AdjunctionUnit F G) : Adjunction F G.
    refine {| AComponentsOf := (fun c d (g : Morphism _ (F c) d) => Compose (G.(MorphismOf) g) (projT1 T c)) |};
      try (intros; exists (fun f => proj1_sig (projT2 T _ _ f)));
      abstract (
        intros; destruct T as [ T s ]; repeat split; simpl in *;
          apply functional_extensionality_dep; intros;
          solve [
              intro_proj2_sig_from_goal;
              unfold unique in *; destruct_hypotheses;
                auto
          ] ||
          solve [
              repeat rewrite FCompositionOf; repeat rewrite Associativity; repeat apply f_equal;
                let H := fresh in assert (H := Commutes T); simpl in H; rewrite <- H; reflexivity
          ]
      ).
  Defined.

  Definition AdjunctionOfCounit (T : AdjunctionCounit F G) : Adjunction F G.
    refine {| AComponentsOf := (fun c d (g : Morphism _ (F c) d) =>
      let inverseOf := (fun s d f => proj1_sig (projT2 T s d f)) in
        let f := inverseOf _ _ g in
          let AComponentsOf_Inverse := Compose (projT1 T d) (F.(MorphismOf) f) in
            inverseOf _ _ AComponentsOf_Inverse
    )
    |};
    try (intros; exists (fun f => Compose (projT1 T _) (F.(MorphismOf) f)));
      abstract (
        destruct T as [ T s ]; repeat split; intros; simpl in *;
          apply functional_extensionality_dep; intros; simpl;
            rewrite_rev_proj2_sig;
            repeat rewrite FCompositionOf;
              let H := fresh in assert (H := Commutes T); simpl in H; try_associativity ltac:(rewrite H);
                try_associativity ltac:(apply f_equal2; try reflexivity);
                try_associativity rewrite_rev_proj2_sig
      ).
  Defined.
End AdjunctionEquivalences.
