Require Import Setoid FunctionalExtensionality.
Require Export Category Functor.
Require Import Common NaturalEquivalence Hom.

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
    intros.
    pose (T.(AIsomorphism) B B').
    pose (T.(AIsomorphism) A A').
    repeat match goal with
             | [ |- appcontext[proj1_sig ?x] ] => unique_pose (proj2_sig x)
           end; unfold InverseOf in *; destruct_hypotheses.
    eapply iso_is_epi; [ eauto | ]; eapply iso_is_mono; [ eauto | ].
      repeat match goal with
               | [ H : _ |- _ ]
                 => try_associativity ltac:(rewrite H; (rewrite LeftIdentity || rewrite RightIdentity))
             end.
    apply ACommutes.
  Qed.

  (**
     Quoting from Awody's "Category Theory",
     An adjunction between categories [C] and [D]
     consists of functors
     [F : C <-> D : G]
     and a natural transformation
     [T : 1_C -> G ○ F]
     with the property:
     (o) For any [c : C], [d : D], and [f : c -> G d], there exists a unique
     [g : F c -> d] such that
     [f = (G g) ○ (T c)]
     as indicated in
                g
     F c ..................> d

                 G g
     G (F c) --------------> G d
       ^                    _
       |                    /|
       |                  /
       |                /
       |              /
       | T c        /
       |          /  f
       |        /
       |      /
       |    /
       |  /
        c

    Terminology and notation:
    * [F] is called the left adjoint, [G] is called the right adjoint, and [T] is called the
    unit of the adjunction.
    * One sometimes writes [F -| G] for ``[F] is left and [G] right adjoint.''
    * The statement (o) is the UMP of the unit [T].
    Note that the situation [F -| G] is a generalization of equivalence of categories,
    in that a pseudo-inverse is an adjoint. In that case, however, it is the relation
    between categories that one is interested in. Here, one is concerned with the
    relation between special functors. That is to say, it is not the relation on
    categories ``there exists an adjunction,'' but rather ``this functor has an adjoint''
    that we are concerned with.
    **)
  Definition AdjunctionUnit (F : Functor C D) (G : Functor D C) :=
    { T : NaturalTransformation (IdentityFunctor C) (ComposeFunctors G F) &
      forall (c : C) (d : D) (f : Morphism _ c (G d)),
        { g : Morphism _ (F c) d | unique (fun g => f = Compose (G.(MorphismOf) g) (T c)) g }
    }.

  (**
     Paraphrasing and quoting from Awody's "Category Theory",
     An adjunction between categories [C] and [D]
     consists of functors
     [F : C <-> D : G]
     and a natural transformation
     [U : F ○ G -> 1_D]
     with the property:
     (o) For any [c : C], [d : D], and [g : F c -> d], there exists a unique
     [f : c -> G d] such that
     [g = (U d) ○ (F f)]
     as indicated in the diagram

                f
     c ..................> G d

               F f
     F c --------------> F (G d)
      \                    |
        \                  |
          \                |
            \              |
              \            | U d
             g  \          |
                  \        |
                    \      |
                      \    |
                       _\| V
                          d

    Terminology and notation:
    * The statement (o) is the UMP of the counit [U].
    **)
  Definition AdjunctionCounit (F : Functor C D) (G : Functor D C) :=
    { U : NaturalTransformation (ComposeFunctors F G) (IdentityFunctor D) &
      forall (c : C) (d : D) (g : Morphism _ (F c) d),
        { f : Morphism _ c (G d) | unique (fun f => g = Compose (U d) (F.(MorphismOf) f)) f }
    }.
End Adjunction.

Section AdjunctionEquivalences.
  Variables C D : Category.
  Variable F : Functor C D.
  Variable G : Functor D C.

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
    eexists (Build_NaturalTransformation _ _ (IdentityFunctor C) (ComposeFunctors G F) (fun c => A.(AComponentsOf) c (F c) (Identity _)) _).
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
    eexists (Build_NaturalTransformation _ _ (ComposeFunctors F G) (IdentityFunctor D) (fun d => proj1_sig (A.(AIsomorphism) (G d) d) (Identity _)) _).
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
