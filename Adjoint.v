Require Import FunctionalExtensionality.
Require Export SpecializedCategory Category Functor NaturalTransformation NaturalEquivalence AdjointUnit.
Require Import Common Hom ProductCategory ProductFunctor Duals.

Set Implicit Arguments.

Section Adjunction.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.
  Variable F : SpecializedFunctor C D.
  Variable G : SpecializedFunctor D C.

  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.
  Let FOp := OppositeFunctor F.

  Let HomCPreFunctor : SpecializedFunctor (COp * D) (COp * C) := ((IdentityFunctor _) * G)%functor.
  Let HomDPreFunctor : SpecializedFunctor (COp * D) (DOp * D) := (FOp * (IdentityFunctor _))%functor.

  Record Adjunction := {
    AMateOf :> SpecializedNaturalTransformation
    (ComposeFunctors (HomFunctor D) HomDPreFunctor)
    (ComposeFunctors (HomFunctor C) HomCPreFunctor);
    AEquivalence : NaturalEquivalence AMateOf
  }.

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

  Record HomAdjunction := {
    AComponentsOf' : forall A A', (HomFunctor D).(ObjectOf') (F.(ObjectOf') A, A') -> (HomFunctor C).(ObjectOf') (A, G.(ObjectOf') A');
    (* ugh, the lack of sort-polymorphisms in [Definition]s is annoying *)
    AIsomorphism' : forall A A', { m' : _ | (fun x => m' (@AComponentsOf' A A' x)) = (fun x => x) /\ (fun x => @AComponentsOf' A A' (m' x)) = (fun x => x) };
    ACommutes' : forall A A' B B' (m : morC B A) (m' : morD A' B'),
      TypeCat.(Compose') _ _ _
      (@AComponentsOf' B B') ((HomFunctor D).(MorphismOf') (F.(ObjectOf') A, A') (F.(ObjectOf') B, B') (F.(MorphismOf') _ _ m, m'))
      = TypeCat.(Compose') _ _ _
      ((HomFunctor C).(MorphismOf') (A, G.(ObjectOf') A') (B, G.(ObjectOf') B') (m, G.(MorphismOf') _ _ m')) (@AComponentsOf' A A')
  }.

  Section AdjunctionInterface.
    Variable T : HomAdjunction.

    Definition AComponentsOf : forall (A : C) (A' : D),
      TypeCat.(Morphism) (HomFunctor D (F A, A')) (HomFunctor C (A, G A'))
      := Eval cbv beta delta [AComponentsOf'] in T.(AComponentsOf').
    Definition AIsomorphism : forall (A : C) (A' : D), @CategoryIsomorphism _ _ TypeCat _ _ (@AComponentsOf A A')
      := Eval cbv beta delta [AIsomorphism'] in T.(AIsomorphism').
    Definition ACommutes : forall (A : C) (A' : D) (B : C) (B' : D) (m : C.(Morphism) B A) (m' : D.(Morphism) A' B'),
      Compose (@AComponentsOf B B') (@MorphismOf _ _ _ _ _ _ (HomFunctor D) (F A, A') (F B, B') (F.(MorphismOf) m, m')) =
      Compose (@MorphismOf _ _ _ _ _ _ (HomFunctor C) (A, G A') (B, G B') (m, G.(MorphismOf) m')) (@AComponentsOf A A')
      := T.(ACommutes').
  End AdjunctionInterface.
  Global Coercion AComponentsOf : HomAdjunction >-> Funclass.

  Lemma ACommutes_Inverse (T : HomAdjunction) :
    forall A A' B B' (m : C.(Morphism) B A) (m' : D.(Morphism) A' B'),
      Compose (@MorphismOf _ _ _ _ _ _ (HomFunctor D) (F A, A') (F B, B') (F.(MorphismOf) m, m')) (proj1_sig (T.(AIsomorphism) A A')) =
      Compose (proj1_sig (T.(AIsomorphism) B B')) (@MorphismOf _ _ _ _ _ _ (HomFunctor C) (A, G A') (B, G B') (m, G.(MorphismOf) m')).
    Opaque TypeCat HomFunctor.
    intros.
    pose (T.(AIsomorphism) B B').
    pose (T.(AIsomorphism) A A').
    intro_proj2_sig_from_goal.
    unfold InverseOf in *; destruct_hypotheses;
      pre_compose_to_identity; post_compose_to_identity;
      apply ACommutes.
  Qed.
End Adjunction.

Arguments AComponentsOf {objC morC C objD morD D} [F G] T A A' _ : simpl nomatch.
Arguments AIsomorphism {objC morC C objD morD D} [F G] T A A' : simpl nomatch.

Section AdjunctionEquivalences.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.
  Variable F : SpecializedFunctor C D.
  Variable G : SpecializedFunctor D C.

  Definition HomAdjunction2Adjunction_AMateOf (A : HomAdjunction F G) :
    SpecializedNaturalTransformation
    (ComposeFunctors (HomFunctor D)
      (ProductFunctor (OppositeFunctor F) (IdentityFunctor D)))
    (ComposeFunctors (HomFunctor C)
      (ProductFunctor (IdentityFunctor (OppositeCategory C)) G)).
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun cd : objC * objD => A.(AComponentsOf) (fst cd) (snd cd))
          _
        )
    end.
    abstract (
      simpl in *; intros;
        apply functional_extensionality_dep; intro;
          destruct A;
            simpl in *;
              fg_equal;
              trivial
    ).
  Defined.

  Definition HomAdjunction2Adjunction (A : HomAdjunction F G) : Adjunction F G.
    exists (HomAdjunction2Adjunction_AMateOf A).
    intro x; hnf; simpl.
    exact (AIsomorphism A (fst x) (snd x)).
  Defined.

  Definition Adjunction2HomAdjunction (A : Adjunction F G) : HomAdjunction F G.
    hnf; simpl.
    exists (fun c d => ComponentsOf A.(AMateOf) (c, d));
      simpl;
        [ exact (fun A0 A' => A.(AEquivalence) (A0, A')) |
          exact (fun A0 A' B B' m m' => A.(Commutes') (A0, A') (B, B') (m, m')) ].
  Defined.

  Hint Rewrite FIdentityOf.

  Lemma adjunction_naturality_pre (A : HomAdjunction F G) c d d' (f : D.(Morphism) (F c) d) (g : D.(Morphism) d d') :
    @Compose _ _ C _ _ _ (G.(MorphismOf) g) (A.(AComponentsOf) _ _ f) =
    A.(AComponentsOf) _ _ (Compose g f).
    assert (H := fg_equal (A.(ACommutes) _ _ _ _ (Identity c) g) f).
    simpl in *; autorewrite with core in *.
    auto.
  Qed.

  Lemma adjunction_naturality'_pre (A : HomAdjunction F G) c' c d (f : C.(Morphism) c (G d)) (h : C.(Morphism) c' c) :
    @Compose _ _ D _ _ _ (proj1_sig (A.(AIsomorphism) _ _) f) (F.(MorphismOf) h) =
    proj1_sig (A.(AIsomorphism) _ _) (Compose f h).
    assert (H := fg_equal (ACommutes_Inverse A _ _ _ _ h (Identity d)) f).
    simpl in *; autorewrite with core in *.
    auto.
  Qed.

  Section typeof.
    Let typeof (A : Type) (a : A) := A.
    Let adjunction_naturalityT := Eval simpl in typeof adjunction_naturality_pre.
    Let adjunction_naturality'T := Eval simpl in typeof adjunction_naturality'_pre.
    Let adjunction_naturalityT' := Eval cbv beta iota delta [typeof adjunction_naturalityT] zeta in adjunction_naturalityT.
    Let adjunction_naturality'T' := Eval cbv beta iota delta [typeof adjunction_naturality'T] zeta in adjunction_naturality'T.
    Definition adjunction_naturality : adjunction_naturalityT' := adjunction_naturality_pre.
    Definition adjunction_naturality' : adjunction_naturality'T' := adjunction_naturality'_pre.
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
  Definition UnitOf (A : HomAdjunction F G) : AdjunctionUnit F G.
    Transparent Morphism Identity.
    eexists (Build_SpecializedNaturalTransformation (IdentityFunctor C) (ComposeFunctors G F)
      (fun c => A.(AComponentsOf) c (F c) (Identity _))
      _
    ).
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


  Definition CounitOf (A : HomAdjunction F G) : AdjunctionCounit F G.
    Transparent MorphismOf.
    eexists (Build_SpecializedNaturalTransformation (ComposeFunctors F G) (IdentityFunctor D)
      (fun d => proj1_sig (A.(AIsomorphism) (G d) d) (Identity _))
      _
    ).
    simpl.
    intros c d f.
    exists (A.(AComponentsOf) c d f).
    abstract (
      split; intros;
        t_with t';
        repeat rewrite (adjunction_naturality' A), LeftIdentity;
          intro_proj2_sig_from_goal;
          unfold InverseOf in *; simpl in *; destruct_hypotheses; fg_equal; auto
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
End AdjunctionEquivalences.

Section AdjunctionEquivalences'.
  Variables C D : Category.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Definition HomAdjunctionOfUnit (T : AdjunctionUnit F G) : HomAdjunction F G.
    refine {| AComponentsOf' := (fun c d (g : Morphism _ (F c) d) => Compose (G.(MorphismOf) g) (projT1 T c)) |};
      try (intros; exists (fun f => proj1_sig (projT2 T _ _ f)));
      abstract (
        intros; destruct T as [ T s ]; repeat split; simpl in *;
          apply functional_extensionality_dep; intros;
          solve [
              intro_proj2_sig_from_goal;
              destruct_hypotheses;
                auto
            |
              repeat rewrite FCompositionOf; repeat rewrite Associativity; repeat apply f_equal;
                simpl_do do_rewrite_rev (Commutes T); reflexivity
          ]
      ).
  Defined.

  Definition HomAdjunctionOfCounit (T : AdjunctionCounit F G) : HomAdjunction F G.
    refine {| AComponentsOf' := (fun c d (g : Morphism _ (F c) d) =>
      let inverseOf := (fun s d f => proj1_sig (projT2 T s d f)) in
        let f := inverseOf _ _ g in
          let AComponentsOf_Inverse := Compose (projT1 T d) (F.(MorphismOf) f) in
            inverseOf _ _ AComponentsOf_Inverse
    )
    |};
    simpl; present_spnt';
    try (intros; exists (fun f => Compose (projT1 T _) (F.(MorphismOf) f)));
      abstract (
        destruct T as [ T s ]; repeat split; intros; simpl in *;
          apply functional_extensionality_dep; intros; simpl;
            intro_proj2_sig_from_goal;
            destruct_hypotheses;
            repeat match goal with
                     | [ H : _ |- _ ] => rewrite (H _ (eq_refl _)); auto
                   end;
            repeat match goal with
                     | [ H : _ |- _ ] => apply H; auto
                   end;
            intro_proj2_sig_from_goal;
            destruct_hypotheses;
            repeat rewrite FCompositionOf;
              let H := fresh in assert (H := Commutes T); simpl in H; try_associativity ltac:(rewrite H);
                repeat try_associativity ltac:(apply f_equal2; try reflexivity);
                  intro_proj2_sig_from_goal;
                  destruct_hypotheses;
                  trivial
      ).
  Defined.
End AdjunctionEquivalences'.

Coercion HomAdjunction2Adjunction : HomAdjunction >-> Adjunction.
Coercion Adjunction2HomAdjunction : Adjunction >-> HomAdjunction.

Coercion UnitOf : HomAdjunction >-> AdjunctionUnit.
Coercion CounitOf : HomAdjunction >-> AdjunctionCounit.

Coercion HomAdjunctionOfUnit : AdjunctionUnit >-> HomAdjunction.
Coercion HomAdjunctionOfCounit : AdjunctionCounit >-> HomAdjunction.
