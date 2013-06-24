Require Import FunctionalExtensionality.
Require Export Category Category Functor NaturalTransformation NaturalEquivalence AdjointUnit.
Require Import Common Hom ProductCategory FunctorProduct Duals.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Adjunction.
  Context `{C : Category}.
  Context `{D : Category}.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.
  Let FOp := OppositeFunctor F.

  Let HomCPreFunctor : Functor (COp * D) (COp * C) := ((IdentityFunctor _) * G)%functor.
  Let HomDPreFunctor : Functor (COp * D) (DOp * D) := (FOp * (IdentityFunctor _))%functor.

  Record Adjunction := {
    AMateOf :> NaturalIsomorphism
    (ComposeFunctors (HomFunctor D) HomDPreFunctor)
    (ComposeFunctors (HomFunctor C) HomCPreFunctor)
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
    AComponentsOf' : forall A A', D.(Morphism) (F A) A' -> C.(Morphism) A (G A');
    (* [IsomorphismOf] is sort-polymorphic, but it picks up the type of morphisms in [TypeCat].  The [IsInverseOf']s don't *)
    AIsomorphism' : forall A A', { m' : _ |
      IsInverseOf1 (C := TypeCat) _ _ (@AComponentsOf' A A') m' &
      IsInverseOf2 (C := TypeCat) _ _ (@AComponentsOf' A A') m'
    };
    ACommutes' : forall A A' B B' (m : C.(Morphism) B A) (m' : D.(Morphism) A' B'),
      Compose (C := TypeCat)
      (@AComponentsOf' B B') ((HomFunctor D).(MorphismOf) (s := (F A, A')) (d := (F B, B')) (F.(MorphismOf) m, m'))
      = Compose (C := TypeCat)
      ((HomFunctor C).(MorphismOf) (s := (A, G A')) (d := (B, G B')) (m, G.(MorphismOf) m')) (@AComponentsOf' A A')
  }.

  Section AdjunctionInterface.
    Variable T : HomAdjunction.

    Definition AComponentsOf : forall (A : C) (A' : D),
      TypeCat.(Morphism) (HomFunctor D (F A, A')) (HomFunctor C (A, G A'))
      := Eval cbv beta delta [AComponentsOf'] in T.(AComponentsOf').
    Definition AIsomorphism (A : C) (A' : D) : IsomorphismOf (C := TypeCat) (@AComponentsOf A A')
      := Eval cbv beta delta [AIsomorphism'] in T.(AIsomorphism') A A' : IsomorphismOf_sig (@AComponentsOf A A').
    Definition ACommutes : forall (A : C) (A' : D) (B : C) (B' : D) (m : C.(Morphism) B A) (m' : D.(Morphism) A' B'),
      Compose (@AComponentsOf B B') (MorphismOf (HomFunctor D) (s := (F A, A')) (d := (F B, B')) (F.(MorphismOf) m, m')) =
      Compose (MorphismOf (HomFunctor C) (s := (A, G A')) (d := (B, G B')) (m, G.(MorphismOf) m')) (@AComponentsOf A A')
      := T.(ACommutes').
  End AdjunctionInterface.

  Global Coercion AComponentsOf : HomAdjunction >-> Funclass.

  Lemma ACommutes_Inverse (T : HomAdjunction) :
    forall A A' B B' (m : C.(Morphism) B A) (m' : D.(Morphism) A' B'),
      Compose (MorphismOf (HomFunctor D) (s := (F A, A')) (d := (F B, B')) (F.(MorphismOf) m, m')) (proj1_sig (T.(AIsomorphism) A A')) =
      Compose (proj1_sig (T.(AIsomorphism) B B')) (MorphismOf (HomFunctor C) (s := (A, G A')) (d := (B, G B')) (m, G.(MorphismOf) m')).
    Local Opaque TypeCat HomFunctor.
    intros.
    Local Ltac intro_T T A A' :=
      let t := constr:(T.(AIsomorphism) A A') in
        let H := fresh in assert (H := t);
          let H0 := fresh in let H1 := fresh in
            assert (H0 := proj2_sig t);
              assert (H1 := proj3_sig t).
    intro_T T B B'.
    intro_T T A A'.
    (* XXX Figure out how to remove this *)
    Local Opaque AIsomorphism.
    simpl in *.
    match goal with
      | [ H : Compose ?x (?T ?A ?A') = Identity _ |- Compose _ ?x = _ ]
        => eapply (@iso_is_epi _ _ _ (T A A')); [
          exists x; hnf; eauto
          |
            repeat rewrite Associativity; find_composition_to_identity (* slow, but I don't have a better way to do it *); rewrite RightIdentity
        ]
    end.
    match goal with
      | [ H : Compose (?T ?A ?A') ?x = Identity _ |- _ = Compose ?x _ ]
        => eapply (@iso_is_mono _ _ _ (T A A')); [
          exists x; hnf; eauto
          |
            repeat rewrite <- Associativity; find_composition_to_identity; rewrite LeftIdentity
        ]
    end.
(*    pre_compose_to_identity; post_compose_to_identity; *) (* too slow *)
    apply ACommutes.
  Defined.
End Adjunction.

Arguments AComponentsOf {C D} [F G] T A A' _ : simpl nomatch.
Arguments AIsomorphism {C D} [F G] T A A' : simpl nomatch.

Section AdjunctionEquivalences.
  Variable C : Category.
  Variable D : Category.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Definition HomAdjunction2Adjunction_AMateOf (A : HomAdjunction F G) :
    NaturalTransformation
    (ComposeFunctors (HomFunctor D)
      (OppositeFunctor F * IdentityFunctor D))
    (ComposeFunctors (HomFunctor C)
      (IdentityFunctor (OppositeCategory C) * G)).
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun cd : C * D => A.(AComponentsOf) (fst cd) (snd cd))
          _
        )
    end.
    abstract (
      simpl in *; intros;
        destruct A;
          simpl in *;
            destruct_hypotheses;
            unfold Morphism, Object in *;
              simpl in *;
                trivial
    ).
  Defined.

  Definition HomAdjunction2Adjunction (A : HomAdjunction F G) : Adjunction F G.
    constructor.
    exists (HomAdjunction2Adjunction_AMateOf A).
    intro x; hnf; simpl.
    exact (AIsomorphism A (fst x) (snd x)).
  Defined.

  Definition Adjunction2HomAdjunction (A : Adjunction F G) : HomAdjunction F G.
    hnf; simpl.
    exists (fun c d => ComponentsOf A (c, d));
      simpl;
        [ exact (fun A0 A' => A.(NaturalIsomorphism_Isomorphism) (A0, A')) |
          exact (fun A0 A' B B' m m' => A.(Commutes) (A0, A') (B, B') (m, m')) ].
  Defined.

  Lemma adjunction_naturality_pre (A : HomAdjunction F G) c d d' (f : D.(Morphism) (F c) d) (g : D.(Morphism) d d') :
    Compose (C := C) (G.(MorphismOf) g) (A.(AComponentsOf) _ _ f) =
    A.(AComponentsOf) _ _ (Compose g f).
    assert (H := fg_equal (A.(ACommutes) _ _ _ _ (Identity c) g) f).
    simpl in *; autorewrite with category in *.
    auto with category.
  Qed.

  Lemma adjunction_naturality'_pre (A : HomAdjunction F G) c' c d (f : C.(Morphism) c (G d)) (h : C.(Morphism) c' c) :
    Compose (C := D) (proj1_sig (A.(AIsomorphism) _ _) f) (F.(MorphismOf) h) =
    proj1_sig (A.(AIsomorphism) _ _) (Compose f h).
    assert (H := fg_equal (ACommutes_Inverse A _ _ _ _ h (Identity d)) f).
    simpl in *; autorewrite with category in *.
    auto with category.
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
    eexists (Build_NaturalTransformation (IdentityFunctor C) (ComposeFunctors G F)
                                                    (fun c => A.(AComponentsOf) c (F c) (Identity _))
                                                    _
            ).
    simpl.
    intros c d f.
    exists (proj1_sig (A.(AIsomorphism) c d) f).
    abstract (
        pose proof (proj2_sig (A.(AIsomorphism) c d));
        pose proof (proj3_sig (A.(AIsomorphism) c d));
        simpl in *; fg_equal;
        repeat split; intros; [ | t_with t' ];
        subst;
        repeat rewrite adjunction_naturality, RightIdentity;
        destruct A; simpl in *;
        trivial
      ).
    Grab Existential Variables.
    abstract (
      intros s d m; simpl in *;
        repeat rewrite adjunction_naturality, RightIdentity;
          let H := fresh in assert (H := fg_equal (A.(ACommutes) d (F d) s (F d) m (Identity _)) (Identity _));
            simpl in *;
              autorewrite with category in *;
                auto with category
    ).
  Defined.


  Definition CounitOf (A : HomAdjunction F G) : AdjunctionCounit F G.
    eexists (Build_NaturalTransformation (ComposeFunctors F G) (IdentityFunctor D)
      (fun d => proj1_sig (A.(AIsomorphism) (G d) d) (Identity _))
      _
    ).
    simpl.
    intros c d f.
    exists (A.(AComponentsOf) c d f).
    abstract (
      split; intros; [ | t_with t' ];
      subst;
      repeat rewrite (adjunction_naturality' A), LeftIdentity;
      simpl in *;
        intro_proj2_sig_from_goal;
      destruct_hypotheses; fg_equal; auto with category
      ).
    Grab Existential Variables.
    abstract (
      intros s d m; simpl in *;
        rewrite (adjunction_naturality' A);
          let H := fresh in assert (H := fg_equal (ACommutes_Inverse A (G s) s (G s) d (Identity (G s)) m) (Identity _));
            simpl in *;
              autorewrite with category in *;
                auto with category
    ).
  Defined.

  (** Quoting Wikipedia on Adjoint Functors:

      The naturality of [Φ] implies the naturality of [ε] and [η], and
      the two formulas

      [Φ_{Y,X}(f) = G(f) o η_Y]

      [Φ_{Y,X}⁻¹(g) = ε_X o F(g)]

      for each [f: F Y → X] and [g : Y → G X] (which completely
      determine [Φ]). *)
  Lemma UnitCounitOf_Helper1 (Φ : HomAdjunction F G) (ε := projT1 (CounitOf Φ)) (η := projT1 (UnitOf Φ))
  : forall X Y (f : Morphism _ (F Y) X), Φ Y X f = Compose (G.(MorphismOf) f) (η Y).
    intros.
    destruct Φ as [ ? ? ACommutes'0 ]; simpl in *.
    subst_body.
    pose proof (fg_equal (ACommutes'0 _ _ _ _ (Identity _) f) (Identity _)) as H.
    simpl in *.
    autorewrite with functor morphism in H.
    assumption.
  Qed.

  Lemma UnitCounitOf_Helper2
        (Φ : HomAdjunction F G)
        (ε := projT1 (CounitOf Φ))
        (η := projT1 (UnitOf Φ))
        (Φ_Inverse := fun Y X g => proj1_sig ((AIsomorphism Φ) Y X) g)
  : forall X Y (g : Morphism _ Y (G X)), Φ_Inverse Y X g = Compose (ε X) (F.(MorphismOf) g).
    pose proof (ACommutes_Inverse Φ) as ACommutes_Inverse'.
    destruct Φ as [ ? ? ACommutes'0 ]; simpl in *.
    subst_body.
    simpl in *.
    intros X Y g.
    pose proof (fg_equal (ACommutes_Inverse' _ _ _ _ g (Identity _)) (Identity _)) as H.
    simpl in *.
    autorewrite with functor morphism in H.
    symmetry.
    assumption.
  Qed.

  Local Ltac UnitCounitOf_helper make_H :=
    let H := fresh in
    intro X;
      let HT := constr:(make_H X) in
      pose proof HT as H;
        subst_body;
        symmetry; etransitivity; [ | apply H ];
        destruct_head @HomAdjunction; simpl in *;
        intro_proj2_sig_from_goal;
        fg_equal;
        intuition.

  Definition UnitCounitOf (A : HomAdjunction F G) : AdjunctionUnitCounit F G.
    exists (projT1 (UnitOf A))
           (projT1 (CounitOf A));
    [ abstract UnitCounitOf_helper (fun Y => UnitCounitOf_Helper2 A (F Y) Y (projT1 (UnitOf A)(*η*) Y))
    | abstract UnitCounitOf_helper (fun X => UnitCounitOf_Helper1 A X (G X) (projT1 (CounitOf A)(*ε*) X)) ].
  Defined.
End AdjunctionEquivalences.

Section AdjunctionEquivalences'.
  Variable C : Category.
  Variable D : Category.
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
                auto with morphism
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
    simpl;
    try (intros; exists (fun f => Compose (projT1 T _) (F.(MorphismOf) f)));
        abstract (
          elim T; clear T; intros T s; repeat split; intros; simpl in *;
            apply functional_extensionality_dep; intros; simpl;
              intro_proj2_sig_from_goal;
              unfold unique in *;
                split_and';
              repeat match goal with
                       | [ H : _ |- _ ] => rewrite (H _ (eq_refl _))
                     end;
              auto with morphism;
              repeat match goal with
                       | [ H : _ |- _ ] => apply H
                     end;
              intro_proj2_sig_from_goal;
              destruct_hypotheses;
              repeat rewrite FCompositionOf;
                let H := fresh in assert (H := Commutes T); simpl in H; try_associativity ltac:(rewrite H);
                  repeat try_associativity ltac:(apply f_equal2; trivial)
        ).
  Defined.

  Definition HomAdjunctionOfUnitCounit  (T : AdjunctionUnitCounit F G) : HomAdjunction F G.
    refine {| AComponentsOf' := (fun c d (g : Morphism _ (F c) d) => Compose (G.(MorphismOf) g) (Adjunction_Unit T c)) |};
    [ intros; exists (fun f => Compose (Adjunction_Counit T A') (F.(MorphismOf) f)) | ];
    abstract (
        repeat intro; repeat split; simpl in *; repeat (apply functional_extensionality_dep; intro);
        destruct T;
        repeat rewrite FCompositionOf;
        repeat try_associativity ltac:(apply f_equal2; try reflexivity; []);
        destruct Adjunction_Counit, Adjunction_Unit;
        simpl in *;
        repeat try_associativity ltac:(idtac;
                                       match goal with
                                         | [ H : _ |- _ ] => (rewrite H; clear H; autorewrite with morphism; try reflexivity)
                                         | [ H : _ |- _ ] => (rewrite <- H; clear H; autorewrite with morphism; try reflexivity)
                                       end)
      ).
  Defined.
End AdjunctionEquivalences'.

Coercion HomAdjunction2Adjunction : HomAdjunction >-> Adjunction.
Coercion Adjunction2HomAdjunction : Adjunction >-> HomAdjunction.

Coercion UnitOf : HomAdjunction >-> AdjunctionUnit.
Coercion CounitOf : HomAdjunction >-> AdjunctionCounit.
Coercion UnitCounitOf : HomAdjunction >-> AdjunctionUnitCounit.

Coercion HomAdjunctionOfUnit : AdjunctionUnit >-> HomAdjunction.
Coercion HomAdjunctionOfCounit : AdjunctionCounit >-> HomAdjunction.
Coercion HomAdjunctionOfUnitCounit : AdjunctionUnitCounit >-> HomAdjunction.
