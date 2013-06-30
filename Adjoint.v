Require Import FunctionalExtensionality.
Require Export Category Category Functor NaturalTransformation NaturalEquivalence AdjointUnit.
Require Import Common Hom ProductCategory FunctorProduct Duals.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope functor_scope.

Local Ltac intro_laws_from_inverse :=
  repeat match goal with
           | [ |- appcontext[Inverse ?m] ]
             => unique_pose (LeftInverse m);
               unique_pose (RightInverse m)
         end.

Section Adjunction.
  Context {C : Category}.
  Context {D : Category}.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.
  Let FOp := OppositeFunctor F.

  Let HomCPreFunctor : Functor (COp * D) (COp * C) := IdentityFunctor _ * G.
  Let HomDPreFunctor : Functor (COp * D) (DOp * D) := FOp * IdentityFunctor _.

  Record Adjunction :=
    {
      AMateOf :> NaturalIsomorphism
              (HomFunctor D ∘ HomDPreFunctor)
              (HomFunctor C ∘ HomCPreFunctor)
    }.

  (**
     Quoting the 18.705 Lecture Notes:

     Let [C] and [D] be categories, [F : C -> D] and [G : D -> C]
     functors. We call [(F, G)] an adjoint pair, [F] the left adjoint
     of [G], and [G] the right adjoint of [F] if, for each object [A :
     C] and object [A' : D], there is a natural bijection

     [Hom_D (F A) A' ~= Hom_C A (G A')]

     Here natural means that maps [B -> A] and [A' -> B'] induce a
     commutative diagram:

<<
       Hom_D (F A) A' ~= Hom_C A (G A')
             |                  |
             |                  |
             |                  |
             |                  |
             V                  V
       Hom_D (F B) B' ~= Hom_C B (G B')
>>
     *)

  Local Open Scope morphism_scope.

  Record HomAdjunction :=
    {
      AComponentsOf :> forall A A', Morphism TypeCat (HomFunctor D (F A, A')) (HomFunctor C (A, G A'));
      AIsomorphism : forall A A', IsomorphismOf (C := TypeCat) (@AComponentsOf A A');
      ACommutes : forall A A' B B' (m : C.(Morphism) B A) (m' : D.(Morphism) A' B'),
                    (@AComponentsOf B B')
                      ∘ ((HomFunctor D).(MorphismOf) (s := (F A, A')) (d := (F B, B')) (F.(MorphismOf) m, m'))
                    = ((HomFunctor C).(MorphismOf) (s := (A, G A')) (d := (B, G B')) (m, G.(MorphismOf) m'))
                        ∘ (@AComponentsOf A A')
    }.

  Lemma ACommutes_Inverse (T : HomAdjunction)
  : forall A A' B B' (m : C.(Morphism) B A) (m' : D.(Morphism) A' B'),
      (MorphismOf (HomFunctor D) (s := (F A, A')) (d := (F B, B')) (F.(MorphismOf) m, m'))
        ∘ (Inverse (T.(AIsomorphism) A A'))
      = (Inverse (T.(AIsomorphism) B B'))
          ∘ (MorphismOf (HomFunctor C) (s := (A, G A')) (d := (B, G B')) (m, G.(MorphismOf) m')).
  Proof.
    intros A A' B B' m m'.
    pose proof (ACommutes T A A' B B' m m') as H.
    revert H.
    repeat match goal with
             | [ |- appcontext[Inverse ?x] ] => generalize x
           end.
    repeat match goal with
             | [ |- appcontext[?m] ]
               => match m with
                    | Inverse _ => fail 1
                    | _ => idtac
                  end;
                 match type of m with
                   | Morphism ?C ?x ?y => generalize m; try generalize x y; try generalize C
                 end
           end.
    clear; intros.
    destruct_head @IsomorphismOf.
    subst_body.
    pre_compose_to_identity.
    post_compose_to_identity.
    assumption.
  Qed.
End Adjunction.

Arguments AComponentsOf {C D} [F G] T A A' _ : simpl nomatch, rename.
Arguments AIsomorphism {C D} [F G] T A A' : simpl nomatch, rename.

Section AdjunctionEquivalences.
  Variable C : Category.
  Variable D : Category.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Local Open Scope morphism_scope.

  Definition HomAdjunction2Adjunction_AMateOf (A : HomAdjunction F G)
  : NaturalTransformation (HomFunctor D ∘ (OppositeFunctor F * IdentityFunctor D))
                          (HomFunctor C ∘ (IdentityFunctor (OppositeCategory C) * G)).
    let F := match goal with |- NaturalTransformation ?F ?G => constr:(F) end in
    let G := match goal with |- NaturalTransformation ?F ?G => constr:(G) end in
    refine (Build_NaturalTransformation F G
                                        (fun cd : C * D => A.(AComponentsOf) (fst cd) (snd cd))
                                        _).
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

  Definition HomAdjunction2Adjunction (A : HomAdjunction F G) : Adjunction F G
    := Build_Adjunction (Build_NaturalIsomorphism
                           (HomAdjunction2Adjunction_AMateOf A)
                           (fun x => AIsomorphism A (fst x) (snd x))).

  Definition Adjunction2HomAdjunction (A : Adjunction F G) : HomAdjunction F G
    := Build_HomAdjunction F G
                           (fun c d => ComponentsOf A (c, d))
                           (fun A0 A' => A.(NaturalIsomorphism_Isomorphism) (A0, A'))
                           (fun A0 A' B B' m m' => A.(Commutes) (A0, A') (B, B') (m, m')).

  Lemma adjunction_naturality_pre (A : HomAdjunction F G) c d d' (f : D.(Morphism) (F c) d) (g : D.(Morphism) d d')
  : G.(MorphismOf) g ∘ A.(AComponentsOf) _ _ f
    = A.(AComponentsOf) _ _ (g ∘ f).
  Proof.
    assert (H := fg_equal (A.(ACommutes) _ _ _ _ (Identity c) g) f).
    simpl in *; autorewrite with category in *.
    auto with category.
  Qed.

  Lemma adjunction_naturality'_pre (A : HomAdjunction F G) c' c d (f : C.(Morphism) c (G d)) (h : C.(Morphism) c' c)
  : (Inverse (A.(AIsomorphism) _ _) f) ∘ F.(MorphismOf) h
    = Inverse (A.(AIsomorphism) _ _) (f ∘ h).
  Proof.
    assert (H := fg_equal (ACommutes_Inverse A _ _ _ _ h (Identity d)) f).
    simpl in *; autorewrite with category in *.
    auto with category.
  Qed.

  Section typeof.
    Let typeof {A : Type} (a : A) := A.
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
       [f = G g ∘ η c].
     2. For any [c : C] and [d : D] there is an isomorphism,
       [ϕ : Hom_D (F c, d) ~= Hom_C (c, G d)]
       that is natural in both [c] and [d].
     Moreover, the two conditions are related by the formulas
     [ϕ g = G g ∘ η c]
     [η c = ϕ(1_{F c})]
     *)
  Definition UnitOf (A : HomAdjunction F G) : AdjunctionUnit F G.
    eexists (Build_NaturalTransformation (IdentityFunctor C) (G ∘ F)
                                         (fun c => A.(AComponentsOf) c (F c) (Identity _))
                                         _).
    simpl.
    intros c d f.
    exists (Inverse (A.(AIsomorphism) c d) f).
    abstract (
        pose proof (proj2_sig (A.(AIsomorphism) c d));
        pose proof (proj3_sig (A.(AIsomorphism) c d));
        simpl in *; fg_equal;
        repeat split; intros; [ | t_with t' ];
        subst;
        repeat rewrite adjunction_naturality, RightIdentity;
        destruct A;
        simpl in *;
          trivial
      ).
    Grab Existential Variables.
    abstract (
        intros s d m;
        simpl in *;
          repeat rewrite adjunction_naturality, RightIdentity;
        let H := fresh in assert (H := fg_equal (A.(ACommutes) d (F d) s (F d) m (Identity _)) (Identity _));
        simpl in *;
          autorewrite with category in *;
          auto with category
      ).
  Defined.


  Definition CounitOf (A : HomAdjunction F G) : AdjunctionCounit F G.
    eexists (Build_NaturalTransformation (F ∘ G) (IdentityFunctor D)
                                         (fun d => Inverse (A.(AIsomorphism) (G d) d) (Identity _))
                                         _).
    simpl.
    intros c d f.
    exists (A.(AComponentsOf) c d f).
    abstract (
        pose proof (proj2_sig (A.(AIsomorphism) c d));
        pose proof (proj3_sig (A.(AIsomorphism) c d));
        split; intros; [ | t_with t' ];
        subst;
        repeat rewrite (adjunction_naturality' A), LeftIdentity;
        simpl in *;
        destruct_hypotheses; fg_equal; auto with category
      ).
    Grab Existential Variables.
    abstract (
        intros s d m;
        simpl in *;
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
  : forall X Y (f : Morphism _ (F Y) X), Φ Y X f = G.(MorphismOf) f ∘ η Y.
  Proof.
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
        (Φ_Inverse := fun Y X g => Inverse ((AIsomorphism Φ) Y X) g)
  : forall X Y (g : Morphism _ Y (G X)), Φ_Inverse Y X g = ε X ∘ F.(MorphismOf) g.
  Proof.
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
      pose proof HT as H; simpl in H;
      symmetry; etransitivity; [ | apply H ];
      destruct_head @HomAdjunction;
      intro_laws_from_inverse;
      simpl in *;
      (* fg_equal; *)
      repeat match goal with
               | [ H : _ |- _ ] => pose proof (fun x => equal_f H x); clear H; simpl in *
               | [ ACommutes0 : _ |- _ ] => pose proof (fun A A' B B' m m' x => equal_f (ACommutes0 A A' B B' m m') x);
                                           simpl in *;
                                           clear ACommutes0
             end;
      rewrite_hyp;
      reflexivity.

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

  Local Open Scope morphism_scope.

  Definition HomAdjunctionOfUnit (T : AdjunctionUnit F G) : HomAdjunction F G.
    refine {| AComponentsOf := (fun c d (g : Morphism _ (F c) d) => G.(MorphismOf) g ∘ projT1 T c) |};
    [ intros; exists (fun f => proj1_sig (projT2 T _ _ f))
    | abstract (
          repeat (intro || apply functional_extensionality_dep);
          destruct T as [ T s ];
          simpl;
          rewrite ?FCompositionOf, ?Associativity;
          simpl_do do_rewrite_rev (Commutes T); reflexivity
    ) ];
    abstract (
        repeat (intro || apply functional_extensionality_dep); simpl;
        intro_proj2_sig_from_goal;
        destruct T as [ T s ];
        destruct_hypotheses;
        simpl in *;
          auto with morphism
      ).
  Defined.

  Definition HomAdjunctionOfCounit (T : AdjunctionCounit F G) : HomAdjunction F G.
    refine {| AComponentsOf := (fun c d (g : Morphism _ (F c) d) =>
                                  let inverseOf := (fun s d f => proj1_sig (projT2 T s d f)) in
                                  let f := inverseOf _ _ g in
                                  let AComponentsOf_Inverse := projT1 T d ∘ F.(MorphismOf) f in
                                  inverseOf _ _ AComponentsOf_Inverse
                               )
           |};
    simpl;
    try (intros; exists (fun f => projT1 T _ ∘ F.(MorphismOf) f));
    abstract (
        elim T; clear T; intros T s; repeat split; intros;
        simpl in *;
          apply functional_extensionality_dep; intros; simpl;
        intro_proj2_sig_from_goal;
        unfold unique in *;
          split_and';
        repeat match goal with
                 | [ H : _ |- _ ] => rewrite (H _ (eq_refl _))
               end;
        auto with morphism;
        repeat apply_hyp;
        intro_proj2_sig_from_goal;
        destruct_hypotheses;
        rewrite ?FCompositionOf;
        let H := fresh in
        assert (H := Commutes T); simpl in H; try_associativity ltac:(rewrite H);
        repeat try_associativity ltac:(apply f_equal2; trivial)
      ).
  Defined.

  Definition HomAdjunctionOfUnitCounit  (T : AdjunctionUnitCounit F G) : HomAdjunction F G.
    refine {| AComponentsOf := (fun c d (g : Morphism _ (F c) d) => G.(MorphismOf) g ∘ Adjunction_Unit T c) |};
    [ intros; exists (fun f => Adjunction_Counit T A' ∘ F.(MorphismOf) f) | ];
    abstract (
        repeat intro; repeat split; simpl in *; repeat (apply functional_extensionality_dep; intro);
        destruct T;
        rewrite ?FCompositionOf;
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
