Require Import SpecializedCategory Functor NaturalTransformation.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section SimplifiedMorphism.
  Inductive ReifiedMorphism : forall objC (C : SpecializedCategory objC), C -> C -> Type :=
  | ReifiedIdentityMorphism : forall objC C x, @ReifiedMorphism objC C x x
  | ReifiedComposedMorphism : forall objC C s d d', ReifiedMorphism C d d' -> ReifiedMorphism C s d -> @ReifiedMorphism objC C s d'
  | ReifiedNaturalTransformationMorphism : forall objB (B : SpecializedCategory objB)
                                                  objC (C : SpecializedCategory objC)
                                                  (F G : SpecializedFunctor B C)
                                                  (T : SpecializedNaturalTransformation F G)
                                                  x,
                                             ReifiedMorphism C (F x) (G x)
  | ReifiedFunctorMorphism : forall objB (B : SpecializedCategory objB)
                                    objC (C : SpecializedCategory objC)
                                    (F : SpecializedFunctor B C)
                                    s d,
                               @ReifiedMorphism objB B s d -> @ReifiedMorphism objC C (F s) (F d)
  | ReifiedGenericMorphism : forall objC (C : SpecializedCategory objC) s d, Morphism C s d -> @ReifiedMorphism objC C s d.

  Fixpoint ReifiedMorphismSimplify objC C s d (m : @ReifiedMorphism objC C s d) : ReifiedMorphism C s d
    := match
        m in (ReifiedMorphism C s d) return (ReifiedMorphism C s d)
      with
        | ReifiedComposedMorphism _ _ _ _ _ m1 m2 =>
          match
            ReifiedMorphismSimplify m1
            in (ReifiedMorphism C d d')
            return
            (forall s,
               ReifiedMorphism C s d -> ReifiedMorphism C s d')
          with
            | ReifiedIdentityMorphism _ _ _ => fun _ m2' => m2'
            | m1' => fun _ m2' => match m2'
                                        in (ReifiedMorphism C s d)
                                        return (forall d',
                                                  ReifiedMorphism C d d' -> ReifiedMorphism C s d')
                                  with
                                    | ReifiedIdentityMorphism _ _ _ => fun _ m1'' => m1''
                                    | m2'' => fun _ m1'' => ReifiedComposedMorphism m1'' m2''
                                  end _ m1'
          end _ (ReifiedMorphismSimplify m2)
        | ReifiedFunctorMorphism objB B objC0 C0 F s0 d0 m0 =>
          match
            ReifiedMorphismSimplify m0
            in (ReifiedMorphism C1 o o0)
            return
            (forall F0 : SpecializedFunctor C1 C0,
               ReifiedMorphism C0 (F0 o) (F0 o0))
          with
            | ReifiedIdentityMorphism _ _ x =>
              fun F0 => ReifiedIdentityMorphism _ (F0 x)
            | ReifiedComposedMorphism _ _ _ _ _ m11 m12 =>
              fun F0 =>
                ReifiedComposedMorphism (ReifiedFunctorMorphism F0 m11)
                                        (ReifiedFunctorMorphism F0 m12)
            | m' =>
              fun F0 =>
                ReifiedFunctorMorphism F0 m'
          end F
        | m' => m'
  end.

  Fixpoint ReifiedMorphismDenote objC C s d (m : @ReifiedMorphism objC C s d) : Morphism C s d :=
    match m in @ReifiedMorphism objC C s d return Morphism C s d with
      | ReifiedIdentityMorphism _ _ x => Identity x
      | ReifiedComposedMorphism _ _ _ _ _ m1 m2 => Compose (@ReifiedMorphismDenote _ _ _ _ m1)
                                                           (@ReifiedMorphismDenote _ _ _ _ m2)
      | ReifiedNaturalTransformationMorphism _ _ _ _ _ _ T x => T x
      | ReifiedFunctorMorphism _ _ _ _ F _ _ m => MorphismOf F (@ReifiedMorphismDenote _ _ _ _ m)
      | ReifiedGenericMorphism _ _ _ _ m => m
    end.

(*  Fixpoint ReifiedMorphismSimplify' objC C s d (m : @ReifiedMorphism objC C s d)
  : { sm : ReifiedMorphism C s d | ReifiedMorphismDenote m = ReifiedMorphismDenote sm }.
  refine (match m
                as r
                in (ReifiedMorphism C s d)
                return { sm : ReifiedMorphism C s d | ReifiedMorphismDenote r = ReifiedMorphismDenote sm }
          with
            | ReifiedComposedMorphism _ _ _ _ _ m1 m2 =>
              let (m1', H1) := ReifiedMorphismSimplify' _ _ _ _ m1 in
              match
                m1' as r in (ReifiedMorphism C1 o o0)
                return
                (forall (s2 : C1) (m3 : ReifiedMorphism C1 o o0)
                        (m4 : ReifiedMorphism C1 s2 o),
                   ReifiedMorphismDenote m3 = ReifiedMorphismDenote r ->
                   {sm : ReifiedMorphism C1 s2 o0 |
                    ReifiedMorphismDenote (ReifiedComposedMorphism m3 m4) =
                    ReifiedMorphismDenote sm})
              with
                | ReifiedIdentityMorphism objC1 C1 x =>
                  fun _ _ m2' _ =>
                    exist _ m2' _
                | m1'' => fun _ m1''' m2''' H1 => _
              end _ m1 m2 H1
            | ReifiedFunctorMorphism objB B objC C F s0 d0 m0 =>
              let (m0', H) := ReifiedMorphismSimplify' _ _ _ _ m0 in
              match
                m0' as r in (ReifiedMorphism B o o0)
                return
                (forall (F0 : SpecializedFunctor B C)
                        (m1 : ReifiedMorphism B o o0),
                   ReifiedMorphismDenote m1 = ReifiedMorphismDenote r ->
                   {sm : ReifiedMorphism C (F0 o) (F0 o0) |
                    ReifiedMorphismDenote (ReifiedFunctorMorphism F0 m1) =
                    ReifiedMorphismDenote sm})
              with
                | ReifiedIdentityMorphism objC1 C1 x =>
                  fun _ _ _ => exist _ (ReifiedIdentityMorphism _ _) _
                | ReifiedComposedMorphism objC1 C1 s2 d1 d' m0'1 m0'2 =>
                  fun F0 _ _ => exist _ (ReifiedComposedMorphism (ReifiedFunctorMorphism F0 m0'1)
                                                                 (ReifiedFunctorMorphism F0 m0'2)) _
                | m0'' =>
                  fun _ _ _ => exist _ (ReifiedFunctorMorphism _ m0'') _
              end F m0 H
            | m' => exist _ m' eq_refl
          end);
    try abstract (
          simpl;
          repeat match goal with
                   | [ H : _ |- _ ] => rewrite H
                 end;
          simpl;
          repeat rewrite FCompositionOf;
          repeat rewrite Associativity;
          autorewrite with category;
          try reflexivity
        ).
  destruct (ReifiedMorphismSimplify'  _ _ _ _ m2''') as [ m2'''' H2'''' ].
  destruct m2''''.
  exists m1'''.
  simpl.
  Show Proof.

  exists (Reified
  destruct (ReifiedMorphismSimplify' _ _ _ _ m0) as [ m0' H ].
  destruct m0'.
  Show Proof.
    := match
        m in (ReifiedMorphism C s d) return (ReifiedMorphism C s d)
      with
        | ReifiedComposedMorphism _ _ _ _ _ m1 m2 =>
          match
            ReifiedMorphismSimplify m1
            in (ReifiedMorphism C d d')
            return
            (forall s,
               ReifiedMorphism C s d -> ReifiedMorphism C s d')
          with
            | ReifiedIdentityMorphism _ _ _ => fun _ m2' => m2'
            | m1' => fun _ m2' => match m2'
                                        in (ReifiedMorphism C s d)
                                        return (forall d',
                                                  ReifiedMorphism C d d' -> ReifiedMorphism C s d')
                                  with
                                    | ReifiedIdentityMorphism _ _ _ => fun _ m1'' => m1''
                                    | m2'' => fun _ m1'' => ReifiedComposedMorphism m1'' m2''
                                  end _ m1'
          end _ (ReifiedMorphismSimplify m2)
        | ReifiedFunctorMorphism objB B objC0 C0 F s0 d0 m0 =>
          match
            ReifiedMorphismSimplify m0
            in (ReifiedMorphism C1 o o0)
            return
            (forall F0 : SpecializedFunctor C1 C0,
               ReifiedMorphism C0 (F0 o) (F0 o0))
          with
            | ReifiedIdentityMorphism _ _ x =>
              fun F0 => ReifiedIdentityMorphism _ (F0 x)
            | ReifiedComposedMorphism _ _ _ _ _ m11 m12 =>
              fun F0 =>
                ReifiedComposedMorphism (ReifiedFunctorMorphism F0 m11)
                                        (ReifiedFunctorMorphism F0 m12)
            | m' =>
              fun F0 =>
                ReifiedFunctorMorphism F0 m'
          end F
        | m' => m'
  end.
*)

  Local Ltac ok_fin_t :=
    simpl;
    repeat rewrite Associativity;
    repeat rewrite FCompositionOf;
    autorewrite with category;
    try reflexivity.

  Lemma ReifiedMorphismSimplifyOk objC C s d (m : @ReifiedMorphism objC C s d)
  : ReifiedMorphismDenote m =
    ReifiedMorphismDenote (ReifiedMorphismSimplify m).
    induction m;
    repeat match goal with
             | _ => progress ok_fin_t
             | [ IH : ReifiedMorphismDenote _ = _ |- _ ] => rewrite IH; clear IH
             | [ |- context[ReifiedMorphismSimplify ?m] ] =>
               let H := fresh in
               set (H := ReifiedMorphismSimplify m);
                 clearbody H;
                 destruct H
             | [ |- context[match ReifiedMorphismSimplify ?m with _ => _ end _ ?m'] ] =>
               (* simply destructing H didn't work, so we need to be more tricky *)
               let H := fresh in
               set (H := ReifiedMorphismSimplify m);
                 clearbody H;
                 match type of H with
                   | ReifiedMorphism _ ?A ?B =>
                     let FH := fresh in
                     let H2 := fresh in
                     (* save the troublesome term, so we can [clearbody] it *)
                     set (FH := m');
                       let FH' := (eval simpl in (ReifiedMorphismDenote FH)) in
                       (* save the value of the term *)
                       assert (H2 : ReifiedMorphismDenote FH = FH') by reflexivity;
                         (* the denoted version shows up, so rewrite with it *)
                         rewrite <- H2;
                         clear H2;
                         clearbody FH;
                         simpl in *;
                         set (A' := A) in *;
                         set (B' := B) in *;
                         clearbody A' B';
                         destruct H
                 end
           end.
  Qed.

  Section single_category.
    Context `{C : SpecializedCategory objC}.

    Class SimplifiedMorphism {s d} (m : Morphism C s d) :=
      SimplifyMorphism { reified_morphism : ReifiedMorphism C s d;
                         reified_morphism_ok : m = ReifiedMorphismDenote reified_morphism }.

    Lemma SimplifyReifiyMorphismOk `(@SimplifiedMorphism s d m)
    : m
      = ReifiedMorphismDenote (ReifiedMorphismSimplify (reified_morphism (m := m))).
      rewrite <- ReifiedMorphismSimplifyOk.
      rewrite <- reified_morphism_ok.
      reflexivity.
    Qed.

    Global Instance unchanged_morphism s d (m : Morphism C s d) : SimplifiedMorphism m | 1000
      := SimplifyMorphism (m := m) (ReifiedGenericMorphism C s d m) eq_refl.

    Global Instance identity_morphism x : SimplifiedMorphism (Identity x) | 10
      := SimplifyMorphism (m := Identity x) (ReifiedIdentityMorphism C x) eq_refl.

    Global Instance composition_morphism s d d'
           `(@SimplifiedMorphism d d' m1) `(@SimplifiedMorphism s d m2)
    : SimplifiedMorphism (Compose m1 m2) | 10
      := SimplifyMorphism (m := Compose m1 m2)
                          (ReifiedComposedMorphism (reified_morphism (m := m1))
                                                   (reified_morphism (m := m2)))
                          (f_equal2 _
                                    reified_morphism_ok
                                    reified_morphism_ok).
  End single_category.

  Section functor.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.
    Variable F : SpecializedFunctor C D.

    Global Instance functor_morphism `(@SimplifiedMorphism objC C s d m)
    : SimplifiedMorphism (MorphismOf F m) | 50
      := SimplifyMorphism (m := MorphismOf F m)
                          (ReifiedFunctorMorphism F (reified_morphism (m := m)))
                          (f_equal _ reified_morphism_ok).
  End functor.

  Section natural_transformation.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.
    Variables F G : SpecializedFunctor C D.
    Variable T : SpecializedNaturalTransformation F G.

    Global Instance nt_morphism x
    : SimplifiedMorphism (T x) | 50
      := SimplifyMorphism (m := T x) (ReifiedNaturalTransformationMorphism T x) eq_refl.
  End natural_transformation.
End SimplifiedMorphism.

Ltac rsimplify_morphisms :=
  match goal with
    | [ |- @eq (Morphism _ _ _) ?A ?B ] =>
      erewrite (SimplifyReifiyMorphismOk (m := A));
        erewrite (SimplifyReifiyMorphismOk (m := B))
    | _ => erewrite SimplifyReifiyMorphismOk
  end;
  simpl.

(* ******************** non-reified version, which is slower ********* *)
(*

Section SimplifiedMorphism.
  Section single_category.
    Context `{C : SpecializedCategory objC}.

    Class SimplifiedMorphism {s d} (m : Morphism C s d) :=
      { SimplifiedMorphismValue : Morphism C s d;
        SimplifiedMorphismOk : m = SimplifiedMorphismValue }.

    Local Ltac t := repeat rewrite <- SimplifiedMorphismOk; autorewrite with category; try reflexivity.

    Global Instance UnchangedMorphism s d (m : Morphism C s d) : SimplifiedMorphism m | 1000 :=
      {| SimplifiedMorphismValue := m;
         SimplifiedMorphismOk := eq_refl |}.

    Global Instance SimplifyLeftIdentity `(SimplifiedMorphism s d m) : SimplifiedMorphism (Compose (Identity _) m) | 10
      := {| SimplifiedMorphismValue := SimplifiedMorphismValue (m := m) |}.
    Proof. abstract t. Defined.

    Global Instance SimplifyRightIdentity `(SimplifiedMorphism s d m) : SimplifiedMorphism (Compose m (Identity _)) | 10
      := {| SimplifiedMorphismValue := SimplifiedMorphismValue (m := m) |}.
    Proof. abstract t. Defined.

    Global Instance SimplifyComposition `(SimplifiedMorphism d d' m1) `(SimplifiedMorphism s d m2)
    : SimplifiedMorphism (Compose m1 m2) | 50
      := {| SimplifiedMorphismValue := Compose (SimplifiedMorphismValue (m := m1)) (SimplifiedMorphismValue (m := m2)) |}.
    Proof. abstract t. Defined.

    Definition NormalizeLeftAssociativity `(SimplifiedMorphism s d m1) `(SimplifiedMorphism d d' m2) `(SimplifiedMorphism d' d'' m3)
    : SimplifiedMorphism (Compose m3 (Compose m2 m1)).
      refine {| SimplifiedMorphismValue := (Compose (Compose (SimplifiedMorphismValue (m := m3)) (SimplifiedMorphismValue (m := m2)))
                                                    (SimplifiedMorphismValue (m := m1))) |}.
      abstract t.
    Defined.

    Definition NormalizeRightAssociativity `(SimplifiedMorphism s d m1) `(SimplifiedMorphism d d' m2) `(SimplifiedMorphism d' d'' m3)
    : SimplifiedMorphism (Compose (Compose m3 m2) m1).
      refine {| SimplifiedMorphismValue := (Compose (SimplifiedMorphismValue (m := m3))
                                                    (Compose (SimplifiedMorphismValue (m := m2))
                                                             (SimplifiedMorphismValue (m := m1)))) |}.
      abstract t.
    Defined.
  End single_category.

  Local Ltac t := repeat rewrite <- SimplifiedMorphismOk;
                 repeat rewrite Associativity;
                 repeat rewrite FCompositionOf;
                 repeat rewrite Commutes;
                 autorewrite with category; try reflexivity.

  Section functor.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.
    Variable F : SpecializedFunctor C D.

    Global Instance SimplifyFIdentityOf x : SimplifiedMorphism (MorphismOf F (Identity x)) | 5
      := {| SimplifiedMorphismValue := Identity (F x) |}.
    Proof. abstract t. Defined.

    Definition NormalizeFCompositionOfRight `(SimplifiedMorphism objC C d d' m1) `(SimplifiedMorphism objC C s d m2)
    : SimplifiedMorphism (MorphismOf F (Compose m1 m2)).
      refine {| SimplifiedMorphismValue := Compose (MorphismOf F (SimplifiedMorphismValue (m := m1)))
                                                   (MorphismOf F (SimplifiedMorphismValue (m := m2))) |}.
      abstract t. Defined.

    Definition NormalizeFCompositionOfLeft `(SimplifiedMorphism objC C d d' m1) `(SimplifiedMorphism objC C s d m2)
    : SimplifiedMorphism (Compose (MorphismOf F m1) (MorphismOf F m2)).
      refine {| SimplifiedMorphismValue := MorphismOf F (Compose (SimplifiedMorphismValue (m := m1))
                                                                 (SimplifiedMorphismValue (m := m2))) |}.
      abstract t. Defined.

    Global Instance SimplifyFunctorOf `(@SimplifiedMorphism objC C s d m) : SimplifiedMorphism (MorphismOf F m) | 500
      := {| SimplifiedMorphismValue := MorphismOf F (SimplifiedMorphismValue (m := m)) |}.
    Proof. abstract t. Defined.
  End functor.

  Section natural_transformation.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.
    Variables F G : SpecializedFunctor C D.
    Variable T : SpecializedNaturalTransformation F G.

    Global Instance SimplifyNTOf x : SimplifiedMorphism (T x) | 500
      := {| SimplifiedMorphismValue := T x;
            SimplifiedMorphismOk := eq_refl |}.

    Definition NormalizeTCommutesRight `(SimplifiedMorphism objC C s d m)
    : SimplifiedMorphism (Compose (T d) (MorphismOf F m)).
      refine {| SimplifiedMorphismValue := SimplifiedMorphismValue (m := Compose (MorphismOf G m) (T s)) |}.
      abstract t. Defined.

    Definition NormalizeTCommutesLeft `(SimplifiedMorphism objC C s d m)
    : SimplifiedMorphism (Compose (MorphismOf G m) (T s)).
      refine {| SimplifiedMorphismValue := SimplifiedMorphismValue (m := Compose (T d) (MorphismOf F m)) |}.
      abstract t. Defined.
  End natural_transformation.
End SimplifiedMorphism.
(*
Inductive SimpleMorphism objC (C : SpecializedCategory objC) : C -> C -> Type :=
    | SimpleIdentityMorphism : forall x, SimpleMorphism C x x
    | SimpleComposedMorphism : forall s d d', SimpleMorphism C d d' -> SimpleMorphism C s d -> SimpleMorphism C s d'
    | SimpleNaturalTransformationMorphism : forall objB (B : SpecializedCategory objB)
                                                   (F G : SpecializedFunctor B C)
                                                   (T : SpecializedNaturalTransformation F G)
                                                   x,
                                              SimpleMorphism C (F x) (G x)
    | SimpleGenericMorphism : forall s d, Morphism C s d -> SimpleMorphism C s d.
    Inductive ComplicatedMorphism : forall objC (C : SpecializedCategory objC), C -> C -> Type :=
    | ComplicatedIdentityMorphism : forall objC C x, @ComplicatedMorphism objC C x x
    | ComplicatedComposedMorphism : forall objC C s d d', ComplicatedMorphism C d d' -> ComplicatedMorphism C s d -> @ComplicatedMorphism objC C s d'
    | ComplicatedNaturalTransformationMorphism : forall objB (B : SpecializedCategory objB)
                                                        objC (C : SpecializedCategory objC)
                                                        (F G : SpecializedFunctor B C)
                                                        (T : SpecializedNaturalTransformation F G)
                                                        x,
                                                   ComplicatedMorphism C (F x) (G x)
    | ComplicatedFunctorMorphism : forall objB (B : SpecializedCategory objB)
                                          objC (C : SpecializedCategory objC)
                                          (F : SpecializedFunctor B C)
                                          s d,
                                     @ComplicatedMorphism objB B s d -> @ComplicatedMorphism objC C (F s) (F d)
    | ComplicatedGenericMorphism : forall objC (C : SpecializedCategory objC) s d, Morphism C s d -> @ComplicatedMorphism objC C s d.

    Fixpoint ComplicatedMorphismDenote objC C s d (m : @ComplicatedMorphism objC C s d) : Morphism C s d :=
      match m in @ComplicatedMorphism objC C s d return Morphism C s d with
        | ComplicatedIdentityMorphism _ _ x => Identity x
        | ComplicatedComposedMorphism _ _ _ _ _ m1 m2 => Compose (@ComplicatedMorphismDenote _ _ _ _ m1)
                                                                 (@ComplicatedMorphismDenote _ _ _ _ m2)
        | ComplicatedNaturalTransformationMorphism _ _ _ _ _ _ T x => T x
        | ComplicatedFunctorMorphism _ _ _ _ F _ _ m => MorphismOf F (@ComplicatedMorphismDenote _ _ _ _ m)
        | ComplicatedGenericMorphism _ _ _ _ m => m
      end.

    Fixpoint ComplicatedMorphismSimplify0 objC C s d (m : @ComplicatedMorphism objC C s d) : ComplicatedMorphism C s d.
    refine (match m in @ComplicatedMorphism objC C s d return @ComplicatedMorphism objC C s d with
              | ComplicatedComposedMorphism objC C _ _ d m1 m2 => _
              | ComplicatedIdentityMorphism _ _ x => ComplicatedIdentityMorphism _ x
              (*| ComplicatedComposedMorphism _ _ _ _ _ m1 m2 => ComplicatedComposedMorphism m1 m2*)
              | ComplicatedNaturalTransformationMorphism _ _ _ _ _ _ T x => ComplicatedNaturalTransformationMorphism T x
              | ComplicatedFunctorMorphism _ _ _ _ F _ _ m => ComplicatedFunctorMorphism F m
              | ComplicatedGenericMorphism _ _ _ _ m => ComplicatedGenericMorphism _ _ _ m
            end).
    Fixpoint ComplicatedMorphismSimplify0 objC C s d (m : @ComplicatedMorphism objC C s d) : ComplicatedMorphism C s d.
    refine (match m in @ComplicatedMorphism objC C s d return @ComplicatedMorphism objC C s d with
              | ComplicatedComposedMorphism objC C _ _ d m1 m2 => _
              | ComplicatedIdentityMorphism _ _ x => ComplicatedIdentityMorphism _ x
              (*| ComplicatedComposedMorphism _ _ _ _ _ m1 m2 => ComplicatedComposedMorphism m1 m2*)
              | ComplicatedNaturalTransformationMorphism _ _ _ _ _ _ T x => ComplicatedNaturalTransformationMorphism T x
              | ComplicatedFunctorMorphism _ _ _ _ F _ _ m => ComplicatedFunctorMorphism F m
              | ComplicatedGenericMorphism _ _ _ _ m => ComplicatedGenericMorphism _ _ _ m
            end).
    refine (match (@ComplicatedMorphismSimplify _ _ _ _ m1, @ComplicatedMorphismSimplify _ _ _ _ m2) with
              | (ComplicatedIdentityMorphism _ _ x, m2') => _
              | _ => _
            end).
              | ComplicatedComposedMorphism objC C _ _ d m1 m2 => _
              | ComplicatedIdentityMorphism _ _ x => ComplicatedIdentityMorphism _ x
              (*| ComplicatedComposedMorphism _ _ _ _ _ m1 m2 => ComplicatedComposedMorphism m1 m2*)
              | ComplicatedNaturalTransformationMorphism _ _ _ _ _ _ T x => ComplicatedNaturalTransformationMorphism T x
              | ComplicatedFunctorMorphism _ _ _ _ F _ _ m => ComplicatedFunctorMorphism F m
              | ComplicatedGenericMorphism _ _ _ _ m => ComplicatedGenericMorphism _ _ _ m
            end).
*)
*)
