Require Import SpecializedCategory Functor NaturalTransformation.

Set Implicit Arguments.

Generalizable All Variables.

(*
Require Import Setoid.
Set Implicit Arguments.
Generalizable All Variables.

(* the reification datatype and *)
(* denotation and simplification functions *)

Structure reified :=
  RT | RF | RAnd : reified -> reified -> reified | RProp : Prop -> reified.

Fixpoint denote r :=
  match r with
      RT => True
    | RF => False
    | RAnd a b => denote a /\ denote b
    | RProp p => p
  end.

Fixpoint simplify_and r1 r2 :=
  match r1, r2 with
      RT, r2' => r2'
    | RF, _ => RF
    | r1', RT => r1'
    | _, RF => RF
    | r1', r2' => RAnd r1' r2'
  end.

Fixpoint simplify r :=
  match r with
      RT => RT
    | RF => RF
    | RAnd r1 r2 => simplify_and (simplify r1) (simplify r2)
    | RProp p => RProp p
  end.

Lemma simplify_and_sound r1 r2 :
  denote (RAnd r1 r2) <-> denote (simplify_and r1 r2).
Proof. case r1, r2; simpl; intuition. Qed.

Lemma simplify_sound r : denote r <-> denote (simplify r).
Proof.
  induction r; simpl; intuition;
  try rewrite <- simplify_and_sound in *; simpl in *; intuition.
Qed.

(* structure for packaging a prop and its reification *)

Structure reify := Reify {
                       prop_of :> Prop;
                       reified_of : reified;
                       _ : prop_of <-> denote reified_of}.

(* main overloaded lemma for simplification *)
(* when this lemma is applied to a proposition, it will *)
(* scan over it, trying to build the canonical instance r *)
(* thus obtaining the reified version of the proposition *)
(* then the reified version is simplifed, thus replacing the *)
(* old proposition with a simpler, but equivalent form. *)

Lemma rsimpl (r : reify) :
  r <-> denote (simplify (reified_of r)).
Proof.
  induction r; simpl in *; intuition;
  rewrite <- simplify_sound in *; intuition.
Qed.

(* canonical instances reifying each propositional constructor *)
(* into a respective value from reified *)

Lemma reifyTrueAx : True <-> denote RT. Proof. tauto. Qed.
Canonical Structure reifyTrue := Reify _ reifyTrueAx.

Lemma reifyFalseAx : False <-> denote RF. Proof. tauto. Qed.
Canonical Structure reifyFalse := Reify _ reifyFalseAx.

Lemma reifyAndAx (r1 r2 : reify) :
  r1 /\ r2 <-> denote (RAnd (reified_of r1) (reified_of r2)).
Proof.
  induction r1, r2; simpl in *; intuition.
Qed.

Canonical Structure reifyAnd r1 r2 := Reify _ (reifyAndAx r1 r2).

(* default case, when no other propositional constructors match *)

Lemma reifyPropAx P : P <-> denote (RProp P). Proof. tauto. Qed.
Canonical Structure reifyProp P := Reify _ (reifyPropAx P).

(* example *)

Example xx : True /\ (1 = 1) <-> True.
Proof.
  split; intro;
  rewrite rsimpl.
  simpl.
  constructor.
  simpl.
  constructor.
Qed.
*)
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

    (* structure for packaging a morphism and its reification *)

    Structure SimplifiedMorphism s d :=
      ReifyMorphism
        {
          morphism_of : Morphism C s d;
          reified_morphism_of : ReifiedMorphism C s d;
          reified_morphism_ok : morphism_of = ReifiedMorphismDenote reified_morphism_of
        }.

    (* main overloaded lemma for simplification *)

    Lemma rsimplify_morphisms `(r : SimplifiedMorphism s d)
    : morphism_of r = ReifiedMorphismDenote (ReifiedMorphismSimplify (reified_morphism_of r)).
      rewrite <- ReifiedMorphismSimplifyOk.
      destruct r; assumption.
    Qed.

    (* tags to control the order of application *)

    Definition generic_ReifyMorphism s d a b c := @ReifyMorphism s d a b c.
    Definition functor_ReifyMorphism s d a b c := @generic_ReifyMorphism s d a b c.
    Definition nt_ReifyMorphism s d a b c := @functor_ReifyMorphism s d a b c.
    Definition compose_ReifyMorphism s d a b c := @nt_ReifyMorphism s d a b c.
    Definition identity_ReifyMorphism s d a b c := @compose_ReifyMorphism s d a b c.
  End single_category.

  (* canonical instances reifying each propositional constructor *)
  (* into a respective value from reified *)

  Local Ltac t := simpl;
                 repeat rewrite <- reified_morphism_ok;
                 reflexivity.

  Section generic.
    Context `{C : SpecializedCategory objC}.

    Lemma reifyGeneric s d (m : Morphism C s d) : m = ReifiedMorphismDenote (ReifiedGenericMorphism C s d m). reflexivity. Qed.
    Canonical Structure reify_generic_morphism s d m := generic_ReifyMorphism _ (@reifyGeneric s d m).
  End generic.

  Section more_single_category.
    Context `{C : SpecializedCategory objC}.

    Global Opaque Identity'.
    Lemma reifyIdentity x : Identity' C x = ReifiedMorphismDenote (ReifiedIdentityMorphism C x). reflexivity. Qed.
    Canonical Structure reify_identity_morphism x := identity_ReifyMorphism _ (reifyIdentity x).

    Global Opaque Compose'.
    Lemma reifyCompose s d d'
          `(m1' : @SimplifiedMorphism objC C d d') `(m2' : @SimplifiedMorphism objC C s d)
    : Compose' C s d d' (morphism_of m1') (morphism_of m2')
      = ReifiedMorphismDenote (ReifiedComposedMorphism (reified_morphism_of m1') (reified_morphism_of m2')).
      t.
    Qed.
    Canonical Structure reify_composition_morphism s d d' m1' m2' := compose_ReifyMorphism _ (@reifyCompose s d d' m1' m2').
  End more_single_category.

  Section functor.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.
    Variable F : SpecializedFunctor C D.

    Global Opaque MorphismOf'.
    Lemma reifyFunctor `(m' : @SimplifiedMorphism objC C s d)
    : MorphismOf' F _ _ (morphism_of m') = ReifiedMorphismDenote (ReifiedFunctorMorphism F (reified_morphism_of m')).
      t.
    Qed.
    Canonical Structure reify_functor_morphism s d m' := functor_ReifyMorphism _ (@reifyFunctor s d m').
  End functor.

  Section natural_transformation.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.
    Variables F G : SpecializedFunctor C D.
    Variable T : SpecializedNaturalTransformation F G.

    Global Opaque ComponentsOf'.
    Lemma reifyNT (x : C) : ComponentsOf' T x = ReifiedMorphismDenote (ReifiedNaturalTransformationMorphism T x). reflexivity. Qed.
    Canonical Structure reify_nt_morphism x := nt_ReifyMorphism _ (@reifyNT x).
  End natural_transformation.
End SimplifiedMorphism.

Ltac rsimplify_morphisms :=
  change @Identity with @Identity';
  change @MorphismOf with @MorphismOf';
  change @Compose with @Compose';
  change @ComponentsOf with @ComponentsOf';
  change @ObjectOf with @ObjectOf';
  simpl;
  etransitivity; [ apply rsimplify_morphisms | ];
  etransitivity; [ | symmetry; apply rsimplify_morphisms ];
  instantiate;
  simpl;
  present_spnt.


(**************** example **********************)
Require Export Adjoint.
Require Import Notations Common FunctorCategoryFunctorial Duals.

Set Implicit Arguments.

Generalizable All Variables.

Section AdjointPointwise.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).
  Context `(C' : @SpecializedCategory objC').
  Context `(D' : @SpecializedCategory objD').

  Variable F : SpecializedFunctor C D.
  Variable G : SpecializedFunctor D C.

  Variable A : HomAdjunction F G.

  Variables F' G' : SpecializedFunctor C' D'.

(*  Variable T' : SpecializedNaturalTransformation F' G'.*)

  Definition AdjointPointwise_NT_Unit : SpecializedNaturalTransformation (IdentityFunctor (C ^ E))
                                                                    (ComposeFunctors (G ^ IdentityFunctor E) (F ^ IdentityFunctor E)).
    pose proof (A : AdjunctionUnit _ _) as A'.
    refine (NTComposeT _ (LiftIdentityPointwise _ _)).
    refine (NTComposeT _ (projT1 A' ^ (IdentityNaturalTransformation (IdentityFunctor E)))).
    refine (NTComposeT (LiftComposeFunctorsPointwise _ _ (IdentityFunctor E) (IdentityFunctor E)) _).
    refine (LiftNaturalTransformationPointwise (IdentityNaturalTransformation _) _).
    exact (LeftIdentityFunctorNaturalTransformation2 _).
  Defined.

  Definition AdjointPointwise_NT_Counit : SpecializedNaturalTransformation (ComposeFunctors (F ^ IdentityFunctor E) (G ^ IdentityFunctor E))
                                                                           (IdentityFunctor (D ^ E)).
    pose proof (A : AdjunctionCounit _ _) as A'.
    refine (NTComposeT (LiftIdentityPointwise_Inverse _ _) _).
    refine (NTComposeT (projT1 A' ^ (IdentityNaturalTransformation (IdentityFunctor E))) _).
    refine (NTComposeT _ (LiftComposeFunctorsPointwise_Inverse _ _ (IdentityFunctor E) (IdentityFunctor E))).
    refine (LiftNaturalTransformationPointwise (IdentityNaturalTransformation _) _).
    exact (LeftIdentityFunctorNaturalTransformation1 _).
  Defined.

  Definition AdjointPointwise : Adjunction (F ^ (IdentityFunctor E)) (G ^ (IdentityFunctor E)).
    match goal with
      | [ |- Adjunction ?F ?G ] =>
        refine (_ : AdjunctionUnitCounit F G)
    end.
    exists AdjointPointwise_NT_Unit
           AdjointPointwise_NT_Counit.
    nt_eq.
    present_spfunctor.
    Focus 2.
    nt_eq.
    present_spfunctor.
    Unfocus.
    simpl.
    Require Import FunctorProduct.
    simpl.
    Goal forall x (Y : SpecializedFunctor E C) (m :=
(*Compose
     (Compose (Identity (F (Y x)))
        (Compose
           (Compose
              (Compose (MorphismOf F (MorphismOf Y (Identity x)))
                 (Identity (F (Y x))))
              (proj1_sig
                 ((let (AComponentsOf', AIsomorphism', _) as h
                       return
                         (forall (A0 : C) (A' : objD),
                          {m' : Morphism C A0 (G A') -> Morphism D (F A0) A'
                          |
                          Compose'
                            {|
                            Morphism' := fun s d : Type => s -> d;
                            Identity' := fun (o : Type) (x0 : o) => x0;
                            Compose' := fun (s d d' : Type)
                                          (f : d -> d')
                                          (g : s -> d)
                                          (x0 : s) =>
                                        f (g x0) |}
                            (Morphism D (F A0) A')
                            (Morphism C A0 (G A'))
                            (Morphism D (F A0) A') m'
                            (AComponentsOf' h A0 A') =
                          Identity'
                            {|
                            Morphism' := fun s d : Type => s -> d;
                            Identity' := fun (o : Type) (x0 : o) => x0;
                            Compose' := fun (s d d' : Type)
                                          (f : d -> d')
                                          (g : s -> d)
                                          (x0 : s) =>
                                        f (g x0) |}
                            (Morphism D (F A0) A') &
                          Compose'
                            {|
                            Morphism' := fun s d : Type => s -> d;
                            Identity' := fun (o : Type) (x0 : o) => x0;
                            Compose' := fun (s d d' : Type)
                                          (f : d -> d')
                                          (g : s -> d)
                                          (x0 : s) =>
                                        f (g x0) |}
                            (Morphism C A0 (G A'))
                            (Morphism D (F A0) A')
                            (Morphism C A0 (G A'))
                            (AComponentsOf' h A0 A') m' =
                          Identity'
                            {|
                            Morphism' := fun s d : Type => s -> d;
                            Identity' := fun (o : Type) (x0 : o) => x0;
                            Compose' := fun (s d d' : Type)
                                          (f : d -> d')
                                          (g : s -> d)
                                          (x0 : s) =>
                                        f (g x0) |}
                            (Morphism C A0 (G A'))}) := A in
                   AIsomorphism') (G (F (Y x))) (F (Y x)))
                 (Identity (G (F (Y x))))))
           (Compose
              (Compose
                 (MorphismOf F
                    (MorphismOf G
                       (Compose (MorphismOf F (MorphismOf Y (Identity x)))
                          (Identity (F (Y x))))))
                 (Identity (F (G (F (Y x))))))
              (Compose (Identity (F (G (F (Y x)))))
                 (Compose
                    (MorphismOf F
                       (Compose
                          (Compose (MorphismOf G (Identity (F (Y x))))
                             (Identity (G (F (Y x)))))
                          (Identity (G (F (Y x))))))
                    (Identity (F (G (F (Y x))))))))))*)
     ((*Compose*)
        ((*MorphismOf F*)
           ((*Compose (MorphismOf G (MorphismOf F (MorphismOf Y (Identity x))))*)
              (Compose
                 ((*Compose
                    ((*Compose
                       (Compose
                          (Compose
                             (MorphismOf G
                                (Compose (Identity (F (Y x)))
                                   (Compose (MorphismOf F (Identity (Y x)))
                                      (Identity (F (Y x))))))
                             (Identity (G (F (Y x)))))
                          (Identity (G (F (Y x)))))*)
                       (Compose
                          (MorphismOf G
                             (MorphismOf F
                                (Compose (MorphismOf Y (Identity x))
                                   (Identity (Y x)))))
                          (Identity (G (F (Y x))))))*)
                    (Compose
                       (MorphismOf G
                          (MorphismOf F
                             ((*Compose (MorphismOf Y (Identity x))*)
                                (Identity (Y x)))))
                       (A (Y x) (F (Y x)) (Identity (F (Y x))))))
                 (Identity (Y x)))))(* (Identity (F (Y x)))*))
), m = m.
    simpl; intros.
    rsimplify_morphisms.
