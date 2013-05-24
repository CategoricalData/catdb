Require Import Bool.
Require Import SpecializedCategory Functor NaturalTransformation.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

(** This Ltac controls the simplification routine. *)

Local Ltac do_simplification :=
    repeat rewrite ?LeftIdentity, ?RightIdentity, ?FIdentityOf;
    repeat rewrite ?Associativity;
    repeat rewrite ?FCompositionOf.

Section ReifiedMorphism.
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

  Fixpoint ReifiedMorphismDenote objC C s d (m : @ReifiedMorphism objC C s d) : Morphism C s d :=
    match m in @ReifiedMorphism objC C s d return Morphism C s d with
      | ReifiedIdentityMorphism _ _ x => Identity x
      | ReifiedComposedMorphism _ _ _ _ _ m1 m2 => Compose (@ReifiedMorphismDenote _ _ _ _ m1)
                                                           (@ReifiedMorphismDenote _ _ _ _ m2)
      | ReifiedNaturalTransformationMorphism _ _ _ _ _ _ T x => T x
      | ReifiedFunctorMorphism _ _ _ _ F _ _ m => MorphismOf F (@ReifiedMorphismDenote _ _ _ _ m)
      | ReifiedGenericMorphism _ _ _ _ m => m
    end.
End ReifiedMorphism.

Ltac Ltac_reify_morphism m :=
  let objC := match type of m with @Morphism ?objC _ ?s ?d => constr:(objC) end in
  let C := match type of m with @Morphism ?objC ?C ?s ?d => constr:(C) end in
  let s := match type of m with @Morphism ?objC _ ?s ?d => constr:(s) end in
  let d := match type of m with @Morphism ?objC _ ?s ?d => constr:(d) end in
  match m with
    | @Identity _ _ ?x => constr:(@ReifiedIdentityMorphism _ C x)
    | Compose ?m1 ?m2 => let m1' := Ltac_reify_morphism m1 in
                         let m2' := Ltac_reify_morphism m2 in
                         constr:(@ReifiedComposedMorphism _ _ _ _ _ m1' m2')
    | ComponentsOf ?T ?x => constr:(@ReifiedNaturalTransformationMorphism _ _ _ _ _ _ T x)
    | MorphismOf ?F ?m => let m' := Ltac_reify_morphism m in
                          constr:(@ReifiedFunctorMorphism _ _ _ _ F _ _ m')
    | ReifiedMorphismDenote ?m' => constr:(m')
    | _ => constr:(@ReifiedGenericMorphism objC C s d m)
  end.

Section SimplifiedMorphism.
  Fixpoint ReifiedHasIdentities `(m : @ReifiedMorphism objC C s d) : bool
    := match m with
         | ReifiedIdentityMorphism _ _ _ => true
         | ReifiedComposedMorphism _ _ _ _ _ m1 m2 => orb (@ReifiedHasIdentities _ _ _ _ m1) (@ReifiedHasIdentities _ _ _ _ m2)
         | ReifiedNaturalTransformationMorphism _ _ _ _ _ _ _ _ => false
         | ReifiedFunctorMorphism _ _ _ _ _ _ _ m0 => (@ReifiedHasIdentities _ _ _ _ m0)
         | ReifiedGenericMorphism _ _ _ _ _ => false
       end.

  Fixpoint ReifiedMorphismSimplifyWithProof objC C s d (m : @ReifiedMorphism objC C s d) {struct m}
  : { m' : ReifiedMorphism C s d | ReifiedMorphismDenote m = ReifiedMorphismDenote m' }.
  refine match m with
           | ReifiedComposedMorphism _ _ s0 d0 d0' m1 m2 => _
           | ReifiedFunctorMorphism _ _ _ _ F _ _ m' => _
           | ReifiedIdentityMorphism _ _ x => exist _ _ eq_refl
           | ReifiedNaturalTransformationMorphism _ _ _ _ _ _ T x => exist _ _ eq_refl
           | ReifiedGenericMorphism _ _ _ _ m => exist _ _ eq_refl
         end; clear m;
  [ destruct (@ReifiedMorphismSimplifyWithProof _ _ _ _ m1) as [ m1' H1 ], (@ReifiedMorphismSimplifyWithProof _ _ _ _ m2) as [ m2' H2 ];
    clear ReifiedMorphismSimplifyWithProof;
    destruct m1';
    ((destruct m2')
       || (

         (* we failed to destruct m2', so m1' is either a functor
         thing or a natural transformation thing.  We don't care about
         either, so generalize them away *)

         match type of H1 with
             | _ = ReifiedMorphismDenote ?T => generalize dependent T; intros
         end;
         match type of m2' with
           | ReifiedMorphism _ _ (?f ?x) => generalize dependent (f x); intros; destruct m2'
         end))
    | destruct (@ReifiedMorphismSimplifyWithProof _ _ _ _ m') as [ m'' ? ];
      clear ReifiedMorphismSimplifyWithProof;
      destruct m''];
  simpl in *;
  match goal with
    | [ |- { m' : _ | ?m'' = ReifiedMorphismDenote m' } ]
      => let T := type of m'' in
         let t := fresh in
         let H := fresh in
         evar (t : T);
           assert (H : t = m'');
           [ repeat match goal with
                      | [ H : ReifiedMorphismDenote _ = _ |- _ ] => rewrite H; clear H
                    end;
             do_simplification;
             subst t;
             reflexivity
           | ];
           instantiate;
           let m := (eval unfold t in t) in
           let m' := Ltac_reify_morphism m in
           (exists m');
             clear H t
  end;
  repeat match goal with
           | [ H : _ = _ |- _ ] => revert H
           | _ => clear
         end;
  intros;
  abstract (
      repeat match goal with
               | [ H : ReifiedMorphismDenote _ = _ |- _ ] => rewrite H; clear H
             end;
      do_simplification;
      reflexivity
    ).
  Defined.

  Local Ltac solve_t :=
    simpl in *;
    solve [ match goal with
              | _ => clear; reflexivity
              | _ => clear; abstract (exists eq_refl; subst; reflexivity)
              | [ H : _ = _ |- _ ] => revert H; clear; intros; abstract (exists eq_refl; subst; reflexivity)
              | [ H : true = false |- _ ] => exfalso; revert H; clear; intro H; abstract inversion H
              | _ => assumption
            end
          | repeat match goal with
                     | [ H : appcontext[orb] |- _ ] => revert H
                     | [ H : @eq bool _ _ |- _ ] => revert H
                   end;
            clear;
            intros;
            abstract (
                repeat match goal with
                         | _ => reflexivity
                         | [ H : _ |- _ ] => (apply orb_false_iff in H; destruct H)
                         | [ H : _ = false |- _ ] => rewrite H
                         | [ H : _ = true |- _ ] => rewrite H
                       end
          ) ].

  Local Ltac solve_t' :=
    repeat match goal with
             | _ => subst; solve_t
             | [ |- appcontext[match ?E with _ => _ end] ]
               => match E with
                    | ?f _ => fail 1
                    | _ => destruct E
                    | _ => match type of E with
                             | ReifiedMorphism _ ?s ?d => generalize dependent s; generalize dependent d;
                                                          intros; destruct E
                           end
                  end
           end.

  Local Ltac gen_id_H H m :=
    let H' := fresh in
    set (H' := m) in *;
      destruct H';
      simpl in H.

  Fixpoint ReifiedMorphismSimplifyWithProofNoIdentity `(C : @SpecializedCategory objC) s d
           (m : ReifiedMorphism C s d)
  : {ReifiedHasIdentities (proj1_sig (ReifiedMorphismSimplifyWithProof m)) = false}
    + { exists H : s = d, proj1_sig (ReifiedMorphismSimplifyWithProof m) = match H with eq_refl => ReifiedIdentityMorphism C s end }.
  destruct m;
  try solve [ right; clear; abstract (exists eq_refl; subst; reflexivity)
            | left; clear; reflexivity ];
  [ destruct (@ReifiedMorphismSimplifyWithProofNoIdentity _ _ _ _ m1), (@ReifiedMorphismSimplifyWithProofNoIdentity _ _ _ _ m2);
    [ left | left | left | right ]
  | destruct (@ReifiedMorphismSimplifyWithProofNoIdentity _ _ _ _ m);
    [ left | right ] ];
  clear ReifiedMorphismSimplifyWithProofNoIdentity;
  try abstract (
        destruct_head_hnf @ex;
        subst;
        simpl in *;
          repeat match goal with
                   | [ H : ReifiedHasIdentities (proj1_sig ?m) = _ |- _ ] => gen_id_H H m
                   | [ H : proj1_sig ?m = ReifiedIdentityMorphism _ _ |- _ ] => gen_id_H H m
                 end;
        repeat match goal with
                 | _ => progress subst
                 | _ => progress solve_t'
                 | [ H : ReifiedHasIdentities (?f ?x) = false |- _ ] => generalize dependent (f x); intros
                                                                                                  | _ => progress simpl in *
               end
      ).
  Defined.

  Section ReifiedMorphismSimplify.
    Local Arguments ReifiedMorphismSimplifyWithProof / .

    Definition ReifiedMorphismSimplify objC C s d (m : @ReifiedMorphism objC C s d)
    : ReifiedMorphism C s d
      := Eval simpl in proj1_sig (ReifiedMorphismSimplifyWithProof m).

    (*Local Arguments ReifiedMorphismSimplify / .*)
  End ReifiedMorphismSimplify.

  Lemma ReifiedMorphismSimplifyOk objC C s d (m : @ReifiedMorphism objC C s d)
  : ReifiedMorphismDenote m =
    ReifiedMorphismDenote (ReifiedMorphismSimplify m).
  Proof.
    exact (proj2_sig (ReifiedMorphismSimplifyWithProof m)).
  Qed.

  Local Arguments ReifiedMorphismSimplifyWithProofNoIdentity / .

  Definition ReifiedMorphismSimplifyNoIdentity `(C : @SpecializedCategory objC) s d
             (m : ReifiedMorphism C s d)
  : {ReifiedHasIdentities (ReifiedMorphismSimplify m) = false}
    + { exists H : s = d, ReifiedMorphismSimplify m = match H with eq_refl => ReifiedIdentityMorphism C s end }
    := Eval simpl in ReifiedMorphismSimplifyWithProofNoIdentity m.
End SimplifiedMorphism.

Ltac Ltac_rsimplify_morphisms :=
  simpl;
  let m1 := match goal with [ |- ?m1 = ?m2 ] => constr:(m1) end in
  let m2 := match goal with [ |- ?m1 = ?m2 ] => constr:(m2) end in
  let m1' := Ltac_reify_morphism m1 in
  let m2' := Ltac_reify_morphism m2 in
  change (ReifiedMorphismDenote m1' = ReifiedMorphismDenote m2');
    rewrite (ReifiedMorphismSimplifyOk m1');
    rewrite (ReifiedMorphismSimplifyOk m2');
    simpl.
(* Note: Using [lazy] in the above tactic makes ExponentialLaws die on
   OOM after 1-2 GB of RAM and 40 minutes. *)

(*******************************************************************************)
(**                Goals which are solved by [rsimplify_morphisms]            **)
(*******************************************************************************)
Section good_examples.
  Section id.
    Context `(C : @SpecializedCategory objC).
    Context `(D : @SpecializedCategory objC).
    Variables F G : SpecializedFunctor C D.
    Variable T : SpecializedNaturalTransformation F G.

    Lemma good_example_00001 (x : C) :Compose (Identity x) (Identity x) = Identity (C := C) x.
      Ltac_rsimplify_morphisms.
      reflexivity.
    Qed.

    Lemma good_example_00002 s d (m : Morphism C s d)
    : MorphismOf F (Compose m (Identity s)) = MorphismOf F m.
      Ltac_rsimplify_morphisms.
      reflexivity.
    Qed.

    Lemma good_example_00003 s d (m : Morphism C s d)
    : MorphismOf F (Compose (Identity d) m) = MorphismOf F m.
      Ltac_rsimplify_morphisms.
      reflexivity.
    Qed.
  End id.

  Lemma good_example_00004
  : forall (objC : Type) (C : SpecializedCategory objC)
           (objD : Type) (D : SpecializedCategory objD) (objC' : Type)
           (C' : SpecializedCategory objC') (objD' : Type)
           (D' : SpecializedCategory objD') (F : SpecializedFunctor C C')
           (G : SpecializedFunctor D' D) (s d d' : SpecializedFunctor D C)
           (m1 : SpecializedNaturalTransformation s d)
           (m2 : SpecializedNaturalTransformation d d') (x : objD'),
      Compose (MorphismOf F (m2 (G x))) (MorphismOf F (m1 (G x))) =
      Compose
        (Compose
           (MorphismOf F (Compose (MorphismOf d' (Identity (G x))) (m2 (G x))))
           (Identity (F (d (G x))))) (MorphismOf F (m1 (G x))).
    intros.
    Ltac_rsimplify_morphisms.
    reflexivity.
  Qed.

  Lemma good_example_00005
  : forall (objC : Type) (C : SpecializedCategory objC)
           (objD : Type) (D : SpecializedCategory objD) (objC' : Type)
           (C' : SpecializedCategory objC') (objD' : Type)
           (D' : SpecializedCategory objD') (F : SpecializedFunctor C C')
           (G : SpecializedFunctor D' D) (s d d' : SpecializedFunctor D C)
           (m1 : SpecializedNaturalTransformation s d)
           (m2 : SpecializedNaturalTransformation d d') (x : objD'),
      Compose
        (MorphismOf F
                    (Compose (MorphismOf d' (Identity (G x)))
                             (Compose (m2 (G x)) (m1 (G x))))) (Identity (F (s (G x)))) =
      Compose
        (Compose
           (MorphismOf F (Compose (MorphismOf d' (Identity (G x))) (m2 (G x))))
           (Identity (F (d (G x)))))
        (Compose
           (MorphismOf F (Compose (MorphismOf d (Identity (G x))) (m1 (G x))))
           (Identity (F (s (G x))))).
    intros.
    Ltac_rsimplify_morphisms.
    reflexivity.
  Qed.
End good_examples.


(***************************************************)
(* Confusing examples that don't quite work *)
Section bad_examples.
  Require Import SumCategory.
  Section bad_example_0001.
    Context `(C0 : SpecializedCategory objC0).
    Context `(C1 : SpecializedCategory objC1).
    Context `(D : SpecializedCategory objD).

    Variables s d d' : C0.
    Variable m1 : Morphism C0 s d.
    Variable m2 : Morphism C0 d d'.
    Variable F : SpecializedFunctor (C0 + C1) D.

    Goal MorphismOf F (s := inl _) (d := inl _) (Compose m2 m1) = Compose (MorphismOf F (s := inl _) (d := inl _) m2) (MorphismOf F (s := inl _) (d := inl _) m1).
    Ltac_rsimplify_morphisms.
    Fail reflexivity.
    Abort.
  End bad_example_0001.
End bad_examples.
