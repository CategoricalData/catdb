Require Export Equalizer Duals ProductFunctor DiscreteCategoryFunctors.
Require Import Common Products LimitFunctorTheorems.

Set Implicit Arguments.

Generalizable All Variables.

Local Ltac t := simpl in *; subst_body;
  repeat (let H := fresh in intro H; hnf in H); subst;
    simpl in *;
      repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
        try reflexivity.

Section Coend.
  Context `(C : @SpecializedCategory objC morC).
  Context `(D : @SpecializedCategory objD morD).

  Let COp := OppositeCategory C.

  Variable F : SpecializedFunctor (COp * C) D.

  Let MorC := @MorphismFunctor _ _ _ (fun _ : unit => C) tt. (* [((c0, c1) & f : morC c0 c1)], the set of morphisms of C *)

  Variable Fmor : ∐_{ c0c1f : MorC } (F (snd (projT1 c0c1f), fst (projT1 c0c1f))).
  Variable Fob : ∐_{ c } (F (c, c)).

  (* There is a morphism in D from [Fmor] to [Fob] which takes the domain of the relevant morphism. *)
  Definition Coend_Fdom : Morphism D (ColimitObject Fmor) (ColimitObject Fob).
    apply (InducedColimitMap (G := InducedDiscreteFunctor _ (DomainNaturalTransformation _ (fun _ => C) tt))).
    hnf; simpl.
    match goal with
      | [ |- SpecializedNaturalTransformation ?F0 ?G0 ] =>
        refine (Build_SpecializedNaturalTransformation F0 G0
          (fun sdf => let s := fst (projT1 sdf) in MorphismOf F (s := (_, s)) (d := (_, s)) (projT2 sdf, Identity (C := C) s))
          _
        )
    end;
    abstract t.
  Defined.

  (* There is a morphism in D from [Fmor] to [Fob] which takes the codomain of the relevant morphism. *)
  Definition Coend_Fcod : Morphism D (ColimitObject Fmor) (ColimitObject Fob).
    apply (InducedColimitMap (G := InducedDiscreteFunctor _ (CodomainNaturalTransformation _ (fun _ => C) tt))).
    hnf; simpl.
    match goal with
      | [ |- SpecializedNaturalTransformation ?F0 ?G0 ] =>
        refine (Build_SpecializedNaturalTransformation F0 G0
          (fun sdf => let d := snd (projT1 sdf) in MorphismOf F (s := (d, _)) (d := (d, _)) (Identity (C := C) d, projT2 sdf))
          _
        )
    end;
    abstract t.
  Defined.

  Definition Coend := Coequalizer D _ _ Coend_Fdom Coend_Fcod.
End Coend.

(* TODO: Figure out why the notation for this is the same as the notation for the Grothendieck construction *)
(*Notation "∫ F" := (Coend F) (at level 0).*)
