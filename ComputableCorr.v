Require Import FunctionalExtensionality.
Require Export ComputableCategory Correspondences.
Require Import Common Notations SetCategory Duals ProductCategory FunctorProduct ProductNaturalTransformation Hom Coend SetColimits SetLimits ProductInducedFunctors ExponentialLaws NatCategory FunctorCategory LimitFunctors CoendFunctor.

Set Implicit Arguments.

Generalizable All Variables.

Local Notation "∫ F" := (CoendFunctor (fun F0 => TypeHasColimits F0) F).

Section ComputableCategory.
  Variable I : Type.
  Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i)).

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Section CorrType.
    Let ComputableCorr_Morphism (C D : I) := SpecializedFunctor ((OppositeCategory C) * D) TypeCat.

    Definition InducedProductFstFunctor_op `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD) `(E : @SpecializedCategory objE)
      (F : SpecializedFunctor (OppositeCategory C * D) E) (d : D) :
      SpecializedFunctor (OppositeCategory C) E
      := InducedProductFstFunctor (C := OppositeCategory C) (D := D) (E := E) F d.
    Definition InducedProductSndFunctor_op `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD) `(E : @SpecializedCategory objE)
      (F : SpecializedFunctor (OppositeCategory C * D) E) (c : C) :
      SpecializedFunctor D E
      := InducedProductSndFunctor (C := OppositeCategory C) (D := D) (E := E) F c.
    Arguments InducedProductSndFunctor_op / _ _ _ _ _ _ _ _.
    Arguments InducedProductFstFunctor_op / _ _ _ _ _ _ _ _.

    Local Notation "F ⟨ c , - ⟩" := (InducedProductSndFunctor_op F c) : functor_scope.
    Local Notation "F ⟨ - , d ⟩" := (InducedProductFstFunctor_op F d) : functor_scope.

    Definition ComputableCorr_Compose_ObjectOf : forall C D E (G : ComputableCorr_Morphism D E) (F : ComputableCorr_Morphism C D),
      OppositeCategory C * E -> Type (* TypeCat *).
    Proof.
      subst ComputableCorr_Morphism; simpl in *.
      intros C D E G F ce.
      pose (TypeLimit (C := 1 + 1)) as HL.
      pose (LimitFunctor (C := TypeCat) (D := 1 + 1) HL) as LF.
      pose (ComposeFunctors (ExponentialLaw2Functor_Inverse _ _ _) (ExponentialLaw1Functor_Inverse TypeCat * ExponentialLaw1Functor_Inverse TypeCat)) as F'.
      pose (ComposeFunctors LF F') as F''.
      pose (ComposeFunctors F'' ((G ⟨ - , (snd ce) ⟩) * (F ⟨ (fst ce), - ⟩))) as F'''.
(*      apply (∫ ((G [ - , (snd ce) ]) * (F [ (fst ce), - ]))%functor). *)
      apply (∫ F''').
  (*
        unfold Coproduct;
          apply TypeHasColimits. *)
    Defined.

    (* XXX These things don't belong here... *)
    Definition InducedProductFstNaturalTransformation_op `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD) `(E : @SpecializedCategory objE)
      (F : SpecializedFunctor (OppositeCategory C * D) E) (s d : C) (m : Morphism (OppositeCategory C) s d) :
      SpecializedNaturalTransformation (F ⟨ s , - ⟩) (F ⟨ d , - ⟩)
      := InducedProductFstNaturalTransformation (C := OppositeCategory C) (D := D) (E := E) F (s := s) (d := d) m.
    Definition InducedProductSndNaturalTransformation_op `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD) `(E : @SpecializedCategory objE)
      (F : SpecializedFunctor (OppositeCategory C * D) E) (s d : D) (m : Morphism D s d) :
      SpecializedNaturalTransformation (F ⟨ - , s ⟩) (F ⟨ - , d ⟩)
      := InducedProductSndNaturalTransformation (C := OppositeCategory C) (D := D) (E := E) F (s := s) (d := d) m.
    Arguments InducedProductSndNaturalTransformation_op / _ _ _ _ _ _ _ _ _ _.
    Arguments InducedProductFstNaturalTransformation_op / _ _ _ _ _ _ _ _ _ _.

    Local Notation "F ⟨ m , - ⟩" := (InducedProductFstNaturalTransformation_op F _ _ m) : natural_transformation_scope.
    Local Notation "F ⟨ - , m ⟩" := (InducedProductSndNaturalTransformation_op F _ _ m) : natural_transformation_scope.

    Definition ComputableCorr_Compose_MorphismOf : forall C D E (G : ComputableCorr_Morphism D E) (F : ComputableCorr_Morphism C D),
      forall s d (m : Morphism (OppositeCategory C * E) s d),
        ComputableCorr_Compose_ObjectOf G F s -> ComputableCorr_Compose_ObjectOf G F d.
    Proof.
      intros C D E G F s d m.
      destruct m as [ i j ].
      destruct s as [ c e ], d as [ c' e' ].
      simpl in *.
      present_spcategory.
      unfold ComputableCorr_Morphism in *.
      pose ((G ⟨ - , j ⟩) * (F ⟨ i , - ⟩))%natural_transformation.
      pose (CoendFunctor (C := D) (D := TypeCat) (fun F => TypeHasColimits F)) as coend.


      pose (TypeLimit (C := 1 + 1)) as HL.
      pose (LimitFunctor (C := TypeCat) (D := 1 + 1) HL) as LF.
      pose (ComposeFunctors (ExponentialLaw2Functor_Inverse _ _ _) (ExponentialLaw1Functor_Inverse TypeCat * ExponentialLaw1Functor_Inverse TypeCat)) as F'.
      pose (ComposeFunctors LF F') as pair.

      pose (NTComposeF (IdentityNaturalTransformation pair) s : Morphism (TypeCat ^ ((OppositeCategory D) * D)) _ _) as s'.
      exact (MorphismOf coend s').
    Defined.

    Opaque TypeCat CoendFunctor.

    (* TODO: Clean up this proof *)
    Definition ComputableCorr_Compose C D E (G : ComputableCorr_Morphism D E) (F : ComputableCorr_Morphism C D) :
      ComputableCorr_Morphism C E.
    Proof.
      hnf.
      match goal with
        | [ |- SpecializedFunctor ?C0 ?D0 ] =>
          refine (Build_SpecializedFunctor C0 D0
            (@ComputableCorr_Compose_ObjectOf C D E G F)
            (@ComputableCorr_Compose_MorphismOf C D E G F)
            _
            _
          )
      end;
      present_spcategory;
      abstract (
        intros;
          hnf in *;
            repeat match goal with
                     | [ H : prod _ _ |- _ ] => destruct H
                   end; simpl in *;
            eta_red;
            match goal with
              | [ |- _ = Compose (MorphismOf (C := ?C) ?F ?m1) (MorphismOf (C := ?C) ?F ?m2) ] =>
                transitivity (MorphismOf (C := C) F (Compose (C := C) m1 m2));
                  [ apply f_equal | apply FCompositionOf ];
                  simpl;
                    try rewrite <- NaturalTransformationExchangeLaw;
                      try rewrite LeftIdentityNaturalTransformation
              | [ |- MorphismOf ?F (s := ?s) (d := ?s) _ = _ ] => transitivity (MorphismOf F (Identity s));
                [ apply f_equal | rewrite FIdentityOf; extensionality x; reflexivity ];
                simpl;
                  etransitivity; [ | apply NTComposeFIdentityNaturalTransformation ];
                  cbv beta (* force evar unification knowledge *); []
            end;
            apply f_equal; nt_eq; simpl_eq;
              repeat rewrite <- FCompositionOf;
                repeat rewrite <- FIdentityOf;
                  simpl;
                    present_spcategory;
                    unfold ProductCategory; simpl;
                      repeat rewrite LeftIdentity;
                        reflexivity
      ).
    Defined.

    Transparent TypeCat CoendFunctor.


    Definition ComputableCorr_Identity (C : I) : ComputableCorr_Morphism C C
      := HomFunctor _.

  Ltac hideProof' pf :=
      match goal with
        | [ x : _ |- _ ] => match x with
                              | pf => fail 2
                            end
        | _ => generalize pf; intro
      end.
    Ltac nt_hideProofs := repeat match goal with
                                | [ |- context[{| ComponentsOf' := _; Commutes' := ?pf |}] ] =>
                                  hideProof' pf
                              end; simpl in *.
    Ltac functor_hideProofs := repeat match goal with
                                        | [ |- context[{| ObjectOf' := _; MorphismOf' := _;
                                          FCompositionOf' := ?pf1; FIdentityOf' := ?pf2 |}] ] =>
                                        progress (try hideProof' pf1; try hideProof' pf2)
                                      end; simpl in *.



  Definition ComputableCorr : @SpecializedCategory I.
  Proof.
    refine (@Build_SpecializedCategory I
      ComputableCorr_Morphism
      ComputableCorr_Identity
      ComputableCorr_Compose
      _
      _
      _
    ).
    Focus 3.
    intros; unfold ComputableCorr_Compose, ComputableCorr_Identity.
    functor_eq.
    apply functional_extensionality_dep; intro; simpl.
    unfold ComputableCorr_Compose_ObjectOf; simpl.
    subst ComputableCorr_Morphism.
    unfold ColimitObject.
    rename f into G.
    destruct x as [ c d ]; simpl.
    rename a into C.
    rename b into D.
    simpl in *.
    Check     (ComposeFunctors (LimitFunctor (TypeLimit (C:=1 + 1)))
                 (ComposeFunctors
                    (ExponentialLaw2Functor_Inverse TypeCat 1 1)
                    (ExponentialLaw1Functor_Inverse TypeCat *
                     ExponentialLaw1Functor_Inverse TypeCat))).
    unfold CoendFunctor_Diagram_pre.
    unfold CoendFunctor_Diagram_ObjectOf_pre.
    functor_hideProofs.
    unfold ComposeFunctors at 1.
    functor_hideProofs.
    unfold ComposeFunctors at 10.
    (***** HERE: Do we actually want Set / iso ? *****)


    pattern (CoendFunctor_Diagram_pre_subproof (C:=C)).
    functor_hideProofs.
    simpl in *.
   functor_hideProofs.

    compute.
    unfold CoendFunctor_Diagram_ObjectOf_pre.

    unfold CoendFunctor_Diagram_MorphismOf_pre.
    Unset Printing Notations.



    intro_from_universal_objects.
    unfold Colimit in *.
    intro_universal_properties.
    unfold unique in *.


    admit.
    admit.
    admit.
    Defined.
    refine {|
      Identity' := (fun o : I => @IdentityFunctor _ _ o);
      Compose' := (fun C D E : I => @ComposeFunctors _ _ C _ _ D _ _ E)
      |}; abstract functor_eq.
  Defined.
End ComputableCategory.
