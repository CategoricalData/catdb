Require Import FunctionalExtensionality.
Require Export LimitFunctors SpecializedLaxCommaCategory Subcategory.
Require Import Common DefinitionSimplification SpecializedCategory Functor FunctorCategory NaturalTransformation SmallCat Duals.

Set Implicit Arguments.

Generalizable All Variables.

Section InducedMaps.
  (** Quoting David:
     Given a commutative triangle consisting of
     [[
            G
     C_1 -------> C_2
      \            /
       \          /
        \        /
     F_1 \      / F_2
         _\|  |/_
            D
     ]]
     there are induced maps in [D],
     [colim G : colim F_1 -> colim F_2]
     and
     [lim G : lim F_2 -> lim F_1]

     To get a feel for why this is true (and for the variance of colim
     vs. lim), imagine that [C_1] is the discrete category on 1 object,
     that [C_2] is the discrete category on 2 objects, that that [G]
     is one or the other inclusion, and that [D = Set]. Then [colim G]
     injects one set into its union with another and [lim G] projects a
     product of two sets onto one factor.
     *)
  Variable objC1 : Type.
  Variable morC1 : objC1 -> objC1 -> Type.
  Variable C1 : SpecializedCategory morC1.
  Variable objC2 : Type.
  Variable morC2 : objC2 -> objC2 -> Type.
  Variable C2 : SpecializedCategory morC2.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.
  Variable F1 : SpecializedFunctor C1 D.
  Variable F2 : SpecializedFunctor C2 D.
  Variable G : SpecializedFunctor C1 C2.

  Section Limit.
    Variable T : NaturalTransformation (ComposeFunctors F2 G) F1.

    Hypothesis F1_Limit : Limit F1.
    Hypothesis F2_Limit : Limit F2.

    Let limF1 := LimitObject F1_Limit.
    Let limF2 := LimitObject F2_Limit.

    Definition InducedLimitMapNT' : SpecializedNaturalTransformation ((DiagonalFunctor D C1) limF2) F1.
      Transparent Object Morphism.
      unfold LimitObject, Limit in *;
        intro_universal_morphisms.
      subst_body.
      match goal with
        | [ t : _, F : _, T : _ |- _ ] => eapply (NTComposeT (NTComposeT T (NTComposeF t (IdentityNaturalTransformation F))) _)
      end.
      Grab Existential Variables.
      unfold ComposeFunctors at 1.
      simpl.
      match goal with
        | [ |- SpecializedNaturalTransformation ?F ?G ] =>
          refine (Build_SpecializedNaturalTransformation F G
            (fun x => Identity _)
            _
          )
      end.
      simpl; reflexivity.
    Defined.

    Definition InducedLimitMapNT'' : SpecializedNaturalTransformation ((DiagonalFunctor D C1) limF2) F1.
      simpl_definition_by_exact InducedLimitMapNT'.
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedLimitMapNT : SpecializedNaturalTransformation ((DiagonalFunctor D C1) limF2) F1
      := Eval cbv beta iota zeta delta [InducedLimitMapNT''] in InducedLimitMapNT''.

    Definition InducedLimitMap : D.(Morphism) limF2 limF1
      := TerminalProperty_Morphism F1_Limit _ InducedLimitMapNT.
  End Limit.

  Section Colimit.
    Variable T : NaturalTransformation F1 (ComposeFunctors F2 G).

    Hypothesis F1_Colimit : Colimit F1.
    Hypothesis F2_Colimit : Colimit F2.

    Let colimF1 := ColimitObject F1_Colimit.
    Let colimF2 := ColimitObject F2_Colimit.

    Definition InducedColimitMapNT' : SpecializedNaturalTransformation F1 ((DiagonalFunctor D C1) colimF2).
      Transparent Object Morphism.
      unfold ColimitObject, Colimit in *;
        intro_universal_morphisms.
      subst_body.
      match goal with
        | [ t : _, F : _, T : _ |- _ ] => eapply (NTComposeT _ (NTComposeT (NTComposeF t (IdentityNaturalTransformation F)) T))
      end.
      Grab Existential Variables.
      unfold ComposeFunctors at 1.
      simpl.
      match goal with
        | [ |- SpecializedNaturalTransformation ?F ?G ] =>
          refine (Build_SpecializedNaturalTransformation F G
            (fun x => Identity _)
            _
          )
      end.
      simpl; reflexivity.
    Defined.

    Definition InducedColimitMapNT'' : SpecializedNaturalTransformation F1 ((DiagonalFunctor D C1) colimF2).
      simpl_definition_by_exact InducedColimitMapNT'.
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedColimitMapNT : SpecializedNaturalTransformation F1 ((DiagonalFunctor D C1) colimF2)
      := Eval cbv beta iota zeta delta [InducedColimitMapNT''] in InducedColimitMapNT''.

    Definition InducedColimitMap : Morphism D colimF1 colimF2
      := InitialProperty_Morphism F1_Colimit _ InducedColimitMapNT.
  End Colimit.
End InducedMaps.

Section InducedFunctor.
  Local Transparent Object Morphism.

  Variable I : Type.
  Variable Index2Object : I -> Type.
  Variable Index2Morphism : forall i : I, Index2Object i -> Index2Object i -> Type.
  Variable Index2Cat : forall i : I, SpecializedCategory (@Index2Morphism i).

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Local Notation "'Cat' ⇑ D" := (@LaxCosliceSpecializedCategory _ _ _ Index2Cat _ _ D) (at level 70, no associativity).
  Local Notation "'Cat' ⇓ D" := (@LaxSliceSpecializedCategory _ _ _ Index2Cat _ _ D) (at level 70, no associativity).

  Context `(D : @SpecializedCategory objD morD).
  Let DOp := OppositeCategory D.

  Section Limit.
    Variable HasLimits : forall C : Cat ⇑ D, Limit (projT2 C).

    Let lim (x : Cat ⇑ D) : D
      := LimitObject (HasLimits x).

    Definition InducedLimitFunctor_MorphismOf' (s d : Cat ⇑ D) (m : Morphism _ s d) : Morphism D (lim s) (lim d).
      subst_body; hnf in * |- ; simpl in *.
(*      hnf; change morD with (Morphism D). *)
      apply (InducedLimitMap (G := projT1 m)).
      exact (projT2 m).
    Defined.

    Definition InducedLimitFunctor_MorphismOf'' (s d : Cat ⇑ D) (m : Morphism _ s d) : Morphism D (lim s) (lim d).
      simpl_definition_by_tac_and_exact (@InducedLimitFunctor_MorphismOf' s d m) ltac:(unfold InducedLimitFunctor_MorphismOf' in *).
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedLimitFunctor_MorphismOf (s d : Cat ⇑ D) (m : Morphism _ s d) : Morphism D (lim s) (lim d)
      := Eval cbv beta iota zeta delta [InducedLimitFunctor_MorphismOf''] in @InducedLimitFunctor_MorphismOf'' s d m.

    Definition InducedLimitFunctor : SpecializedFunctor (Cat ⇑ D) D.
      refine {| ObjectOf' := lim;
        MorphismOf' := @InducedLimitFunctor_MorphismOf
      |}; admit.(*
      intros; unfold InducedLimitFunctor_MorphismOf; subst_body;
        abstract (
          present_spcategory;
          unfold InducedLimitMap;
            simpl;
              match goal with
                | [ |- TerminalProperty_Morphism ?a ?b ?c = _ ] => apply (TerminalProperty a b c)
              end (* 9 s *);
              nt_eq (* 5 s *);
              repeat rewrite FIdentityOf;
                repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                  try reflexivity;
                    repeat rewrite Associativity; (* 27 s for this past block *)
                      match goal with
                        | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
                          eapply (@eq_trans _ _ (Compose a' (Compose _ c)) _);
                            try_associativity ltac:(apply f_equal2; try reflexivity)
                      end;
                      match goal with
                        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] =>
                          let H := constr:(TerminalProperty a) in
                            let H' := fresh in
                              pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                                simpl in H'
                      end;
                      etransitivity; solve [ t_with t' ] (* 202 s for this block, ugh *)
        ).*)
    Defined.
  End Limit.

  Section Colimit.
    Variable HasColimits : forall C : Cat ⇓ D, Colimit (projT2 C).

    Let colim (x : Cat ⇓ D) : D
      := ColimitObject (HasColimits x).

    Definition InducedColimitFunctor_MorphismOf' (s d : Cat ⇓ D) (m : Morphism _ s d) : Morphism D (colim s) (colim d).
      subst_body; hnf in * |- ; simpl in *.
(*      hnf; change morD with (Morphism D). *)
      apply (InducedColimitMap (G := projT1 m)).
      exact (projT2 m).
    Defined.

    Definition InducedColimitFunctor_MorphismOf'' (s d : Cat ⇓ D) (m : Morphism _ s d) : Morphism D (colim s) (colim d).
      simpl_definition_by_tac_and_exact (@InducedColimitFunctor_MorphismOf' s d m) ltac:(unfold InducedColimitFunctor_MorphismOf' in *).
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedColimitFunctor_MorphismOf (s d : Cat ⇓ D) (m : Morphism _ s d) : Morphism D (colim s) (colim d)
      := Eval cbv beta iota zeta delta [InducedColimitFunctor_MorphismOf''] in @InducedColimitFunctor_MorphismOf'' s d m.

    Definition InducedColimitFunctor : SpecializedFunctor (Cat ⇓ D) D.
      refine {| ObjectOf' := colim;
        MorphismOf' := @InducedColimitFunctor_MorphismOf
      |};
      intros; unfold InducedColimitFunctor_MorphismOf; subst_body;
(*        abstract ( *)
          present_spcategory;
          unfold InducedColimitMap;
            simpl.
      Focus 2.
      Time match goal with
                | [ |- InitialProperty_Morphism ?a ?b ?c = _ ] => apply (InitialProperty a b c)
              end (* 11 s *).
      Time nt_eq (* 4 s *).
      Time ( repeat rewrite FIdentityOf;
                repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                  try reflexivity;
                    repeat rewrite Associativity). (* 19 s for this past block *)
      Time match goal with
                | [ |- InitialProperty_Morphism ?a ?b ?c = _ ] => apply (InitialProperty a b c)
              end (* 11 s *).
      Time nt_eq (* 4 s *).
      Time ( repeat rewrite FIdentityOf;
                repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                  try reflexivity;
                    repeat rewrite Associativity). (* 19 s for this past block *)
      Time match goal with
             | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
               symmetry; eapply (@eq_trans _ _ (Compose a (Compose _ c')) _);
                 try_associativity ltac:(apply f_equal2; try reflexivity)
           end (* 36 s *).
      Time match goal with
        | [ |- appcontext[InitialProperty_Morphism ?a ?b ?c] ] =>
          let H := constr:(InitialProperty a) in
            let H' := fresh in
              pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                simpl in H'
      end (* 2 s *).
      Time (etransitivity; solve [ t_with t' ]) (* 202 s for this block, ugh *).
      Time match goal with
        | [ |- appcontext[InitialProperty_Morphism ?a ?b ?c] ] =>
          let H := constr:(InitialProperty a) in
            let H' := fresh in
              pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                simpl in H'
      end (* 2 s *).
      (***** XXX HERE *****)
      (* [simpl] does not do what it should *)
(*      etransitivity; [ |
      match goal with
            | [ H : _ |- _ ] => rewrite H; reflexivity
          end ]; simpl. *)
(* but it behaves fine here? o.O *)
      etransitivity; [ |
      match goal with
            | [ H : _ |- _ ] => rewrite H; reflexivity
          end ]; match goal with
                     | _ => simpl
                 end.



      simpl;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
          try reflexivity.
      t'.
      t_with t'.
      symmetry.
      eauto.
      Time (etransitivity; solve [ t_with t' ]) (* 202 s for this block, ugh *).
        ).
    Defined.
  End Colimit.





      unfold InducedColimitMapNT.
      Admitted.
      Goal forall (*(D : LocallySmallCategory
  Pobj : LocallySmallCat / D -> Prop
  HasColimits : forall C : FullSubcategory (LocallySmallCat / D) Pobj,
              Colimit (projT2 (proj1_sig C))*)
  (o : {x | Pobj x}),
(*  ============================*)
  TerminalMorphism_Morphism (HasColimits o) =
  eq_rect
  (ComposeFunctors (projT2 (proj1_sig o))
    (IdentityFunctor (fst (projT1 (proj1_sig o)))))
  (fun F1 : SpecializedFunctor (fst (projT1 (proj1_sig o))) D =>
    SpecializedNaturalTransformation
        {|
          ObjectOf' := fun _ : LSObject (fst (projT1 (proj1_sig o))) =>
                     TerminalMorphism_Object (HasColimits o);
        MorphismOf' := fun (s d : LSObject (fst (projT1 (proj1_sig o))))
                         (_ : LSMorphism (fst (projT1 (proj1_sig o))) s d) =>
                       Identity (TerminalMorphism_Object (HasColimits o));
        FCompositionOf' := diagonal_functor_object_of_subproof
                             (LSMorphism (fst (projT1 (proj1_sig o)))) D
                             (TerminalMorphism_Object (HasColimits o));
        FIdentityOf' := diagonal_functor_object_of_subproof0 D
                          (TerminalMorphism_Object (HasColimits o)) |} F1)
     (NTComposeT
        (NTComposeF (TerminalMorphism_Morphism (HasColimits o))
           (IdentityNaturalTransformation
              (IdentityFunctor (fst (projT1 (proj1_sig o))))))
        {|
        ComponentsOf' := fun _ : LSObject (fst (projT1 (proj1_sig o))) =>
                         Identity (TerminalMorphism_Object (HasColimits o));
        Commutes' := fun (s d : LSObject (fst (projT1 (proj1_sig o))))
                       (_ : LSMorphism (fst (projT1 (proj1_sig o))) s d) =>
                     eq_refl |}) (projT2 (proj1_sig o))
     (InducedColimitFunctor_MorphismOf_subproof HasColimits o o
        (Subcategory_Identity (LocallySmallCat / D)
           (fun (s d : {x | Pobj x})
              (_ : CommaSpecializedCategory_Morphism
                     (proj1_sig s) (proj1_sig d)) => True)
           (fun _ : {x | Pobj x} => I) o)).
      generalize ((ComposeFunctors (projT2 (proj1_sig o))
        (IdentityFunctor (fst (projT1 (proj1_sig o)))))).
      Require Import Eqdep.
      rewrite eq_rect_eq.

      unfold Subcategory_Identity .
      unfold InducedColimitMapNT.
      Opaque DiagonalFunctor.
      simpl

      unfold Subcategory_Identity .
      simpl.
      unfold InducedColimitFunctor_MorphismOf.
      subst lim.
      subst_body.
    Check @ObjectOf' _ _ (LocallySmallCat / D) _ _ D _ .


  (*
    Local Notation "A ↓ F" := (CosliceSpecializedCategory A F) (at level 70, no associativity).
     *)

End InducedFunctor.

Section InducedMapIdentity.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.
  Variable F1 : SpecializedFunctor C D.
  Variable F2 : SpecializedFunctor C D.

  Let G := IdentityFunctor C.

  Hypothesis TriangleCommutes : ComposeFunctors F2 G = F1.

  Section Colimit.
    Hypothesis F1_Colimit : Colimit F1.
    Hypothesis F2_Colimit : Colimit F2.

    Let limF1 := ColimitObject F1_Colimit.
    Let limF2 := ColimitObject F2_Colimit.

    Lemma InducedColimitMap_CompositionOf : InducedColimitMap TriangleCommutes F1_Colimit F2_Colimit = Identity _.
      Compose
      (InducedColimitMap Triangle1Commutes F1_Colimit F2_Colimit)
      (InducedColimitMap Triangle2Commutes F2_Colimit F3_Colimit).
    Proof.
      Transparent Morphism Object.
      subst_body.
      unfold InducedColimitMap, ColimitObject.
      simpl.
      Opaque DiagonalFunctor.
      Time match goal with
        | [ |- TerminalProperty_Morphism ?a ?b ?c = _ ] => apply (TerminalProperty a b c); destruct (TerminalProperty a b c)
      end.
      unfold InducedColimitMapNT.
      Check Compose_DiagonalFunctor.

      unfold unique in *.
      split_and.
      destruct_hypotheses
      intro_universal_properties.
      unfold unique in *.
      destruct_hypotheses.
      etransitivity; try match goal with
                           | [ H : _ |- _ ] => apply H
                         end;
      simpl in *;
        repeat match goal with
                 | [ H : _ |- _ ] => clear H
               end;
        nt_eq.
      unfold InducedColimitMapNT; simpl.
      unfold eq_rect.
      Require Import Eqdep.
      erewrite <- eq_rect_eq.
      unfold Compose_DiagonalFunctor.
      Set Printing All.
      nt_eq
      Print Implicit TerminalProperty_Morphism.
      t_with t'.

    Definition InducedColimitMap' : D.(Morphism) limF2 limF1.
      Transparent Object Morphism.
      unfold ColimitObject, Colimit in *.
      intro_universal_morphisms.
      match goal with


End InducedMapIdentity.

Section InducedMapTheorems.
  (** Quoting David:
     Given a commutative diagram of the form
     [[
           G_1          G_2
     C_1 -------> C_2 -------> C_3
      \            |            /
        \          |          /
          \       F_2       /
        F_1 \      |      / F_3
              \    |    /
               ↘  ↓  ↙
                   D
     ]]
     we want to show that the induced maps from the composition
     are the compositions of the induced maps.
     *)
  Variable objC1 : Type.
  Variable morC1 : objC1 -> objC1 -> Type.
  Variable objC2 : Type.
  Variable morC2 : objC2 -> objC2 -> Type.
  Variable objC3 : Type.
  Variable morC3 : objC2 -> objC2 -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C1 : SpecializedCategory morC1.
  Variable C2 : SpecializedCategory morC2.
  Variable C3 : SpecializedCategory morC2.
  Variable D : SpecializedCategory morD.
  Variable F1 : SpecializedFunctor C1 D.
  Variable F2 : SpecializedFunctor C2 D.
  Variable F3 : SpecializedFunctor C3 D.
  Variable G1 : SpecializedFunctor C1 C2.
  Variable G2 : SpecializedFunctor C2 C3.

  Hypothesis Triangle1Commutes : ComposeFunctors F2 G1 = F1.
  Hypothesis Triangle2Commutes : ComposeFunctors F3 G2 = F2.

  Let G : SpecializedFunctor C1 C3 := ComposeFunctors G2 G1.

  Hypothesis Triangle3Commutes : ComposeFunctors F3 G = F1.


(*  Let Triangle3Commutes : ComposeFunctors F3 G = F1.
    subst G;
      abstract (
        rewrite <- ComposeFunctorsAssociativity;
          t_with t'
      ).
  Qed.
*)
  Section Colimit.
    Hypothesis F1_Colimit : Colimit F1.
    Hypothesis F2_Colimit : Colimit F2.
    Hypothesis F3_Colimit : Colimit F3.

    Let limF1 := ColimitObject F1_Colimit.
    Let limF2 := ColimitObject F2_Colimit.
    Let limF3 := ColimitObject F2_Colimit.

    Lemma InducedColimitMap_CompositionOf : InducedColimitMap Triangle3Commutes F1_Colimit F3_Colimit =
      Compose
      (InducedColimitMap Triangle1Commutes F1_Colimit F2_Colimit)
      (InducedColimitMap Triangle2Commutes F2_Colimit F3_Colimit).
    Proof.
      Transparent Morphism Object.
      subst_body.
      unfold InducedColimitMap, ColimitObject.
      simpl.
      Opaque DiagonalFunctor.
      match goal with
        | [ |- TerminalProperty_Morphism ?a ?b ?c = _ ] => apply (TerminalProperty a b c); destruct (TerminalProperty a b c)
      end.
      unfold InducedColimitMapNT.
      Check Compose_DiagonalFunctor.

      unfold unique in *.
      split_and.
      destruct_hypotheses
      intro_universal_properties.
      unfold unique in *.
      destruct_hypotheses.
      etransitivity; try match goal with
                           | [ H : _ |- _ ] => apply H
                         end;
      simpl in *;
        repeat match goal with
                 | [ H : _ |- _ ] => clear H
               end;
        nt_eq.
      unfold InducedColimitMapNT; simpl.
      unfold eq_rect.
      Require Import Eqdep.
      erewrite <- eq_rect_eq.
      unfold Compose_DiagonalFunctor.
      Set Printing All.
      nt_eq
      Print Implicit TerminalProperty_Morphism.
      t_with t'.

    Definition InducedColimitMap' : D.(Morphism) limF2 limF1.
      Transparent Object Morphism.
      unfold ColimitObject, Colimit in *.
      intro_universal_morphisms.
      match goal with
        | [ t : _, F : _ |- _ ] => unique_pose (NTComposeF t (IdentityNaturalTransformation F))
      end.
      repeat match goal with
               | [ H : _ |- _ ] => rewrite TriangleCommutes in H; autorewrite with core in H
             end.
      intro_universal_property_morphisms.
      unfold Morphism in *; simpl in *.
      specialized_assumption idtac.
    Defined.

    Definition InducedColimitMap'' : Morphism D limF2 limF1.
      simpl_definition_by_exact InducedColimitMap'.
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedColimitMap := Eval cbv beta iota zeta delta [InducedColimitMap''] in InducedColimitMap''.
  End Colimit.

  Section Colimit.
    Hypothesis F1_Colimit : Colimit F1.
    Hypothesis F2_Colimit : Colimit F2.

    Let colimF1 := ColimitObject F1_Colimit.
    Let colimF2 := ColimitObject F2_Colimit.

    Definition InducedColimitMap' : Morphism D colimF1 colimF2.
      Transparent Object Morphism.
      unfold ColimitObject, Colimit in *.
      intro_universal_morphisms.
      match goal with
        | [ t : _, F : _ |- _ ] => unique_pose (NTComposeF t (IdentityNaturalTransformation F))
      end.
      repeat match goal with
               | [ H : _ |- _ ] => rewrite TriangleCommutes in H; autorewrite with core in H
             end.
      intro_universal_property_morphisms.
      unfold Morphism in *; simpl in *.
      specialized_assumption idtac.
    Defined.

    Definition InducedColimitMap'' : Morphism D colimF1 colimF2.
      simpl_definition_by_exact InducedColimitMap'.
    Defined.

    (* Then we clean up a bit with reduction. *)
    Definition InducedColimitMap := Eval cbv beta iota zeta delta [InducedColimitMap''] in InducedColimitMap''.
  End Colimit.
End InducedMaps.

End InducedMapTheorems.
