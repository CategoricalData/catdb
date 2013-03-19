Require Export FunctorCategory NaturalTransformation.
Require Import Common Notations SmallCat ProductCategory Duals ExponentialLaws CanonicalStructureSimplification FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope category_scope.

Section FunctorCategoryParts.
  Section MorphismOf.
    Context `(C : @SpecializedCategory objC).
    Context `(D : @SpecializedCategory objD).
    Context `(C' : @SpecializedCategory objC').
    Context `(D' : @SpecializedCategory objD').

    Variable F : SpecializedFunctor C C'.
    Variable G : SpecializedFunctor D' D.

    Definition FunctorCategoryFunctor_MorphismOf_ObjectOf : (C ^ D)%functor -> (C' ^ D')%functor
      := fun H => ComposeFunctors F (ComposeFunctors H G).

    Global Arguments FunctorCategoryFunctor_MorphismOf_ObjectOf _ / .

    Definition FunctorCategoryFunctor_MorphismOf_MorphismOf s d (m : Morphism (C ^ D) s d) :
      Morphism (C' ^ D') (FunctorCategoryFunctor_MorphismOf_ObjectOf s) (FunctorCategoryFunctor_MorphismOf_ObjectOf d)
      := NTComposeF (IdentityNaturalTransformation _) (NTComposeF m (IdentityNaturalTransformation _)).

    Global Arguments FunctorCategoryFunctor_MorphismOf_MorphismOf _ _ _ / .

    Definition FunctorCategoryFunctor_MorphismOf : SpecializedFunctor (C ^ D) (C' ^ D').
      exists FunctorCategoryFunctor_MorphismOf_ObjectOf FunctorCategoryFunctor_MorphismOf_MorphismOf;
      abstract (
          intros; simpl;
          apply NaturalTransformation_eq;
          rsimplify_morphisms;
          reflexivity
        ).
    Defined.
  End MorphismOf.

  Section FIdentityOf.
    Context `(C : @SpecializedCategory objC).
    Context `(D : @SpecializedCategory objD).

    Lemma FunctorCategoryFunctor_FIdentityOf : FunctorCategoryFunctor_MorphismOf (IdentityFunctor C) (IdentityFunctor D) = IdentityFunctor _.
      repeat (intro || apply Functor_eq || nt_eq); simpl; rsimplify_morphisms; reflexivity.
    Qed.
  End FIdentityOf.

  Section FCompositionOf.
    Context `(C : @SpecializedCategory objC).
    Context `(D : @SpecializedCategory objD).
    Context `(C' : @SpecializedCategory objC').
    Context `(D' : @SpecializedCategory objD').
    Context `(C'' : @SpecializedCategory objC'').
    Context `(D'' : @SpecializedCategory objD'').

    Variable F' : SpecializedFunctor C' C''.
    Variable G : SpecializedFunctor D D'.
    Variable F : SpecializedFunctor C C'.
    Variable G' : SpecializedFunctor  D' D''.

    Lemma FunctorCategoryFunctor_FCompositionOf : FunctorCategoryFunctor_MorphismOf (ComposeFunctors F' F) (ComposeFunctors G' G)
                                                  = ComposeFunctors (FunctorCategoryFunctor_MorphismOf F' G) (FunctorCategoryFunctor_MorphismOf F G').
      abstract (repeat (intro || apply Functor_eq || nt_eq); simpl; rsimplify_morphisms; reflexivity).
    Qed.
  End FCompositionOf.
End FunctorCategoryParts.

Section FunctorCategoryFunctor.
  Definition FunctorCategoryFunctor : SpecializedFunctor (LocallySmallCat * (OppositeCategory LocallySmallCat)) LocallySmallCat.
    refine (Build_SpecializedFunctor (LocallySmallCat * (OppositeCategory LocallySmallCat)) LocallySmallCat
                                     (fun CD => (fst CD) ^ (snd CD) : LocallySmallSpecializedCategory _)
                                     (fun s d m => FunctorCategoryFunctor_MorphismOf (fst m) (snd m))
                                     _
                                     _);
    simpl;
    abstract (intros; apply FunctorCategoryFunctor_FCompositionOf || apply FunctorCategoryFunctor_FIdentityOf).
  Defined.

  (* Definition FunctorCategoryFunctor : ((LocallySmallCat ^ LocallySmallCat) ^ (OppositeCategory LocallySmallCat))%category
    := ExponentialLaw4Functor_Inverse _ _ _ FunctorCategoryUncurriedFunctor. *)
End FunctorCategoryFunctor.

Notation "F ^ G" := (FunctorCategoryFunctor_MorphismOf F G) : functor_scope.

Section NaturalTransformation.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(C' : @SpecializedCategory objC').
  Context `(D' : @SpecializedCategory objD').

  Variables F G : SpecializedFunctor C D.
  Variables F' G' : SpecializedFunctor C' D'.

  Variable T : SpecializedNaturalTransformation F G.
  Variable T' : SpecializedNaturalTransformation F' G'.

  Definition LiftNaturalTransformationPointwise : SpecializedNaturalTransformation (F ^ F') (G ^ G').
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
                                                       (fun _ => NTComposeF T (NTComposeF (IdentityNaturalTransformation _) T'))
                                                       _)
    end;
    present_spfunctor.
    abstract (
        intros;
        simpl;
        apply NaturalTransformation_eq;
        simpl in *;
          intros;
        autorewrite with category;
        repeat (
            reflexivity
              || (progress repeat rewrite <- FCompositionOf)
              || (progress repeat rewrite Commutes)
              || (progress try_associativity ltac:(apply f_equal2; try reflexivity; [])))
      ).
  Defined.
End NaturalTransformation.

Notation "T ^ U" := (LiftNaturalTransformationPointwise T U) : natural_transformation_scope.

Section NaturalTransformation_Properties.
  Section identity.
    Context `(C : @SpecializedCategory objC).
    Context `(D : @SpecializedCategory objD).

    Local Ltac t := intros; simpl; nt_eq; rsimplify_morphisms; try reflexivity.

    Section lift.
      Let LiftIdentityPointwise'
      : SpecializedNaturalTransformation (IdentityFunctor (C ^ D)) (IdentityFunctor C ^ IdentityFunctor D).
        match goal with
          | [ |- SpecializedNaturalTransformation ?F ?G ] =>
            refine (Build_SpecializedNaturalTransformation F G
                                                           (fun x => (Build_SpecializedNaturalTransformation (F x) (G x)
                                                                                                             (fun y => Identity (x y))
                                                                                                             _))
                                                           _)
        end;
        t.
        Grab Existential Variables.
        present_spfunctor; abstract t.
      Defined.

      Let LiftIdentityPointwise''
      : SpecializedNaturalTransformation (IdentityFunctor (C ^ D)) (IdentityFunctor C ^ IdentityFunctor D).
        nt_simpl_abstract_trailing_props LiftIdentityPointwise'.
      Defined.

      Definition LiftIdentityPointwise
      : SpecializedNaturalTransformation (IdentityFunctor (C ^ D)) (IdentityFunctor C ^ IdentityFunctor D)
        := Eval hnf in LiftIdentityPointwise''.
    End lift.

    Section inverse.
      Let LiftIdentityPointwise'_Inverse
      : SpecializedNaturalTransformation (IdentityFunctor C ^ IdentityFunctor D) (IdentityFunctor (C ^ D)).
        match goal with
          | [ |- SpecializedNaturalTransformation ?F ?G ] =>
            refine (Build_SpecializedNaturalTransformation F G
                                                           (fun x => (Build_SpecializedNaturalTransformation (F x) (G x)
                                                                                                             (fun y => Identity (x y))
                                                                                                             _))
                                                           _)
        end;
        t.
        Grab Existential Variables.
        present_spfunctor; abstract t.
      Defined.

      Let LiftIdentityPointwise''_Inverse
      : SpecializedNaturalTransformation (IdentityFunctor C ^ IdentityFunctor D) (IdentityFunctor (C ^ D)).
        nt_simpl_abstract_trailing_props LiftIdentityPointwise'_Inverse.
      Defined.

      Definition LiftIdentityPointwise_Inverse
      : SpecializedNaturalTransformation (IdentityFunctor C ^ IdentityFunctor D) (IdentityFunctor (C ^ D))
        := Eval hnf in LiftIdentityPointwise''_Inverse.
    End inverse.

    Section theorem.
      Theorem LiftIdentityPointwise_Isomorphism
      : NTComposeT LiftIdentityPointwise LiftIdentityPointwise_Inverse = IdentityNaturalTransformation _
        /\ NTComposeT LiftIdentityPointwise_Inverse LiftIdentityPointwise = IdentityNaturalTransformation _.
        abstract (split; nt_eq; autorewrite with morphism; reflexivity).
      Qed.
    End theorem.
  End identity.

  Section compose.
    Context `(C : @SpecializedCategory objC).
    Context `(D : @SpecializedCategory objD).
    Context `(E : @SpecializedCategory objE).
    Context `(C' : @SpecializedCategory objC').
    Context `(D' : @SpecializedCategory objD').
    Context `(E' : @SpecializedCategory objE').

    Variable G : SpecializedFunctor D E.
    Variable F : SpecializedFunctor C D.
    Variable F' : SpecializedFunctor D' E'.
    Variable G' : SpecializedFunctor C' D'.

    Section lift.
      Let LiftComposeFunctorsPointwise_ComponentsOf x
      : SpecializedNaturalTransformation
          (ComposeFunctors (ComposeFunctors G F)
                           (ComposeFunctors x (ComposeFunctors F' G')))
          (ComposeFunctors G
                           (ComposeFunctors (ComposeFunctors F (ComposeFunctors x F')) G')).
        nt_solve_associator.
      Defined.

      Definition LiftComposeFunctorsPointwise : SpecializedNaturalTransformation (ComposeFunctors G F ^ ComposeFunctors F' G')
                                                                                 (ComposeFunctors (G ^ G') (F ^ F')).
        exists LiftComposeFunctorsPointwise_ComponentsOf;
        present_spcategory; subst_body; simpl.
        abstract (intros; apply NaturalTransformation_eq; rsimplify_morphisms; reflexivity).
      Defined.
    End lift.

    Section inverse.
      Let LiftComposeFunctorsPointwise_Inverse_ComponentsOf x
      : SpecializedNaturalTransformation
          (ComposeFunctors G
                           (ComposeFunctors (ComposeFunctors F (ComposeFunctors x F')) G'))
          (ComposeFunctors (ComposeFunctors G F)
                           (ComposeFunctors x (ComposeFunctors F' G'))).
        nt_solve_associator.
      Defined.

      Definition LiftComposeFunctorsPointwise_Inverse : SpecializedNaturalTransformation (ComposeFunctors (G ^ G') (F ^ F'))
                                                                                         (ComposeFunctors G F ^ ComposeFunctors F' G').
        exists LiftComposeFunctorsPointwise_Inverse_ComponentsOf;
        present_spcategory; subst_body; simpl.
        abstract (intros; apply NaturalTransformation_eq; rsimplify_morphisms; reflexivity).
      Defined.
    End inverse.

    Section theorem.
      Theorem LiftComposeFunctorsPointwise_Isomorphism
      : NTComposeT LiftComposeFunctorsPointwise LiftComposeFunctorsPointwise_Inverse = IdentityNaturalTransformation _
        /\ NTComposeT LiftComposeFunctorsPointwise_Inverse LiftComposeFunctorsPointwise = IdentityNaturalTransformation _.
        abstract (
            split;
            repeat (apply NaturalTransformation_eq || intro || simpl);
            rsimplify_morphisms; reflexivity
          ).
      Qed.
    End theorem.
  End compose.
End NaturalTransformation_Properties.
