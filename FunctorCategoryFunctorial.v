Require Export FunctorCategory NaturalTransformation.
Require Import Common Notations Cat ProductCategory Duals ExponentialLaws CanonicalStructureSimplification FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Section FunctorCategoryParts.
  Section MorphismOf.
    Variable C : Category.
    Variable D : Category.
    Variable C' : Category.
    Variable D' : Category.

    Variable F : Functor C C'.
    Variable G : Functor D' D.

    Definition FunctorCategoryFunctor_MorphismOf_ObjectOf : (C ^ D)%functor -> (C' ^ D')%functor
      := fun H => ComposeFunctors F (ComposeFunctors H G).

    Global Arguments FunctorCategoryFunctor_MorphismOf_ObjectOf _ / .

    Definition FunctorCategoryFunctor_MorphismOf_MorphismOf s d (m : Morphism (C ^ D) s d) :
      Morphism (C' ^ D') (FunctorCategoryFunctor_MorphismOf_ObjectOf s) (FunctorCategoryFunctor_MorphismOf_ObjectOf d)
      := NTComposeF (IdentityNaturalTransformation _) (NTComposeF m (IdentityNaturalTransformation _)).

    Global Arguments FunctorCategoryFunctor_MorphismOf_MorphismOf _ _ _ / .

    Definition FunctorCategoryFunctor_MorphismOf : Functor (C ^ D) (C' ^ D').
      refine (Build_Functor
                (C ^ D) (C' ^ D')
                FunctorCategoryFunctor_MorphismOf_ObjectOf
                FunctorCategoryFunctor_MorphismOf_MorphismOf
                _
                _);
      abstract (
          intros; simpl;
          apply NaturalTransformation_eq;
          rsimplify_morphisms;
          reflexivity
        ).
    Defined.
  End MorphismOf.

  Section FIdentityOf.
    Variable C : Category.
    Variable D : Category.

    Lemma FunctorCategoryFunctor_FIdentityOf : FunctorCategoryFunctor_MorphismOf (IdentityFunctor C) (IdentityFunctor D) = IdentityFunctor _.
      repeat (intro || apply Functor_eq || nt_eq); simpl; subst; JMeq_eq; rsimplify_morphisms; reflexivity.
    Qed.
  End FIdentityOf.

  Section FCompositionOf.
    Variable C : Category.
    Variable D : Category.
    Variable C' : Category.
    Variable D' : Category.
    Variable C'' : Category.
    Variable D'' : Category.

    Variable F' : Functor C' C''.
    Variable G : Functor D D'.
    Variable F : Functor C C'.
    Variable G' : Functor  D' D''.

    Lemma FunctorCategoryFunctor_FCompositionOf : FunctorCategoryFunctor_MorphismOf (ComposeFunctors F' F) (ComposeFunctors G' G)
                                                  = ComposeFunctors (FunctorCategoryFunctor_MorphismOf F' G) (FunctorCategoryFunctor_MorphismOf F G').
      abstract (repeat (intro || apply Functor_eq || nt_eq); simpl; subst; JMeq_eq; rsimplify_morphisms; reflexivity).
    Qed.
  End FCompositionOf.
End FunctorCategoryParts.

Section FunctorCategoryFunctor.
  Definition FunctorCategoryFunctor : Functor (Cat * (OppositeCategory Cat)) Cat.
    refine (Build_Functor (Cat * (OppositeCategory Cat)) Cat
                                     (fun CD => (fst CD) ^ (snd CD) : Category)
                                     (fun s d m => FunctorCategoryFunctor_MorphismOf (fst m) (snd m))
                                     _
                                     _);
    simpl;
    abstract (intros; apply FunctorCategoryFunctor_FCompositionOf || apply FunctorCategoryFunctor_FIdentityOf).
  Defined.

  (* Definition FunctorCategoryFunctor : ((Cat ^ Cat) ^ (OppositeCategory Cat))%category
    := ExponentialLaw4Functor_Inverse _ _ _ FunctorCategoryUncurriedFunctor. *)
End FunctorCategoryFunctor.

Notation "F ^ G" := (FunctorCategoryFunctor_MorphismOf F G) : functor_scope.

Section NaturalTransformation.
  Variable C : Category.
  Variable D : Category.
  Variable C' : Category.
  Variable D' : Category.

  Variables F G : Functor C D.
  Variables F' G' : Functor C' D'.

  Variable T : NaturalTransformation F G.
  Variable T' : NaturalTransformation F' G'.

  Definition LiftNaturalTransformationPointwise : NaturalTransformation (F ^ F') (G ^ G').
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
                                                       (fun _ => NTComposeF T (NTComposeF (IdentityNaturalTransformation _) T'))
                                                       _)
    end.
    abstract (
        intros;
        simpl;
        apply NaturalTransformation_eq;
        simpl in *;
          intros;
        rsimplify_morphisms;
        autorewrite with morphism;
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
    Variable C : Category.
    Variable D : Category.

    Local Ltac t := intros; simpl; nt_eq; rsimplify_morphisms; try reflexivity.

    Section lift.
      Let LiftIdentityPointwise'
      : NaturalTransformation (IdentityFunctor (C ^ D)) (IdentityFunctor C ^ IdentityFunctor D).
        match goal with
          | [ |- NaturalTransformation ?F ?G ] =>
            refine (Build_NaturalTransformation F G
                                                           (fun x => (Build_NaturalTransformation (F x) (G x)
                                                                                                             (fun y => Identity (x y))
                                                                                                             _))
                                                           _)
        end;
        t.
        Grab Existential Variables.
        abstract t.
      Defined.

      Let LiftIdentityPointwise''
      : NaturalTransformation (IdentityFunctor (C ^ D)) (IdentityFunctor C ^ IdentityFunctor D).
        nt_simpl_abstract_trailing_props LiftIdentityPointwise'.
      Defined.

      Definition LiftIdentityPointwise
      : NaturalTransformation (IdentityFunctor (C ^ D)) (IdentityFunctor C ^ IdentityFunctor D)
        := Eval hnf in LiftIdentityPointwise''.
    End lift.

    Section inverse.
      Let LiftIdentityPointwise'_Inverse
      : NaturalTransformation (IdentityFunctor C ^ IdentityFunctor D) (IdentityFunctor (C ^ D)).
        match goal with
          | [ |- NaturalTransformation ?F ?G ] =>
            refine (Build_NaturalTransformation F G
                                                           (fun x => (Build_NaturalTransformation (F x) (G x)
                                                                                                             (fun y => Identity (x y))
                                                                                                             _))
                                                           _)
        end;
        t.
        Grab Existential Variables.
        abstract t.
      Defined.

      Let LiftIdentityPointwise''_Inverse
      : NaturalTransformation (IdentityFunctor C ^ IdentityFunctor D) (IdentityFunctor (C ^ D)).
        nt_simpl_abstract_trailing_props LiftIdentityPointwise'_Inverse.
      Defined.

      Definition LiftIdentityPointwise_Inverse
      : NaturalTransformation (IdentityFunctor C ^ IdentityFunctor D) (IdentityFunctor (C ^ D))
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
    Variable C : Category.
    Variable D : Category.
    Variable E : Category.
    Variable C' : Category.
    Variable D' : Category.
    Variable E' : Category.

    Variable G : Functor D E.
    Variable F : Functor C D.
    Variable F' : Functor D' E'.
    Variable G' : Functor C' D'.

    Section lift.
      Let LiftComposeFunctorsPointwise_ComponentsOf x
      : NaturalTransformation
          (ComposeFunctors (ComposeFunctors G F)
                           (ComposeFunctors x (ComposeFunctors F' G')))
          (ComposeFunctors G
                           (ComposeFunctors (ComposeFunctors F (ComposeFunctors x F')) G')).
        nt_solve_associator.
      Defined.

      Definition LiftComposeFunctorsPointwise : NaturalTransformation (ComposeFunctors G F ^ ComposeFunctors F' G')
                                                                                 (ComposeFunctors (G ^ G') (F ^ F')).
        exists LiftComposeFunctorsPointwise_ComponentsOf;
        subst_body; simpl.
        abstract (intros; apply NaturalTransformation_eq; rsimplify_morphisms; reflexivity).
      Defined.
    End lift.

    Section inverse.
      Let LiftComposeFunctorsPointwise_Inverse_ComponentsOf x
      : NaturalTransformation
          (ComposeFunctors G
                           (ComposeFunctors (ComposeFunctors F (ComposeFunctors x F')) G'))
          (ComposeFunctors (ComposeFunctors G F)
                           (ComposeFunctors x (ComposeFunctors F' G'))).
        nt_solve_associator.
      Defined.

      Definition LiftComposeFunctorsPointwise_Inverse : NaturalTransformation (ComposeFunctors (G ^ G') (F ^ F'))
                                                                                         (ComposeFunctors G F ^ ComposeFunctors F' G').
        exists LiftComposeFunctorsPointwise_Inverse_ComponentsOf;
        subst_body; simpl.
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
