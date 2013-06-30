Require Import JMeq.
Require Export CommaCategoryInducedFunctors.
Require Import Common Notations DefinitionSimplification DiscreteCategory FEqualDep DefinitionSimplification ExponentialLaws FunctorProduct ProductLaws.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Local Ltac quick_step :=
  try ((progress repeat subst)
         || (apply sig_eq; simpl)
         || (apply CommaCategory_Morphism_eq; simpl)
         || (apply CommaCategory_Morphism_JMeq; simpl)
         || (apply CommaCategory_Object_eq; simpl)
         || apply f_equal
         || (apply f_equal2; trivial; []));
  trivial.

Local Ltac pre_anihilate :=
  subst_body;
  repeat intro;
  repeat quick_step;
  simpl in *;
  destruct_head_hnf @CommaCategory_Morphism;
  destruct_head_hnf @CommaCategory_Object;
  destruct_head_hnf @prod;
  subst_body;
  simpl in *;
  trivial.

Local Ltac anihilate :=
  pre_anihilate;
  try apply Functor_eq;
  simpl; intros;
  repeat quick_step;
  autorewrite with morphism;
  trivial.

Section CommaCategoryProjectionFunctor.
  Variable A : Category.
  Variable B : Category.
  Variable C : Category.

  Local Open Scope morphism_scope.

  Definition CommaCategoryProjectionFunctor_ObjectOf (ST : (OppositeCategory (C ^ A)) * (C ^ B))
  : Cat / (A * B).
    exists (fst ST ↓ snd ST) tt.
    exact (CommaCategoryProjection (fst ST) (snd ST)).
  Defined.

  Definition CommaCategoryProjectionFunctor_MorphismOf s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d)
  : Morphism (Cat / (A * B))
             (CommaCategoryProjectionFunctor_ObjectOf s)
             (CommaCategoryProjectionFunctor_ObjectOf d).
    exists (CommaCategoryInducedFunctor m) (@unit_eq _ _).
    simpl.
    abstract (destruct_head prod; apply Functor_eq; simpl; reflexivity).
  Defined.

  Lemma CommaCategoryProjectionFunctor_FIdentityOf x
  : CommaCategoryProjectionFunctor_MorphismOf (Identity x) = Identity _.
    abstract anihilate. (* 1.038 s *)
  Qed.

  Lemma CommaCategoryProjectionFunctor_FCompositionOf s d d' m m'
  : CommaCategoryProjectionFunctor_MorphismOf (Compose (s := s) (d := d) (d' := d') m' m)
    = CommaCategoryProjectionFunctor_MorphismOf m' ∘ CommaCategoryProjectionFunctor_MorphismOf m.
    abstract anihilate. (* 5.112 s *)
  Qed.

  Definition CommaCategoryProjectionFunctor
  : Functor ((OppositeCategory (C ^ A)) * (C ^ B))
            (Cat / (A * B))
    := Build_Functor ((OppositeCategory (C ^ A)) * (C ^ B))
                     (Cat / (A * B))
                     CommaCategoryProjectionFunctor_ObjectOf
                     CommaCategoryProjectionFunctor_MorphismOf
                     CommaCategoryProjectionFunctor_FCompositionOf
                     CommaCategoryProjectionFunctor_FIdentityOf.
End CommaCategoryProjectionFunctor.

Section SliceCategoryProjectionFunctor.
  Variable C : Category.
  Variable D : Category.

  Local Open Scope functor_scope.
  Local Open Scope category_scope.

  Definition SliceCategoryProjectionFunctor_pre_pre : Functor (Cat / (C * 1)) (Cat / C)
    := CatOverInducedFunctor (ProductLaw1Functor C : Morphism Cat (C * 1) C).

  Definition SliceCategoryProjectionFunctor_pre : ((Cat / C) ^ (D * (OppositeCategory (D ^ C)))).
    refine (_ ∘ ((ExponentialLaw1Functor_Inverse D) * IdentityFunctor (OppositeCategory (D ^ C)))).
    refine (_ ∘ (SwapFunctor _ _)).
    refine (_ ∘ (CommaCategoryProjectionFunctor C 1 D)).
    exact SliceCategoryProjectionFunctor_pre_pre.
  Defined.

  Definition SliceCategoryProjectionFunctor : (((Cat / C) ^ D) ^ (OppositeCategory (D ^ C))).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    exact SliceCategoryProjectionFunctor_pre.
  Defined.

  Definition CosliceCategoryProjectionFunctor : ((Cat / C) ^ (OppositeCategory D)) ^ (D ^ C).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    refine (_ ∘ ((OppositeFunctor (ExponentialLaw1Functor_Inverse D)) * IdentityFunctor (D ^ C))).
    refine (_ ∘ CommaCategoryProjectionFunctor 1 C D).
    refine (CatOverInducedFunctor _).
    hnf.
    refine (_ ∘ SwapFunctor _ _).
    exact (ProductLaw1Functor _).
  Defined.
End SliceCategoryProjectionFunctor.
