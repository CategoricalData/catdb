Require Import JMeq.
Require Export CommaCategoryInducedFunctors.
Require Import Common Notations DefinitionSimplification DiscreteCategory FEqualDep DefinitionSimplification ExponentialLaws FunctorProduct ProductLaws.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Local Ltac quick_step :=
  ((progress repeat subst)
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
  Context `(A : Category).
  Context `(B : Category).
  Context `(C : Category).

  Definition CommaCategoryProjectionFunctor_ObjectOf (ST : (OppositeCategory (C ^ A)) * (C ^ B)) :
    Cat / (A * B : Category)
    := Eval simpl in
        let S := (fst ST) in
        let T := (snd ST) in
        existT _
               ((S ↓ T : Category) : Category, tt)
               (CommaCategoryProjection S T) :
          CommaCategory_ObjectT (IdentityFunctor _)
                                           (FunctorFromTerminal Cat
                                                                (A * B : Category)).

  Definition CommaCategoryProjectionFunctor_MorphismOf s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    Morphism (Cat / (A * B : Category))
             (CommaCategoryProjectionFunctor_ObjectOf s)
             (CommaCategoryProjectionFunctor_ObjectOf d).
    simpl in *.
    exists (CommaCategoryInducedFunctor m) (@unit_eq _ _).
    simpl.
    abstract (destruct_head prod; functor_eq).
  Defined.

  Lemma CommaCategoryProjectionFunctor_FIdentityOf x :
    CommaCategoryProjectionFunctor_MorphismOf (Identity x) = Identity _.
    abstract anihilate. (* 1.135 s *)
  Qed.

  Lemma CommaCategoryProjectionFunctor_FCompositionOf s d d' m m' :
    CommaCategoryProjectionFunctor_MorphismOf (Compose (s := s) (d := d) (d' := d') m m')
    = Compose (CommaCategoryProjectionFunctor_MorphismOf m)
              (CommaCategoryProjectionFunctor_MorphismOf m').
    abstract anihilate. (* 5.318 s *)
  Qed.

  Definition CommaCategoryProjectionFunctor :
    Functor ((OppositeCategory (C ^ A)) * (C ^ B))
                       (Cat / (A * B : Category)).
    refine (Build_Functor ((OppositeCategory (C ^ A)) * (C ^ B))
                                     (Cat / (A * B : Category))
                                     CommaCategoryProjectionFunctor_ObjectOf
                                     CommaCategoryProjectionFunctor_MorphismOf
                                     _
                                     _);
    intros;
    [ apply CommaCategoryProjectionFunctor_FCompositionOf
    | apply CommaCategoryProjectionFunctor_FIdentityOf ].
  Defined.
End CommaCategoryProjectionFunctor.

Section SliceCategoryProjectionFunctor.
  Context `(C : Category).
  Context `(D : Category).

  Local Arguments ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf / .
  Local Arguments ComposeFunctors / .
  Local Arguments CatOverInducedFunctor / .
  (*Local Arguments ProductLaw1Functor / . *)
  Local Arguments CommaCategoryProjectionFunctor / .
  Local Arguments SwapFunctor / .
  Local Arguments ExponentialLaw1Functor_Inverse / .
  Local Arguments IdentityFunctor / .
(*
  Let ArrowCategoryProjection' : Functor (ArrowCategory A) A
    := ComposeFunctors fst_Functor (CommaCategoryProjection _ (IdentityFunctor A)).
  Let ArrowCategoryProjection'' : Functor (ArrowCategory A) A. functor_simpl_abstract_trailing_props ArrowCategoryProjection'. Defined.
  Definition ArrowCategoryProjection : Functor (ArrowCategory A) A := Eval hnf in ArrowCategoryProjection''.
*)

  Definition SliceCategoryProjectionFunctor_pre_pre'
    := Eval hnf in (CatOverInducedFunctor (ProductLaw1Functor C : Morphism Cat (C * 1 : Category) C)).

  Definition SliceCategoryProjectionFunctor_pre_pre : Functor (Cat / (C * 1 : Category)) (Cat / C).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor_pre_pre'.
  Defined.

  Arguments SliceCategoryProjectionFunctor_pre_pre / .

(*  Arguments Build_CommaCategory_Object' / .

  Eval simpl in SliceCategoryProjectionFunctor_pre_pre'.

  Set Printing Coercions.
  Print SliceCategoryProjectionFunctor_pre_pre'.
    functor_abstract_trailing_props
  Defined.

*)
  (*Local Ltac pose_functor_by_abstract H F :=
    let T := type of F in assert (H : T) by (functor_simpl_abstract_trailing_props F).

  Local Ltac refine_right_compose_functor_by_abstract F :=
    let H := fresh in pose_functor_by_abstract H F; refine (ComposeFunctors _ H); clear H.*)

  Definition SliceCategoryProjectionFunctor_pre' : ((Cat / C) ^ (D * (OppositeCategory (D ^ C)))).
    refine (ComposeFunctors _ ((ExponentialLaw1Functor_Inverse D) * IdentityFunctor (OppositeCategory (D ^ C)))).
    refine (ComposeFunctors _ (SwapFunctor _ _)).
    refine (ComposeFunctors _ (CommaCategoryProjectionFunctor (C : Category) (1 : Category) D)).
    (*
    refine_right_compose_functor_by_abstract ((ExponentialLaw1Functor_Inverse D) * IdentityFunctor (OppositeCategory (D ^ C)))%functor.
    refine_right_compose_functor_by_abstract (SwapFunctor (D ^ 1)%functor (OppositeCategory (D ^ C)%functor)).
    refine_right_compose_functor_by_abstract (CommaCategoryProjectionFunctor (C : Category) (1 : Category) D).*)
    let F := (eval hnf in SliceCategoryProjectionFunctor_pre_pre) in
    exact F.
(* (CatOverInducedFunctor (ProductLaw1Functor C : Morphism Cat (C * 1 : Category) (C : Category))). *)
  Defined.

  Definition SliceCategoryProjectionFunctor_pre'' : ((Cat / C) ^ (D * (OppositeCategory (D ^ C)))).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor_pre'.
  Defined.

  Definition SliceCategoryProjectionFunctor_pre := Eval hnf in SliceCategoryProjectionFunctor_pre''.

  Definition SliceCategoryProjectionFunctor' : (((Cat / C) ^ D) ^ (OppositeCategory (D ^ C))).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    let F := (eval hnf in SliceCategoryProjectionFunctor_pre) in
    exact F.
  Defined.

  Definition SliceCategoryProjectionFunctor'' : (((Cat / C) ^ D) ^ (OppositeCategory (D ^ C))).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor'.
  Defined.

  Definition SliceCategoryProjectionFunctor : ((Cat / C) ^ D) ^ (OppositeCategory (D ^ C))
    := Eval cbv beta iota zeta delta [SliceCategoryProjectionFunctor''] in SliceCategoryProjectionFunctor''.

  Definition CosliceCategoryProjectionFunctor : ((Cat / C) ^ (OppositeCategory D)) ^ (D ^ C).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    refine (ComposeFunctors _ ((OppositeFunctor (ExponentialLaw1Functor_Inverse D)) * IdentityFunctor (D ^ C))).
    refine (ComposeFunctors _ (CommaCategoryProjectionFunctor (1 : Category) (C : Category) D)).
    refine (CatOverInducedFunctor _).
    refine (ComposeFunctors _ (SwapFunctor _ _)).
    exact (ProductLaw1Functor _).
  Defined.
End SliceCategoryProjectionFunctor.
