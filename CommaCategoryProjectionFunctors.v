Require Import JMeq.
Require Export CommaCategoryInducedFunctors.
Require Import Common Notations DefinitionSimplification DiscreteCategory FEqualDep DefinitionSimplification ExponentialLaws FunctorProduct ProductLaws.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Local Ltac rewrite_step :=
  (progress repeat rewrite LeftIdentity in * )
    || (progress repeat rewrite RightIdentity in * )
    || (progress repeat rewrite @LeftIdentityFunctor in * )
    || (progress repeat rewrite @RightIdentityFunctor in * )
    || (progress (repeat rewrite Associativity; (reflexivity || apply f_equal)))
    || (progress (repeat rewrite <- Associativity; apply f_equal2; trivial; [])).

Local Ltac quick_step :=
  ((progress repeat subst)
     || (apply sig_eq; simpl)
     || apply f_equal
     || (apply f_equal2; trivial; []));
  trivial.

Local Ltac pre_anihilate :=
  subst_body;
  repeat intro; simpl in *;
  repeat quick_step;
  simpl in *;
  destruct_head_hnf @CommaSpecializedCategory_Morphism;
  destruct_head_hnf @CommaSpecializedCategory_Object;
  destruct_sig;
  subst_body;
  unfold Object in *;
  simpl in *;
  trivial.

Local Ltac slice_step :=
  match goal with
    | _ => apply Functor_eq; simpl; intros; pre_anihilate
    | [ |- @JMeq (sig _) _ (sig _) _ ] => apply sig_JMeq; pre_anihilate
    | [ |- JMeq (?f ?x) (?f ?y) ] =>
      apply (@f_equal1_JMeq _ _ x y f); pre_anihilate
    | [ |- JMeq (?f ?x) (?g ?y) ] =>
      apply (@f_equal_JMeq _ _ _ _ x y f g); pre_anihilate
  end.

Local Ltac step :=
  (quick_step
     || rewrite_step
     || (progress auto 1 with category)
     || slice_step);
  trivial.

Local Ltac anihilate := pre_anihilate; repeat step.

Local Ltac induced_step :=
  reflexivity
    || (try_associativity ltac:(rewrite <- Commutes))
    || (try_associativity ltac:(apply f_equal))
    || (match goal with
          | [ H : _ = _ |- _ = _ ] => try_associativity ltac:(rewrite H)
        end).

Local Ltac induced_anihilate :=
  unfold Object in *;
  simpl in *;
  destruct_head @prod;
  simpl in *;
  pre_anihilate;
  repeat induced_step.

Section CommaCategoryProjectionFunctor.
  Context `(A : LocallySmallSpecializedCategory objA).
  Context `(B : LocallySmallSpecializedCategory objB).
  Context `(C : SpecializedCategory objC).

  Definition CommaCategoryProjectionFunctor_ObjectOf (ST : (OppositeCategory (C ^ A)) * (C ^ B)) :
    LocallySmallCat / (A * B : LocallySmallSpecializedCategory _)
    := let S := (fst ST) in
       let T := (snd ST) in
       existT _
              ((S ↓ T : LocallySmallSpecializedCategory _) : LocallySmallCategory, tt)
              (CommaCategoryProjection S T) :
         CommaSpecializedCategory_ObjectT (IdentityFunctor _)
                                          (FunctorFromTerminal LocallySmallCat
                                                               (A * B : LocallySmallSpecializedCategory _)).

  Definition CommaCategoryProjectionFunctor_MorphismOf s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    Morphism (LocallySmallCat / (A * B : LocallySmallSpecializedCategory _))
             (CommaCategoryProjectionFunctor_ObjectOf s)
             (CommaCategoryProjectionFunctor_ObjectOf d).
    hnf in *; constructor; simpl in *.
    exists (CommaCategoryInducedFunctor m, @unit_eq _ _).
    abstract (
        simpl;
        functor_eq;
        destruct_head_hnf @CommaSpecializedCategory_Morphism;
        destruct_sig;
        reflexivity
      ).
  Defined.

  Lemma CommaCategoryProjectionFunctor_FIdentityOf x :
    CommaCategoryProjectionFunctor_MorphismOf (Identity x) = Identity _.
    (* admit. *) Time (expand; anihilate). (* 20 s  :-( *)
  Qed.

  Lemma CommaCategoryProjectionFunctor_FCompositionOf s d d' m m' :
    CommaCategoryProjectionFunctor_MorphismOf (@Compose _ _ s d d' m m')
    = Compose (CommaCategoryProjectionFunctor_MorphismOf m)
              (CommaCategoryProjectionFunctor_MorphismOf m').
    (* admit. *) Time (expand; anihilate). (* 57 s  :-( :-( *)
  Qed.

  Definition CommaCategoryProjectionFunctor :
    SpecializedFunctor ((OppositeCategory (C ^ A)) * (C ^ B))
                       (LocallySmallCat / (A * B : LocallySmallSpecializedCategory _)).
    refine (Build_SpecializedFunctor ((OppositeCategory (C ^ A)) * (C ^ B))
                                     (LocallySmallCat / (A * B : LocallySmallSpecializedCategory _))
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
  Context `(C : LocallySmallSpecializedCategory objC).
  Context `(D : SpecializedCategory objD).

  Local Arguments ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf / .
  Local Arguments ComposeFunctors / .
  Local Arguments LocallySmallCatOverInducedFunctor / .
  (*Local Arguments ProductLaw1Functor / . *)
  Local Arguments CommaCategoryProjectionFunctor / .
  Local Arguments SwapFunctor / .
  Local Arguments ExponentialLaw1Functor_Inverse / .
  Local Arguments IdentityFunctor / .
(*
  Let ArrowCategoryProjection' : SpecializedFunctor (ArrowSpecializedCategory A) A
    := ComposeFunctors fst_Functor (CommaCategoryProjection _ (IdentityFunctor A)).
  Let ArrowCategoryProjection'' : SpecializedFunctor (ArrowSpecializedCategory A) A. functor_simpl_abstract_trailing_props ArrowCategoryProjection'. Defined.
  Definition ArrowCategoryProjection : SpecializedFunctor (ArrowSpecializedCategory A) A := Eval hnf in ArrowCategoryProjection''.
*)

  Definition SliceCategoryProjectionFunctor_pre_pre'
    := Eval hnf in (LocallySmallCatOverInducedFunctor (ProductLaw1Functor C : Morphism LocallySmallCat (C * 1 : LocallySmallSpecializedCategory _) C)).

  Definition SliceCategoryProjectionFunctor_pre_pre : SpecializedFunctor (LocallySmallCat / (C * 1 : LocallySmallSpecializedCategory _)) (LocallySmallCat / C).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor_pre_pre'.
  Defined.

  Arguments SliceCategoryProjectionFunctor_pre_pre / .

(*  Arguments Build_CommaSpecializedCategory_Object' / .

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

  Definition SliceCategoryProjectionFunctor_pre' : ((LocallySmallCat / C) ^ (D * (OppositeCategory (D ^ C)))).
    refine (ComposeFunctors _ ((ExponentialLaw1Functor_Inverse D) * IdentityFunctor (OppositeCategory (D ^ C)))).
    refine (ComposeFunctors _ (SwapFunctor _ _)).
    refine (ComposeFunctors _ (CommaCategoryProjectionFunctor (C : LocallySmallSpecializedCategory _) (1 : LocallySmallSpecializedCategory _) D)).
    (*
    refine_right_compose_functor_by_abstract ((ExponentialLaw1Functor_Inverse D) * IdentityFunctor (OppositeCategory (D ^ C)))%functor.
    refine_right_compose_functor_by_abstract (SwapFunctor (D ^ 1)%functor (OppositeCategory (D ^ C)%functor)).
    refine_right_compose_functor_by_abstract (CommaCategoryProjectionFunctor (C : LocallySmallSpecializedCategory _) (1 : LocallySmallSpecializedCategory _) D).*)
    let F := (eval hnf in SliceCategoryProjectionFunctor_pre_pre) in
    exact F.
(* (LocallySmallCatOverInducedFunctor (ProductLaw1Functor C : Morphism LocallySmallCat (C * 1 : LocallySmallSpecializedCategory _) (C : LocallySmallSpecializedCategory _))). *)
  Defined.

  Definition SliceCategoryProjectionFunctor_pre'' : ((LocallySmallCat / C) ^ (D * (OppositeCategory (D ^ C)))).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor_pre'.
  Defined.

  Definition SliceCategoryProjectionFunctor_pre := Eval hnf in SliceCategoryProjectionFunctor_pre''.

  Definition SliceCategoryProjectionFunctor' : (((LocallySmallCat / C) ^ D) ^ (OppositeCategory (D ^ C))).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    let F := (eval hnf in SliceCategoryProjectionFunctor_pre) in
    exact F.
  Defined.

  Definition SliceCategoryProjectionFunctor'' : (((LocallySmallCat / C) ^ D) ^ (OppositeCategory (D ^ C))).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor'.
  Defined.

  Definition SliceCategoryProjectionFunctor : ((LocallySmallCat / C) ^ D) ^ (OppositeCategory (D ^ C))
    := Eval cbv beta iota zeta delta [SliceCategoryProjectionFunctor''] in SliceCategoryProjectionFunctor''.

  Definition CosliceCategoryProjectionFunctor : ((LocallySmallCat / C) ^ (OppositeCategory D)) ^ (D ^ C).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    refine (ComposeFunctors _ ((OppositeFunctor (ExponentialLaw1Functor_Inverse D)) * IdentityFunctor (D ^ C))).
    refine (ComposeFunctors _ (CommaCategoryProjectionFunctor (1 : LocallySmallSpecializedCategory _) (C : LocallySmallSpecializedCategory _) D)).
    refine (LocallySmallCatOverInducedFunctor _).
    refine (ComposeFunctors _ (SwapFunctor _ _)).
    exact (ProductLaw1Functor _).
  Defined.
End SliceCategoryProjectionFunctor.
