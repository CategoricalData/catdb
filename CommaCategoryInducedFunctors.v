Require Import JMeq.
Require Export CommaCategoryProjection Cat Duals FunctorCategory.
Require Import Common Notations DefinitionSimplification DiscreteCategory FEqualDep DefinitionSimplification ExponentialLaws FunctorProduct ProductLaws CanonicalStructureSimplification.

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
     || (apply CommaCategory_Morphism_eq; simpl)
     || (simpl; apply f_equal)
     || (simpl; apply f_equal2; trivial; []));
  trivial.

Local Ltac pre_anihilate :=
  subst_body;
  repeat intro;
  repeat quick_step;
  simpl in *;
  destruct_head @CommaCategory_Morphism;
  destruct_head @CommaCategory_Object;
  destruct_head @prod;
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
  pre_anihilate;
  repeat induced_step.

Section CommaCategoryInducedFunctor.
  Variable A : Category.
  Variable B : Category.
  Variable C : Category.

  Definition CommaCategoryInducedFunctor_ObjectOf s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d)
      (x : fst s ↓ snd s) : (fst d ↓ snd d)
    := Eval simpl in
        existT _
               (projT1 x)
               (Compose ((snd m) (snd (projT1 x))) (Compose (projT2 x) ((fst m) (fst (projT1 x))))) :
          CommaCategory_ObjectT (fst d) (snd d).

  Definition CommaCategoryInducedFunctor_MorphismOf s d m s0 d0 (m0 : Morphism (fst s ↓ snd s) s0 d0) :
    Morphism (fst d ↓ snd d)
             (@CommaCategoryInducedFunctor_ObjectOf s d m s0)
             (@CommaCategoryInducedFunctor_ObjectOf s d m d0).
    simpl.
    let s := match goal with |- CommaCategory_Morphism ?s ?d => constr:(s) end in
    let d := match goal with |- CommaCategory_Morphism ?s ?d => constr:(d) end in
    refine (Build_CommaCategory_Morphism s d (CCM_g m0) (CCM_h m0) _);
      simpl in *; clear.
    abstract induced_anihilate. (* 4.097 s *)
  Defined.

  Definition CommaCategoryInducedFunctor s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    Functor (fst s ↓ snd s) (fst d ↓ snd d).
    refine (Build_Functor (fst s ↓ snd s) (fst d ↓ snd d)
                                     (@CommaCategoryInducedFunctor_ObjectOf s d m)
                                     (@CommaCategoryInducedFunctor_MorphismOf s d m)
                                     _
                                     _
           );
    abstract pre_anihilate.
  Defined.
End CommaCategoryInducedFunctor.

Section SliceCategoryInducedFunctor.
  Variable C : Category.

  Section Slice_Coslice.
    Variable D : Category.

    (* TODO(jgross): See if this can be recast as an exponential law functor about how Cat ^ 1 is isomorphic to Cat, or something *)
    Definition SliceCategoryInducedFunctor_NT s d (m : Morphism D s d) :
      NaturalTransformation (FunctorFromTerminal D s)
                                       (FunctorFromTerminal D d).
      exists (fun _ : unit => m).
      simpl; intros; clear;
      abstract (autorewrite with category; reflexivity).
    Defined.

    Variable F : Functor C D.
    Variable a : D.

    Section Slice.
      Local Notation "F ↓ A" := (SliceCategory A F) : category_scope.

      Local Arguments CommaCategoryInducedFunctor_MorphismOf / .
      Local Arguments CommaCategoryInducedFunctor_ObjectOf / .

      Let SliceCategoryInducedFunctor' F' a' (m : Morphism D a a') (T : NaturalTransformation F' F)
      : Functor (F ↓ a) (F' ↓ a').
        functor_simpl_abstract_trailing_props (CommaCategoryInducedFunctor (s := (F, FunctorFromTerminal D a))
                                                                           (d := (F', FunctorFromTerminal D a'))
                                                                           (T, @SliceCategoryInducedFunctor_NT a a' m)).
      Defined.
      Definition SliceCategoryInducedFunctor F' a' (m : Morphism D a a') (T : NaturalTransformation F' F)
      : Functor (F ↓ a) (F' ↓ a')
        := Eval hnf in @SliceCategoryInducedFunctor' F' a' m T.

      Definition SliceCategoryNTInducedFunctor F' T := @SliceCategoryInducedFunctor F' a (Identity _) T.
      Definition SliceCategoryMorphismInducedFunctor a' m := @SliceCategoryInducedFunctor F a' m (IdentityNaturalTransformation _).
    End Slice.

    Section Coslice.
      Local Notation "A ↓ F" := (CosliceCategory A F) : category_scope.

      Local Arguments CommaCategoryInducedFunctor_MorphismOf / .
      Local Arguments CommaCategoryInducedFunctor_ObjectOf / .

      Let CosliceCategoryInducedFunctor' F' a' (m : Morphism D a' a) (T : NaturalTransformation F F')
      : Functor (a ↓ F) (a' ↓ F').
        functor_simpl_abstract_trailing_props (CommaCategoryInducedFunctor (s := (FunctorFromTerminal D a, F))
                                                                           (d := (FunctorFromTerminal D a', F'))
                                                                           (@SliceCategoryInducedFunctor_NT a' a m, T)).
      Defined.
      Definition CosliceCategoryInducedFunctor F' a' (m : Morphism D a' a) (T : NaturalTransformation F F')
      : Functor (a ↓ F) (a' ↓ F')
        := Eval hnf in @CosliceCategoryInducedFunctor' F' a' m T.

      Definition CosliceCategoryNTInducedFunctor F' T := @CosliceCategoryInducedFunctor F' a (Identity _) T.
      Definition CosliceCategoryMorphismInducedFunctor a' m := @CosliceCategoryInducedFunctor F a' m (IdentityNaturalTransformation _).
    End Coslice.
  End Slice_Coslice.

  Definition SliceCategoryOverInducedFunctor a a' (m : Morphism C a a') : Functor (C / a) (C / a')
    := Eval hnf in SliceCategoryMorphismInducedFunctor _ _ _ m.
  Definition CosliceCategoryOverInducedFunctor a a' (m : Morphism C a' a) : Functor (a \ C) (a' \ C)
    := Eval hnf in CosliceCategoryMorphismInducedFunctor _ _ _ m.
End SliceCategoryInducedFunctor.

Section CatOverInducedFunctor.
  (* Let's do this from scratch so we get better polymorphism *)
  Let C := Cat.
  (*Local Opaque Cat.*)

  Let CatOverInducedFunctor_ObjectOf a a' (m : Morphism C a a') : C / a -> C / a'.
    refine (fun x => existT (fun αβ : _ * unit => Morphism C (fst αβ) a')
                            (projT1 x)
                            _ :
                       CommaCategory_ObjectT (IdentityFunctor C) (FunctorFromTerminal C a')).
    functor_simpl_abstract_trailing_props (Compose m (projT2 x)).
  Defined.
  Let OverCatInducedFunctor_ObjectOf a a' (m : Morphism C a' a) : a \ C -> a' \ C.
    refine (fun x => existT (fun αβ : unit * _ => Morphism C a' (snd αβ))
                            (projT1 x)
                            _ :
                       CommaCategory_ObjectT (FunctorFromTerminal C a') (IdentityFunctor C)).
    functor_simpl_abstract_trailing_props (Compose (projT2 x) m).
  Defined.

  Let CatOverInducedFunctor_MorphismOf a a' (m : Morphism C a a') s d (m0 : Morphism (C / a) s d) :
    Morphism (C / a') (@CatOverInducedFunctor_ObjectOf _ _ m s) (@CatOverInducedFunctor_ObjectOf _ _ m d).
    refine (_ : CommaCategory_MorphismT _ _).
    exists (projT1 m0).
      subst_body; simpl in *; clear.
    abstract anihilate.
  Defined.
  Let OverCatInducedFunctor_MorphismOf a a' (m : Morphism C a' a) s d (m0 : Morphism (a \ C) s d) :
    Morphism (a' \ C) (@OverCatInducedFunctor_ObjectOf _ _ m s) (@OverCatInducedFunctor_ObjectOf _ _ m d).
    refine (_ : CommaCategory_MorphismT _ _).
    exists (projT1 m0);
      subst_body; simpl in *; clear.
    abstract anihilate.
  Defined.

  Local Opaque Cat.
  Let CatOverInducedFunctor'' a a' (m : Morphism C a a') : Functor (C / a) (C / a').
    refine (Build_Functor (C / a) (C / a')
                                     (@CatOverInducedFunctor_ObjectOf _ _ m)
                                     (@CatOverInducedFunctor_MorphismOf _ _ m)
                                     _
                                     _
           );
    subst_body; simpl; clear;
    (* admit. *)
    abstract anihilate.
  Defined.
  Let OverCatInducedFunctor'' a a' (m : Morphism C a' a) : Functor (a \ C) (a' \ C).
    refine (Build_Functor (a \ C) (a' \ C)
                                     (@OverCatInducedFunctor_ObjectOf _ _ m)
                                     (@OverCatInducedFunctor_MorphismOf _ _ m)
                                     _
                                     _
           );
    subst_body; simpl; clear;
    (* admit. *) abstract anihilate.
  Defined.

  Let CatOverInducedFunctor''' a a' (m : Morphism C a a') : Functor (C / a) (C / a').
    simpl_definition_by_tac_and_exact (@CatOverInducedFunctor'' _ _ m) ltac:(subst_body; eta_red).
  Defined.
  Let OverCatInducedFunctor''' a a' (m : Morphism C a' a) : Functor (a \ C) (a' \ C).
    simpl_definition_by_tac_and_exact (@OverCatInducedFunctor'' _ _ m) ltac:(subst_body; eta_red).
  Defined.

  Definition CatOverInducedFunctor a a' (m : Morphism C a a') : Functor (C / a) (C / a')
    := Eval cbv beta iota zeta delta [CatOverInducedFunctor'''] in @CatOverInducedFunctor''' _ _ m.
  Definition OverCatInducedFunctor a a' (m : Morphism C a' a) : Functor (a \ C) (a' \ C)
    := Eval cbv beta iota zeta delta [OverCatInducedFunctor'''] in @OverCatInducedFunctor''' _ _ m.
  Local Transparent Cat.
End CatOverInducedFunctor.
