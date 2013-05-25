Require Import JMeq.
Require Export CommaCategoryProjection SmallCat Duals FunctorCategory.
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

Section CommaCategoryInducedFunctor.
  Context `(A : @SpecializedCategory objA).
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).

  Let CommaCategoryInducedFunctor_ObjectOf s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d)
      (x : fst s ↓ snd s) : (fst d ↓ snd d)
    := existT _
              (projT1 x)
              (Compose ((snd m) (snd (projT1 x))) (Compose (projT2 x) ((fst m) (fst (projT1 x))))) :
         CommaSpecializedCategory_ObjectT (fst d) (snd d).

  Let CommaCategoryInducedFunctor_MorphismOf s d m s0 d0 (m0 : Morphism (fst s ↓ snd s) s0 d0) :
    Morphism (fst d ↓ snd d)
             (@CommaCategoryInducedFunctor_ObjectOf s d m s0)
             (@CommaCategoryInducedFunctor_ObjectOf s d m d0).
    refine (_ : CommaSpecializedCategory_MorphismT _ _); subst_body; simpl in *.
    exists (projT1 m0);
      simpl in *; clear.
    abstract induced_anihilate.
  Defined.

  Let CommaCategoryInducedFunctor' s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    SpecializedFunctor (fst s ↓ snd s) (fst d ↓ snd d).
    refine (Build_SpecializedFunctor (fst s ↓ snd s) (fst d ↓ snd d)
                                     (@CommaCategoryInducedFunctor_ObjectOf s d m)
                                     (@CommaCategoryInducedFunctor_MorphismOf s d m)
                                     _
                                     _
           );
    subst_body; simpl; clear;
    (* admit. *)
    abstract pre_anihilate. (* TODO(jgross): speed this up :-( *)
  Defined.

  Let CommaCategoryInducedFunctor'' s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    SpecializedFunctor (fst s ↓ snd s) (fst d ↓ snd d).
    simpl_definition_by_tac_and_exact (@CommaCategoryInducedFunctor' s d m) ltac:(subst_body; eta_red).
  Defined.

  Definition CommaCategoryInducedFunctor s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    SpecializedFunctor (fst s ↓ snd s) (fst d ↓ snd d)
    := Eval cbv beta iota zeta delta [CommaCategoryInducedFunctor''] in @CommaCategoryInducedFunctor'' s d m.
End CommaCategoryInducedFunctor.

Section SliceCategoryInducedFunctor.
  Context `(C : @SpecializedCategory objC).

  Section Slice_Coslice.
    Context `(D : @SpecializedCategory objD).

    (* TODO(jgross): See if this can be recast as an exponential law functor about how Cat ^ 1 is isomorphic to Cat, or something *)
    Definition SliceCategoryInducedFunctor_NT s d (m : Morphism D s d) :
      SpecializedNaturalTransformation (FunctorFromTerminal D s)
                                       (FunctorFromTerminal D d).
      exists (fun _ : unit => m).
      simpl; intros; clear;
      abstract (autorewrite with category; reflexivity).
    Defined.

    Variable F : SpecializedFunctor C D.
    Variable a : D.

    Section Slice.
      Local Notation "F ↓ A" := (SliceSpecializedCategory A F) : category_scope.

      Let SliceCategoryInducedFunctor' F' a' (m : Morphism D a a') (T : SpecializedNaturalTransformation F' F) :
        SpecializedFunctor (F ↓ a) (F' ↓ a').
        functor_simpl_abstract_trailing_props (CommaCategoryInducedFunctor (s := (F, FunctorFromTerminal D a))
                                                                       (d := (F', FunctorFromTerminal D a'))
                                                                       (T, @SliceCategoryInducedFunctor_NT a a' m)).
      Defined.
      Definition SliceCategoryInducedFunctor F' a' (m : Morphism D a a') (T : SpecializedNaturalTransformation F' F) :
        SpecializedFunctor (F ↓ a) (F' ↓ a')
        := Eval hnf in @SliceCategoryInducedFunctor' F' a' m T.

      Definition SliceCategoryNTInducedFunctor F' T := @SliceCategoryInducedFunctor F' a (Identity _) T.
      Definition SliceCategoryMorphismInducedFunctor a' m := @SliceCategoryInducedFunctor F a' m (IdentityNaturalTransformation _).
    End Slice.

    Section Coslice.
      Local Notation "A ↓ F" := (CosliceSpecializedCategory A F) : category_scope.

      Let CosliceCategoryInducedFunctor' F' a' (m : Morphism D a' a) (T : SpecializedNaturalTransformation F F') :
        SpecializedFunctor (a ↓ F) (a' ↓ F').
        functor_simpl_abstract_trailing_props (CommaCategoryInducedFunctor (s := (FunctorFromTerminal D a, F))
                                                                       (d := (FunctorFromTerminal D a', F'))
                                                                       (@SliceCategoryInducedFunctor_NT a' a m, T)).
      Defined.
      Definition CosliceCategoryInducedFunctor F' a' (m : Morphism D a' a) (T : SpecializedNaturalTransformation F F') :
        SpecializedFunctor (a ↓ F) (a' ↓ F')
        := Eval hnf in @CosliceCategoryInducedFunctor' F' a' m T.

      Definition CosliceCategoryNTInducedFunctor F' T := @CosliceCategoryInducedFunctor F' a (Identity _) T.
      Definition CosliceCategoryMorphismInducedFunctor a' m := @CosliceCategoryInducedFunctor F a' m (IdentityNaturalTransformation _).
    End Coslice.
  End Slice_Coslice.

  Definition SliceCategoryOverInducedFunctor a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a')
    := Eval hnf in SliceCategoryMorphismInducedFunctor _ _ _ m.
  Definition CosliceCategoryOverInducedFunctor a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C)
    := Eval hnf in CosliceCategoryMorphismInducedFunctor _ _ _ m.
End SliceCategoryInducedFunctor.

Section LocallySmallCatOverInducedFunctor.
  (* Let's do this from scratch so we get better polymorphism *)
  Let C := LocallySmallCat.
  (*Local Opaque LocallySmallCat.*)

  Let LocallySmallCatOverInducedFunctor_ObjectOf a a' (m : Morphism C a a') : C / a -> C / a'.
    refine (fun x => existT (fun αβ : _ * unit => Morphism C (fst αβ) a')
                            (projT1 x)
                            _ :
                       CommaSpecializedCategory_ObjectT (IdentityFunctor C) (FunctorFromTerminal C a')).
    functor_simpl_abstract_trailing_props (Compose m (projT2 x)).
  Defined.
  Let OverLocallySmallCatInducedFunctor_ObjectOf a a' (m : Morphism C a' a) : a \ C -> a' \ C.
    refine (fun x => existT (fun αβ : unit * _ => Morphism C a' (snd αβ))
                            (projT1 x)
                            _ :
                       CommaSpecializedCategory_ObjectT (FunctorFromTerminal C a') (IdentityFunctor C)).
    functor_simpl_abstract_trailing_props (Compose (projT2 x) m).
  Defined.

  Let LocallySmallCatOverInducedFunctor_MorphismOf a a' (m : Morphism C a a') s d (m0 : Morphism (C / a) s d) :
    Morphism (C / a') (@LocallySmallCatOverInducedFunctor_ObjectOf _ _ m s) (@LocallySmallCatOverInducedFunctor_ObjectOf _ _ m d).
    refine (_ : CommaSpecializedCategory_MorphismT _ _).
    exists (projT1 m0).
      subst_body; simpl in *; clear.
    abstract anihilate.
  Defined.
  Let OverLocallySmallCatInducedFunctor_MorphismOf a a' (m : Morphism C a' a) s d (m0 : Morphism (a \ C) s d) :
    Morphism (a' \ C) (@OverLocallySmallCatInducedFunctor_ObjectOf _ _ m s) (@OverLocallySmallCatInducedFunctor_ObjectOf _ _ m d).
    refine (_ : CommaSpecializedCategory_MorphismT _ _).
    exists (projT1 m0);
      subst_body; simpl in *; clear.
    abstract anihilate.
  Defined.

  Local Opaque LocallySmallCat.
  Let LocallySmallCatOverInducedFunctor'' a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a').
    refine (Build_SpecializedFunctor (C / a) (C / a')
                                     (@LocallySmallCatOverInducedFunctor_ObjectOf _ _ m)
                                     (@LocallySmallCatOverInducedFunctor_MorphismOf _ _ m)
                                     _
                                     _
           );
    subst_body; simpl; clear;
    (* admit. *)
    abstract anihilate.
  Defined.
  Let OverLocallySmallCatInducedFunctor'' a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C).
    refine (Build_SpecializedFunctor (a \ C) (a' \ C)
                                     (@OverLocallySmallCatInducedFunctor_ObjectOf _ _ m)
                                     (@OverLocallySmallCatInducedFunctor_MorphismOf _ _ m)
                                     _
                                     _
           );
    subst_body; simpl; clear;
    (* admit. *) abstract anihilate.
  Defined.

  Let LocallySmallCatOverInducedFunctor''' a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a').
    simpl_definition_by_tac_and_exact (@LocallySmallCatOverInducedFunctor'' _ _ m) ltac:(subst_body; eta_red).
  Defined.
  Let OverLocallySmallCatInducedFunctor''' a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C).
    simpl_definition_by_tac_and_exact (@OverLocallySmallCatInducedFunctor'' _ _ m) ltac:(subst_body; eta_red).
  Defined.

  Definition LocallySmallCatOverInducedFunctor a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a')
    := Eval cbv beta iota zeta delta [LocallySmallCatOverInducedFunctor'''] in @LocallySmallCatOverInducedFunctor''' _ _ m.
  Definition OverLocallySmallCatInducedFunctor a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C)
    := Eval cbv beta iota zeta delta [OverLocallySmallCatInducedFunctor'''] in @OverLocallySmallCatInducedFunctor''' _ _ m.
  Local Transparent LocallySmallCat.
End LocallySmallCatOverInducedFunctor.
