Require Import FunctionalExtensionality.
Require Export DiscreteCategory Functor SetCategory ComputableCategory SmallCat.
Require Import Common Adjoint.

Set Implicit Arguments.

Generalizable All Variables.

Section Obj.
  Local Ltac build_ob_functor Index2Object :=
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (fun C' => Index2Object C')
          (fun _ _ F => ObjectOf' F)
          _
          _
        )
    end;
    intros; simpl in *; reflexivity.

  Section type.
    Variable I : Type.
    Variable Index2Object : I -> Type.
    Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i) (@Index2Morphism i)).

    Definition ObjectFunctor : SpecializedFunctor (@ComputableCategory _ _ _ Index2Cat) TypeCat.
      build_ob_functor Index2Object.
    Defined.
  End type.

  Section set.
    Variable I : Type.
    Variable Index2Object : I -> Set.
    Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i) (@Index2Morphism i)).

    Definition ObjectFunctorToSet : SpecializedFunctor (@ComputableCategory _ _ _ Index2Cat) SetCat.
      build_ob_functor Index2Object.
    Defined.
  End set.

  Section prop.
    Variable I : Type.
    Variable Index2Object : I -> Prop.
    Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i) (@Index2Morphism i)).

    Definition ObjectFunctorToProp : SpecializedFunctor (@ComputableCategory _ _ _ Index2Cat) PropCat.
      build_ob_functor Index2Object.
    Defined.
  End prop.
End Obj.

Arguments ObjectFunctor {I Index2Object Index2Morphism Index2Cat}.
Arguments ObjectFunctorToSet {I Index2Object Index2Morphism Index2Cat}.
Arguments ObjectFunctorToProp {I Index2Object Index2Morphism Index2Cat}.

Section Mor.
  Local Ltac build_mor_functor Index2Object Index2Morphism :=
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (fun C' => { sd : Index2Object C' * Index2Object C' & @Index2Morphism _ (fst sd) (snd sd) } )
          (fun _ _ F => (fun sdm =>
            existT (fun sd => @Index2Morphism _ (fst sd) (snd sd))
            (F (fst (projT1 sdm)), F (snd (projT1 sdm)))
            (MorphismOf' F (fst (projT1 sdm)) (snd (projT1 sdm)) (projT2 sdm))
          ))
          _
          _
        )
    end;
    intros; simpl in *; try reflexivity;
      repeat (apply functional_extensionality_dep; intro);
        simpl_eq;
        reflexivity.

  Section type.
    Variable I : Type.
    Variable Index2Object : I -> Type.
    Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i) (@Index2Morphism i)).

    Definition MorphismFunctor : SpecializedFunctor (@ComputableCategory _ _ _ Index2Cat) TypeCat.
      build_mor_functor Index2Object @Index2Morphism.
    Defined.
  End type.

  Section set.
    Variable I : Type.
    Context `(Index2Cat : forall i : I, @SmallSpecializedCategory (@Index2Object i) (@Index2Morphism i)).

    Definition MorphismFunctorToSet : SpecializedFunctor (@ComputableCategory _ _ _ Index2Cat) SetCat.
      build_mor_functor Index2Object @Index2Morphism.
    Defined.
  End set.

  Section prop.
    Variable I : Type.
    Variable Index2Object : I -> Prop.
    Variable Index2Morphism : forall i : I, Index2Object i -> Index2Object i -> Prop.
    Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i) (@Index2Morphism i)).

    Definition MorphismFunctorToProp : SpecializedFunctor (@ComputableCategory _ _ _ Index2Cat) PropCat.
      build_mor_functor Index2Object @Index2Morphism.
    Defined.
  End prop.
End Mor.

Arguments MorphismFunctor {I Index2Object Index2Morphism Index2Cat}.
Arguments MorphismFunctorToSet {I Index2Object Index2Morphism Index2Cat}.
Arguments MorphismFunctorToProp {I Index2Object Index2Morphism Index2Cat}.

Section InducedFunctor.
  Local Transparent Object Morphism.
  Variable O : Type.
  Context `(O' : @SpecializedCategory obj mor).
  Variable f : O -> O'.


  Definition InducedDiscreteFunctor : SpecializedFunctor (DiscreteCategory O) O'.
    refine {| ObjectOf' := f; MorphismOf' := (fun s d_ m => match m return _ with eq_refl => Identity (f s) end) |};
      abstract (
        intros; simpl in *; repeat subst; trivial;
          repeat rewrite RightIdentity; repeat rewrite LeftIdentity;
            repeat rewrite Associativity;
              reflexivity
      ).
  Defined.
End InducedFunctor.

Section disc.
  Local Transparent Object Morphism.

  Local Ltac t := simpl; intros; functor_eq;
    repeat (apply functional_extensionality_dep; intro);
      hnf in *; subst;
        auto.

  Definition DiscreteFunctor : SpecializedFunctor TypeCat LocallySmallCat.
    refine (Build_SpecializedFunctor TypeCat LocallySmallCat
      (fun O => DiscreteCategory O : LocallySmallSpecializedCategory _)
      (fun s d f => InducedDiscreteFunctor _ f)
      _
      _
    );
    abstract t.
  Defined.

  Definition DiscreteSetFunctor : SpecializedFunctor SetCat SmallCat.
    refine (Build_SpecializedFunctor SetCat SmallCat
      (fun O => DiscreteCategory O : SmallSpecializedCategory _)
      (fun s d f => InducedDiscreteFunctor _ f)
      _
      _
    );
    abstract t.
  Defined.
End disc.

Section Adjoints.
  Local Transparent Object Morphism.

  Lemma DiscreteObjectIdentity : ComposeFunctors ObjectFunctor DiscreteFunctor = IdentityFunctor _.
    functor_eq.
  Qed.

  Definition DiscreteObjectAdjunction : HomAdjunction DiscreteFunctor ObjectFunctor.
    match goal with
      | [ |- HomAdjunction ?F ?G ] =>
        refine (Build_HomAdjunction F G
          (fun _ _ F => (fun x => F x))
          _
          _
        )
    end;
    try abstract trivial;
      simpl; intros.
    exists (fun f => (InducedDiscreteFunctor _ f));
      abstract (repeat match goal with
                         | _ => progress trivial
                         | _ => progress repeat (apply functional_extensionality_dep; intro)
                         | _ => hnf in *;
                           match goal with
                             | [ H : _ = _ |- _ ] => destruct H; simpl in *
                           end
                         | _ => rewrite FIdentityOf
                         | _ => progress functor_eq
                       end).
  Defined.
End Adjoints.
