Require Import FunctionalExtensionality.
Require Export PathsCategory Functor SetCategory ComputableCategory SmallCat NaturalTransformation.
Require Import Common Adjoint.

Set Implicit Arguments.

Generalizable All Variables.

Section FunctorFromPaths.
  Variable V : Type.
  Variable E : V -> V -> Type.
  Context `(D : @SpecializedCategory objD).
  Variable objOf : V -> objD.
  Variable morOf : forall s d, E s d -> Morphism' D (objOf s) (objOf d).

  Fixpoint FunctorFromPaths_MorphismOf s d (m : Morphism' (PathsCategory E) s d) : Morphism' D (objOf s) (objOf d) :=
    match m with
      | NoEdges => Identity _
      | AddEdge _ _ m' e => Compose (morOf e) (FunctorFromPaths_MorphismOf m')
    end.

  Lemma FunctorFromPaths_FCompositionOf s d d' (p1 : path E s d) (p2 : path E d d') :
    FunctorFromPaths_MorphismOf (concatenate p1 p2) = Compose (FunctorFromPaths_MorphismOf p2) (FunctorFromPaths_MorphismOf p1).
  Proof.
    induction p2; t_with t'.
  Qed.

  Definition FunctorFromPaths : SpecializedFunctor (PathsCategory E) D.
  Proof.
    refine {| ObjectOf' := objOf; MorphismOf' := FunctorFromPaths_MorphismOf |};
      present_spcategory.
    Focus 2.
      abstract (
        intros; auto;
          hnf in *;
            match goal with
              | [ p : path _ _ _ |- _ ] => induction p; solve [ t_with t' ]
            end
      ).
      (***  XXXXX  This fails? ***)
      intros; auto;
        hnf in *;
          abstract (
            match goal with
              | [ p : path _ _ _ |- _ ] => induction p; solve [ t_with t' ]
            end
          ).
        intros; hnf in *; subst; simpl;
          auto.

      ).
  Defined.
End FunctorFromPaths.

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
    Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i)).

    Definition ObjectFunctor : SpecializedFunctor (@ComputableCategory _ _ Index2Cat) TypeCat.
      build_ob_functor Index2Object.
    Defined.
  End type.

  Section set.
    Variable I : Type.
    Variable Index2Object : I -> Set.
    Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i)).

    Definition ObjectFunctorToSet : SpecializedFunctor (@ComputableCategory _ _ Index2Cat) SetCat.
      build_ob_functor Index2Object.
    Defined.
  End set.

  Section prop.
    Variable I : Type.
    Variable Index2Object : I -> Prop.
    Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i)).

    Definition ObjectFunctorToProp : SpecializedFunctor (@ComputableCategory _ _ Index2Cat) PropCat.
      build_ob_functor Index2Object.
    Defined.
  End prop.
End Obj.

Arguments ObjectFunctor {I Index2Object Index2Cat}.
Arguments ObjectFunctorToSet {I Index2Object Index2Cat}.
Arguments ObjectFunctorToProp {I Index2Object Index2Cat}.

Section Mor.
  Local Ltac build_mor_functor Index2Object Index2Cat :=
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (fun C' => { sd : Index2Object C' * Index2Object C' & (Index2Cat C').(Morphism') (fst sd) (snd sd) } )
          (fun _ _ F => (fun sdm =>
            existT (fun sd => Morphism' _ (fst sd) (snd sd))
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
    Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i)).

    Definition MorphismFunctor : SpecializedFunctor (@ComputableCategory _ _ Index2Cat) TypeCat.
      build_mor_functor Index2Object Index2Cat.
    Defined.
  End type.
End Mor.

Arguments MorphismFunctor {I Index2Object Index2Cat}.

Section dom_cod.
  Local Ltac build_dom_cod fst_snd :=
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun _ => (fun sdf => fst_snd _ _ (projT1 sdf)))
          _
        )
    end;
    reflexivity.

  Section type.
    Variable I : Type.
    Variable Index2Object : I -> Type.
    Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i)).

    Definition DomainNaturalTransformation : SpecializedNaturalTransformation (@MorphismFunctor _ _ Index2Cat) ObjectFunctor.
      build_dom_cod @fst.
    Defined.

    Definition CodomainNaturalTransformation : SpecializedNaturalTransformation (@MorphismFunctor _ _ Index2Cat) ObjectFunctor.
      build_dom_cod @snd.
    Defined.
  End type.
End dom_cod.

Section InducedFunctor.
  Variable V : Type.
  Context `(O' : @SpecializedCategory obj).
  Variable f : V -> O'.

  Definition InducedPathsFunctor : SpecializedFunctor (PathsCategory V) O'.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          f
          (fun s d_ m => match m return _ with eq_refl => Identity (f s) end)
          _
          _
        )
    end;
    abstract (
      intros; simpl in *; repeat subst; trivial;
        repeat rewrite RightIdentity; repeat rewrite LeftIdentity;
          repeat rewrite Associativity;
            reflexivity
    ).
  Defined.
End InducedFunctor.

Section disc.
  Local Ltac t := simpl; intros; functor_eq;
    repeat (apply functional_extensionality_dep; intro);
      hnf in *; subst;
        auto.

  Definition PathsFunctor : SpecializedFunctor TypeCat LocallySmallCat.
    refine (Build_SpecializedFunctor TypeCat LocallySmallCat
      (fun V => PathsCategory V : LocallySmallSpecializedCategory _)
      (fun s d f => InducedPathsFunctor _ f)
      _
      _
    );
    abstract t.
  Defined.

  Definition PathsSetFunctor : SpecializedFunctor SetCat SmallCat.
    refine (Build_SpecializedFunctor SetCat SmallCat
      (fun V => PathsCategory V : SmallSpecializedCategory _)
      (fun s d f => InducedPathsFunctor _ f)
      _
      _
    );
    abstract t.
  Defined.
End disc.

Section Adjoints.
  Lemma PathsObjectIdentity : ComposeFunctors ObjectFunctor PathsFunctor = IdentityFunctor _.
    functor_eq.
  Qed.

  Definition PathsObjectAdjunction : HomAdjunction PathsFunctor ObjectFunctor.
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
    exists (fun f => (InducedPathsFunctor _ f));
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
