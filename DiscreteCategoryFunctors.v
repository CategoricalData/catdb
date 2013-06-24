Require Import FunctionalExtensionality.
Require Export DiscreteCategory Functor SetCategory ComputableCategory Cat NaturalTransformation.
Require Import Common Adjoint.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section FunctorFromDiscrete.
  Variable O : Type.
  Variable D : Category.
  Variable objOf : O -> D.

  Let FunctorFromDiscrete_MorphismOf s d (m : Morphism (DiscreteCategory O) s d) : Morphism D (objOf s) (objOf d)
    := match m with
         | eq_refl => Identity _
       end.

  Definition FunctorFromDiscrete : Functor (DiscreteCategory O) D.
  Proof.
    refine (@Build_Functor (DiscreteCategory O)
                                      D
                                      objOf
                                      FunctorFromDiscrete_MorphismOf
                                      _
                                      _);
      abstract (
        intros; hnf in *; subst; simpl;
          auto with category
      ).
  Defined.
End FunctorFromDiscrete.

Section Obj.
  Local Ltac build_ob_functor Index2Cat :=
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (@Build_Functor C D
                                          (fun C' => Object (Index2Cat C'))
                                          (fun _ _ F => ObjectOf F)
                                          _
                                          _
               )
    end;
    intros; simpl in *; reflexivity.

  Section type.
    Variable I : Type.
    Variable Index2Cat : I -> Category.

    Definition ObjectFunctor : Functor (ComputableCategory Index2Cat) TypeCat.
      build_ob_functor Index2Cat.
    Defined.
  End type.
End Obj.

Arguments ObjectFunctor {I Index2Cat}.

Section Mor.
  Local Ltac build_mor_functor Index2Cat :=
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor C D
          (fun C' => { sd : Index2Cat C' * Index2Cat C' & (Index2Cat C').(Morphism) (fst sd) (snd sd) } )
          (fun _ _ F => (fun sdm =>
            existT (fun sd => Morphism _ (fst sd) (snd sd))
            (F (fst (projT1 sdm)), F (snd (projT1 sdm)))
            (MorphismOf F (s := fst (projT1 sdm)) (d := snd (projT1 sdm)) (projT2 sdm))
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
    Variable Index2Cat : I -> Category.

    Definition MorphismFunctor : Functor (ComputableCategory Index2Cat) TypeCat.
      build_mor_functor Index2Cat.
    Defined.
  End type.
End Mor.

Arguments MorphismFunctor {I Index2Cat}.

Section dom_cod.
  Local Ltac build_dom_cod fst_snd :=
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun _ => (fun sdf => fst_snd _ _ (projT1 sdf)))
          _
        )
    end;
    reflexivity.

  Section type.
    Variable I : Type.
    Variable Index2Cat : I -> Category.

    Definition DomainNaturalTransformation : NaturalTransformation (@MorphismFunctor _ Index2Cat) ObjectFunctor.
      build_dom_cod @fst.
    Defined.

    Definition CodomainNaturalTransformation : NaturalTransformation (@MorphismFunctor _ Index2Cat) ObjectFunctor.
      build_dom_cod @snd.
    Defined.
  End type.
End dom_cod.

Section InducedFunctor.
  Variable O : Type.
  Variable O' : Category.
  Variable f : O -> O'.

  Definition InducedDiscreteFunctor : Functor (DiscreteCategory O) O'.
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor C D
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

  Definition DiscreteFunctor : Functor TypeCat Cat.
    refine (Build_Functor TypeCat Cat
      (fun O => DiscreteCategory O : Category)
      (fun s d f => InducedDiscreteFunctor (DiscreteCategory d) f)
      _
      _
    );
    abstract t.
  Defined.

  Definition DiscreteSetFunctor : Functor SetCat Cat.
    refine (Build_Functor SetCat Cat
      (fun O => DiscreteCategory O : Category)
      (fun s d f => InducedDiscreteFunctor (DiscreteCategory d) f)
      _
      _
    );
    abstract t.
  Defined.
End disc.

Section Adjoints.
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
