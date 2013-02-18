Require Export FunctorCategory.
Require Import Common Notations SmallCat ProductCategory Duals ExponentialLaws.

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

    Polymorphic Definition FunctorCategoryFunctor_MorphismOf_ObjectOf : (C ^ D)%functor -> (C' ^ D')%functor
      := fun H => ComposeFunctors F (ComposeFunctors H G).

    Global Arguments FunctorCategoryFunctor_MorphismOf_ObjectOf _ / .

    Polymorphic Definition FunctorCategoryFunctor_MorphismOf_MorphismOf s d (m : Morphism (C ^ D) s d) :
      Morphism (C' ^ D') (FunctorCategoryFunctor_MorphismOf_ObjectOf s) (FunctorCategoryFunctor_MorphismOf_ObjectOf d)
      := NTComposeF (IdentityNaturalTransformation _) (NTComposeF m (IdentityNaturalTransformation _)).

    Global Arguments FunctorCategoryFunctor_MorphismOf_MorphismOf _ _ _ / .

    Polymorphic Definition FunctorCategoryFunctor_MorphismOf : SpecializedFunctor (C ^ D) (C' ^ D').
      exists FunctorCategoryFunctor_MorphismOf_ObjectOf FunctorCategoryFunctor_MorphismOf_MorphismOf;
      abstract (
          repeat intro;
          simpl in *; unfold Object in *;
          nt_eq;
          repeat autorewrite with category;
          present_spfunctor;
          try rewrite <- FCompositionOf;
          reflexivity
        ).
    Defined.
  End MorphismOf.

  Section FIdentityOf.
    Context `(C : @SpecializedCategory objC).
    Context `(D : @SpecializedCategory objD).

    Polymorphic Lemma FunctorCategoryFunctor_FIdentityOf : FunctorCategoryFunctor_MorphismOf (IdentityFunctor C) (IdentityFunctor D) = IdentityFunctor _.
      repeat (functor_eq; nt_eq); autorewrite with category; reflexivity.
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

    Polymorphic Lemma FunctorCategoryFunctor_FCompositionOf : FunctorCategoryFunctor_MorphismOf (ComposeFunctors F' F) (ComposeFunctors G' G)
                                                  = ComposeFunctors (FunctorCategoryFunctor_MorphismOf F' G) (FunctorCategoryFunctor_MorphismOf F G').
      repeat (functor_eq; nt_eq); autorewrite with category; reflexivity.
    Qed.
  End FCompositionOf.
End FunctorCategoryParts.

Section FunctorCategoryFunctor.
  Polymorphic Definition FunctorCategoryFunctor : SpecializedFunctor (LocallySmallCat * (OppositeCategory LocallySmallCat)) LocallySmallCat.
    refine (Build_SpecializedFunctor (LocallySmallCat * (OppositeCategory LocallySmallCat)) LocallySmallCat
                                     (fun CD => (fst CD) ^ (snd CD) : LocallySmallSpecializedCategory _)
                                     (fun s d m => FunctorCategoryFunctor_MorphismOf (fst m) (snd m))
                                     _
                                     _);
    simpl;
    abstract (intros; apply FunctorCategoryFunctor_FCompositionOf || apply FunctorCategoryFunctor_FIdentityOf).
  Defined.


  (* Polymorphic Definition FunctorCategoryFunctor : ((LocallySmallCat ^ LocallySmallCat) ^ (OppositeCategory LocallySmallCat))%category
    := ExponentialLaw4Functor_Inverse _ _ _ FunctorCategoryUncurriedFunctor. *)
End FunctorCategoryFunctor.
