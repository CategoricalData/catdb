Require Export ProductCategory Functor.
Require Import Common.

Set Implicit Arguments.

Section ProductFunctor.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.
  Variable objC' : Type.
  Variable morC' : objC' -> objC' -> Type.
  Variable C' : SpecializedCategory morC'.
  Variable objD' : Type.
  Variable morD' : objD' -> objD' -> Type.
  Variable D' : SpecializedCategory morD'.
  Variable F : Functor C D.
  Variable F' : Functor C' D'.

  Hint Resolve FCompositionOf FIdentityOf.

  Definition ProductFunctor : SpecializedFunctor  (C * C') (D * D').
    refine {| ObjectOf' := (fun c'c : Object (C * C') => (F (fst c'c), F' (snd c'c)) : Object (D * D'));
      MorphismOf' := (fun s d (m : Morphism (C * C') s d) => (F.(MorphismOf) (fst m), F'.(MorphismOf) (snd m)))
      |}; abstract (intros; unfold ProductCategory in *; destruct_type @prod; simpl in *; f_equal; auto).
  Defined.
End ProductFunctor.

Infix "*" := ProductFunctor : functor_scope.
