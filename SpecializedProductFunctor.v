Require Export SpecializedProductCategory SpecializedFunctor.
Require Import Common.

Set Implicit Arguments.

Local Infix "*" := ProductSpecializedCategory.

Section ProductSpecializedFunctor.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable objC' : Type.
  Variable morC' : objC' -> objC' -> Type.
  Variable objD' : Type.
  Variable morD' : objD' -> objD' -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable C' : SpecializedCategory morC'.
  Variable D' : SpecializedCategory morD'.
  Variable F : SpecializedFunctor C D.
  Variable F' : SpecializedFunctor C' D'.

  Hint Resolve FCompositionOf FIdentityOf.

  Definition ProductSpecializedFunctor : SpecializedFunctor  (C * C') (D * D').
    Transparent Object Morphism Compose Identity.
    refine {| ObjectOf' := (fun c'c : Object (C * C') => (F (fst c'c), F' (snd c'c)) : Object (D * D'));
      MorphismOf' := (fun s d (m : Morphism (C * C') s d) => (F.(MorphismOf) (fst m), F'.(MorphismOf) (snd m)))
      |}; abstract (intros; unfold Morphism, ProductSpecializedCategory in *; destruct_type @prod; simpl in *; f_equal; auto).
  Defined.
End ProductSpecializedFunctor.
