Require Export ProductCategory Functor.
Require Import Common.

Set Implicit Arguments.

Local Infix "*" := ProductCategory.

Section ProductFunctor.
  Variables C D C' D' : Category.
  Variable F : Functor C D.
  Variable F' : Functor C' D'.

  Hint Resolve FCompositionOf FIdentityOf.

  Definition ProductFunctor : Functor  (C * C') (D * D').
    refine {| ObjectOf := (fun c'c : Object (C * C') => (F (fst c'c), F' (snd c'c)) : Object (D * D'));
      MorphismOf := (fun s d (m : Morphism (C * C') s d) => (F.(MorphismOf) (fst m), F'.(MorphismOf) (snd m)))
      |}; abstract (intros; unfold Morphism, ProductCategory in *; destruct_type @prod; simpl in *; f_equal; auto).
  Defined.
End ProductFunctor.
