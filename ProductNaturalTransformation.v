Require Export ProductCategory FunctorProduct NaturalTransformation.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Section ProductNaturalTransformation.
  Context `{A : @SpecializedCategory objA}.
  Context `{B : @SpecializedCategory objB}.
  Context `{C : @SpecializedCategory objC}.
  Context `{D : @SpecializedCategory objD}.
  Variables F F' : SpecializedFunctor A B.
  Variables G G' : SpecializedFunctor C D.
  Variable T : SpecializedNaturalTransformation F F'.
  Variable U : SpecializedNaturalTransformation G G'.

  Definition ProductNaturalTransformation : SpecializedNaturalTransformation (F * G) (F' * G').
    refine (Build_SpecializedNaturalTransformation (F * G) (F' * G')
      (fun ac : A * C => (T (fst ac), U (snd ac)))
      _
    );
    abstract (intros; simpl; simpl_eq; auto with natural_transformation).
  Defined.
End ProductNaturalTransformation.

Infix "*" := ProductNaturalTransformation : natural_transformation_scope.
