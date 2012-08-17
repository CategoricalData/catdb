Require Export ProductCategory ProductFunctor NaturalTransformation.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Section ProductNaturalTransformation.
  Context `{A : @SpecializedCategory objA morA}.
  Context `{B : @SpecializedCategory objB morB}.
  Context `{C : @SpecializedCategory objC morC}.
  Context `{D : @SpecializedCategory objD morD}.
  Variables F F' : SpecializedFunctor A B.
  Variables G G' : SpecializedFunctor C D.
  Variable T : SpecializedNaturalTransformation F F'.
  Variable U : SpecializedNaturalTransformation G G'.

  Definition ProductNaturalTransformation : SpecializedNaturalTransformation (F * G) (F' * G').
    refine (Build_SpecializedNaturalTransformation (F * G) (F' * G')
      (fun ac : A * C => (T (fst ac), U (snd ac)))
      _
    );
    simpl; present_spnt;
      abstract (
        intros; simpl_eq;
          apply Commutes
      ).
  Defined.
End ProductNaturalTransformation.

Infix "*" := ProductNaturalTransformation : natural_transformation_scope.
