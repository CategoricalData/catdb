Require Export ProductCategory FunctorProduct NaturalTransformation.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section ProductNaturalTransformation.
  Context `{A : Category}.
  Context `{B : Category}.
  Context `{C : Category}.
  Context `{D : Category}.
  Variables F F' : Functor A B.
  Variables G G' : Functor C D.
  Variable T : NaturalTransformation F F'.
  Variable U : NaturalTransformation G G'.

  Definition ProductNaturalTransformation : NaturalTransformation (F * G) (F' * G').
    refine (Build_NaturalTransformation (F * G) (F' * G')
      (fun ac : A * C => (T (fst ac), U (snd ac)))
      _
    );
    abstract (intros; simpl; simpl_eq; auto with natural_transformation).
  Defined.
End ProductNaturalTransformation.

Infix "*" := ProductNaturalTransformation : natural_transformation_scope.
