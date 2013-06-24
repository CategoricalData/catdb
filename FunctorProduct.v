Require Export ProductCategory Functor NaturalTransformation.
Require Import Common TypeclassUnreifiedSimplification.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section FunctorProduct.
  Variable C : Category.
  Variable D : Category.
  Variable D' : Category.

  Definition FunctorProduct (F : Functor C D) (F' : Functor C D') : Functor C (D * D').
    match goal with
      | [ |- Functor ?C0 ?D0 ] =>
        refine (Build_Functor
                  C0 D0
                  (fun c => (F c, F' c))
                  (fun s d m => (MorphismOf F m, MorphismOf F' m))
                  _
                  _)
    end;
    abstract (intros; expand; apply f_equal2; rsimplify_morphisms; reflexivity).
  Defined.

  Definition FunctorProductFunctorial
             (F G : Functor C D)
             (F' G' : Functor C D')
             (T : NaturalTransformation F G)
             (T' : NaturalTransformation F' G')
  : NaturalTransformation (FunctorProduct F F') (FunctorProduct G G').
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
                                                       (fun x => (T x, T' x))
                                                       _)
    end.
    abstract (simpl; intros; repeat rewrite Commutes; reflexivity).
  Defined.
End FunctorProduct.

Section FunctorProduct'.
  Variable C : Category.
  Variable D : Category.
  Variable C' : Category.
  Variable D' : Category.
  Variable F : Functor C D.
  Variable F' : Functor C' D'.

  Definition FunctorProduct' : Functor  (C * C') (D * D')
    := FunctorProduct (ComposeFunctors F fst_Functor) (ComposeFunctors F' snd_Functor).
End FunctorProduct'.

(** XXX TODO(jgross): Change this to [FunctorProduct]. *)
Infix "*" := FunctorProduct' : functor_scope.
