Require Export ProductCategory Functor.
Require Import Common TypeclassUnreifiedSimplification.

Set Implicit Arguments.

Generalizable All Variables.

Section FunctorProduct.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(D' : @SpecializedCategory objD').
  Variable F : Functor C D.
  Variable F' : Functor C D'.

  Definition FunctorProduct : SpecializedFunctor C (D * D').
    match goal with
      | [ |- SpecializedFunctor ?C0 ?D0 ] =>
        refine (Build_SpecializedFunctor
                  C0 D0
                  (fun c => (F c, F' c))
                  (fun s d m => (MorphismOf F m, MorphismOf F' m))
                  _
                  _)
    end;
    abstract (intros; expand; apply f_equal2; rsimplify_morphisms; reflexivity).
  Defined.
End FunctorProduct.

Section FunctorProduct'.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(C' : @SpecializedCategory objC').
  Context `(D' : @SpecializedCategory objD').
  Variable F : Functor C D.
  Variable F' : Functor C' D'.

  Definition FunctorProduct' : SpecializedFunctor  (C * C') (D * D')
    := FunctorProduct (ComposeFunctors F fst_Functor) (ComposeFunctors F' snd_Functor).
End FunctorProduct'.

(** XXX TODO(jgross): Change this to [FunctorProduct]. *)
Infix "*" := FunctorProduct' : functor_scope.
