Require Export FunctorCategory SumCategory ProductCategory Functor.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Section Law1.
  Context `(D : @SpecializedCategory objD).
  Context `(C1 : @SpecializedCategory objC1).
  Context `(C2 : @SpecializedCategory objC2).

  Definition ExponentialLaw1Functor : SpecializedFunctor (D ^ (C1 + C2)) ((D ^ C1) * (D ^ C2)).
  Admitted.

  Definition ExponentialLaw1Functor_Inverse : SpecializedFunctor ((D ^ C1) * (D ^ C2)) (D ^ (C1 + C2)).
  Admitted.

  Lemma ExponentialLaw1 : ComposeFunctors ExponentialLaw1Functor ExponentialLaw1Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw1Functor_Inverse ExponentialLaw1Functor = IdentityFunctor _.
  Admitted.
End Law1.

Section Law2.
  Context `(C1 : @SpecializedCategory objC1).
  Context `(C2 : @SpecializedCategory objC2).
  Context `(D : @SpecializedCategory objD).

  Definition ExponentialLaw2Functor : SpecializedFunctor ((C1 * C2) ^ D) (C1 ^ D * C2 ^ D).
  Admitted.

  Definition ExponentialLaw2Functor_Inverse : SpecializedFunctor (C1 ^ D * C2 ^ D) ((C1 * C2) ^ D).
  Admitted.

  Lemma ExponentialLaw2 : ComposeFunctors ExponentialLaw2Functor ExponentialLaw2Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw2Functor_Inverse ExponentialLaw2Functor = IdentityFunctor _.
  Admitted.
End Law2.

Section Law3.
  Context `(C1 : @SpecializedCategory objC1).
  Context `(C2 : @SpecializedCategory objC2).
  Context `(D : @SpecializedCategory objD).

  Definition ExponentialLaw3Functor : SpecializedFunctor ((D ^ C1) ^ C2) (D ^ (C1 * C2)).
  Admitted.

  Definition ExponentialLaw3Functor_Inverse : SpecializedFunctor (D ^ (C1 * C2)) ((D ^ C1) ^ C2).
  Admitted.

  Lemma ExponentialLaw3 : ComposeFunctors ExponentialLaw3Functor ExponentialLaw3Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw3Functor_Inverse ExponentialLaw3Functor = IdentityFunctor _.
  Admitted.
End Law3.
