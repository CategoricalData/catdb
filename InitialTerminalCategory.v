Require Export SpecializedCategory Functor.
Require Import Common Notations NatCategory.

Set Implicit Arguments.

Generalizable All Variables.

Section InitialTerminal.
   Polymorphic Definition InitialCategory : SmallSpecializedCategory _ := 0.
   Polymorphic Definition TerminalCategory : SmallSpecializedCategory _ := 1.
End InitialTerminal.

Section Functors.
  Context `(C : SpecializedCategory objC).

  Polymorphic Definition FunctorTo1 : SpecializedFunctor C 1
    := Build_SpecializedFunctor C 1 (fun _ => tt) (fun _ _ _ => eq_refl) (fun _ _ _ _ _ => eq_refl) (fun _ => eq_refl).
  Polymorphic Definition FunctorToTerminal : SpecializedFunctor C TerminalCategory := FunctorTo1.

  Polymorphic Definition FunctorFrom1 (c : C) : SpecializedFunctor 1 C
    := Build_SpecializedFunctor 1 C (fun _ => c) (fun _ _ _ => Identity c) (fun _ _ _ _ _ => eq_sym (RightIdentity C _ _ _)) (fun _ => eq_refl).
  Polymorphic Definition FunctorFromTerminal (c : C) : SpecializedFunctor TerminalCategory C := FunctorFrom1 c.

  Polymorphic Definition FunctorFrom0 : SpecializedFunctor 0 C
    := Build_SpecializedFunctor 0 C (fun x => match x with end) (fun x _ _ => match x with end) (fun x _ _ _ _ => match x with end) (fun x => match x with end).
  Polymorphic Definition FunctorFromInitial : SpecializedFunctor InitialCategory C := FunctorFrom0.
End Functors.
