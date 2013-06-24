Require Import Setoid FunctionalExtensionality.
Require Export SetCategory.
Require Import Common Limits Functor NaturalTransformation FunctorCategory InitialTerminalCategory.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Ltac limit_t :=
  repeat (repeat intro; repeat split);
  simpl in *;

  nt_eq;
  subst; expand;

  repeat (apply functional_extensionality_dep; intro; try simpl_eq);

  destruct_head @NaturalTransformation;
  fg_equal;

  destruct_sig;

  trivial; t_with t'; intuition.

Section SetLimits.
  Context `(C : @Category).
  Variable F : Functor C SetCat.

  (* Quoting David:
     let F:C-->Set be a functor. An element of the limit is a collection of elements x_c,
     one for each c in C, such that under every arrow g: c-->c' in C, x_c is sent to x_{c'}.
     *)
  Definition SetLimit_Object : SetCat :=
    { S : forall c : C, F c | forall c c' (g : C.(Morphism) c c'), F.(MorphismOf) g (S c) = (S c') }.

  Definition SetLimit_Morphism : NaturalTransformation
                                   ((DiagonalFunctor SetCat C) SetLimit_Object)
                                   F.
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun c : C => (fun S => (proj1_sig S) c))
          _
        )
    end.
    abstract limit_t.
  Defined.

  Definition SetLimit_Property_Morphism A'
             (φ' : NaturalTransformation ((DiagonalFunctor SetCat C) A') F) :
    A' -> SetLimit_Object.
    intro x; hnf.
    exists (fun c => ComponentsOf φ' c x).
    abstract limit_t.
  Defined.

  Definition SetLimit : Limit F.
    refine (Build_TerminalMorphism (DiagonalFunctor SetCat C) F SetLimit_Object SetLimit_Morphism _).
    intros A' φ'.
    exists (SetLimit_Property_Morphism φ').
    abstract limit_t.
  Defined.
End SetLimits.

Section TypeLimits.
  Context `(C : @Category).
  Variable F : Functor C TypeCat.

  (* Quoting David:
     let F:C-->Type be a functor. An element of the limit is a collection of elements x_c,
     one for each c in C, such that under every arrow g: c-->c' in C, x_c is sent to x_{c'}.
     *)
  Definition TypeLimit_Object : TypeCat :=
    { S : forall c : C, F c | forall c c' (g : C.(Morphism) c c'), F.(MorphismOf) g (S c) = (S c') }.

  Definition TypeLimit_Morphism : NaturalTransformation
                                   ((DiagonalFunctor TypeCat C) TypeLimit_Object)
                                   F.
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun c : C => (fun S => (proj1_sig S) c))
          _
        )
    end.
    abstract limit_t.
  Defined.

  Definition TypeLimit_Property_Morphism A'
             (φ' : NaturalTransformation ((DiagonalFunctor TypeCat C) A') F) :
    A' -> TypeLimit_Object.
    intro x; hnf.
    exists (fun c => ComponentsOf φ' c x).
    abstract limit_t.
  Defined.

  Definition TypeLimit : Limit F.
    refine (Build_TerminalMorphism (DiagonalFunctor TypeCat C) F TypeLimit_Object TypeLimit_Morphism _).
    intros A' φ'.
    exists (TypeLimit_Property_Morphism φ').
    abstract limit_t.
  Defined.
End TypeLimits.
