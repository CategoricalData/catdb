Require Import JMeq Eqdep.
Require Export SpecializedCategory CategoryIsomorphisms Functor ProductCategory NaturalTransformation.
Require Import Common Notations FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Local Infix "==" := JMeq.

Local Open Scope category_scope.

Section OppositeCategory.
  Polymorphic Definition OppositeComputationalCategory `(C : @ComputationalCategory objC) : ComputationalCategory objC :=
    @Build_ComputationalCategory objC
                                 (fun s d => Morphism' C d s)
                                 (Identity' C)
                                 (fun _ _ _ m1 m2 => Compose' C _ _ _ m2 m1).

  Polymorphic Definition OppositeCategory `(C : @SpecializedCategory objC) : @SpecializedCategory objC :=
    @Build_SpecializedCategory' objC
                                (OppositeComputationalCategory (UnderlyingCCategory C))
                                (fun _ _ _ _ _ _ _ => Associativity'_sym C _ _ _ _ _ _ _)
                                (fun _ _ _ _ _ _ _ => Associativity' C _ _ _ _ _ _ _)
                                (fun _ _ => RightIdentity' C _ _)
                                (fun _ _ => LeftIdentity' C _ _).
End OppositeCategory.

(*Notation "C ᵒᵖ" := (OppositeCategory C) : category_scope.*)

Section DualCategories.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Polymorphic Lemma op_op_id : OppositeCategory (OppositeCategory C) = C.
    clear D objD.
    unfold OppositeCategory, OppositeComputationalCategory; simpl.
    repeat change (fun a => ?f a) with f.
    destruct C as [ [ ] ]; intros; simpl; reflexivity.
  Qed.

  Polymorphic Lemma op_distribute_prod : OppositeCategory (C * D) = (OppositeCategory C) * (OppositeCategory D).
    spcat_eq.
  Qed.
End DualCategories.

(* Polymorphic Hint Rewrite can't deal with maximally inserted implicit parameters *)
Arguments op_op_id [_] C.
Arguments op_distribute_prod [_] C [_] D.

Polymorphic Hint Rewrite op_op_id op_distribute_prod : category.

Section DualObjects.
  Context `(C : @SpecializedCategory objC).

  Polymorphic Definition terminal_opposite_initial (o : C) : IsTerminalObject o -> IsInitialObject (C := OppositeCategory C) o
    := fun H o' => H o'.

  Polymorphic Definition initial_opposite_terminal (o : C) : IsInitialObject o -> IsTerminalObject (C := OppositeCategory C) o
    := fun H o' => H o'.

  Polymorphic Definition terminal_to_opposite_initial : TerminalObject C -> InitialObject (OppositeCategory C)
    := Eval cbv beta iota zeta delta [terminal_opposite_initial TerminalObject_IsTerminalObject IsInitialObject_InitialObject proj1_sig proj2_sig] in
        fun x => terminal_opposite_initial x.

  Polymorphic Definition initial_to_opposite_terminal : InitialObject C -> TerminalObject (OppositeCategory C)
    := Eval cbv beta iota zeta delta [initial_opposite_terminal IsTerminalObject_TerminalObject InitialObject_IsInitialObject proj1_sig proj2_sig] in
        fun x => initial_opposite_terminal x.
End DualObjects.

Section OppositeFunctor.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.
  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.

  Polymorphic Definition OppositeFunctor : SpecializedFunctor COp DOp.
    refine (Build_SpecializedFunctor COp DOp
      (fun c : COp => F c : DOp)
      (fun (s d : COp) (m : C.(Morphism) d s) => MorphismOf F (s := d) (d := s) m)
      (fun d' d s m1 m2 => FCompositionOf F s d d' m2 m1)
      (FIdentityOf F)
    ).
  Defined.
End OppositeFunctor.

(*Notation "C ᵒᵖ" := (OppositeFunctor C) : functor_scope.*)

Section OppositeFunctor_Id.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.

  Polymorphic Lemma op_op_functor_id : OppositeFunctor (OppositeFunctor F) == F.
    functor_eq; autorewrite with category; trivial.
  Qed.
End OppositeFunctor_Id.

(* not terribly useful, given that this would make [autorewrite with core] give "Anomaly: Uncaught exception Failure("nth"). Please report." *)
(*Hint Rewrite op_op_functor_id.*)

Section OppositeNaturalTransformation.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variables F G : SpecializedFunctor C D.
  Variable T : SpecializedNaturalTransformation F G.
  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.
  Let FOp := OppositeFunctor F.
  Let GOp := OppositeFunctor G.

  Polymorphic Definition OppositeNaturalTransformation : SpecializedNaturalTransformation GOp FOp.
    refine (Build_SpecializedNaturalTransformation GOp FOp
      (fun c : COp => T.(ComponentsOf) c : DOp.(Morphism) (GOp c) (FOp c))
      (fun s d m => eq_sym (Commutes T d s m))
    ).
  Defined.
End OppositeNaturalTransformation.

(*Notation "C ᵒᵖ" := (OppositeNaturalTransformation C) : natural_transformation_scope.*)

Section OppositeNaturalTransformation_Id.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variables F G : SpecializedFunctor C D.
  Variable T : SpecializedNaturalTransformation F G.

  Polymorphic Lemma op_op_nt_id : OppositeNaturalTransformation (OppositeNaturalTransformation T) == T.
    nt_eq; intros; try functor_eq; autorewrite with category; trivial.
  Qed.
End OppositeNaturalTransformation_Id.

(* not terribly useful, given that this would make [autorewrite with core] give "Anomaly: Uncaught exception Failure("nth"). Please report." *)
(*Hint Rewrite op_op_nt_id.*)
