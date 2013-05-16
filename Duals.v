Require Import JMeq Eqdep.
Require Export SpecializedCategory CategoryIsomorphisms Functor ProductCategory NaturalTransformation.
Require Import Common Notations FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Local Open Scope category_scope.

Section OppositeCategory.
  Definition OppositeComputationalCategory `(C : @ComputationalCategory objC) : ComputationalCategory objC :=
    @Build_ComputationalCategory objC
                                 (fun s d => Morphism C d s)
                                 (Identity (C := C))
                                 (fun _ _ _ m1 m2 => Compose m2 m1).

  Instance OppositeIsSpecializedCategory `(H : @IsSpecializedCategory objC C) : IsSpecializedCategory (OppositeComputationalCategory C) :=
    @Build_IsSpecializedCategory objC (OppositeComputationalCategory C)
                                 (fun _ _ _ _ _ _ _ => @Associativity_sym _ _ _ _ _ _ _ _ _ _)
                                 (fun _ _ _ _ _ _ _ => @Associativity _ _ _ _ _ _ _ _ _ _)
                                 (fun _ _ => @RightIdentity _ _ _ _ _)
                                 (fun _ _ => @LeftIdentity _ _ _ _ _).

  Definition OppositeCategory `(C : @SpecializedCategory objC) : @SpecializedCategory objC :=
    @Build_SpecializedCategory' objC
                                (OppositeComputationalCategory (UnderlyingCCategory C))
                                _.

End OppositeCategory.

(*Notation "C ᵒᵖ" := (OppositeCategory C) : category_scope.*)

Section DualCategories.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Lemma op_op_id : OppositeCategory (OppositeCategory C) = C.
    clear D objD.
    unfold OppositeCategory, OppositeComputationalCategory; simpl.
    repeat change (fun a => ?f a) with f.
    destruct C as [ C' [ ] ]; destruct C'; intros; simpl; reflexivity.
  Qed.

  Lemma op_distribute_prod : OppositeCategory (C * D) = (OppositeCategory C) * (OppositeCategory D).
    spcat_eq.
  Qed.
End DualCategories.

Hint Rewrite @op_op_id @op_distribute_prod : category.

Section DualObjects.
  Context `(C : @SpecializedCategory objC).

  Definition terminal_opposite_initial (o : C) : IsTerminalObject o -> IsInitialObject (C := OppositeCategory C) o
    := fun H o' => H o'.

  Definition initial_opposite_terminal (o : C) : IsInitialObject o -> IsTerminalObject (C := OppositeCategory C) o
    := fun H o' => H o'.

  Definition terminal_to_opposite_initial : TerminalObject C -> InitialObject (OppositeCategory C)
    := Eval cbv beta iota zeta delta [terminal_opposite_initial TerminalObject_IsTerminalObject IsInitialObject_InitialObject proj1_sig proj2_sig] in
        fun x => terminal_opposite_initial x.

  Definition initial_to_opposite_terminal : InitialObject C -> TerminalObject (OppositeCategory C)
    := Eval cbv beta iota zeta delta [initial_opposite_terminal IsTerminalObject_TerminalObject InitialObject_IsInitialObject proj1_sig proj2_sig] in
        fun x => initial_opposite_terminal x.
End DualObjects.

Section OppositeFunctor.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.
  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.

  Definition OppositeFunctor : SpecializedFunctor COp DOp.
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

  Lemma op_op_functor_id : OppositeFunctor (OppositeFunctor F) == F.
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

  Definition OppositeNaturalTransformation : SpecializedNaturalTransformation GOp FOp.
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

  Lemma op_op_nt_id : OppositeNaturalTransformation (OppositeNaturalTransformation T) == T.
    nt_eq; intros; try functor_eq; autorewrite with category; subst; trivial.
  Qed.
End OppositeNaturalTransformation_Id.

(* not terribly useful, given that this would make [autorewrite with core] give "Anomaly: Uncaught exception Failure("nth"). Please report." *)
(*Hint Rewrite op_op_nt_id.*)
