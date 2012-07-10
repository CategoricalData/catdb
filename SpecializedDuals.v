Require Import JMeq Eqdep.
Require Export SpecializedCategory SpecializedFunctor SpecializedProductCategory SpecializedNaturalTransformation.
Require Import Common FEqualDep.

Set Implicit Arguments.

Local Infix "*" := ProductSpecializedCategory.
Local Infix "==" := JMeq (at level 70).

Section OppositeSpecializedCategory.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Definition OppositeSpecializedCategory : @SpecializedCategory objC (fun s d => morC d s).
    refine (Build_SpecializedCategory (fun s d => morC d s)
      (@Identity _ _ C)
      (fun (s d d' : C) (m1 : C.(Morphism) d' d) (m2 : C.(Morphism) d s) => Compose m2 m1)
      _ _ _);
    abstract (t; eauto).
  Defined.
End OppositeSpecializedCategory.

Ltac unOppositeSpecializedCategory C :=
  match eval unfold C in C with
    @OppositeSpecializedCategory ?obj ?mor ?C' => C'
  end.

Ltac unfold_OppositeSpecializedCategory_of obj mor C :=
  let C' := unOppositeSpecializedCategory C in
    progress (
      change (@Object obj mor C) with (Object C') in *; simpl in *;
        change (@Morphism obj mor C) with (fun s d => Morphism C' d s) in *; simpl in *;
          change (@Identity obj mor C) with (fun o => Identity C' o) in *; simpl in *;
            change (@Compose obj mor C) with (fun s d d' m1 m2 => Morphism C' m2 m1) in *; simpl in *
    ).

Ltac unfold_OppositeSpecializedCategory :=
  repeat match goal with
           | [ _ : appcontext[@Object ?obj ?mor ?C] |- _ ] => unfold_OppositeSpecializedCategory_of obj mor C
           | [ _ : appcontext[@Morphism ?obj ?mor ?C] |- _ ] => unfold_OppositeSpecializedCategory_of obj mor C
           | [ _ : appcontext[@Identity ?obj ?mor ?C] |- _ ] => unfold_OppositeSpecializedCategory_of obj mor C
           | [ _ : appcontext[@Compose ?obj ?mor ?C] |- _ ] => unfold_OppositeSpecializedCategory_of obj mor C
           | [ |- appcontext[@Object ?obj ?mor ?C] ] => unfold_OppositeSpecializedCategory_of obj mor C
           | [ |- appcontext[@Morphism ?obj ?mor ?C] ] => unfold_OppositeSpecializedCategory_of obj mor C
           | [ |- appcontext[@Identity ?obj ?mor ?C] ] => unfold_OppositeSpecializedCategory_of obj mor C
           | [ |- appcontext[@Compose ?obj ?mor ?C] ] => unfold_OppositeSpecializedCategory_of obj mor C
         end.

(*Hint Extern 1 => unfold_OppositeSpecializedCategory.*)

Section DualCategories.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.

  Lemma op_op_id : OppositeSpecializedCategory (OppositeSpecializedCategory C) = C.
    spcat_eq.
  Qed.

  Lemma op_distribute_prod : OppositeSpecializedCategory (C * D) = (OppositeSpecializedCategory C) * (OppositeSpecializedCategory D).
    spcat_eq.
  Qed.
End DualCategories.

Hint Rewrite op_op_id op_distribute_prod.

Section DualObjects.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Lemma initial_opposite_terminal (o : C) :
    InitialObject o -> @TerminalObject _ _ (OppositeSpecializedCategory C) o.
    t.
  Qed.

  Lemma terminal_opposite_initial (o : C) :
    TerminalObject o -> @InitialObject _ _ (OppositeSpecializedCategory C) o.
    t.
  Qed.
End DualObjects.

Section OppositeSpecializedFunctor.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable F : SpecializedFunctor C D.
  Let COp := OppositeSpecializedCategory C.
  Let DOp := OppositeSpecializedCategory D.

  Definition OppositeSpecializedFunctor : SpecializedFunctor COp DOp.
    refine (Build_SpecializedFunctor COp DOp
      (fun c : COp => F c : DOp)
      (fun (s d : COp) (m : C.(Morphism) d s) => @MorphismOf _ _ _ _ _ _ F d s m)
      (fun d' d s m1 m2 => @FCompositionOf _ _ _ _ _ _ F s d d' m2 m1)
      (@FIdentityOf _ _ _ _ _ _ F)
    ).
  Defined.
End OppositeSpecializedFunctor.

Section OppositeSpecializedFunctor_Id.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable F : SpecializedFunctor C D.

  Lemma op_op_functor_id : OppositeSpecializedFunctor (OppositeSpecializedFunctor F) == F.
    spfunctor_eq; autorewrite with core; trivial.
  Qed.
End OppositeSpecializedFunctor_Id.

(* not terribly useful, given that this would make [autorewrite with core] give "Anomaly: Uncaught exception Failure("nth"). Please report." *)
(*Hint Rewrite op_op_functor_id.*)

Section OppositeSpecializedNaturalTransformation.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variables F G : SpecializedFunctor C D.
  Variable T : SpecializedNaturalTransformation F G.
  Let COp := OppositeSpecializedCategory C.
  Let DOp := OppositeSpecializedCategory D.
  Let FOp := OppositeSpecializedFunctor F.
  Let GOp := OppositeSpecializedFunctor G.

  Definition OppositeSpecializedNaturalTransformation : SpecializedNaturalTransformation GOp FOp.
    refine (Build_SpecializedNaturalTransformation GOp FOp
      (fun c : COp => T.(ComponentsOf) c : DOp.(Morphism) (GOp c) (FOp c))
      (fun s d m => eq_sym (@Commutes _ _ _ _ _ _ _ _ T d s m))
    ).
  Defined.
End OppositeSpecializedNaturalTransformation.

Section OppositeSpecializedNaturalTransformation_Id.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variables F G : SpecializedFunctor C D.
  Variable T : SpecializedNaturalTransformation F G.

  Lemma op_op_nt_id : OppositeSpecializedNaturalTransformation (OppositeSpecializedNaturalTransformation T) == T.
    spnt_eq; intros; try spfunctor_eq; autorewrite with core; trivial.
  Qed.
End OppositeSpecializedNaturalTransformation_Id.

(* not terribly useful, given that this would make [autorewrite with core] give "Anomaly: Uncaught exception Failure("nth"). Please report." *)
(*Hint Rewrite op_op_nt_id.*)
