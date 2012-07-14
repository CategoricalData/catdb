Require Import JMeq.
Require Export Category Functor ProductCategory NaturalTransformation.
Require Import Common CategoryEquality.

Set Implicit Arguments.

Local Infix "*" := ProductCategory.
Local Infix "==" := JMeq (at level 70).

Section OppositeCategory.
  Variable C : Category.

  Definition OppositeCategory : Category.
    refine {| Object := C.(Object);
      Morphism := (fun s d => C.(Morphism) d s);
      Identity := @Identity C;
      Compose := (fun s d d' m1 m2 => @Compose C d' d s m2 m1)
      |}; abstract (t; eauto).
  Defined.
End OppositeCategory.

Section DualCategories.
  Variables C D : Category.

  Lemma op_op_id : OppositeCategory (OppositeCategory C) = C.
    cat_eq.
  Qed.

  Hint Unfold OppositeCategory ProductCategory.

  Lemma op_distribute_prod : OppositeCategory (C * D) = (OppositeCategory C) * (OppositeCategory D).
    cat_eq.
  Qed.
End DualCategories.

Hint Rewrite op_op_id op_distribute_prod.

Section DualObjects.
  Variable C : Category.

  Lemma initial_opposite_terminal (o : C) :
    InitialObject o -> @TerminalObject (OppositeCategory C) o.
    t.
  Qed.

  Lemma terminal_opposite_initial (o : C) :
    TerminalObject o -> @InitialObject (OppositeCategory C) o.
    t.
  Qed.
End DualObjects.

Section OppositeFunctor.
  Variables C D : Category.
  Variable F : Functor C D.
  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.

  Definition OppositeFunctor : Functor COp DOp.
    refine {| ObjectOf := (fun c : COp => F c : DOp);
      MorphismOf := (fun s d : COp => fun m : Morphism _ s d => @MorphismOf _ _ F d s m);
      FCompositionOf := (fun (d' d s : COp) (m1 : Morphism COp d' d) (m2 : Morphism COp d s) => @FCompositionOf _ _ F s d d' m2 m1);
      FIdentityOf := (fun o : COp => @FIdentityOf _ _ F o)
      |}.
  Defined.
End OppositeFunctor.

Section OppositeFunctor_Id.
  Variables C D : Category.
  Variable F : Functor C D.

  Lemma op_op_functor_id : OppositeFunctor (OppositeFunctor F) == F.
    functor_eq; cat_eq.
  Qed.
End OppositeFunctor_Id.

(* not terribly useful, given that this would make [autorewrite with core] give "Anomaly: Uncaught exception Failure("nth"). Please report." *)
(*Hint Rewrite op_op_functor_id.*)


Section OppositeNaturalTransformation.
  Variables C D : Category.
  Variable F G : Functor C D.
  Variable T : NaturalTransformation F G.
  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.
  Let FOp := OppositeFunctor F.
  Let GOp := OppositeFunctor G.

  Definition OppositeNaturalTransformation : NaturalTransformation GOp FOp.
    refine {| ComponentsOf := (fun c : COp => T.(ComponentsOf) c : Morphism DOp (GOp c) (FOp c));
      Commutes := (fun s d m => eq_sym (@Commutes _ _ _ _ T d s m))
    |}.
  Defined.
End OppositeNaturalTransformation.

Section OppositeNaturalTransformation_Id.
  Variables C D : Category.
  Variables F G : Functor C D.
  Variable T : NaturalTransformation F G.

  Lemma op_op_nt_id : OppositeNaturalTransformation (OppositeNaturalTransformation T) == T.
    nt_eq; functor_eq; cat_eq.
  Qed.
End OppositeNaturalTransformation_Id.

(* not terribly useful, given that this would make [autorewrite with core] give "Anomaly: Uncaught exception Failure("nth"). Please report." *)
(*Hint Rewrite op_op_nt_id.*)
