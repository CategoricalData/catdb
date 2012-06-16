Require Export Category Functor ProductCategory.
Require Import Common CategoryEquality.

Local Infix "*" := ProductCategory.

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

  Hint Unfold OppositeCategory ProductCategory prod_identity prod_compose prod_morphism prod_object.

  Lemma op_distribute_prod : OppositeCategory (C * D) = (OppositeCategory C) * (OppositeCategory D).
    cat_eq_with ltac:(autounfold with core in *; destruct_type @prod).
  Qed.
End DualCategories.

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

Implicit Arguments OppositeFunctor [C D].
