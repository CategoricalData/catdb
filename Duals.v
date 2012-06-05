Require Import Common EquivalenceRelation Category Functor.

Section OppositeCategory.
  Variable C : Category.

  Hint Resolve Transitive.

  Definition OppositeCategory : Category.
    refine {| Object := C.(Object);
      Morphism := (fun s d => C.(Morphism) d s);
      MorphismsEquivalent' := (fun _ _ m m' => @MorphismsEquivalent' C _ _ m m');
      Identity := @Identity C;
      Compose := (fun s d d' m1 m2 => @Compose C d' d s m2 m1)
      |}; abstract (t; eauto).
  Defined.

End OppositeCategory.

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
  Definition COp := OppositeCategory C.
  Definition DOp := OppositeCategory D.

  Definition OppositeFunctor : Functor COp DOp.
    refine {| ObjectOf := (fun c : COp => F c : DOp);
      MorphismOf := (fun s d : COp => fun m : Morphism _ s d => @MorphismOf _ _ F d s m);
      FEquivalenceOf := (fun s d : COp => fun m1 m2 : Morphism _ s d => @FEquivalenceOf _ _ F d s m1 m2);
      FCompositionOf := (fun (d' d s : COp) (m1 : Morphism COp d' d) (m2 : Morphism COp d s) => @FCompositionOf _ _ F s d d' m2 m1);
      FIdentityOf := (fun o : COp => @FIdentityOf _ _ F o)
      |}.
  Defined.
End OppositeFunctor.
