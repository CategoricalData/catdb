Require Export Limits.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Section Equalizer.
  Context `(C : @SpecializedCategory objC).
  Variables A B : objC.
  Variables f g : C.(Morphism) A B.

  Inductive EqualizerTwo := EqualizerA | EqualizerB.

  Definition EqualizerDiagram_Morphism (a b : EqualizerTwo) : Set :=
    match (a, b) with
      | (EqualizerA, EqualizerA) => unit
      | (EqualizerB, EqualizerB) => unit
      | (EqualizerB, EqualizerA) => Empty_set
      | (EqualizerA, EqualizerB) => EqualizerTwo
    end.

  Global Arguments EqualizerDiagram_Morphism a b /.

  Definition EqualizerDiagram_Compose s d d' (m1 : EqualizerDiagram_Morphism d d') (m2 : EqualizerDiagram_Morphism s d) :
    EqualizerDiagram_Morphism s d'.
    destruct s, d, d'; simpl in *; trivial.
  Defined.

  Definition EqualizerDiagram : @SpecializedCategory EqualizerTwo.
    refine {|
      Morphism' := EqualizerDiagram_Morphism;
      Identity' := (fun x => match x with EqualizerA => tt | EqualizerB => tt end);
      Compose' := EqualizerDiagram_Compose
    |};
    abstract (
      intros; destruct_type EqualizerTwo; simpl in *; destruct_type Empty_set; trivial
    ).
  Defined.

  Definition EqualizerFunctor_ObjectOf x :=
    match x with
      | EqualizerA => A
      | EqualizerB => B
    end.

  Global Arguments EqualizerFunctor_ObjectOf x /.

  Definition EqualizerFunctor_MorphismOf s d (m : Morphism EqualizerDiagram s d) :
    Morphism C (EqualizerFunctor_ObjectOf s) (EqualizerFunctor_ObjectOf d).
    destruct s, d; simpl in *; try apply Identity;
      try solve [ destruct m ];
        exact match m with
                | EqualizerA => f
                | EqualizerB => g
              end.
  Defined.

  Definition EqualizerFunctor : SpecializedFunctor EqualizerDiagram C.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          EqualizerFunctor_ObjectOf
          EqualizerFunctor_MorphismOf
          _
          _
        )
    end;
    abstract (
      unfold EqualizerFunctor_MorphismOf; simpl; intros;
        destruct_type EqualizerTwo;
        repeat rewrite @LeftIdentity; repeat rewrite @RightIdentity;
          trivial; try destruct_to_empty_set
    ).
  Defined.

  Definition Equalizer := Limit EqualizerFunctor.
  Definition Coequalizer := Colimit EqualizerFunctor.
End Equalizer.
