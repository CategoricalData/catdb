Require Export Limits.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Equalizer.
  Variable C : Category.
  Variables A B : C.
  Variables f g : C.(Morphism) A B.

  Inductive EqualizerTwo := EqualizerA | EqualizerB.

  Definition EqualizerIndex_Morphism (a b : EqualizerTwo) : Set :=
    match (a, b) with
      | (EqualizerA, EqualizerA) => unit
      | (EqualizerB, EqualizerB) => unit
      | (EqualizerB, EqualizerA) => Empty_set
      | (EqualizerA, EqualizerB) => EqualizerTwo
    end.

  Global Arguments EqualizerIndex_Morphism a b /.

  Definition EqualizerIndex_Compose s d d' (m1 : EqualizerIndex_Morphism d d') (m2 : EqualizerIndex_Morphism s d) :
    EqualizerIndex_Morphism s d'.
    destruct s, d, d'; simpl in *; trivial.
  Defined.

  Definition EqualizerIndex : Category.
    refine (@Build_Category EqualizerTwo
                                       EqualizerIndex_Morphism
                                       (fun x => match x with EqualizerA => tt | EqualizerB => tt end)
                                       EqualizerIndex_Compose
                                       _
                                       _
                                       _);
    abstract (
        intros; destruct_type EqualizerTwo; simpl in *; destruct_type Empty_set; trivial
      ).
  Defined.

  Definition EqualizerDiagram_ObjectOf x :=
    match x with
      | EqualizerA => A
      | EqualizerB => B
    end.

  Global Arguments EqualizerDiagram_ObjectOf x /.

  Definition EqualizerDiagram_MorphismOf s d (m : Morphism EqualizerIndex s d) :
    Morphism C (EqualizerDiagram_ObjectOf s) (EqualizerDiagram_ObjectOf d).
    destruct s, d; simpl in *; try apply Identity;
      try solve [ destruct m ];
        exact match m with
                | EqualizerA => f
                | EqualizerB => g
              end.
  Defined.

  Definition EqualizerDiagram : Functor EqualizerIndex C.
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor C D
          EqualizerDiagram_ObjectOf
          EqualizerDiagram_MorphismOf
          _
          _
        )
    end;
    abstract (
      unfold EqualizerDiagram_MorphismOf; simpl; intros;
        destruct_type EqualizerTwo;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
          trivial; try destruct_to_empty_set
    ).
  Defined.

  Definition Equalizer := Limit EqualizerDiagram.
  Definition Coequalizer := Colimit EqualizerDiagram.
End Equalizer.
