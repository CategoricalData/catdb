Require Export Limits.
Require Import Common Duals.

Set Implicit Arguments.

Generalizable All Variables.

Section Pullback.
  (* Quoting nCatLab (http://ncatlab.org/nlab/show/pullback):

     A pullback is a limit of a diagram like this:
     [[
        a       b
         \     /
        f \   / g
           ↘ ↙
            c
     ]]
   *)

  Context `(C : @SpecializedCategory objC).
  Variables a b c : objC.
  Section pullback.
    Variable f : C.(Morphism) a c.
    Variable g : C.(Morphism) b c.

    Inductive PullbackThree := PullbackA | PullbackB | PullbackC.

    Definition PullbackIndex_Morphism (a b : PullbackThree) : Set :=
      match (a, b) with
        | (PullbackA, PullbackA) => unit
        | (PullbackB, PullbackB) => unit
        | (PullbackC, PullbackC) => unit
        | (PullbackA, PullbackC) => unit
        | (PullbackB, PullbackC) => unit
        | _ => Empty_set
      end.

    Global Arguments PullbackIndex_Morphism a b /.

           Definition PullbackIndex_Compose s d d' (m1 : PullbackIndex_Morphism d d') (m2 : PullbackIndex_Morphism s d) :
      PullbackIndex_Morphism s d'.
             destruct s, d, d'; simpl in *; trivial.
           Defined.

    Definition PullbackIndex : @SpecializedCategory PullbackThree.
      refine (@Build_SpecializedCategory _
                                         PullbackIndex_Morphism
                                         (fun x => match x as p return (PullbackIndex_Morphism p p) with
                                                       PullbackA => tt | PullbackB => tt | PullbackC => tt
                                                   end)
                                         PullbackIndex_Compose
                                         _
                                         _
                                         _);
      abstract (
          intros; destruct_type PullbackThree; simpl in *; destruct_type Empty_set; trivial
        ).
    Defined.

    Definition PullbackDiagram_ObjectOf x :=
      match x with
        | PullbackA => a
        | PullbackB => b
        | PullbackC => c
      end.

    Global Arguments PullbackDiagram_ObjectOf x / .

    Definition PullbackDiagram_MorphismOf s d (m : Morphism PullbackIndex s d) :
      Morphism C (PullbackDiagram_ObjectOf s) (PullbackDiagram_ObjectOf d).
      destruct s, d; simpl in *;
      try apply Identity;
      try assumption;
      try solve [ destruct m ].
    Defined.

    Definition PullbackDiagram : SpecializedFunctor PullbackIndex C.
      match goal with
        | [ |- SpecializedFunctor ?C ?D ] =>
          refine (Build_SpecializedFunctor C D
                                           PullbackDiagram_ObjectOf
                                           PullbackDiagram_MorphismOf
                                           _
                                           _
                 )
      end;
      abstract (
          unfold PullbackDiagram_MorphismOf; simpl; intros;
          destruct_type PullbackThree;
          repeat rewrite @LeftIdentity; repeat rewrite @RightIdentity;
          trivial; try destruct_to_empty_set
        ).
    Defined.

    Definition Pullback := Limit PullbackDiagram.
  End pullback.

  Section pushout.
    Variable f : C.(Morphism) c a.
    Variable g : C.(Morphism) c b.

    Definition PushoutIndex := OppositeCategory PullbackIndex.
    Definition PushoutDiagram_ObjectOf := PullbackDiagram_ObjectOf.

    Global Arguments PushoutDiagram_ObjectOf x / .


    Definition PushoutDiagram_MorphismOf s d (m : Morphism PushoutIndex s d) :
      Morphism C (PushoutDiagram_ObjectOf s) (PushoutDiagram_ObjectOf d).
      destruct s, d; simpl in *;
      try apply Identity;
      try assumption;
      try solve [ destruct m ].
    Defined.

    Definition PushoutDiagram : SpecializedFunctor PushoutIndex C.
      match goal with
        | [ |- SpecializedFunctor ?C ?D ] =>
          refine (Build_SpecializedFunctor C D
                                           PushoutDiagram_ObjectOf
                                           PushoutDiagram_MorphismOf
                                           _
                                           _
                 )
      end;
      abstract (
          unfold PushoutDiagram_MorphismOf; simpl; intros;
          destruct_type PullbackThree;
          repeat rewrite @LeftIdentity; repeat rewrite @RightIdentity;
          trivial; try destruct_to_empty_set
        ).
    Defined.

    Definition Pushout := Colimit PushoutDiagram.
  End pushout.
End Pullback.
