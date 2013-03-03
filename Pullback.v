Require Export Limits.
Require Import Common Duals SpecializedCommaCategory FunctorCategory.

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
  Section pullback.
    Variables a b c : objC.
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
          repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
          trivial; try destruct_to_empty_set
        ).
    Defined.

    Definition Pullback := Limit PullbackDiagram.
    Definition IsPullback := IsLimit (F := PullbackDiagram).
  End pullback.

  Section pullback_functorial.
    Local Infix "/" := SliceSpecializedCategoryOver.

    Variable c : C.

    Definition PullbackDiagramFunctor_ObjectOf : ((C / c) * (C / c)) -> (C ^ PullbackIndex)%category
      := fun fg => PullbackDiagram _ _ c (projT2 (fst fg)) (projT2 (snd fg)).

    Definition PullbackDiagramFunctor_MorphismOf_ComponentsOf s d (m : Morphism ((C / c) * (C / c)) s d)
    : forall x, Morphism _ (PullbackDiagramFunctor_ObjectOf s x) (PullbackDiagramFunctor_ObjectOf d x)
      := fun x => match x with
                    | PullbackA => (fst (proj1_sig (fst m)))
                    | PullbackB => (fst (proj1_sig (snd m)))
                    | PullbackC => Identity _
                  end.

    Definition PullbackDiagramFunctor_MorphismOf s d (m : Morphism ((C / c) * (C / c)) s d)
    : Morphism (C ^ PullbackIndex) (PullbackDiagramFunctor_ObjectOf s) (PullbackDiagramFunctor_ObjectOf d).
      exists (PullbackDiagramFunctor_MorphismOf_ComponentsOf m).
      present_spfunctor.
      abstract (
          destruct m as [[[]] [[]]];
          simpl in *;
            intros [] [] [];
          simpl in *;
            autorewrite with morphism in *;
            trivial
        ).
    Defined.

    Definition PullbackDiagramFunctor : SpecializedFunctor ((C / c) * (C / c)) (C ^ PullbackIndex).
      match goal with
        | [ |- SpecializedFunctor ?C ?D ] =>
          refine (Build_SpecializedFunctor C D
                                           PullbackDiagramFunctor_ObjectOf
                                           PullbackDiagramFunctor_MorphismOf
                                           _
                                           _)
      end;
      present_spfunctor;
      abstract (
          repeat intros [[[[? []] ?]] [[[? []] ?]]];
          simpl in *;
            nt_eq;
          destruct_head PullbackThree;
          autorewrite with morphism;
          trivial
        ).
    Defined.
  End pullback_functorial.

  Section pushout.
    Variables a b c : objC.
    Variable f : C.(Morphism) c a.
    Variable g : C.(Morphism) c b.

    Definition PushoutIndex := OppositeCategory PullbackIndex.
    Definition PushoutDiagram_ObjectOf := PullbackDiagram_ObjectOf a b c.

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
          repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
          trivial; try destruct_to_empty_set
        ).
    Defined.

    Definition Pushout := Colimit PushoutDiagram.
    Definition IsPushout := IsColimit (F := PushoutDiagram).
  End pushout.

  Section pushout_functorial.
    Local Notation "a /  C" := (CosliceSpecializedCategoryOver C a).

    Variable c : C.

    Definition PushoutDiagramFunctor_ObjectOf : ((c / C) * (c / C)) -> (C ^ PushoutIndex)%category
      := fun fg => PushoutDiagram _ _ c (projT2 (fst fg)) (projT2 (snd fg)).

    Definition PushoutDiagramFunctor_MorphismOf_ComponentsOf s d (m : Morphism ((c / C) * (c / C)) s d)
    : forall x, Morphism _ (PushoutDiagramFunctor_ObjectOf s x) (PushoutDiagramFunctor_ObjectOf d x)
      := fun x => match x with
                    | PullbackA => (snd (proj1_sig (fst m)))
                    | PullbackB => (snd (proj1_sig (snd m)))
                    | PullbackC => Identity _
                  end.

    Definition PushoutDiagramFunctor_MorphismOf s d (m : Morphism ((c / C) * (c / C)) s d)
    : Morphism (C ^ PushoutIndex) (PushoutDiagramFunctor_ObjectOf s) (PushoutDiagramFunctor_ObjectOf d).
      exists (PushoutDiagramFunctor_MorphismOf_ComponentsOf m).
      present_spfunctor.
      abstract (
          destruct m as [[[]] [[]]];
          simpl in *;
            intros [] [] [];
          simpl in *;
            autorewrite with morphism in *;
            trivial
        ).
    Defined.

    Definition PushoutDiagramFunctor : SpecializedFunctor ((c / C) * (c / C)) (C ^ PushoutIndex).
      match goal with
        | [ |- SpecializedFunctor ?C ?D ] =>
          refine (Build_SpecializedFunctor C D
                                           PushoutDiagramFunctor_ObjectOf
                                           PushoutDiagramFunctor_MorphismOf
                                           _
                                           _)
      end;
      present_spfunctor;
      abstract (
          repeat intros [[[[? []] ?]] [[[? []] ?]]];
          simpl in *;
            nt_eq;
          destruct_head PullbackThree;
          autorewrite with morphism;
          trivial
        ).
    Defined.
  End pushout_functorial.
End Pullback.

Section PullbackObjects.
  Context `{C : @SpecializedCategory objC}.
  Variables a b c : objC.

  (** Does an object [d] together with the functions [i] and [j]
    fit into a pullback diagram?

    [[
           i
        d ----> a
        |       |
      j |       | f
        ↓       ↓
        b ----> c
           g
    ]]
   *)

  Local Ltac t :=
    intros;
    destruct_head_hnf PullbackThree;
    destruct_head_hnf Empty_set;
    destruct_head_hnf unit;
    autorewrite with morphism;
    trivial.

  Definition IsPullbackGivenMorphisms_Object
             (f : Morphism C a c)
             (g : Morphism C b c)
             PullbackObject
             (i : Morphism C PullbackObject a)
             (j : Morphism C PullbackObject b)
             (PullbackCompatible : Compose f i = Compose g j)
  : CommaCategory_Object (DiagonalFunctor C PullbackIndex)
                         (SliceCategory_Functor
                            (FunctorCategory.FunctorCategory PullbackIndex C)
                            (PullbackDiagram C a b c f g)).
    exists (PullbackObject, tt).
    exists (fun x => match x as x return (Morphism C PullbackObject (PullbackDiagram_ObjectOf a b c x)) with
                       | PullbackA => i
                       | PullbackB => j
                       | PullbackC => Compose f i
                     end);
      simpl; present_spcategory;
      abstract t.
  Defined.

  Definition IsPullbackGivenMorphisms
             (f : Morphism C a c)
             (g : Morphism C b c)
             PullbackObject
             (i : Morphism C PullbackObject a)
             (j : Morphism C PullbackObject b)
             (PullbackCompatible : Compose f i = Compose g j)
    := @IsPullback _ _ a b c f g (IsPullbackGivenMorphisms_Object f g PullbackObject i j PullbackCompatible).

  Definition IsPushoutGivenMorphisms_Object
             (f : Morphism C c a)
             (g : Morphism C c b)
             PushoutObject
             (i : Morphism C a PushoutObject)
             (j : Morphism C b PushoutObject)
             (PushoutCompatible : Compose j g = Compose i f)
  : CommaCategory_Object (SliceCategory_Functor
                            (FunctorCategory.FunctorCategory PushoutIndex C)
                            (PushoutDiagram C a b c f g))
                         (DiagonalFunctor C PushoutIndex).
    exists (tt, PushoutObject).
    exists (fun x => match x as x return (Morphism C (PushoutDiagram_ObjectOf a b c x) PushoutObject) with
                       | PullbackA => i
                       | PullbackB => j
                       | PullbackC => Compose i f
                     end);
      simpl; present_spcategory;
      abstract t.
  Defined.

  Definition IsPushoutGivenMorphisms
             (f : Morphism C c a)
             (g : Morphism C c b)
             PushoutObject
             (i : Morphism C a PushoutObject)
             (j : Morphism C b PushoutObject)
             (PushoutCompatible : Compose j g = Compose i f)
    := @IsPushout _ _ a b c f g (IsPushoutGivenMorphisms_Object f g PushoutObject i j PushoutCompatible).
End PullbackObjects.
