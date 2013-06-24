Require Import ProofIrrelevance.
Require Export Coend LimitFunctors LimitFunctors FunctorCategory ProductInducedFunctors FunctorialComposition.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope type_scope.

Section Coend.
  Variable C : Category.

  Let COp := OppositeCategory C.

  Definition CoendFunctor_Index_Object := { ds : C * C & Morphism C (snd ds) (fst ds) } + C.

  Global Arguments CoendFunctor_Index_Object /.

  Definition CoendFunctor_Index_Morphism (s d : CoendFunctor_Index_Object) : Set :=
    match (s, d) with
      | (inl sdm, inr c) => (fst (projT1 sdm) = c) + (snd (projT1 sdm) = c)
      | _ => (s = d)
    end.

  Global Arguments CoendFunctor_Index_Morphism s d /.

  Definition CoendFunctor_Index_Identity x : CoendFunctor_Index_Morphism x x :=
    match x as s return (CoendFunctor_Index_Morphism s s) with
      | inl s => eq_refl
      | inr s => eq_refl
    end.

  Global Arguments CoendFunctor_Index_Identity x /.

  Ltac inj H := injection H; clear H; intros; subst.

  Definition CoendFunctor_Index_Compose s d d' :
    CoendFunctor_Index_Morphism d d'
    -> CoendFunctor_Index_Morphism s d
    -> CoendFunctor_Index_Morphism s d'.
  Proof.
    destruct s, d, d'; simpl; intros;
    match goal with
      | [ H : _ + _ |- _ ] => destruct H; [ left | right ];
                              abstract congruence
      | _ => abstract congruence
    end.
  Defined.

  Definition CoendFunctor_Index : Category.
  Proof.
    refine (@Build_Category CoendFunctor_Index_Object
                                       CoendFunctor_Index_Morphism
                                       CoendFunctor_Index_Identity
                                       CoendFunctor_Index_Compose
                                       _
                                       _
                                       _);
    abstract (
        simpl; intros;
        repeat (match goal with
                  | [ x : _ + _ |- _ ] => destruct x; simpl in *
                                                    | _ => apply proof_irrelevance
                                                    | _ => congruence
                                                    | _ => f_equal
                end)
      ).
  Defined.

  Definition CoendFunctor_Diagram_ObjectOf_pre : CoendFunctor_Index -> (COp * C) :=
    fun x => match x with
               | inl c0c1 => (projT1 c0c1)
               | inr c => (c, c)
             end.

  Global Arguments CoendFunctor_Diagram_ObjectOf_pre _ /.

  Hint Extern 1 (Morphism _ ?X ?X) => apply Identity : morphism.
(*  Hint Extern 1 (Morphism _ _ _) => hnf. *)

  Definition CoendFunctor_Diagram_MorphismOf_pre s d :
    CoendFunctor_Index_Morphism s d
    -> Morphism (COp * C) (CoendFunctor_Diagram_ObjectOf_pre s) (CoendFunctor_Diagram_ObjectOf_pre d).
  Proof.
    destruct s, d; simpl in *; intros; split;
    repeat match goal with
             | _ => discriminate
             | _ => assumption
             | [ H : inl _ = inl _ |- _ ] => inj H
             | [ H : inr _ = inr _ |- _ ] => inj H
             | [ H : sigT _ |- _ ] => destruct H; simpl in *
             | [ H : _ + _ |- _ ] => destruct H; subst
           end;
    apply Identity.
  Defined.

  Ltac inj' H :=
    match type of H with
      | ?X = ?X => fail 1
      | _ => injection H; intros; subst
    end.

  Definition CoendFunctor_Diagram_pre : Functor CoendFunctor_Index (COp * C).
  Proof.
    refine (Build_Functor
      CoendFunctor_Index (COp * C)
      CoendFunctor_Diagram_ObjectOf_pre
      CoendFunctor_Diagram_MorphismOf_pre
      _
      _);
    abstract (
      repeat match goal with
               | [ |- forall x : CoendFunctor_Index_Object, _ ] =>
                 destruct x
             end; simpl; intros;
      repeat match goal with
               | _ => discriminate
               | _ => progress (subst; unfold eq_rect_r)
               | [ H : inl _ = inl _ |- _ ] => inj' H
               | [ H : inr _ = inr _ |- _ ] => inj' H
               | [ x : sigT _ |- _ ] => destruct x; simpl in *
               | [ H : _ + _ |- _ ] => destruct H
               | _ => rewrite <- eq_rect_eq
               | _ => apply injective_projections; simpl
             end; auto with category
    ).
  Defined.
End Coend.

Section CoendFunctor.
  Variable C : Category.
  Variable D : Category.

  Let COp := OppositeCategory C.

  Hypothesis HasColimits : forall F : Functor (CoendFunctor_Index C) D, Colimit F.

  Let CoendFunctor_post := ColimitFunctor HasColimits.

  Let o := (FunctorialComposition (CoendFunctor_Index C) (COp * C) D).
  Let CoendFunctor_pre := (o ⟨ - , (CoendFunctor_Diagram_pre C) ⟩)%functor.

  Definition CoendFunctor := ComposeFunctors CoendFunctor_post CoendFunctor_pre.
End CoendFunctor.
