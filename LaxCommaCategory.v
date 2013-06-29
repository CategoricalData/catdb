Require Import ProofIrrelevance.
Require Export Category Functor ProductCategory NaturalTransformation.
Require Import Common DecidableDiscreteCategory ComputableCategory DefinitionSimplification FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Local Hint Immediate ComposeFunctorsAssociativity LeftIdentityFunctor RightIdentityFunctor.

Local Ltac lax_comma_t :=
  repeat (let H := fresh in intro H; destruct H as [ [ ? ? ] ? ]);
  repeat match goal with
           | _ => intro
           | _ => progress subst
           | [ |- @eq ?T _ _ ]
             => match eval hnf in T with
                  | sigT _ => apply sigT_eq
                  | prod _ _ => apply injective_projections
                  | unit => solve [ simpl; trivial ]
                  | Functor _ _ => apply Functor_eq
                  | _ => solve [ simpl; auto ]
                end
           | [ |- JMeq _ _ ] => solve [ simpl; reflexivity ]
           | [ |- @JMeq ?A _ ?A _ ] => apply eq_JMeq
           | [ |- @JMeq ?A ?x ?B ?y ]
             => match eval hnf in A with
                  | NaturalTransformation _ _ => apply NaturalTransformation_JMeq; trivial
                  | _ => let A' := (eval simpl in A) in
                         let B' := (eval simpl in B) in
                         progress change (@JMeq A' x B' y)
                end
         end;
  simpl in *;
  repeat rewrite FIdentityOf;
  repeat rewrite LeftIdentity;
  repeat rewrite RightIdentity;
  repeat rewrite Associativity;
  reflexivity.

Section LaxSliceCategory.
  Variable I : Type.
  Variable Index2Cat : I -> Category.

  Local Coercion Index2Cat : I >-> Category.

  Let Cat := ComputableCategory Index2Cat.

  Variable C : Category.

  (** Quoting David Spivak:
     David: ok
       so an object of [FC ⇓ D] is a pair [(X, G)], where [X] is a
       finite category (or a small category or whatever you wanted)
       and [G : X --> D] is a functor.
       a morphism in [FC ⇓ D] is a ``natural transformation diagram''
       (as opposed to a commutative diagram, in which the natural
       transformation would be ``identity'')
       so a map in [FC ⇓ D] from [(X, G)] to [(X', G')] is a pair
       [(F, α)] where [F : X --> X'] is a functor and
       [α : G --> G' ○ F] is a natural transformation
       and the punchline is that there is a functor
       [colim : FC ⇓ D --> D]
     David: consider for yourself the case where [F : X --> X'] is
       identity ([X = X']) and (separately) the case where
       [α : G --> G ○ F] is identity.
       the point is, you've already done the work to get this colim
       functor.
       because every map in [FC ⇓ D] can be written as a composition
       of two maps, one where the [F]-part is identity and one where
       the [α]-part is identity.
       and you've worked both of those cases out already.
       *)
  (* use a pair, so that it's easily interchangable with [SliceCategory] *)
  Definition LaxSliceCategory_Object := { X : I * unit & Functor (fst X) C }.

  Definition LaxSliceCategory_Morphism (XG X'G' : LaxSliceCategory_Object) :=
    { F : Functor (fst (projT1 XG)) (fst (projT1 X'G')) * unit &
      NaturalTransformation (projT2 XG) (ComposeFunctors (projT2 X'G') (fst F))
    }.

  Global Arguments LaxSliceCategory_Object / .
  Global Arguments LaxSliceCategory_Morphism _ _ / .

  Definition LaxSliceCategory_Compose' s d d' (Fα : LaxSliceCategory_Morphism d d') (F'α' : LaxSliceCategory_Morphism s d) :
    LaxSliceCategory_Morphism s d'.
    exists (ComposeFunctors (fst (projT1 Fα)) (fst (projT1 F'α')), tt).
    repeat match goal with
             | [ H : _ |- _ ] => unique_pose_with_body (fst (projT1 H))
             | [ H : _ |- _ ] => unique_pose_with_body (projT2 H)
           end; simpl in *.
    repeat match goal with
             | [ x : _, T : _ |- _ ] => unique_pose (NTComposeF T (IdentityNaturalTransformation x))
           end.
    match goal with
      | [ T0 : _, T1 : _ |- _ ] => eapply (NTComposeT _ (NTComposeT T0 T1))
    end.
    Grab Existential Variables.
    match goal with
      | [ C : _ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
      subst_body;
      intros; simpl;
      autorewrite with morphism;
      reflexivity
    ).
  Defined.

  Definition LaxSliceCategory_Compose'' s d d' (Fα : LaxSliceCategory_Morphism d d') (F'α' : LaxSliceCategory_Morphism s d) :
    LaxSliceCategory_Morphism s d'.
    simpl_definition_by_tac_and_exact (@LaxSliceCategory_Compose' s d d' Fα F'α') ltac:(unfold LaxSliceCategory_Compose' in *).
  Defined.

  (* Then we clean up a bit with reduction. *)
  Definition LaxSliceCategory_Compose s d d' (Fα : LaxSliceCategory_Morphism d d') (F'α' : LaxSliceCategory_Morphism s d) :
    LaxSliceCategory_Morphism s d'
    := Eval cbv beta iota zeta delta [LaxSliceCategory_Compose''] in (@LaxSliceCategory_Compose'' s d d' Fα F'α').

  Global Arguments LaxSliceCategory_Compose _ _ _ _ _ / .

  Definition LaxSliceCategory_Identity o : LaxSliceCategory_Morphism o o.
    exists (IdentityFunctor _, tt).
    eapply (NTComposeT _ (IdentityNaturalTransformation _)).
    Grab Existential Variables.
    match goal with
      | [ C : _ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
        intros; simpl;
        autorewrite with morphism;
        reflexivity
      ).
  Defined.

  Global Arguments LaxSliceCategory_Identity _ /.

  Lemma LaxSliceCategory_Associativity : forall (o1 o2 o3 o4 : LaxSliceCategory_Object)
    (m1 : LaxSliceCategory_Morphism o1 o2)
    (m2 : LaxSliceCategory_Morphism o2 o3)
    (m3 : LaxSliceCategory_Morphism o3 o4),
    LaxSliceCategory_Compose
    (LaxSliceCategory_Compose m3 m2) m1 =
    LaxSliceCategory_Compose m3
    (LaxSliceCategory_Compose m2 m1).
  Proof.
    abstract lax_comma_t.
  Qed.

  Lemma LaxSliceCategory_LeftIdentity : forall (a b : LaxSliceCategory_Object)
    (f : LaxSliceCategory_Morphism a b),
    LaxSliceCategory_Compose
    (LaxSliceCategory_Identity b) f = f.
  Proof.
    abstract lax_comma_t.
  Qed.

  Lemma LaxSliceCategory_RightIdentity : forall (a b : LaxSliceCategory_Object)
    (f : LaxSliceCategory_Morphism a b),
    LaxSliceCategory_Compose
    f (LaxSliceCategory_Identity a) = f.
  Proof.
    abstract lax_comma_t.
  Qed.

  Definition LaxSliceCategory : Category
    := @Build_Category
         LaxSliceCategory_Object
         LaxSliceCategory_Morphism
         LaxSliceCategory_Identity
         LaxSliceCategory_Compose
         LaxSliceCategory_Associativity
         LaxSliceCategory_LeftIdentity
         LaxSliceCategory_RightIdentity.
End LaxSliceCategory.

Hint Unfold LaxSliceCategory_Compose LaxSliceCategory_Identity : category.

Section LaxCosliceCategory.
  (* [Definition]s are not sort-polymorphic. *)

  Variable I : Type.
  Variable Index2Cat : I -> Category.

  Local Coercion Index2Cat : I >-> Category.

  Let Cat := ComputableCategory Index2Cat.

  Variable C : Category.

  Definition LaxCosliceCategory_Object := { X : unit * I & Functor (snd X) C }.
  Definition LaxCosliceCategory_Morphism (XG X'G' : LaxCosliceCategory_Object) :=
    { F : unit * Functor (snd (projT1 X'G')) (snd (projT1 XG)) &
      NaturalTransformation (ComposeFunctors (projT2 XG) (snd F)) (projT2 X'G')
    }.

  Global Arguments LaxCosliceCategory_Object / .
  Global Arguments LaxCosliceCategory_Morphism _ _ /.

  Definition LaxCosliceCategory_Compose' s d d' (Fα : LaxCosliceCategory_Morphism d d') (F'α' : LaxCosliceCategory_Morphism s d) :
    LaxCosliceCategory_Morphism s d'.
    exists (tt, ComposeFunctors (snd (projT1 F'α')) (snd (projT1 Fα))).
    repeat match goal with
             | [ H : _ |- _ ] => unique_pose_with_body (snd (projT1 H))
             | [ H : _ |- _ ] => unique_pose_with_body (projT2 H)
           end; simpl in *.
    repeat match goal with
             | [ x : _, T : _ |- _ ] => unique_pose (NTComposeF T (IdentityNaturalTransformation x))
           end.
    match goal with
      | [ T0 : _, T1 : _ |- _ ] => eapply (NTComposeT (NTComposeT T0 T1) _)
    end.
    Grab Existential Variables.
    match goal with
      | [ C : _ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
      subst_body;
      intros; simpl;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
          reflexivity
    ).
  Defined.

  Definition LaxCosliceCategory_Compose'' s d d' (Fα : LaxCosliceCategory_Morphism d d') (F'α' : LaxCosliceCategory_Morphism s d) :
    LaxCosliceCategory_Morphism s d'.
    simpl_definition_by_tac_and_exact (@LaxCosliceCategory_Compose' s d d' Fα F'α') ltac:(unfold LaxCosliceCategory_Compose' in *).
  Defined.

  (* Then we clean up a bit with reduction. *)
  Definition LaxCosliceCategory_Compose s d d' (Fα : LaxCosliceCategory_Morphism d d') (F'α' : LaxCosliceCategory_Morphism s d) :
    LaxCosliceCategory_Morphism s d'
    := Eval cbv beta iota zeta delta [LaxCosliceCategory_Compose''] in (@LaxCosliceCategory_Compose'' s d d' Fα F'α').

  Global Arguments LaxCosliceCategory_Compose _ _ _ _ _ /.

  Definition LaxCosliceCategory_Identity o : LaxCosliceCategory_Morphism o o.
    exists (tt, IdentityFunctor _).
    eapply (NTComposeT _ (IdentityNaturalTransformation _)).
    Grab Existential Variables.
    match goal with
      | [ C : _ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
      intros; simpl;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
          reflexivity
    ).
  Defined.

  Global Arguments LaxCosliceCategory_Identity _ /.

  Lemma LaxCosliceCategory_Associativity : forall (o1 o2 o3 o4 : LaxCosliceCategory_Object)
    (m1 : LaxCosliceCategory_Morphism o1 o2)
    (m2 : LaxCosliceCategory_Morphism o2 o3)
    (m3 : LaxCosliceCategory_Morphism o3 o4),
    LaxCosliceCategory_Compose
    (LaxCosliceCategory_Compose m3 m2) m1 =
    LaxCosliceCategory_Compose m3
    (LaxCosliceCategory_Compose m2 m1).
  Proof.
    abstract lax_comma_t.
  Qed.

  Lemma LaxCosliceCategory_LeftIdentity : forall (a b : LaxCosliceCategory_Object)
    (f : LaxCosliceCategory_Morphism a b),
    LaxCosliceCategory_Compose
    (LaxCosliceCategory_Identity b) f = f.
  Proof.
    abstract lax_comma_t.
  Qed.

  Lemma LaxCosliceCategory_RightIdentity : forall (a b : LaxCosliceCategory_Object)
    (f : LaxCosliceCategory_Morphism a b),
    LaxCosliceCategory_Compose
    f (LaxCosliceCategory_Identity a) = f.
  Proof.
    abstract lax_comma_t.
  Qed.

  Definition LaxCosliceCategory : Category
    := @Build_Category
         LaxCosliceCategory_Object
         LaxCosliceCategory_Morphism
         LaxCosliceCategory_Identity
         LaxCosliceCategory_Compose
         LaxCosliceCategory_Associativity
         LaxCosliceCategory_LeftIdentity
         LaxCosliceCategory_RightIdentity.
End LaxCosliceCategory.

Hint Unfold LaxCosliceCategory_Compose LaxCosliceCategory_Identity : category.
