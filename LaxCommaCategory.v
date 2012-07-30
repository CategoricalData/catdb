Require Import ProofIrrelevance.
Require Export Category Functor ProductCategory NaturalTransformation.
Require Import Common DiscreteCategory ComputableCategory DefinitionSimplification FEqualDep.

Set Implicit Arguments.

Local Open Scope category_scope.

Section LaxSliceCategory.
  (* [Definition]s are not sort-polymorphic. *)

  Variable I : Type.
  Variable Index2Cat : I -> Category.

  Local Coercion Index2Cat : I >-> Category.

  Let Cat := ComputableCategory _ _ Index2Cat.

  Variable C : Category.


  Hint Resolve Associativity RightIdentity LeftIdentity.

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
  Definition LaxSliceCategory_Object := { X : I & Functor X C }.
  Definition LaxSliceCategory_Morphism (XG X'G' : LaxSliceCategory_Object) :=
    { F : Functor (projT1 XG) (projT1 X'G') &
      NaturalTransformation (projT2 XG) (ComposeFunctors (projT2 X'G') F)
    }.

  Definition LaxSliceCategory_Compose' s d d' (Fα : LaxSliceCategory_Morphism d d') (F'α' : LaxSliceCategory_Morphism s d) :
    LaxSliceCategory_Morphism s d'.
    Transparent Object Morphism.
    exists (ComposeFunctors (projT1 Fα) (projT1 F'α')).
    repeat match goal with
             | [ H : _ |- _ ] => unique_pose_with_body (projT1 H)
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
      | [ C : _ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
      subst_body;
      intros; simpl; present_spnt;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
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

  Global Arguments LaxSliceCategory_Compose _ _ _ _ _ /.

  Definition LaxSliceCategory_Identity o : LaxSliceCategory_Morphism o o.
    exists (IdentityFunctor _).
    eapply (NTComposeT _ (IdentityNaturalTransformation _)).
    Grab Existential Variables.
    match goal with
      | [ C : _ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
      intros; simpl; present_spnt;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
          reflexivity
    ).
  Defined.

  Global Arguments LaxSliceCategory_Identity _ /.

  Definition LaxSliceCategory : Category.
    refine (@Build_SpecializedCategory LaxSliceCategory_Object LaxSliceCategory_Morphism
      LaxSliceCategory_Identity
      LaxSliceCategory_Compose
      _
      _
      _
    );
    abstract (
      repeat (let H := fresh in intro H; destruct H; simpl in * |- );
        simpl_eq;
        nt_eq (* slow; ~ 7s / goal *); clear_refl_eq;
        repeat rewrite ComposeFunctorsAssociativity;
          repeat rewrite LeftIdentityFunctor; repeat rewrite RightIdentityFunctor;
            repeat rewrite FIdentityOf;
              repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                repeat rewrite Associativity;
                  try reflexivity
    ).
  Defined.
End LaxSliceCategory.

Hint Unfold LaxSliceCategory_Compose LaxSliceCategory_Identity.

Section LaxCosliceCategory.
  (* [Definition]s are not sort-polymorphic. *)

  Variable I : Type.
  Variable Index2Cat : I -> Category.

  Local Coercion Index2Cat : I >-> Category.

  Let Cat := ComputableCategory _ _ Index2Cat.

  Variable C : Category.

  Definition LaxCosliceCategory_Object := { X : I & Functor X C }.
  Definition LaxCosliceCategory_Morphism (XG X'G' : LaxCosliceCategory_Object) :=
    { F : Functor (projT1 X'G') (projT1 XG) &
      NaturalTransformation (ComposeFunctors (projT2 XG) F) (projT2 X'G')
    }.

  Global Arguments LaxCosliceCategory_Object /.
  Global Arguments LaxCosliceCategory_Morphism _ _ /.

  Definition LaxCosliceCategory_Compose' s d d' (Fα : LaxCosliceCategory_Morphism d d') (F'α' : LaxCosliceCategory_Morphism s d) :
    LaxCosliceCategory_Morphism s d'.
    Transparent Object Morphism.
    exists (ComposeFunctors (projT1 F'α') (projT1 Fα)).
    repeat match goal with
             | [ H : _ |- _ ] => unique_pose_with_body (projT1 H)
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
      | [ C : _ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
      subst_body;
      intros; simpl; present_spnt;
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
    exists (IdentityFunctor _).
    eapply (NTComposeT _ (IdentityNaturalTransformation _)).
    Grab Existential Variables.
    match goal with
      | [ C : _ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
      intros; simpl; present_spnt;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
          reflexivity
    ).
  Defined.

  Global Arguments LaxCosliceCategory_Identity _ /.

  Definition LaxCosliceCategory : Category.
  refine (@Build_SpecializedCategory LaxCosliceCategory_Object LaxCosliceCategory_Morphism
    LaxCosliceCategory_Identity
    LaxCosliceCategory_Compose
    _
    _
    _
  );
  abstract (
    repeat (let H := fresh in intro H; destruct H; simpl in * |- );
      simpl_eq;
      nt_eq (* slow; ~ 7s / goal *); clear_refl_eq;
      repeat rewrite ComposeFunctorsAssociativity;
        repeat rewrite LeftIdentityFunctor; repeat rewrite RightIdentityFunctor;
          repeat rewrite FIdentityOf;
            repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
              repeat rewrite Associativity;
                try reflexivity
  ).
  Defined.
End LaxCosliceCategory.

Hint Unfold LaxCosliceCategory_Compose LaxCosliceCategory_Identity.
