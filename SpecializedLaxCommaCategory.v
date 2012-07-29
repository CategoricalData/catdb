Require Import ProofIrrelevance.
Require Export Category Functor ProductCategory NaturalTransformation.
Require Import Common DiscreteCategory ComputableCategory DefinitionSimplification FEqualDep.

Set Implicit Arguments.

Local Open Scope category_scope.

Section LaxSliceSpecializedCategory.
  (* [Definition]s are not sort-polymorphic. *)

  Variable I : Type.
  Variable Index2Object : I -> Type.
  Variable Index2Morphism : forall i : I, Index2Object i -> Index2Object i -> Type.
  Variable Index2Cat : forall i : I, SpecializedCategory (@Index2Morphism i).

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Let Cat := ComputableCategory Index2Object Index2Morphism Index2Cat.

  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.


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
  Record LaxSliceSpecializedCategory_Object := { LaxSliceSpecializedCategory_Object_Member :> { X : I & SpecializedFunctor X C } }.

  Let SortPolymorphic_Helper (A T : Type) (Build_T : A -> T) := A.

  Definition LaxSliceSpecializedCategory_ObjectT := Eval hnf in SortPolymorphic_Helper Build_LaxSliceSpecializedCategory_Object.
  Global Identity Coercion LaxSliceSpecializedCategory_Object_Id : LaxSliceSpecializedCategory_ObjectT >-> sigT.
  Definition Build_LaxSliceSpecializedCategory_Object' (mem : LaxSliceSpecializedCategory_ObjectT) := Build_LaxSliceSpecializedCategory_Object mem.
  Global Coercion Build_LaxSliceSpecializedCategory_Object' : LaxSliceSpecializedCategory_ObjectT >-> LaxSliceSpecializedCategory_Object.

  Record LaxSliceSpecializedCategory_Morphism (XG X'G' : LaxSliceSpecializedCategory_ObjectT) := { LaxSliceSpecializedCategory_Morphism_Member :>
    { F : SpecializedFunctor (projT1 XG) (projT1 X'G') &
      SpecializedNaturalTransformation (projT2 XG) (ComposeFunctors (projT2 X'G') F)
    }
  }.

  Definition LaxSliceSpecializedCategory_MorphismT (XG X'G' : LaxSliceSpecializedCategory_ObjectT) :=
    Eval hnf in SortPolymorphic_Helper (@Build_LaxSliceSpecializedCategory_Morphism XG X'G').
  Global Identity Coercion LaxSliceSpecializedCategory_Morphism_Id : LaxSliceSpecializedCategory_MorphismT >-> sigT.
  Definition Build_LaxSliceSpecializedCategory_Morphism' XG X'G' (mem : @LaxSliceSpecializedCategory_MorphismT XG X'G') :=
    @Build_LaxSliceSpecializedCategory_Morphism _ _ mem.
  Global Coercion Build_LaxSliceSpecializedCategory_Morphism' : LaxSliceSpecializedCategory_MorphismT >-> LaxSliceSpecializedCategory_Morphism.

  Global Arguments LaxSliceSpecializedCategory_Object_Member _ : simpl nomatch.
  Global Arguments LaxSliceSpecializedCategory_Morphism_Member _ _ _ : simpl nomatch.
  Global Arguments LaxSliceSpecializedCategory_ObjectT /.
  Global Arguments LaxSliceSpecializedCategory_MorphismT _ _ /.

  Definition LaxSliceSpecializedCategory_Compose' s d d' (Fα : LaxSliceSpecializedCategory_MorphismT d d') (F'α' : LaxSliceSpecializedCategory_MorphismT s d) :
    LaxSliceSpecializedCategory_MorphismT s d'.
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

  Definition LaxSliceSpecializedCategory_Compose'' s d d' (Fα : LaxSliceSpecializedCategory_MorphismT d d') (F'α' : LaxSliceSpecializedCategory_MorphismT s d) :
    LaxSliceSpecializedCategory_MorphismT s d'.
    simpl_definition_by_tac_and_exact (@LaxSliceSpecializedCategory_Compose' s d d' Fα F'α') ltac:(unfold LaxSliceSpecializedCategory_Compose' in *).
  Defined.

  (* Then we clean up a bit with reduction. *)
  Definition LaxSliceSpecializedCategory_Compose s d d' (Fα : LaxSliceSpecializedCategory_MorphismT d d') (F'α' : LaxSliceSpecializedCategory_MorphismT s d) :
    LaxSliceSpecializedCategory_MorphismT s d'
    := Eval cbv beta iota zeta delta [LaxSliceSpecializedCategory_Compose''] in (@LaxSliceSpecializedCategory_Compose'' s d d' Fα F'α').

  Global Arguments LaxSliceSpecializedCategory_Compose _ _ _ _ _ /.

  Definition LaxSliceSpecializedCategory_Identity o : LaxSliceSpecializedCategory_MorphismT o o.
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

  Global Arguments LaxSliceSpecializedCategory_Identity _ /.

  Definition LaxSliceSpecializedCategory : @SpecializedCategory LaxSliceSpecializedCategory_Object LaxSliceSpecializedCategory_Morphism.
    match goal with
      | [ |- @SpecializedCategory ?obj ?mor ] =>
        refine (@Build_SpecializedCategory obj mor
          LaxSliceSpecializedCategory_Identity
          LaxSliceSpecializedCategory_Compose
          _
          _
          _
        )
    end;
    abstract (
      repeat (
        let H := fresh in intro H; destruct H as [ [ ] ]; simpl in * |-
      );
      unfold LaxSliceSpecializedCategory_Object_Member, LaxSliceSpecializedCategory_Morphism_Member, Build_LaxSliceSpecializedCategory_Morphism',
        projT1, projT2;
        try unfold LaxSliceSpecializedCategory_Compose at 1; try (symmetry; unfold LaxSliceSpecializedCategory_Compose at 1);
          try apply f_equal (* slow; ~ 3s / goal *);
            simpl_eq (* slow; ~ 4s / goal *);
            nt_eq (* slow; ~ 2s / goal *); clear_refl_eq;
            repeat rewrite ComposeFunctorsAssociativity;
              repeat rewrite LeftIdentityFunctor; repeat rewrite RightIdentityFunctor;
                repeat rewrite FIdentityOf;
                  repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                    repeat rewrite Associativity;
                      try reflexivity
    ).
  Defined.
End LaxSliceSpecializedCategory.

Hint Unfold LaxSliceSpecializedCategory_Compose LaxSliceSpecializedCategory_Identity.
Hint Constructors LaxSliceSpecializedCategory_Morphism LaxSliceSpecializedCategory_Object.

Section LaxCosliceSpecializedCategory.
  (* [Definition]s are not sort-polymorphic. *)

  Variable I : Type.
  Variable Index2Object : I -> Type.
  Variable Index2Morphism : forall i : I, Index2Object i -> Index2Object i -> Type.
  Variable Index2Cat : forall i : I, SpecializedCategory (@Index2Morphism i).

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Let Cat := ComputableCategory Index2Object Index2Morphism Index2Cat.

  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Record LaxCosliceSpecializedCategory_Object := { LaxCosliceSpecializedCategory_Object_Member :> { X : I & SpecializedFunctor C X } }.

  Let SortPolymorphic_Helper (A T : Type) (Build_T : A -> T) := A.

  Definition LaxCosliceSpecializedCategory_ObjectT := Eval hnf in SortPolymorphic_Helper Build_LaxCosliceSpecializedCategory_Object.
  Global Identity Coercion LaxCosliceSpecializedCategory_Object_Id : LaxCosliceSpecializedCategory_ObjectT >-> sigT.
  Definition Build_LaxCosliceSpecializedCategory_Object' (mem : LaxCosliceSpecializedCategory_ObjectT) := Build_LaxCosliceSpecializedCategory_Object mem.
  Global Coercion Build_LaxCosliceSpecializedCategory_Object' : LaxCosliceSpecializedCategory_ObjectT >-> LaxCosliceSpecializedCategory_Object.

  Record LaxCosliceSpecializedCategory_Morphism (XG X'G' : LaxCosliceSpecializedCategory_ObjectT) := { LaxCosliceSpecializedCategory_Morphism_Member :>
    { F : SpecializedFunctor (projT1 XG) (projT1 X'G') &
      SpecializedNaturalTransformation (ComposeFunctors F (projT2 XG)) (projT2 X'G')
    }
  }.

  Definition LaxCosliceSpecializedCategory_MorphismT (XG X'G' : LaxCosliceSpecializedCategory_ObjectT) :=
    Eval hnf in SortPolymorphic_Helper (@Build_LaxCosliceSpecializedCategory_Morphism XG X'G').
  Global Identity Coercion LaxCosliceSpecializedCategory_Morphism_Id : LaxCosliceSpecializedCategory_MorphismT >-> sigT.
  Definition Build_LaxCosliceSpecializedCategory_Morphism' XG X'G' (mem : @LaxCosliceSpecializedCategory_MorphismT XG X'G') :=
    @Build_LaxCosliceSpecializedCategory_Morphism _ _ mem.
  Global Coercion Build_LaxCosliceSpecializedCategory_Morphism' : LaxCosliceSpecializedCategory_MorphismT >-> LaxCosliceSpecializedCategory_Morphism.

  Global Arguments LaxCosliceSpecializedCategory_Object_Member _ : simpl nomatch.
  Global Arguments LaxCosliceSpecializedCategory_Morphism_Member _ _ _ : simpl nomatch.
  Global Arguments LaxCosliceSpecializedCategory_ObjectT /.
  Global Arguments LaxCosliceSpecializedCategory_MorphismT _ _ /.

  Definition LaxCosliceSpecializedCategory_Compose' s d d' (Fα : LaxCosliceSpecializedCategory_MorphismT d d') (F'α' : LaxCosliceSpecializedCategory_MorphismT s d) :
    LaxCosliceSpecializedCategory_MorphismT s d'.
    Transparent Object Morphism.
    exists (ComposeFunctors (projT1 Fα) (projT1 F'α')).
    repeat match goal with
             | [ H : _ |- _ ] => unique_pose_with_body (projT1 H)
             | [ H : _ |- _ ] => unique_pose_with_body (projT2 H)
           end; simpl in *.
    repeat match goal with
             | [ x : _, T : _ |- _ ] => unique_pose (NTComposeF (IdentityNaturalTransformation x) T)
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

  Definition LaxCosliceSpecializedCategory_Compose'' s d d' (Fα : LaxCosliceSpecializedCategory_MorphismT d d') (F'α' : LaxCosliceSpecializedCategory_MorphismT s d) :
    LaxCosliceSpecializedCategory_MorphismT s d'.
    simpl_definition_by_tac_and_exact (@LaxCosliceSpecializedCategory_Compose' s d d' Fα F'α') ltac:(unfold LaxCosliceSpecializedCategory_Compose' in *).
  Defined.

  (* Then we clean up a bit with reduction. *)
  Definition LaxCosliceSpecializedCategory_Compose s d d' (Fα : LaxCosliceSpecializedCategory_MorphismT d d') (F'α' : LaxCosliceSpecializedCategory_MorphismT s d) :
    LaxCosliceSpecializedCategory_MorphismT s d'
    := Eval cbv beta iota zeta delta [LaxCosliceSpecializedCategory_Compose''] in (@LaxCosliceSpecializedCategory_Compose'' s d d' Fα F'α').

  Global Arguments LaxCosliceSpecializedCategory_Compose _ _ _ _ _ /.

  Definition LaxCosliceSpecializedCategory_Identity o : LaxCosliceSpecializedCategory_MorphismT o o.
    exists (IdentityFunctor _).
    eapply (NTComposeT _ (IdentityNaturalTransformation _)).
    Grab Existential Variables.
    match goal with
      | [ C : _ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun x => Identity (C := projT1 C) _)
          _
        )
    end.
    abstract (
      intros; simpl; present_spnt;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
          reflexivity
    ).
  Defined.

  Global Arguments LaxCosliceSpecializedCategory_Identity _ /.

  Definition LaxCosliceSpecializedCategory : @SpecializedCategory LaxCosliceSpecializedCategory_Object LaxCosliceSpecializedCategory_Morphism.
    match goal with
      | [ |- @SpecializedCategory ?obj ?mor ] =>
        refine (@Build_SpecializedCategory obj mor
          LaxCosliceSpecializedCategory_Identity
          LaxCosliceSpecializedCategory_Compose
          _
          _
          _
        )
    end;
    abstract (
      repeat (
        let H := fresh in intro H; destruct H as [ [ ] ]; simpl in * |-
      );
      unfold LaxCosliceSpecializedCategory_Object_Member, LaxCosliceSpecializedCategory_Morphism_Member, Build_LaxCosliceSpecializedCategory_Morphism',
        projT1, projT2;
        try unfold LaxCosliceSpecializedCategory_Compose at 1; try (symmetry; unfold LaxCosliceSpecializedCategory_Compose at 1);
          try apply f_equal (* slow; ~ 3s / goal *);
            simpl_eq (* slow; ~ 4s / goal *);
            nt_eq (* slow; ~ 2s / goal *); clear_refl_eq;
            repeat rewrite ComposeFunctorsAssociativity;
              repeat rewrite LeftIdentityFunctor; repeat rewrite RightIdentityFunctor;
                repeat rewrite FCompositionOf;
                  repeat rewrite FIdentityOf;
                    repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                      repeat rewrite Associativity;
                        try reflexivity
    ).
  Defined.
End LaxCosliceSpecializedCategory.

Hint Unfold LaxCosliceSpecializedCategory_Compose LaxCosliceSpecializedCategory_Identity.
Hint Constructors LaxCosliceSpecializedCategory_Morphism LaxCosliceSpecializedCategory_Object.
