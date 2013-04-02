Require Import ProofIrrelevance.
Require Export Category Functor ProductCategory NaturalTransformation.
Require Import Common DecidableDiscreteCategory ComputableCategory DefinitionSimplification FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope category_scope.

Section LaxSliceSpecializedCategory.
  (* [Definition]s are not sort-polymorphic. *)

  Variable I : Type.
  Variable Index2Object : I -> Type.
  Variable Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i).

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Let Cat := ComputableCategory Index2Object Index2Cat.

  Context `(C : @SpecializedCategory objC).

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
  (* use a pair, so that it's easily interchangable with [SliceSpecializedCategory] *)
  Record LaxSliceSpecializedCategory_Object := { LaxSliceSpecializedCategory_Object_Member :> { X : I * unit & SpecializedFunctor (fst X) C } }.

  Let SortPolymorphic_Helper (A T : Type) (Build_T : A -> T) := A.

  Definition LaxSliceSpecializedCategory_ObjectT := Eval hnf in SortPolymorphic_Helper Build_LaxSliceSpecializedCategory_Object.
  Global Identity Coercion LaxSliceSpecializedCategory_Object_Id : LaxSliceSpecializedCategory_ObjectT >-> sigT.
  Definition Build_LaxSliceSpecializedCategory_Object' (mem : LaxSliceSpecializedCategory_ObjectT) := Build_LaxSliceSpecializedCategory_Object mem.
  Global Coercion Build_LaxSliceSpecializedCategory_Object' : LaxSliceSpecializedCategory_ObjectT >-> LaxSliceSpecializedCategory_Object.

  Record LaxSliceSpecializedCategory_Morphism (XG X'G' : LaxSliceSpecializedCategory_ObjectT) := { LaxSliceSpecializedCategory_Morphism_Member :>
    { F : SpecializedFunctor (fst (projT1 XG)) (fst (projT1 X'G')) * unit &
      SpecializedNaturalTransformation (projT2 XG) (ComposeFunctors (projT2 X'G') (fst F))
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
      | [ C : _ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
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
    exists (IdentityFunctor _, tt).
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
        intros; simpl;
        autorewrite with morphism;
        reflexivity
      ).
  Defined.

  Global Arguments LaxSliceSpecializedCategory_Identity _ /.

  Local Ltac lax_slice_t :=
    repeat (
      let H := fresh in intro H; destruct H; simpl in * |-
    );
    unfold projT1, projT2;
      try unfold LaxSliceSpecializedCategory_Compose at 1; try (symmetry; unfold LaxSliceSpecializedCategory_Compose at 1);
        try apply f_equal (* slow; ~ 3s / goal *);
          simpl_eq (* slow; ~ 4s / goal *);
          nt_eq (* slow; ~ 2s / goal *); clear_refl_eq;
          repeat rewrite ComposeFunctorsAssociativity;
            repeat rewrite LeftIdentityFunctor; repeat rewrite RightIdentityFunctor;
              repeat rewrite FIdentityOf;
                repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                  repeat rewrite Associativity;
                    try reflexivity;
                    subst;
                    trivial.

  Lemma LaxSliceSpecializedCategory_Associativity : forall (o1 o2 o3 o4 : LaxSliceSpecializedCategory_ObjectT)
    (m1 : LaxSliceSpecializedCategory_MorphismT o1 o2)
    (m2 : LaxSliceSpecializedCategory_MorphismT o2 o3)
    (m3 : LaxSliceSpecializedCategory_MorphismT o3 o4),
    LaxSliceSpecializedCategory_Compose
    (LaxSliceSpecializedCategory_Compose m3 m2) m1 =
    LaxSliceSpecializedCategory_Compose m3
    (LaxSliceSpecializedCategory_Compose m2 m1).
  Proof.
    abstract lax_slice_t.
  Qed.

  Lemma LaxSliceSpecializedCategory_LeftIdentity : forall (a b : LaxSliceSpecializedCategory_ObjectT)
    (f : LaxSliceSpecializedCategory_MorphismT a b),
    LaxSliceSpecializedCategory_Compose
    (LaxSliceSpecializedCategory_Identity b) f = f.
  Proof.
    abstract lax_slice_t.
  Qed.

  Lemma LaxSliceSpecializedCategory_RightIdentity : forall (a b : LaxSliceSpecializedCategory_ObjectT)
    (f : LaxSliceSpecializedCategory_MorphismT a b),
    LaxSliceSpecializedCategory_Compose
    f (LaxSliceSpecializedCategory_Identity a) = f.
  Proof.
    abstract lax_slice_t.
  Qed.

  Definition LaxSliceSpecializedCategory : @SpecializedCategory LaxSliceSpecializedCategory_Object.
    match goal with
      | [ |- @SpecializedCategory ?obj ] =>
        refine (@Build_SpecializedCategory obj
          LaxSliceSpecializedCategory_Morphism
          LaxSliceSpecializedCategory_Identity
          LaxSliceSpecializedCategory_Compose
          _
          _
          _
        )
    end;
    abstract (
      repeat (
        let H := fresh in intro H; destruct H as [ ]; simpl in * |-
      );
      unfold LaxSliceSpecializedCategory_Morphism_Member, LaxSliceSpecializedCategory_Object_Member,
        Build_LaxSliceSpecializedCategory_Morphism', Build_LaxSliceSpecializedCategory_Object';
        apply f_equal;
          apply LaxSliceSpecializedCategory_Associativity ||
            apply LaxSliceSpecializedCategory_LeftIdentity ||
              apply LaxSliceSpecializedCategory_RightIdentity
    ).
  Defined.
End LaxSliceSpecializedCategory.

Hint Unfold LaxSliceSpecializedCategory_Compose LaxSliceSpecializedCategory_Identity : category.
Hint Constructors LaxSliceSpecializedCategory_Morphism LaxSliceSpecializedCategory_Object : category.

Section LaxCosliceSpecializedCategory.
  (* [Definition]s are not sort-polymorphic. *)

  Variable I : Type.
  Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i)).

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Let Cat := ComputableCategory Index2Object Index2Cat.

  Context `(C : @SpecializedCategory objC).

  Record LaxCosliceSpecializedCategory_Object := { LaxCosliceSpecializedCategory_Object_Member :> { X : unit * I & SpecializedFunctor (snd X) C } }.

  Let SortPolymorphic_Helper (A T : Type) (Build_T : A -> T) := A.

  Definition LaxCosliceSpecializedCategory_ObjectT := Eval hnf in SortPolymorphic_Helper Build_LaxCosliceSpecializedCategory_Object.
  Global Identity Coercion LaxCosliceSpecializedCategory_Object_Id : LaxCosliceSpecializedCategory_ObjectT >-> sigT.
  Definition Build_LaxCosliceSpecializedCategory_Object' (mem : LaxCosliceSpecializedCategory_ObjectT) := Build_LaxCosliceSpecializedCategory_Object mem.
  Global Coercion Build_LaxCosliceSpecializedCategory_Object' : LaxCosliceSpecializedCategory_ObjectT >-> LaxCosliceSpecializedCategory_Object.

  Record LaxCosliceSpecializedCategory_Morphism (XG X'G' : LaxCosliceSpecializedCategory_ObjectT) := { LaxCosliceSpecializedCategory_Morphism_Member :>
    { F : unit * SpecializedFunctor (snd (projT1 X'G')) (snd (projT1 XG)) &
      SpecializedNaturalTransformation (ComposeFunctors (projT2 XG) (snd F)) (projT2 X'G')
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
      | [ C : _ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
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
    exists (tt, IdentityFunctor _).
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
      intros; simpl;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
          reflexivity
    ).
  Defined.

  Global Arguments LaxCosliceSpecializedCategory_Identity _ /.

  Local Ltac lax_coslice_t :=
    repeat (
      let H := fresh in intro H; destruct H; simpl in * |-
    );
    unfold projT1, projT2;
      try unfold LaxCosliceSpecializedCategory_Compose at 1; try (symmetry; unfold LaxCosliceSpecializedCategory_Compose at 1);
        try apply f_equal (* slow; ~ 3s / goal *);
          simpl_eq (* slow; ~ 4s / goal *);
          nt_eq (* slow; ~ 2s / goal *); clear_refl_eq;
          repeat rewrite ComposeFunctorsAssociativity;
            repeat rewrite LeftIdentityFunctor; repeat rewrite RightIdentityFunctor;
              repeat rewrite FIdentityOf;
                repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                  repeat rewrite Associativity;
                    try reflexivity;
                      trivial.

  Lemma LaxCosliceSpecializedCategory_Associativity : forall (o1 o2 o3 o4 : LaxCosliceSpecializedCategory_ObjectT)
    (m1 : LaxCosliceSpecializedCategory_MorphismT o1 o2)
    (m2 : LaxCosliceSpecializedCategory_MorphismT o2 o3)
    (m3 : LaxCosliceSpecializedCategory_MorphismT o3 o4),
    LaxCosliceSpecializedCategory_Compose
    (LaxCosliceSpecializedCategory_Compose m3 m2) m1 =
    LaxCosliceSpecializedCategory_Compose m3
    (LaxCosliceSpecializedCategory_Compose m2 m1).
  Proof.
    abstract lax_coslice_t.
  Qed.

  Lemma LaxCosliceSpecializedCategory_LeftIdentity : forall (a b : LaxCosliceSpecializedCategory_ObjectT)
    (f : LaxCosliceSpecializedCategory_MorphismT a b),
    LaxCosliceSpecializedCategory_Compose
    (LaxCosliceSpecializedCategory_Identity b) f = f.
  Proof.
    abstract lax_coslice_t.
  Qed.

  Lemma LaxCosliceSpecializedCategory_RightIdentity : forall (a b : LaxCosliceSpecializedCategory_ObjectT)
    (f : LaxCosliceSpecializedCategory_MorphismT a b),
    LaxCosliceSpecializedCategory_Compose
    f (LaxCosliceSpecializedCategory_Identity a) = f.
  Proof.
    abstract lax_coslice_t.
  Qed.

  Definition LaxCosliceSpecializedCategory : @SpecializedCategory LaxCosliceSpecializedCategory_Object.
    match goal with
      | [ |- @SpecializedCategory ?obj ] =>
        refine (@Build_SpecializedCategory obj
          LaxCosliceSpecializedCategory_Morphism
          LaxCosliceSpecializedCategory_Identity
          LaxCosliceSpecializedCategory_Compose
          _
          _
          _
        )
    end;
    abstract (
      repeat (
        let H := fresh in intro H; destruct H as [ ]; simpl in * |-
      );
      unfold LaxCosliceSpecializedCategory_Morphism_Member, LaxCosliceSpecializedCategory_Object_Member,
        Build_LaxCosliceSpecializedCategory_Morphism', Build_LaxCosliceSpecializedCategory_Object';
        apply f_equal;
          apply LaxCosliceSpecializedCategory_Associativity ||
            apply LaxCosliceSpecializedCategory_LeftIdentity ||
              apply LaxCosliceSpecializedCategory_RightIdentity
    ).
  Defined.
End LaxCosliceSpecializedCategory.

Hint Unfold LaxCosliceSpecializedCategory_Compose LaxCosliceSpecializedCategory_Identity : category.
Hint Constructors LaxCosliceSpecializedCategory_Morphism LaxCosliceSpecializedCategory_Object : category.
