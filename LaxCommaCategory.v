Require Import ProofIrrelevance.
Require Export Category Functor ProductCategory NaturalTransformation.
Require Import Common DiscreteCategory ComputableCategory DefinitionSimplification FEqualDep SpecializedLaxCommaCategory.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope category_scope.

Local Ltac fold_functor :=
  change (@SpecializedFunctor) with (fun objC (C : @SpecializedCategory objC) objD (D : @SpecializedCategory objD) => @Functor C D) in *;
    change (@SpecializedNaturalTransformation) with (fun objC (C : @SpecializedCategory objC) objD (D : @SpecializedCategory objD)
      (F G : SpecializedFunctor C D)
      => @NaturalTransformation C D F G) in *.

Section LaxSliceCategory.
  (* [Definition]s are not sort-polymorphic. *)

  Variable I : Type.
  Variable Index2Cat : I -> Category.

  Local Coercion Index2Cat : I >-> Category.

  Let Cat := ComputableCategory _ Index2Cat.

  Variable C : Category.

  Hint Resolve Associativity RightIdentity LeftIdentity.

  (* Pull the definitions from SpecializedLaxCommaCategory.v,
     removing [Specialized], so that we have smaller definitions.
     *)

  Let LaxSliceCategory_Object' := Eval hnf in LaxSliceSpecializedCategory_ObjectT _ Index2Cat C.
  Let LaxSliceCategory_Object'' : Type.
    simpl_definition_by_tac_and_exact LaxSliceCategory_Object' ltac:(simpl in *; fold_functor; simpl in *).
  Defined.
  Definition LaxSliceCategory_Object := Eval hnf in LaxSliceCategory_Object''.

  Let LaxSliceCategory_Morphism' (XG X'G' : LaxSliceCategory_Object) := Eval hnf in @LaxSliceSpecializedCategory_MorphismT _ _ Index2Cat _ C XG X'G'.
  Let LaxSliceCategory_Morphism'' (XG X'G' : LaxSliceCategory_Object) : Type.
    simpl_definition_by_tac_and_exact (LaxSliceCategory_Morphism' XG X'G') ltac:(subst_body; cbv beta in *; fold_functor; cbv beta in *; present_spnt).
  Defined.
  Definition LaxSliceCategory_Morphism (XG X'G' : LaxSliceCategory_Object) := Eval hnf in LaxSliceCategory_Morphism'' XG X'G'.

  Let LaxSliceCategory_Compose' s d d' Fα F'α'
    := Eval hnf in @LaxSliceSpecializedCategory_Compose _ _ Index2Cat _ C s d d' Fα F'α'.
  Let LaxSliceCategory_Compose'' s d d' (Fα : LaxSliceCategory_Morphism d d') (F'α' : LaxSliceCategory_Morphism s d) :
    LaxSliceCategory_Morphism s d'.
    simpl_definition_by_tac_and_exact (@LaxSliceCategory_Compose' s d d' Fα F'α') ltac:(subst_body; cbv beta in *; fold_functor; cbv beta in *; present_spnt).
  Defined.
  Definition LaxSliceCategory_Compose s d d' (Fα : LaxSliceCategory_Morphism d d') (F'α' : LaxSliceCategory_Morphism s d) :
    LaxSliceCategory_Morphism s d'
    := Eval hnf in @LaxSliceCategory_Compose'' s d d' Fα F'α'.

  Let LaxSliceCategory_Identity' o := Eval hnf in @LaxSliceSpecializedCategory_Identity _ _ Index2Cat _ C o.
  Let LaxSliceCategory_Identity'' (o : LaxSliceCategory_Object) : LaxSliceCategory_Morphism o o.
    simpl_definition_by_tac_and_exact (@LaxSliceCategory_Identity' o) ltac:(subst_body; cbv beta in *; fold_functor; cbv beta in *; present_spnt).
  Defined.
  Definition LaxSliceCategory_Identity (o : LaxSliceCategory_Object) : LaxSliceCategory_Morphism o o
    := Eval hnf in @LaxSliceCategory_Identity'' o.

  Global Arguments LaxSliceCategory_Compose _ _ _ _ _ /.
  Global Arguments LaxSliceCategory_Identity _ /.

  Lemma LaxSliceCategory_Associativity o1 o2 o3 o4 (m1 : LaxSliceCategory_Morphism o1 o2) (m2 : LaxSliceCategory_Morphism o2 o3) (m3 : LaxSliceCategory_Morphism o3 o4) :
    LaxSliceCategory_Compose (LaxSliceCategory_Compose m3 m2) m1 = LaxSliceCategory_Compose m3 (LaxSliceCategory_Compose m2 m1).
    abstract apply (@LaxSliceSpecializedCategory_Associativity _ _ Index2Cat _ C o1 o2 o3 o4 m1 m2 m3).
  Qed.

  Lemma LaxSliceCategory_LeftIdentity (a b : LaxSliceCategory_Object) (f : LaxSliceCategory_Morphism a b) :
    LaxSliceCategory_Compose (LaxSliceCategory_Identity b) f = f.
  Proof.
    abstract apply (@LaxSliceSpecializedCategory_LeftIdentity _ _ Index2Cat _ C a b f).
  Qed.

  Lemma LaxSliceCategory_RightIdentity (a b : LaxSliceCategory_Object) (f : LaxSliceCategory_Morphism a b) :
    LaxSliceCategory_Compose f (LaxSliceCategory_Identity a) = f.
  Proof.
    abstract apply (@LaxSliceSpecializedCategory_RightIdentity _ _ Index2Cat _ C a b f).
  Qed.

  Definition LaxSliceCategory : Category.
    refine (@Build_SpecializedCategory LaxSliceCategory_Object LaxSliceCategory_Morphism
      LaxSliceCategory_Identity
      LaxSliceCategory_Compose
      _ _ _
    );
    subst_body;
    abstract (apply LaxSliceCategory_Associativity || apply LaxSliceCategory_LeftIdentity || apply LaxSliceCategory_RightIdentity).
  Defined.
End LaxSliceCategory.

Hint Unfold LaxSliceCategory_Compose LaxSliceCategory_Identity.

Section LaxCosliceCategory.
  (* [Definition]s are not sort-polymorphic. *)

  Variable I : Type.
  Variable Index2Cat : I -> Category.

  Local Coercion Index2Cat : I >-> Category.

  Let Cat := ComputableCategory _ Index2Cat.

  Variable C : Category.

  Let LaxCosliceCategory_Object' := Eval hnf in LaxCosliceSpecializedCategory_ObjectT Index2Cat C.
  Let LaxCosliceCategory_Object'' : Type.
    simpl_definition_by_tac_and_exact LaxCosliceCategory_Object' ltac:(simpl in *; fold_functor; simpl in *).
  Defined.
  Definition LaxCosliceCategory_Object := Eval hnf in LaxCosliceCategory_Object''.

  Let LaxCosliceCategory_Morphism' (XG X'G' : LaxCosliceCategory_Object) := Eval hnf in @LaxCosliceSpecializedCategory_MorphismT _ _ Index2Cat _ C XG X'G'.
  Let LaxCosliceCategory_Morphism'' (XG X'G' : LaxCosliceCategory_Object) : Type.
    simpl_definition_by_tac_and_exact (LaxCosliceCategory_Morphism' XG X'G') ltac:(subst_body; cbv beta in *; fold_functor; cbv beta in *; present_spnt).
  Defined.
  Definition LaxCosliceCategory_Morphism (XG X'G' : LaxCosliceCategory_Object) := Eval hnf in LaxCosliceCategory_Morphism'' XG X'G'.

  Let LaxCosliceCategory_Compose' s d d' Fα F'α'
    := Eval hnf in @LaxCosliceSpecializedCategory_Compose _ _ Index2Cat _ C s d d' Fα F'α'.
  Let LaxCosliceCategory_Compose'' s d d' (Fα : LaxCosliceCategory_Morphism d d') (F'α' : LaxCosliceCategory_Morphism s d) :
    LaxCosliceCategory_Morphism s d'.
    simpl_definition_by_tac_and_exact (@LaxCosliceCategory_Compose' s d d' Fα F'α') ltac:(subst_body; cbv beta in *; fold_functor; cbv beta in *; present_spnt).
  Defined.
  Definition LaxCosliceCategory_Compose s d d' (Fα : LaxCosliceCategory_Morphism d d') (F'α' : LaxCosliceCategory_Morphism s d) :
    LaxCosliceCategory_Morphism s d'
    := Eval hnf in @LaxCosliceCategory_Compose'' s d d' Fα F'α'.

  Let LaxCosliceCategory_Identity' o := Eval hnf in @LaxCosliceSpecializedCategory_Identity _ _ Index2Cat _ C o.
  Let LaxCosliceCategory_Identity'' (o : LaxCosliceCategory_Object) : LaxCosliceCategory_Morphism o o.
    simpl_definition_by_tac_and_exact (@LaxCosliceCategory_Identity' o) ltac:(subst_body; cbv beta in *; fold_functor; cbv beta in *; present_spnt).
  Defined.
  Definition LaxCosliceCategory_Identity (o : LaxCosliceCategory_Object) : LaxCosliceCategory_Morphism o o
    := Eval hnf in @LaxCosliceCategory_Identity'' o.

  Global Arguments LaxCosliceCategory_Compose _ _ _ _ _ /.
  Global Arguments LaxCosliceCategory_Identity _ /.

  Lemma LaxCosliceCategory_Associativity o1 o2 o3 o4 (m1 : LaxCosliceCategory_Morphism o1 o2) (m2 : LaxCosliceCategory_Morphism o2 o3) (m3 : LaxCosliceCategory_Morphism o3 o4) :
    LaxCosliceCategory_Compose (LaxCosliceCategory_Compose m3 m2) m1 = LaxCosliceCategory_Compose m3 (LaxCosliceCategory_Compose m2 m1).
    abstract apply (@LaxCosliceSpecializedCategory_Associativity _ _ Index2Cat _ C o1 o2 o3 o4 m1 m2 m3).
  Qed.

  Lemma LaxCosliceCategory_LeftIdentity (a b : LaxCosliceCategory_Object) (f : LaxCosliceCategory_Morphism a b) :
    LaxCosliceCategory_Compose (LaxCosliceCategory_Identity b) f = f.
  Proof.
    abstract apply (@LaxCosliceSpecializedCategory_LeftIdentity _ _ Index2Cat _ C a b f).
  Qed.

  Lemma LaxCosliceCategory_RightIdentity (a b : LaxCosliceCategory_Object) (f : LaxCosliceCategory_Morphism a b) :
    LaxCosliceCategory_Compose f (LaxCosliceCategory_Identity a) = f.
  Proof.
    abstract apply (@LaxCosliceSpecializedCategory_RightIdentity _ _ Index2Cat _ C a b f).
  Qed.

  Definition LaxCosliceCategory : Category.
    refine (@Build_SpecializedCategory LaxCosliceCategory_Object LaxCosliceCategory_Morphism
      LaxCosliceCategory_Identity
      LaxCosliceCategory_Compose
      _ _ _
    );
    subst_body;
    abstract (apply LaxCosliceCategory_Associativity || apply LaxCosliceCategory_LeftIdentity || apply LaxCosliceCategory_RightIdentity).
  Defined.
End LaxCosliceCategory.

Hint Unfold LaxCosliceCategory_Compose LaxCosliceCategory_Identity.
