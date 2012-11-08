Require Import ProofIrrelevance.
Require Export Category SpecializedCategory Functor ProductCategory.
Require Import Common Notations InitialTerminalCategory SpecializedCommaCategory DefinitionSimplification.

Set Implicit Arguments.

Local Open Scope category_scope.

Local Ltac fold_functor :=
  change CObject with (fun C => @Object (CObject C) C) in *;
    present_spcategory;
    change (@SpecializedFunctor) with (fun objC (C : @SpecializedCategory objC) objD (D : @SpecializedCategory objD) => @Functor C D) in *.

Section CommaCategory.
  (* [Definition]s are not sort-polymorphic, and it's too slow to not use
     [Definition]s, so we might as well use [Category]s rather than [SpecializedCategory]s. *)
  Variable A B C : Category.
  Variable S : Functor A C.
  Variable T : Functor B C.

  (** Quoting Wikipedia:
     Suppose that [A], [B], and [C] are categories, and [S] and [T]
     are functors
     [S : A -> C <- B : T]
     We can form the comma category [(S ↓ T)] as follows:
     (o) The objects are all triples [(α, β, f)] with [α] an object in
         [A], [β] an object in [B], and [f : S α -> T β] a morphism in
         [C].
     (o) The morphisms from [(α, β, f)] to [(α', β', f')] are all
         pairs [(g, h)] where [g : α -> α'] and [h : β -> β'] are
         morphisms in [A] and [B] respectively, such that the
         following diagram commutes:
         [[
               S g
          S α -----> S α'
           |          |
         f |          | f'
           |          |
           V          V
          T β -----> T β'
               T h
         ]]
     Morphisms are composed by taking [(g, h) ○ (g', h')] to be
     [(g ○ g', h ○ h')], whenever the latter expression is defined.
     The identity morphism on an object [(α, β, f)] is [(Identity α, Identity β)].
     *)

  (* By definining all the parts separately, we can make the [Prop]
     Parts of the definition opaque via [abstract].  This speeds things
     up significantly.  We unfold the definitions at the very end with
     [Eval]. *)
  (* stupid lack of sort-polymorphism in definitions... *)
  Let CommaCategory_Object' := Eval hnf in CommaSpecializedCategory_ObjectT S T.
  Let CommaCategory_Object'' : Type.
    simpl_definition_by_tac_and_exact CommaCategory_Object' ltac:(simpl in *; fold_functor).
  Defined.
  Definition CommaCategory_Object := Eval cbv beta delta [CommaCategory_Object''] in CommaCategory_Object''.

  Let CommaCategory_Morphism' (XG X'G' : CommaCategory_Object) := Eval hnf in CommaSpecializedCategory_MorphismT (S := S) (T := T) XG X'G'.
  Let CommaCategory_Morphism'' (XG X'G' : CommaCategory_Object) : Type.
    simpl_definition_by_tac_and_exact (CommaCategory_Morphism' XG X'G') ltac:(subst_body; cbv beta in *; fold_functor; cbv beta in *; present_spfunctor).
  Defined.
  Definition CommaCategory_Morphism (XG X'G' : CommaCategory_Object) := Eval hnf in CommaCategory_Morphism'' XG X'G'.

  Let CommaCategory_Compose' s d d' Fα F'α'
    := Eval hnf in CommaSpecializedCategory_Compose (S := S) (T := T) (s := s) (d := d) (d' := d') Fα F'α'.
  Let CommaCategory_Compose'' s d d' (Fα : CommaCategory_Morphism d d') (F'α' : CommaCategory_Morphism s d) :
    CommaCategory_Morphism s d'.
    simpl_definition_by_tac_and_exact (@CommaCategory_Compose' s d d' Fα F'α') ltac:(subst_body; cbv beta in *; fold_functor; cbv beta in *; present_spfunctor).
  Defined.
  Definition CommaCategory_Compose s d d' (Fα : CommaCategory_Morphism d d') (F'α' : CommaCategory_Morphism s d) :
    CommaCategory_Morphism s d'
    := Eval hnf in @CommaCategory_Compose'' s d d' Fα F'α'.

  Let CommaCategory_Identity' o := Eval hnf in CommaSpecializedCategory_Identity (S := S) (T := T) o.
  Let CommaCategory_Identity'' (o : CommaCategory_Object) : CommaCategory_Morphism o o.
    simpl_definition_by_tac_and_exact (@CommaCategory_Identity' o) ltac:(subst_body; cbv beta in *; fold_functor; cbv beta in *; present_spfunctor).
  Defined.
  Definition CommaCategory_Identity (o : CommaCategory_Object) : CommaCategory_Morphism o o
    := Eval hnf in @CommaCategory_Identity'' o.

  Global Arguments CommaCategory_Compose _ _ _ _ _ /.
  Global Arguments CommaCategory_Identity _ /.

  Lemma CommaCategory_Associativity o1 o2 o3 o4 (m1 : CommaCategory_Morphism o1 o2) (m2 : CommaCategory_Morphism o2 o3) (m3 : CommaCategory_Morphism o3 o4) :
    CommaCategory_Compose (CommaCategory_Compose m3 m2) m1 = CommaCategory_Compose m3 (CommaCategory_Compose m2 m1).
    abstract apply (CommaSpecializedCategory_Associativity (S := S) (T := T) m1 m2 m3).
  Qed.

  Lemma CommaCategory_LeftIdentity (a b : CommaCategory_Object) (f : CommaCategory_Morphism a b) :
    CommaCategory_Compose (CommaCategory_Identity b) f = f.
  Proof.
    abstract apply (CommaSpecializedCategory_LeftIdentity (S := S) (T := T) f).
  Qed.

  Lemma CommaCategory_RightIdentity (a b : CommaCategory_Object) (f : CommaCategory_Morphism a b) :
    CommaCategory_Compose f (CommaCategory_Identity a) = f.
  Proof.
    abstract apply (CommaSpecializedCategory_RightIdentity (S := S) (T := T) f).
  Qed.

  Definition CommaCategory : Category.
    refine (@Build_SpecializedCategory CommaCategory_Object CommaCategory_Morphism
      CommaCategory_Identity
      CommaCategory_Compose
      _ _ _
    );
    subst_body;
    abstract (apply CommaCategory_Associativity || apply CommaCategory_LeftIdentity || apply CommaCategory_RightIdentity).
  Defined.
End CommaCategory.

Hint Unfold CommaCategory_Compose CommaCategory_Identity CommaCategory_Morphism CommaCategory_Object : category.

Arguments CommaCategory [A B C] S T.

Local Notation "S ↓ T" := (CommaCategory S T).

Section SliceCategory.
  Variables A C : Category.
  Variable a : C.
  Variable S : Functor A C.
  Let B := TerminalCategory.

  Definition SliceCategory_Functor : Functor B C.
    refine {| ObjectOf' := (fun _ => a);
      MorphismOf' := (fun _ _ _ => Identity a)
    |}; abstract (intros; auto with morphism).
  Defined.

  Definition SliceCategory := CommaCategory S SliceCategory_Functor.
  Definition CosliceCategory := CommaCategory SliceCategory_Functor S.
End SliceCategory.

Section SliceCategoryOver.
  Variable C : Category.
  Variable a : C.

  Definition SliceCategoryOver := SliceCategory a (IdentityFunctor C).
  Definition CosliceCategoryOver := CosliceCategory a (IdentityFunctor C).
End SliceCategoryOver.

Section ArrowCategory.
  Variable C : Category.

  Definition ArrowCategory := CommaCategory (IdentityFunctor C) (IdentityFunctor C).
End ArrowCategory.
