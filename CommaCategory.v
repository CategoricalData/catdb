Require Import ProofIrrelevance.
Require Export Category SpecializedCategory Functor ProductCategory.
Require Import Common DiscreteCategory SpecializedCommaCategory DefinitionSimplification.

Set Implicit Arguments.

Local Open Scope category_scope.

Local Ltac fold_category :=
  change CMorphism with (fun C => @Morphism (CObject C) (CMorphism C) C) in *;
    change CObject with (fun C => @Object (CObject C) (CMorphism C) C) in *;
      present_spcategory.

Section CommaCategory.
  (* [Definition]s are not sort-polymorphic, and it's too slow to not use
     [Definition]s, so we might as well use [Category]s rather than [SpecializedCategory]s. *)
  Variable A B C : Category.
  Variable S : Functor A C.
  Variable T : Functor B C.

  Hint Resolve Associativity RightIdentity LeftIdentity.

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
  Let CommaCategory' : Category := Eval hnf in CommaSpecializedCategory S T.
  Let CommaCategory'' : Category.
    change (@Morphism _ ?mor _) with mor in *;
      change (@Object ?obj _ _) with obj in *;
        simpl in *;
          fold_category; simpl in *.
    simpl_definition_by_exact CommaCategory'.
  Defined.
  Definition CommaCategory : Category := Eval cbv beta delta [CommaCategory''] in CommaCategory''.
End CommaCategory.

Local Notation "S ↓ T" := (CommaCategory S T) (at level 70, no associativity).

Section SliceCategory.
  Variables A C : Category.
  Variable a : C.
  Variable S : Functor A C.
  Let B := TerminalCategory.

  Definition SliceCategory_Functor : Functor B C.
    refine {| ObjectOf' := (fun _ => a);
      MorphismOf' := (fun _ _ _ => Identity a)
    |}; abstract (t_with t').
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
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Definition ArrowCategory := CommaCategory (IdentityFunctor C) (IdentityFunctor C).
End ArrowCategory.
