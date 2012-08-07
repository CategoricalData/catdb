Require Import ProofIrrelevance.
Require Export Category SpecializedCategory Functor ProductCategory SigTSigCategory.
Require Import Common DiscreteCategory.

Set Implicit Arguments.

Local Open Scope category_scope.

Section CommaSpecializedCategory.
  (* [Definition]s are not sort-polymorphic. *)
  Variable objA : Type.
  Variable morA : objA -> objA -> Type.
  Variable A : SpecializedCategory morA.
  Variable objB : Type.
  Variable morB : objB -> objB -> Type.
  Variable B : SpecializedCategory morB.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable S : SpecializedFunctor A C.
  Variable T : SpecializedFunctor B C.

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
  Definition CommaSpecializedCategory : @SpecializedCategory
    { αβ : objA * objB & morC (S (fst αβ)) (T (snd αβ)) }
    (fun αβf α'β'f' =>
      { gh : (morA (fst (projT1 αβf)) (fst (projT1 α'β'f'))) * (morB (snd (projT1 αβf)) (snd (projT1 α'β'f'))) |
        Compose (T.(MorphismOf) (snd gh)) (projT2 αβf) = Compose (projT2 α'β'f') (S.(MorphismOf) (fst gh))
      }
    ).
    eapply (@SpecializedCategory_sigT_sig _ _ (A * B)
      (fun αβ => morC (S (fst αβ)) (T (snd αβ)))
      (fun αβf α'β'f' gh => (Compose (T.(MorphismOf) (snd gh)) (projT2 αβf) = Compose (projT2 α'β'f') (S.(MorphismOf) (fst gh))))
    );
    abstract (
      simpl; intros;
        present_spcategory;
        repeat rewrite FIdentityOf;
          repeat rewrite LeftIdentity;
            repeat rewrite RightIdentity;
              try reflexivity;
                destruct_sig; destruct_type @prod;
                repeat rewrite FCompositionOf;
                  t_with t';
                  try_associativity ltac:(apply f_equal2; try reflexivity; []);
                  t_with t'
    ).
  Defined.
End CommaSpecializedCategory.

Local Notation "S ↓ T" := (CommaSpecializedCategory S T) (at level 70, no associativity).

Section SliceSpecializedCategory.
  Variable objA : Type.
  Variable morA : objA -> objA -> Type.
  Variable A : SpecializedCategory morA.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable a : C.
  Variable S : SpecializedFunctor A C.
  Let B := TerminalCategory.

  Definition SliceSpecializedCategory_Functor : SpecializedFunctor B C.
    refine {| ObjectOf' := (fun _ => a);
      MorphismOf' := (fun _ _ _ => Identity a)
    |}; abstract (t_with t').
  Defined.

  Definition SliceSpecializedCategory := CommaSpecializedCategory S SliceSpecializedCategory_Functor.
  Definition CosliceSpecializedCategory := CommaSpecializedCategory SliceSpecializedCategory_Functor S.
End SliceSpecializedCategory.

Section SliceSpecializedCategoryOver.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable a : C.

  Definition SliceSpecializedCategoryOver := SliceSpecializedCategory a (IdentityFunctor C).
  Definition CosliceSpecializedCategoryOver := CosliceSpecializedCategory a (IdentityFunctor C).
End SliceSpecializedCategoryOver.

Section ArrowSpecializedCategory.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Definition ArrowSpecializedCategory := CommaSpecializedCategory (IdentityFunctor C) (IdentityFunctor C).
End ArrowSpecializedCategory.
