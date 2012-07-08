Require Import ProofIrrelevance.
Require Export SpecializedCategory SpecializedFunctor SpecializedProductCategory.
Require Import Common SpecializedDiscreteCategory.

Set Implicit Arguments.

Local Infix "*" := ProductSpecializedCategory.

Section CommaSpecializedCategory.
  Variable objA : Type.
  Variable morA : objA -> objA -> Type.
  Variable objB : Type.
  Variable morB : objB -> objB -> Type.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable A : SpecializedCategory morA.
  Variable B : SpecializedCategory morB.
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
     parts of the definition opaque via [abstract].  This speeds things
     up significantly.  We unfold the definitions at the very end with
     [Eval]. *)
  Definition CommaSpecializedCategory_Object := { αβ : A * B & C.(Morphism) (S (fst αβ)) (T (snd αβ)) }.
  Definition CommaSpecializedCategory_Morphism (αβf α'β'f' : CommaSpecializedCategory_Object) :=
    { gh : (A * B).(Morphism) (projT1 αβf) (projT1 α'β'f') |
      Compose (T.(MorphismOf) (snd gh)) (projT2 αβf) = Compose (projT2 α'β'f') (S.(MorphismOf) (fst gh))
    }.
  Definition CommaSpecializedCategory_Compose s d d' (gh : CommaSpecializedCategory_Morphism d d') (g'h' : CommaSpecializedCategory_Morphism s d) :
    CommaSpecializedCategory_Morphism s d'.
    Transparent Object Morphism Compose.
    exists (Compose (proj1_sig gh) (proj1_sig g'h')).
    abstract (
      simpl; unfold CommaSpecializedCategory_Object, CommaSpecializedCategory_Morphism in *; simpl in *;
        destruct_all_hypotheses;
        unfold Morphism in *;
          destruct_hypotheses;
          repeat rewrite FCompositionOf;
            repeat rewrite <- Associativity;
              t_rev_with t'
    ).
  Defined.

  Definition CommaSpecializedCategory_Identity o : CommaSpecializedCategory_Morphism o o.
    exists (@Identity _ _ (A * B) (projT1 o)).
    abstract (
      simpl;
        repeat rewrite FIdentityOf;
          repeat rewrite LeftIdentity;
            repeat rewrite RightIdentity;
              reflexivity
    ).
  Defined.

  Definition CommaSpecializedCategory' : @SpecializedCategory CommaSpecializedCategory_Object CommaSpecializedCategory_Morphism.
    refine {|
      Compose' := CommaSpecializedCategory_Compose;
      Identity' := CommaSpecializedCategory_Identity
    |};
    abstract (
      simpl in *;
        repeat (let H:= fresh in intro H; destruct H as [ [ ] ? ]; simpl in *);
          try apply eq_exist; simpl; present_spcategory; autorewrite with core;
            f_equal
    ).
  Defined.

  Definition CommaSpecializedCategory := Eval cbv beta iota zeta delta
    [CommaSpecializedCategory' (*CommaSpecializedCategory_Compose CommaSpecializedCategory_Identity CommaSpecializedCategory_Morphism CommaSpecializedCategory_Object*)]
    in CommaSpecializedCategory'.
End CommaSpecializedCategory.

Hint Unfold CommaSpecializedCategory_Compose CommaSpecializedCategory_Identity CommaSpecializedCategory_Morphism CommaSpecializedCategory_Object.

Local Notation "S ↓ T" := (CommaSpecializedCategory S T) (at level 70, no associativity).

Section SliceSpecializedCategory.
  Variable objA : Type.
  Variable morA : objA -> objA -> Type.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable A : SpecializedCategory morA.
  Variable C : SpecializedCategory morC.
  Variable a : C.
  Variable S : SpecializedFunctor A C.
  Let B := TerminalSpecializedCategory.

  Definition SliceSpecializedCategory_SpecializedFunctor : SpecializedFunctor B C.
    refine {| ObjectOf' := (fun _ => a);
      MorphismOf' := (fun _ _ _ => Identity a)
    |}; abstract (t_with t').
  Defined.

  Definition SliceSpecializedCategory := CommaSpecializedCategory S SliceSpecializedCategory_SpecializedFunctor.
  Definition CosliceSpecializedCategory := CommaSpecializedCategory SliceSpecializedCategory_SpecializedFunctor S.
End SliceSpecializedCategory.

Section SliceSpecializedCategoryOver.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable a : C.

  Definition SliceSpecializedCategoryOver := SliceSpecializedCategory a (IdentitySpecializedFunctor C).
  Definition CosliceSpecializedCategoryOver := CosliceSpecializedCategory a (IdentitySpecializedFunctor C).
End SliceSpecializedCategoryOver.

Section ArrowSpecializedCategory.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Definition ArrowSpecializedCategory := CommaSpecializedCategory (IdentitySpecializedFunctor C) (IdentitySpecializedFunctor C).
End ArrowSpecializedCategory.
