Require Import ProofIrrelevance.
Require Export Category Functor ProductCategory.
Require Import Common SmallCat.

Set Implicit Arguments.

Local Infix "*" := ProductCategory.

Section CommaCategory.
  Variables A B C : Category.
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
     parts of the definition opaque via [abstract].  This speeds things
     up significantly.  We unfold the definitions at the very end with
     [Eval]. *)
  Definition CommaCategory_Object := { αβ : A * B & Morphism C (S (fst αβ)) (T (snd αβ)) }.
  Definition CommaCategory_Morphism (αβf α'β'f' : CommaCategory_Object) :=
    { gh : Morphism (A * B) (projT1 αβf) (projT1 α'β'f') |
      Compose (T.(MorphismOf) (snd gh)) (projT2 αβf) = Compose (projT2 α'β'f') (S.(MorphismOf) (fst gh))
    }.
  Definition CommaCategory_Compose s d d' (gh : CommaCategory_Morphism d d') (g'h' : CommaCategory_Morphism s d) : CommaCategory_Morphism s d'.
    exists (Compose (proj1_sig gh) (proj1_sig g'h')).
    abstract (
      simpl; unfold CommaCategory_Object, CommaCategory_Morphism in *; simpl;
        repeat match goal with
                 | [ H : @sig _ _ |- _ ] => destruct H; simpl in *
               end;
        repeat rewrite FCompositionOf;
          repeat rewrite <- Associativity;
            t_rev_with t'
    ).
  Defined.

  Definition CommaCategory_Identity o : CommaCategory_Morphism o o.
    exists (@Identity (A * B) (projT1 o)).
    abstract (
      simpl;
        repeat rewrite FIdentityOf;
          repeat rewrite LeftIdentity;
            repeat rewrite RightIdentity;
              reflexivity
    ).
  Defined.

  Definition CommaCategory' : Category.
    refine {| Object := CommaCategory_Object;
      Morphism := CommaCategory_Morphism;
      Compose := CommaCategory_Compose;
      Identity := CommaCategory_Identity
    |};
    abstract (
      simpl in *;
        repeat (let H:= fresh in intro H; destruct H as [ [ ] ? ]; simpl in *);
          try apply eq_exist; simpl; f_equal; auto
    ).
  Defined.

  Definition CommaCategory := Eval cbv beta iota zeta delta
    [CommaCategory' CommaCategory_Compose CommaCategory_Identity CommaCategory_Morphism CommaCategory_Object]
    in CommaCategory'.
End CommaCategory.

Local Notation "S ↓ T" := (CommaCategory S T) (at level 70, no associativity).

Section SliceCategory.
  Variables A C : Category.
  Variable a : C.
  Variable S : Functor A C.
  Let B := TerminalCategory.

  Definition SliceCategory_Functor : Functor B C.
    refine {| ObjectOf := (fun _ => a);
      MorphismOf := (fun _ _ _ => Identity a)
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
  Variable C : Category.

  Definition ArrowCategory := CommaCategory (IdentityFunctor C) (IdentityFunctor C).
End ArrowCategory.
