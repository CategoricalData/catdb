Require Import JMeq ProofIrrelevance.
Require Export Category SpecializedCategory Functor ProductCategory.
Require Import Common Notations InitialTerminalCategory FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Local Infix "==" := JMeq.

Local Open Scope category_scope.

Section CommaSpecializedCategory.
  (* [Definition]s are not sort-polymorphic. *)
  Context `(A : @SpecializedCategory objA).
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).
  Variable S : SpecializedFunctor A C.
  Variable T : SpecializedFunctor B C.

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
  Record CommaSpecializedCategory_Object := { CommaSpecializedCategory_Object_Member :> { αβ : objA * objB & C.(Morphism) (S (fst αβ)) (T (snd αβ)) } }.

  Let SortPolymorphic_Helper (A T : Type) (Build_T : A -> T) := A.

  Definition CommaSpecializedCategory_ObjectT := Eval hnf in SortPolymorphic_Helper Build_CommaSpecializedCategory_Object.
  Global Identity Coercion CommaSpecializedCategory_Object_Id : CommaSpecializedCategory_ObjectT >-> sigT.
  Definition Build_CommaSpecializedCategory_Object' (mem : CommaSpecializedCategory_ObjectT) := Build_CommaSpecializedCategory_Object mem.
  Global Coercion Build_CommaSpecializedCategory_Object' : CommaSpecializedCategory_ObjectT >-> CommaSpecializedCategory_Object.

  Record CommaSpecializedCategory_Morphism (αβf α'β'f' : CommaSpecializedCategory_ObjectT) := { CommaSpecializedCategory_Morphism_Member :>
    { gh : (A.(Morphism) (fst (projT1 αβf)) (fst (projT1 α'β'f'))) * (B.(Morphism) (snd (projT1 αβf)) (snd (projT1 α'β'f')))  |
      Compose (T.(MorphismOf) (snd gh)) (projT2 αβf) = Compose (projT2 α'β'f') (S.(MorphismOf) (fst gh))
    }
  }.

  Definition CommaSpecializedCategory_MorphismT (αβf α'β'f' : CommaSpecializedCategory_ObjectT) :=
    Eval hnf in SortPolymorphic_Helper (@Build_CommaSpecializedCategory_Morphism αβf α'β'f').
  Global Identity Coercion CommaSpecializedCategory_Morphism_Id : CommaSpecializedCategory_MorphismT >-> sig.
  Definition Build_CommaSpecializedCategory_Morphism' αβf α'β'f' (mem : @CommaSpecializedCategory_MorphismT αβf α'β'f') :=
    @Build_CommaSpecializedCategory_Morphism _ _ mem.
  Global Coercion Build_CommaSpecializedCategory_Morphism' : CommaSpecializedCategory_MorphismT >-> CommaSpecializedCategory_Morphism.

  Lemma CommaSpecializedCategory_Morphism_eq αβf α'β'f' αβf2 α'β'f'2
        (M : CommaSpecializedCategory_Morphism αβf α'β'f')
        (N : CommaSpecializedCategory_Morphism αβf2 α'β'f'2) :
    αβf = αβf2
    -> α'β'f' = α'β'f'2
    -> proj1_sig M == proj1_sig N
    -> M == N.
    clear; intros; destruct N as [ [ ] ], M as [ [ ] ]; simpl in *;
    repeat subst;
    apply eq_JMeq;
    f_equal; simpl_eq; reflexivity.
  Qed.

  Global Arguments CommaSpecializedCategory_Object_Member _ : simpl nomatch.
  Global Arguments CommaSpecializedCategory_Morphism_Member _ _ _ : simpl nomatch.

  Definition CommaSpecializedCategory_Compose s d d'
    (gh : CommaSpecializedCategory_MorphismT d d') (g'h' : CommaSpecializedCategory_MorphismT s d) :
    CommaSpecializedCategory_MorphismT s d'.
    exists (Compose (C := A * B) (proj1_sig gh) (proj1_sig g'h')).
    hnf in *; simpl in *.
    abstract (
        present_spcategory;
        destruct_all_hypotheses;
        unfold Morphism in *;
          destruct_hypotheses;
        repeat rewrite FCompositionOf;
        repeat rewrite <- Associativity;
        t_rev_with t';
        repeat rewrite Associativity;
        t_rev_with t'
      ).
  Defined.

  Global Arguments CommaSpecializedCategory_Compose _ _ _ _ _ /.

  Definition CommaSpecializedCategory_Identity o : CommaSpecializedCategory_MorphismT o o.
    exists (Identity (C := A * B) (projT1 o)).
    abstract (
        simpl; autorewrite with category; reflexivity
      ).
  Defined.

  Global Arguments CommaSpecializedCategory_Identity _ /.

  Local Ltac comma_t :=
    repeat (
      let H:= fresh in intro H; destruct H as [ [ ] ]
    );
    destruct_hypotheses;
    simpl in *;
    present_spcategory;
    simpl_eq;
    present_spcategory; autorewrite with category;
    f_equal;
    try reflexivity.

  Lemma CommaSpecializedCategory_Associativity : forall o1 o2 o3 o4 (m1 : CommaSpecializedCategory_MorphismT o1 o2) (m2 : CommaSpecializedCategory_MorphismT o2 o3) (m3 : CommaSpecializedCategory_MorphismT o3 o4),
    CommaSpecializedCategory_Compose (CommaSpecializedCategory_Compose m3 m2) m1 =
    CommaSpecializedCategory_Compose m3 (CommaSpecializedCategory_Compose m2 m1).
  Proof.
    comma_t.
  Qed.

  Lemma CommaSpecializedCategory_LeftIdentity : forall a b (f : CommaSpecializedCategory_MorphismT a b),
    CommaSpecializedCategory_Compose (CommaSpecializedCategory_Identity b) f = f.
  Proof.
    comma_t.
  Qed.

  Lemma CommaSpecializedCategory_RightIdentity : forall a b (f : CommaSpecializedCategory_MorphismT a b),
    CommaSpecializedCategory_Compose f (CommaSpecializedCategory_Identity a) = f.
  Proof.
    comma_t.
  Qed.

  Definition CommaSpecializedCategory : @SpecializedCategory CommaSpecializedCategory_Object.
    match goal with
      | [ |- @SpecializedCategory ?obj ] =>
        refine (@Build_SpecializedCategory obj
          CommaSpecializedCategory_Morphism
          CommaSpecializedCategory_Identity
          CommaSpecializedCategory_Compose
          _ _ _
        )
    end;
    abstract (
      intros;
        destruct_type' @CommaSpecializedCategory_Morphism;
        unfold CommaSpecializedCategory_Morphism_Member, Build_CommaSpecializedCategory_Morphism';
          try apply f_equal;
            apply CommaSpecializedCategory_Associativity ||
              apply CommaSpecializedCategory_LeftIdentity ||
                apply CommaSpecializedCategory_RightIdentity
    ).
  Defined.
End CommaSpecializedCategory.

Hint Unfold CommaSpecializedCategory_Compose CommaSpecializedCategory_Identity : category.
Hint Constructors CommaSpecializedCategory_Morphism CommaSpecializedCategory_Object : category.

Local Notation "S ↓ T" := (CommaSpecializedCategory S T).

Section SliceSpecializedCategory.
  Context `(A : @SpecializedCategory objA).
  Context `(C : @SpecializedCategory objC).
  Variable a : C.
  Variable S : SpecializedFunctor A C.
  Let B := TerminalCategory.

  Definition SliceSpecializedCategory_Functor : SpecializedFunctor B C.
    refine {| ObjectOf' := (fun _ => a);
      MorphismOf' := (fun _ _ _ => Identity a)
    |}; abstract (intros; auto with morphism).
  Defined.

  Definition SliceSpecializedCategory := CommaSpecializedCategory S SliceSpecializedCategory_Functor.
  Definition CosliceSpecializedCategory := CommaSpecializedCategory SliceSpecializedCategory_Functor S.
End SliceSpecializedCategory.

Section SliceSpecializedCategoryOver.
  Context `(C : @SpecializedCategory objC).
  Variable a : C.

  Definition SliceSpecializedCategoryOver := SliceSpecializedCategory a (IdentityFunctor C).
  Definition CosliceSpecializedCategoryOver := CosliceSpecializedCategory a (IdentityFunctor C).
End SliceSpecializedCategoryOver.

Section ArrowSpecializedCategory.
  Context `(C : @SpecializedCategory objC).

  Definition ArrowSpecializedCategory := CommaSpecializedCategory (IdentityFunctor C) (IdentityFunctor C).
End ArrowSpecializedCategory.
