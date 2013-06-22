Require Import JMeq ProofIrrelevance.
Require Export Category SpecializedCategory Functor ProductCategory InitialTerminalCategory.
Require Import Common Notations FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Local Open Scope category_scope.

Section CommaSpecializedCategory.
  (* [Definition]s are not sort-polymorphic. *)
  Context `(A : SpecializedCategory).
  Context `(B : SpecializedCategory).
  Context `(C : SpecializedCategory).
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
  Record CommaSpecializedCategory_Object := { CommaSpecializedCategory_Object_Member :> { αβ : A * B & C.(Morphism) (S (fst αβ)) (T (snd αβ)) } }.

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
    clear; intros; subst.
    destruct N as [ [ ] ], M as [ [ ] ]; simpl in *.
    subst.
    apply eq_JMeq.
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
        destruct_all_hypotheses;
        unfold Morphism in *;
          destruct_hypotheses;
        repeat rewrite FCompositionOf;
        repeat try_associativity ltac:(t_rev_with t')
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
    simpl_eq;
    autorewrite with category;
    f_equal;
    try reflexivity.

  Lemma CommaSpecializedCategory_Associativity : forall o1 o2 o3 o4 (m1 : CommaSpecializedCategory_MorphismT o1 o2) (m2 : CommaSpecializedCategory_MorphismT o2 o3) (m3 : CommaSpecializedCategory_MorphismT o3 o4),
    CommaSpecializedCategory_Compose (CommaSpecializedCategory_Compose m3 m2) m1 =
    CommaSpecializedCategory_Compose m3 (CommaSpecializedCategory_Compose m2 m1).
  Proof.
    abstract (
        simpl_eq;
        repeat rewrite Associativity;
        reflexivity
      ).
  Qed.

  Lemma CommaSpecializedCategory_LeftIdentity : forall a b (f : CommaSpecializedCategory_MorphismT a b),
    CommaSpecializedCategory_Compose (CommaSpecializedCategory_Identity b) f = f.
  Proof.
    abstract comma_t.
  Qed.

  Lemma CommaSpecializedCategory_RightIdentity : forall a b (f : CommaSpecializedCategory_MorphismT a b),
    CommaSpecializedCategory_Compose f (CommaSpecializedCategory_Identity a) = f.
  Proof.
    abstract comma_t.
  Qed.

  Definition CommaSpecializedCategory : SpecializedCategory.
    refine (@Build_SpecializedCategory
              CommaSpecializedCategory_Object
              CommaSpecializedCategory_Morphism
              CommaSpecializedCategory_Identity
              CommaSpecializedCategory_Compose
              _ _ _
           );
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

Section SliceSpecializedCategory.
  Context `(A : SpecializedCategory).
  Context `(C : SpecializedCategory).
  Variable a : C.
  Variable S : SpecializedFunctor A C.

  Definition SliceSpecializedCategory := CommaSpecializedCategory S (FunctorFromTerminal C a).
  Definition CosliceSpecializedCategory := CommaSpecializedCategory (FunctorFromTerminal C a) S.

  (* [x ↓ F] is a coslice category; [F ↓ x] is a slice category; [x ↓ F] deals with morphisms [x -> F y]; [F ↓ x] has morphisms [F y -> x] *)
End SliceSpecializedCategory.

Section SliceSpecializedCategoryOver.
  Context `(C : SpecializedCategory).
  Variable a : C.

  Definition SliceSpecializedCategoryOver := SliceSpecializedCategory a (IdentityFunctor C).
  Definition CosliceSpecializedCategoryOver := CosliceSpecializedCategory a (IdentityFunctor C).
End SliceSpecializedCategoryOver.

Section ArrowSpecializedCategory.
  Context `(C : SpecializedCategory).

  Definition ArrowSpecializedCategory := CommaSpecializedCategory (IdentityFunctor C) (IdentityFunctor C).
End ArrowSpecializedCategory.

Notation "C / a" := (@SliceSpecializedCategoryOver C a) : category_scope.
Notation "a \ C" := (@CosliceSpecializedCategoryOver C a) (at level 70) : category_scope.

Definition CC_SpecializedFunctor' `(C : SpecializedCategory) `(D : SpecializedCategory) := SpecializedFunctor C D.
Coercion CC_FunctorFromTerminal' `(C : SpecializedCategory) (x : C) : CC_SpecializedFunctor' TerminalCategory C := FunctorFromTerminal C x.
Arguments CC_SpecializedFunctor' / .
Arguments CC_FunctorFromTerminal' / .

(* Set some notations for printing *)
Notation "x ↓ F" := (CosliceSpecializedCategory x F) : category_scope.
Notation "F ↓ x" := (SliceSpecializedCategory x F) : category_scope.
Notation "S ↓ T" := (CommaSpecializedCategory S T) : category_scope.
(* set the notation for parsing *)
Notation "S ↓ T" := (CommaSpecializedCategory (S : CC_SpecializedFunctor' _ _)
                                              (T : CC_SpecializedFunctor' _ _)) : category_scope.
(*Set Printing All.
Check (fun `(C : SpecializedCategory) `(D : SpecializedCategory) `(E : SpecializedCategory) (S : SpecializedFunctor C D) (T : SpecializedFunctor E D) => (S ↓ T)%category).
Check (fun `(D : SpecializedCategory) `(E : SpecializedCategory) (S : SpecializedFunctor E D) (x : D) => (x ↓ S)%category).*)
