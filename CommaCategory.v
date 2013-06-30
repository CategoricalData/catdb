Require Import JMeq ProofIrrelevance.
Require Export Category Category Functor ProductCategory InitialTerminalCategory.
Require Import Common Notations FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Local Open Scope category_scope.

Section CommaCategory.
  (* [Definition]s are not sort-polymorphic. *)
  Variable A : Category.
  Variable B : Category.
  Variable C : Category.
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
  Record CommaCategory_Object :=
    {
      CCO_α : A;
      CCO_β : B;
      CCO_f : Morphism C (S CCO_α) (T CCO_β)
    }.

  Definition CommaCategory_ObjectT := { αβ : A * B & C.(Morphism) (S (fst αβ)) (T (snd αβ)) }.
  Global Identity Coercion CommaCategory_Object_Id : CommaCategory_ObjectT >-> sigT.
  Global Coercion sigT_of_CCO (αβf : CommaCategory_Object)
  : CommaCategory_ObjectT
    := existT (fun αβ : A * B
               => Morphism C (S (fst αβ)) (T (snd αβ)))
              (CCO_α αβf, CCO_β αβf)
              (CCO_f αβf).
  Global Coercion CCO_of_sigT (αβf : CommaCategory_ObjectT)
  : CommaCategory_Object
    := Build_CommaCategory_Object _
                                             _
                                             (projT2 αβf).

  Global Arguments CCO_of_sigT _ / .
  Global Arguments sigT_of_CCO _ / .

  Lemma CommaCategory_Object_eq' (x y : CommaCategory_Object)
  : forall (Hα : CCO_α x = CCO_α y)
           (Hβ : CCO_β x = CCO_β y),
      match Hα in _ = X, Hβ in _ = Y return Morphism C (S X) (T Y) with
        | eq_refl, eq_refl => CCO_f x
      end = CCO_f y
      -> x = y.
  Proof.
    destruct x, y; simpl.
    intros; subst; reflexivity.
  Defined.

  Lemma CommaCategory_Object_eq (x y : CommaCategory_Object)
  : forall (Hα : CCO_α x = CCO_α y)
           (Hβ : CCO_β x = CCO_β y),
      CCO_f x == CCO_f y
      -> x = y.
  Proof.
    destruct x, y; simpl.
    intros; repeat subst; reflexivity.
  Qed.

  Record CommaCategory_Morphism (αβf α'β'f' : CommaCategory_Object) :=
    {
      CCM_g : Morphism A (CCO_α αβf) (CCO_α α'β'f');
      CCM_h : Morphism B (CCO_β αβf) (CCO_β α'β'f');
      CCM_φ : Compose (MorphismOf T CCM_h) (CCO_f αβf) = Compose (CCO_f α'β'f') (MorphismOf S CCM_g)
    }.

  Definition CommaCategory_MorphismT (αβf α'β'f' : CommaCategory_ObjectT)
    := { gh : (A.(Morphism) (fst (projT1 αβf)) (fst (projT1 α'β'f'))) * (B.(Morphism) (snd (projT1 αβf)) (snd (projT1 α'β'f')))  |
         Compose (T.(MorphismOf) (snd gh)) (projT2 αβf) = Compose (projT2 α'β'f') (S.(MorphismOf) (fst gh))
       }.

  Global Identity Coercion CommaCategory_Morphism_Id : CommaCategory_MorphismT >-> sig.
  Global Coercion sig_of_CCM αβf α'β'f' (gh : CommaCategory_Morphism αβf α'β'f')
  : CommaCategory_MorphismT αβf α'β'f'
    := exist (fun gh : Morphism (A * B) (projT1 αβf) (projT1 α'β'f')
              => Compose (MorphismOf T (snd gh)) (projT2 αβf)
                 = Compose (projT2 α'β'f') (MorphismOf S (fst gh)))
             (CCM_g gh, CCM_h gh)
             (CCM_φ gh).
  Global Coercion CCM_of_sig αβf α'β'f' (gh : CommaCategory_MorphismT αβf α'β'f')
  : CommaCategory_Morphism αβf α'β'f'
    := Build_CommaCategory_Morphism
         αβf
         α'β'f'
         _
         _
         (proj2_sig gh).

  Global Arguments CCM_of_sig _ _ _ / .
  Global Arguments sig_of_CCM _ _ _ / .

  Lemma CommaCategory_Morphism_contr_eq αβf α'β'f'
        (gh g'h' : CommaCategory_Morphism αβf α'β'f')
        (C_morphism_proof_irrelevance : forall s d (m1 m2 : Morphism C s d)
                                               (pf1 pf2 : m1 = m2),
                                          pf1 = pf2)
  : CCM_g gh = CCM_g g'h'
    -> CCM_h gh = CCM_h g'h'
    -> gh = g'h'.
  Proof.
    destruct gh, g'h'; simpl.
    intros; subst.
    f_equal.
    apply_hyp.
  Defined.

  Lemma CommaCategory_Morphism_eq αβf α'β'f'
        (gh g'h' : CommaCategory_Morphism αβf α'β'f')
  : CCM_g gh = CCM_g g'h'
    -> CCM_h gh = CCM_h g'h'
    -> gh = g'h'.
  Proof.
    intros; apply CommaCategory_Morphism_contr_eq;
    try assumption.
    intros; apply proof_irrelevance.
  Qed.

  Lemma CommaCategory_Morphism_JMeq αβf0 α'β'f'0 αβf1 α'β'f'1
        (gh : CommaCategory_Morphism αβf0 αβf1)
        (g'h' : CommaCategory_Morphism α'β'f'0 α'β'f'1)
  : αβf0 = α'β'f'0
    -> αβf1 = α'β'f'1
    -> CCM_g gh == CCM_g g'h'
    -> CCM_h gh == CCM_h g'h'
    -> gh == g'h'.
  Proof.
    destruct gh, g'h'; simpl.
    intros; repeat subst.
    JMeq_eq; f_equal.
    apply proof_irrelevance.
  Qed.

  Definition CommaCategory_Compose s d d'
             (gh : CommaCategory_Morphism d d') (g'h' : CommaCategory_Morphism s d)
  : CommaCategory_Morphism s d'.
  Proof.
    exists (Compose (CCM_g gh) (CCM_g g'h')) (Compose (CCM_h gh) (CCM_h g'h')).
    hnf in *; simpl in *.
    abstract (
        destruct_head CommaCategory_Morphism;
        repeat rewrite FCompositionOf;
        repeat try_associativity ltac:(t_rev_with t')
      ).
  Defined.

  Global Arguments CommaCategory_Compose _ _ _ _ _ /.

  Definition CommaCategory_Identity o : CommaCategory_Morphism o o.
    exists (Identity (CCO_α o)) (Identity (CCO_β o)).
    abstract (
        simpl; autorewrite with category; reflexivity
      ).
  Defined.

  Global Arguments CommaCategory_Identity _ /.

  Local Ltac comma_t :=
    intros;
    destruct_head CommaCategory_Morphism;
    simpl in *;
    simpl_eq;
    autorewrite with category;
    f_equal;
    try reflexivity.

  Local Ltac comma_eq_t :=
    intros;
    apply CommaCategory_Morphism_eq;
    simpl;
    autorewrite with category;
    reflexivity.

  Lemma CommaCategory_Associativity : forall o1 o2 o3 o4 (m1 : CommaCategory_Morphism o1 o2) (m2 : CommaCategory_Morphism o2 o3) (m3 : CommaCategory_Morphism o3 o4),
    CommaCategory_Compose (CommaCategory_Compose m3 m2) m1 =
    CommaCategory_Compose m3 (CommaCategory_Compose m2 m1).
  Proof.
    abstract comma_eq_t.
  Qed.

  Lemma CommaCategory_LeftIdentity : forall a b (f : CommaCategory_Morphism a b),
    CommaCategory_Compose (CommaCategory_Identity b) f = f.
  Proof.
    abstract comma_eq_t.
  Qed.

  Lemma CommaCategory_RightIdentity : forall a b (f : CommaCategory_Morphism a b),
    CommaCategory_Compose f (CommaCategory_Identity a) = f.
  Proof.
    abstract comma_eq_t.
  Qed.

  Definition CommaCategory : Category.
    refine (@Build_Category
              CommaCategory_Object
              CommaCategory_Morphism
              CommaCategory_Identity
              CommaCategory_Compose
              _ _ _
           );
    abstract comma_eq_t.
  Defined.
End CommaCategory.

Hint Unfold CommaCategory_Compose CommaCategory_Identity : category.
Hint Constructors CommaCategory_Morphism CommaCategory_Object : category.

Section SliceCategory.
  Variable A : Category.
  Variable C : Category.
  Variable a : C.
  Variable S : Functor A C.

  Definition SliceCategory := CommaCategory S (FunctorFromTerminal C a).
  Definition CosliceCategory := CommaCategory (FunctorFromTerminal C a) S.

  (* [x ↓ F] is a coslice category; [F ↓ x] is a slice category; [x ↓ F] deals with morphisms [x -> F y]; [F ↓ x] has morphisms [F y -> x] *)
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

Notation "C / a" := (@SliceCategoryOver C a) : category_scope.
Notation "a \ C" := (@CosliceCategoryOver C a) : category_scope.

Definition CC_Functor' (C : Category)(D : Category):= Functor C D.
Coercion CC_FunctorFromTerminal' (C : Category)(x : C) : CC_Functor' TerminalCategory C := FunctorFromTerminal C x.
Arguments CC_Functor' / .
Arguments CC_FunctorFromTerminal' / .

(* Set some notations for printing *)
Notation "x ↓ F" := (CosliceCategory x F) : category_scope.
Notation "F ↓ x" := (SliceCategory x F) : category_scope.
Notation "S ↓ T" := (CommaCategory S T) : category_scope.
(* set the notation for parsing *)
Notation "S ↓ T" := (CommaCategory (S : CC_Functor' _ _)
                                              (T : CC_Functor' _ _)) : category_scope.
(*Set Printing All.
Check (fun (C : Category)(D : Category)(E : Category)(S : Functor C D) (T : Functor E D) => (S ↓ T)%category).
Check (fun (D : Category)(E : Category)(S : Functor E D) (x : D) => (x ↓ S)%category).*)
