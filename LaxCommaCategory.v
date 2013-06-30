Require Import ProofIrrelevance JMeq.
Require Export Category Functor ProductCategory NaturalTransformation.
Require Import Common DecidableDiscreteCategory ComputableCategory DefinitionSimplification FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Local Open Scope natural_transformation_scope.
Local Open Scope functor_scope.
Local Open Scope category_scope.

Local Hint Immediate ComposeFunctorsAssociativity LeftIdentityFunctor RightIdentityFunctor.

Local Ltac lax_comma_t eq_lemma :=
  repeat intros [ ? ? ];
  repeat match goal with
           | _ => intro
           | _ => progress subst
           | _ => apply eq_lemma
           | _ => reflexivity
           | [ |- @JMeq ?A _ ?A _ ] => apply eq_JMeq
           | [ |- @JMeq ?A ?x ?B ?y ]
             => match eval hnf in A with
                  | NaturalTransformation _ _ => apply NaturalTransformation_JMeq; trivial
                  | _ => let A' := (eval simpl in A) in
                         let B' := (eval simpl in B) in
                         progress change (@JMeq A' x B' y)
                end
         end;
  simpl;
  try rewrite !ComposeFunctorsAssociativity;
  try rewrite !LeftIdentityFunctor;
  try rewrite !RightIdentityFunctor;
  try rewrite !FIdentityOf;
  try rewrite !LeftIdentity;
  try rewrite !RightIdentity;
  try rewrite !Associativity;
  try reflexivity.

Section LaxSliceCategory.
  Variable I : Type.
  Variable Index2Cat : I -> Category.

  Local Coercion Index2Cat : I >-> Category.

  Let Cat := ComputableCategory Index2Cat.

  Variable C : Category.

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
  Record LaxSliceCategory_Object :=
    {
      LSCO_X : I;
      LSCO_G : Functor LSCO_X C
    }.

  Definition LaxSliceCategory_ObjectT := { X : I * unit & Functor (fst X) C }.
  Global Identity Coercion LaxSliceCategory_Object_Id : LaxSliceCategory_ObjectT >-> sigT.
  Global Coercion sigT_of_LSCO (XG : LaxSliceCategory_Object)
  : LaxSliceCategory_ObjectT
    := existT (fun X : I * unit => Functor (fst X) C)
              (LSCO_X XG, tt)
              (LSCO_G XG).
  Global Coercion LSCO_of_sigT (XG : LaxSliceCategory_ObjectT)
  : LaxSliceCategory_Object
    := Build_LaxSliceCategory_Object (projT2 XG).

  Global Arguments LSCO_of_sigT _ / .
  Global Arguments sigT_of_LSCO _ / .

  Lemma LaxSliceCategory_Object_eq' (x y : LaxSliceCategory_Object)
  : forall (HX : LSCO_X x = LSCO_X y),
      match HX in _ = X return Functor X C with
        | eq_refl => LSCO_G x
      end = LSCO_G y
      -> x = y.
  Proof.
    destruct x, y; simpl.
    intros; subst; reflexivity.
  Defined.

  Lemma LaxSliceCategory_Object_eq (x y : LaxSliceCategory_Object)
  : LSCO_X x = LSCO_X y
    -> LSCO_G x == LSCO_G y
    -> x = y.
  Proof.
    destruct x, y; simpl.
    intros; repeat subst; reflexivity.
  Qed.

  Record LaxSliceCategory_Morphism (XG X'G' : LaxSliceCategory_Object) :=
    {
      LSCM_F : Functor (LSCO_X XG) (LSCO_X X'G');
      LSCM_T : NaturalTransformation (LSCO_G XG)
                                     (LSCO_G X'G' ∘ LSCM_F)
    }.

  Definition LaxSliceCategory_MorphismT (XG X'G' : LaxSliceCategory_ObjectT) :=
    { F : Functor (fst (projT1 XG)) (fst (projT1 X'G')) * unit &
      NaturalTransformation (projT2 XG) (projT2 X'G' ∘ fst F)
    }.

  Global Identity Coercion LaxSliceCategory_Morphism_Id : LaxSliceCategory_MorphismT >-> sigT.
  Global Coercion sigT_of_LSCM XG X'G' (gh : LaxSliceCategory_Morphism XG X'G')
  : LaxSliceCategory_MorphismT XG X'G'
    := existT (fun F : Functor (fst (projT1 XG)) (fst (projT1 X'G')) * unit
               => NaturalTransformation (projT2 XG) (projT2 X'G' ∘ fst F))
              (LSCM_F gh, tt)
              (LSCM_T gh).
  Global Coercion LSCM_of_sigT XG X'G' (gh : LaxSliceCategory_MorphismT XG X'G')
  : LaxSliceCategory_Morphism XG X'G'
    := @Build_LaxSliceCategory_Morphism
         XG
         X'G'
         _
         (projT2 gh).

  Global Arguments LSCM_of_sigT _ _ _ / .
  Global Arguments sigT_of_LSCM _ _ _ / .

  Lemma LaxSliceCategory_Morphism_eq' XG X'G'
        (gh g'h' : LaxSliceCategory_Morphism XG X'G')
  : forall (HF : LSCM_F gh = LSCM_F g'h'),
      match HF in _ = F return NaturalTransformation _ (_ ∘ F) with
        | eq_refl => LSCM_T gh
      end = LSCM_T g'h'
      -> gh = g'h'.
  Proof.
    destruct gh, g'h'; simpl.
    intros; subst.
    reflexivity.
  Defined.

  Lemma LaxSliceCategory_Morphism_eq XG X'G'
        (gh g'h' : LaxSliceCategory_Morphism XG X'G')
  : LSCM_F gh = LSCM_F g'h'
    -> LSCM_T gh == LSCM_T g'h'
    -> gh = g'h'.
  Proof.
    destruct gh, g'h'.
    simpl; intros.
    repeat subst.
    reflexivity.
  Qed.

  Lemma LaxSliceCategory_Morphism_JMeq XG0 X'G'0 XG1 X'G'1
        (gh : LaxSliceCategory_Morphism XG0 XG1)
        (g'h' : LaxSliceCategory_Morphism X'G'0 X'G'1)
  : XG0 = X'G'0
    -> XG1 = X'G'1
    -> LSCM_F gh == LSCM_F g'h'
    -> LSCM_T gh == LSCM_T g'h'
    -> gh == g'h'.
  Proof.
    destruct gh, g'h'; simpl.
    intros; repeat subst.
    reflexivity.
  Qed.

  Definition LaxSliceCategory_Compose' s d d' (FT : LaxSliceCategory_Morphism d d') (F'T' : LaxSliceCategory_Morphism s d)
  : LaxSliceCategory_Morphism s d'.
    exists (LSCM_F FT ∘ LSCM_F F'T').
    refine (_ ∘₁ LSCM_T F'T').
    refine (_ ∘₁ (LSCM_T FT ∘₀ IdentityNaturalTransformation _)).
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (GeneralizedIdentityNaturalTransformation F G eq_refl eq_refl)
    end.
  Defined.

  Definition LaxSliceCategory_Compose'' s d d' (FT : LaxSliceCategory_Morphism d d') (F'T' : LaxSliceCategory_Morphism s d) :
    LaxSliceCategory_Morphism s d'.
    simpl_definition_by_tac_and_exact (@LaxSliceCategory_Compose' s d d' FT F'T') ltac:(unfold LaxSliceCategory_Compose' in *).
  Defined.

  (* Then we clean up a bit with reduction. *)
  Definition LaxSliceCategory_Compose s d d' (FT : LaxSliceCategory_Morphism d d') (F'T' : LaxSliceCategory_Morphism s d) :
    LaxSliceCategory_Morphism s d'
    := Eval cbv beta iota zeta delta [LaxSliceCategory_Compose''] in (@LaxSliceCategory_Compose'' s d d' FT F'T').

  Global Arguments LaxSliceCategory_Compose _ _ _ _ _ / .

  Definition LaxSliceCategory_Identity x : LaxSliceCategory_Morphism x x.
    exists (IdentityFunctor _).
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (GeneralizedIdentityNaturalTransformation F G eq_refl eq_refl)
    end.
  Defined.

  Global Arguments LaxSliceCategory_Identity _ / .

  Lemma LaxSliceCategory_Associativity
  : forall (o1 o2 o3 o4 : LaxSliceCategory_Object)
           (m1 : LaxSliceCategory_Morphism o1 o2)
           (m2 : LaxSliceCategory_Morphism o2 o3)
           (m3 : LaxSliceCategory_Morphism o3 o4),
      LaxSliceCategory_Compose (LaxSliceCategory_Compose m3 m2) m1 =
      LaxSliceCategory_Compose m3 (LaxSliceCategory_Compose m2 m1).
  Proof.
    abstract lax_comma_t LaxSliceCategory_Morphism_eq.
  Qed.

  Lemma LaxSliceCategory_LeftIdentity
  : forall (a b : LaxSliceCategory_Object)
           (f : LaxSliceCategory_Morphism a b),
      LaxSliceCategory_Compose (LaxSliceCategory_Identity b) f = f.
  Proof.
    lax_comma_t LaxSliceCategory_Morphism_eq.

  Qed.

  Lemma LaxSliceCategory_RightIdentity
  : forall (a b : LaxSliceCategory_Object)
           (f : LaxSliceCategory_Morphism a b),
      LaxSliceCategory_Compose f (LaxSliceCategory_Identity a) = f.
  Proof.
    abstract lax_comma_t LaxSliceCategory_Morphism_eq.
  Qed.

  Definition LaxSliceCategory : Category
    := @Build_Category
         LaxSliceCategory_Object
         LaxSliceCategory_Morphism
         LaxSliceCategory_Identity
         LaxSliceCategory_Compose
         LaxSliceCategory_Associativity
         LaxSliceCategory_LeftIdentity
         LaxSliceCategory_RightIdentity.
End LaxSliceCategory.

Hint Unfold LaxSliceCategory_Compose LaxSliceCategory_Identity : category.

Section LaxCosliceCategory.
  Variable I : Type.
  Variable Index2Cat : I -> Category.

  Local Coercion Index2Cat : I >-> Category.

  Let Cat := ComputableCategory Index2Cat.

  Variable C : Category.

  Record LaxCosliceCategory_Object :=
    {
      LCCO_X : I;
      LCCO_G : Functor LCCO_X C
    }.

  Definition LaxCosliceCategory_ObjectT := { X : unit * I & Functor (snd X) C }.
  Global Identity Coercion LaxCosliceCategory_Object_Id : LaxCosliceCategory_ObjectT >-> sigT.
  Global Coercion sigT_of_LCCO (XG : LaxCosliceCategory_Object)
  : LaxCosliceCategory_ObjectT
    := existT (fun X : unit * I => Functor (snd X) C)
              (tt, LCCO_X XG)
              (LCCO_G XG).
  Global Coercion LCCO_of_sigT (XG : LaxCosliceCategory_ObjectT)
  : LaxCosliceCategory_Object
    := Build_LaxCosliceCategory_Object (projT2 XG).

  Global Arguments LCCO_of_sigT _ / .
  Global Arguments sigT_of_LCCO _ / .

  Lemma LaxCosliceCategory_Object_eq' (x y : LaxCosliceCategory_Object)
  : forall (HX : LCCO_X x = LCCO_X y),
      match HX in _ = X return Functor X C with
        | eq_refl => LCCO_G x
      end = LCCO_G y
      -> x = y.
  Proof.
    destruct x, y; simpl.
    intros; subst; reflexivity.
  Defined.

  Lemma LaxCosliceCategory_Object_eq (x y : LaxCosliceCategory_Object)
  : LCCO_X x = LCCO_X y
    -> LCCO_G x == LCCO_G y
    -> x = y.
  Proof.
    destruct x, y; simpl.
    intros; repeat subst; reflexivity.
  Qed.

  Record LaxCosliceCategory_Morphism (XG X'G' : LaxCosliceCategory_Object) :=
    {
      LCCM_F : Functor (LCCO_X X'G') (LCCO_X XG);
      LCCM_T : NaturalTransformation (LCCO_G XG ∘ LCCM_F)
                                     (LCCO_G X'G')
    }.

  Definition LaxCosliceCategory_MorphismT (XG X'G' : LaxCosliceCategory_ObjectT) :=
    { F : unit * Functor (snd (projT1 X'G')) (snd (projT1 XG)) &
      NaturalTransformation (projT2 XG ∘ snd F) (projT2 X'G')
    }.

  Global Identity Coercion LaxCosliceCategory_Morphism_Id : LaxCosliceCategory_MorphismT >-> sigT.
  Global Coercion sigT_of_LCCM XG X'G' (gh : LaxCosliceCategory_Morphism XG X'G')
  : LaxCosliceCategory_MorphismT XG X'G'
    := existT (fun F : unit * Functor (snd (projT1 X'G')) (snd (projT1 XG))
               => NaturalTransformation (projT2 XG ∘ snd F) (projT2 X'G'))
              (tt, LCCM_F gh)
              (LCCM_T gh).
  Global Coercion LCCM_of_sigT XG X'G' (gh : LaxCosliceCategory_MorphismT XG X'G')
  : LaxCosliceCategory_Morphism XG X'G'
    := @Build_LaxCosliceCategory_Morphism
         XG
         X'G'
         _
         (projT2 gh).

  Global Arguments LCCM_of_sigT _ _ _ / .
  Global Arguments sigT_of_LCCM _ _ _ / .

  Lemma LaxCosliceCategory_Morphism_eq' XG X'G'
        (gh g'h' : LaxCosliceCategory_Morphism XG X'G')
  : forall (HF : LCCM_F gh = LCCM_F g'h'),
      match HF in _ = F return NaturalTransformation (_ ∘ F) _ with
        | eq_refl => LCCM_T gh
      end = LCCM_T g'h'
      -> gh = g'h'.
  Proof.
    destruct gh, g'h'; simpl.
    intros; subst.
    reflexivity.
  Defined.

  Lemma LaxCosliceCategory_Morphism_eq XG X'G'
        (gh g'h' : LaxCosliceCategory_Morphism XG X'G')
  : LCCM_F gh = LCCM_F g'h'
    -> LCCM_T gh == LCCM_T g'h'
    -> gh = g'h'.
  Proof.
    destruct gh, g'h'.
    simpl; intros.
    repeat subst.
    reflexivity.
  Qed.

  Lemma LaxCosliceCategory_Morphism_JMeq XG0 X'G'0 XG1 X'G'1
        (gh : LaxCosliceCategory_Morphism XG0 XG1)
        (g'h' : LaxCosliceCategory_Morphism X'G'0 X'G'1)
  : XG0 = X'G'0
    -> XG1 = X'G'1
    -> LCCM_F gh == LCCM_F g'h'
    -> LCCM_T gh == LCCM_T g'h'
    -> gh == g'h'.
  Proof.
    destruct gh, g'h'; simpl.
    intros; repeat subst.
    reflexivity.
  Qed.

  Definition LaxCosliceCategory_Compose' s d d' (FT : LaxCosliceCategory_Morphism d d') (F'T' : LaxCosliceCategory_Morphism s d)
  : LaxCosliceCategory_Morphism s d'.
    exists (LCCM_F F'T' ∘ LCCM_F FT).
    refine (LCCM_T FT ∘₁ _).
    refine ((LCCM_T F'T' ∘₀ IdentityNaturalTransformation _) ∘₁ _).
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (GeneralizedIdentityNaturalTransformation F G eq_refl eq_refl)
    end.
  Defined.

  Definition LaxCosliceCategory_Compose'' s d d' (FT : LaxCosliceCategory_Morphism d d') (F'T' : LaxCosliceCategory_Morphism s d) :
    LaxCosliceCategory_Morphism s d'.
    simpl_definition_by_tac_and_exact (@LaxCosliceCategory_Compose' s d d' FT F'T') ltac:(unfold LaxCosliceCategory_Compose' in *).
  Defined.

  (* Then we clean up a bit with reduction. *)
  Definition LaxCosliceCategory_Compose s d d' (FT : LaxCosliceCategory_Morphism d d') (F'T' : LaxCosliceCategory_Morphism s d) :
    LaxCosliceCategory_Morphism s d'
    := Eval cbv beta iota zeta delta [LaxCosliceCategory_Compose''] in (@LaxCosliceCategory_Compose'' s d d' FT F'T').

  Global Arguments LaxCosliceCategory_Compose _ _ _ _ _ / .

  Definition LaxCosliceCategory_Identity x : LaxCosliceCategory_Morphism x x.
    exists (IdentityFunctor _).
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (GeneralizedIdentityNaturalTransformation F G eq_refl eq_refl)
    end.
  Defined.

  Global Arguments LaxCosliceCategory_Identity _ / .

  Lemma LaxCosliceCategory_Associativity
  : forall (o1 o2 o3 o4 : LaxCosliceCategory_Object)
           (m1 : LaxCosliceCategory_Morphism o1 o2)
           (m2 : LaxCosliceCategory_Morphism o2 o3)
           (m3 : LaxCosliceCategory_Morphism o3 o4),
      LaxCosliceCategory_Compose (LaxCosliceCategory_Compose m3 m2) m1 =
      LaxCosliceCategory_Compose m3 (LaxCosliceCategory_Compose m2 m1).
  Proof.
    abstract lax_comma_t LaxCosliceCategory_Morphism_eq.
  Qed.

  Lemma LaxCosliceCategory_LeftIdentity
  : forall (a b : LaxCosliceCategory_Object)
           (f : LaxCosliceCategory_Morphism a b),
      LaxCosliceCategory_Compose (LaxCosliceCategory_Identity b) f = f.
  Proof.
    lax_comma_t LaxCosliceCategory_Morphism_eq.

  Qed.

  Lemma LaxCosliceCategory_RightIdentity
  : forall (a b : LaxCosliceCategory_Object)
           (f : LaxCosliceCategory_Morphism a b),
      LaxCosliceCategory_Compose f (LaxCosliceCategory_Identity a) = f.
  Proof.
    abstract lax_comma_t LaxCosliceCategory_Morphism_eq.
  Qed.

  Definition LaxCosliceCategory : Category
    := @Build_Category
         LaxCosliceCategory_Object
         LaxCosliceCategory_Morphism
         LaxCosliceCategory_Identity
         LaxCosliceCategory_Compose
         LaxCosliceCategory_Associativity
         LaxCosliceCategory_LeftIdentity
         LaxCosliceCategory_RightIdentity.
End LaxCosliceCategory.

Hint Unfold LaxCosliceCategory_Compose LaxCosliceCategory_Identity : category.
