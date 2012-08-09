Require Import Setoid FunctionalExtensionality.
Require Export SetCategory DecidableDiscreteCategory.
Require Import Common Limits Functor NaturalTransformation FunctorCategory.

Set Implicit Arguments.

Section SetLimits.
  Local Transparent Object Morphism Identity Compose.

  Variable objC : Set.
  Variable morC : objC -> objC -> Set.
  Variable C : SmallSpecializedCategory morC.
  Variable F : SpecializedFunctor C SetCat.

  (* Quoting David:
     let F:C-->Set be a functor. An element of the limit is a collection of elements x_c,
     one for each c in C, such that under every arrow g: c-->c' in C, x_c is sent to x_{c'}.
     *)
  Definition SetLimit_Object : SetCat * TerminalCategory :=
    (
      { S : forall c : objC, F c | forall c c' (g : C.(Morphism) c c'), F.(MorphismOf) g (S c) = (S c') },
      tt
    ).

  Definition SetLimit_Morphism : SpecializedNaturalTransformation
    ((DiagonalFunctor SetCat C) (fst SetLimit_Object))
    ((SliceCategory_Functor
      (FunctorCategory C SetCat) F) (snd SetLimit_Object)).
    simpl.
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun c : objC => (fun S => (proj1_sig S) c))
          _
        )
    end.
    abstract (
      simpl; intros;
        apply functional_extensionality_dep; intro;
          destruct_sig;
          t_with t'
    ).
  Defined.

  Definition SetLimit_Property_Morphism_mor (o' : @SliceCategory _ (SetCat ^ C) F (DiagonalFunctor SetCat C)) :
    Morphism (SetCat * TerminalCategory) (projT1 o')
    SetLimit_Object.
    refine (
      (fun x : (fst (projT1 o')) => exist _ (fun c : C => ComponentsOf (projT2 o') c x) _),
      tt
    ).
    abstract (
      simpl in *; intros;
        destruct_type @SpecializedNaturalTransformation; simpl in *;
          fg_equal;
          symmetry;
            specialized_assumption idtac
    ).
  Defined.

  Definition SetLimit_Property_Morphism (o' : @SliceCategory _ (SetCat ^ C) F (DiagonalFunctor SetCat C)) :
    Morphism
    (@SliceCategory _ (SetCat ^ C) F (DiagonalFunctor SetCat C)) o'
    (existT _ SetLimit_Object SetLimit_Morphism).
    exists (SetLimit_Property_Morphism_mor _).
    abstract nt_eq.
  Defined.

  Definition SetLimit : Limit F.
    Transparent Object Morphism Compose Identity.
    exists (existT _ SetLimit_Object SetLimit_Morphism).
    hnf; intros.
    exists (SetLimit_Property_Morphism _).
    abstract (
      unfold SetLimit_Property_Morphism, SetLimit_Property_Morphism_mor; simpl in *;
        repeat (hnf in *; intros; simpl in *);
          simpl_eq;
          trivial;
            repeat (apply functional_extensionality_dep; intro; try simpl_eq);
              destruct_sig;
              rewrite LeftIdentityNaturalTransformation in *;
                subst;
                  unfold Morphism;
                    trivial
    ).
  Defined.
End SetLimits.

Section TypeLimits.
  Local Transparent Object Morphism Identity Compose.

  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable F : SpecializedFunctor C TypeCat.

  (* Quoting David:
     let F:C-->Set be a functor. An element of the limit is a collection of elements x_c,
     one for each c in C, such that under every arrow g: c-->c' in C, x_c is sent to x_{c'}.
     *)
  Definition TypeLimit_Object : TypeCat * TerminalCategory :=
    (
      { S : forall c : objC, F c | forall c c' (g : C.(Morphism) c c'), F.(MorphismOf) g (S c) = (S c') },
      tt
    ).

  Definition TypeLimit_Morphism : SpecializedNaturalTransformation
    ((DiagonalFunctor TypeCat C) (fst TypeLimit_Object))
    ((SliceCategory_Functor
      (FunctorCategory C TypeCat) F) (snd TypeLimit_Object)).
    simpl.
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun c : objC => (fun S => (proj1_sig S) c))
          _
        )
    end.
    abstract (
      simpl; intros;
        apply functional_extensionality_dep; intro;
          destruct_sig;
          t_with t'
    ).
  Defined.

  Definition TypeLimit_Property_Morphism_mor (o' : @SliceCategory _ (TypeCat ^ C) F (DiagonalFunctor TypeCat C)) :
    Morphism (TypeCat * TerminalCategory) (projT1 o')
    TypeLimit_Object.
    refine (
      (fun x : (fst (projT1 o')) => exist _ (fun c : C => ComponentsOf (projT2 o') c x) _),
      tt
    ).
    abstract (
      simpl in *; intros;
        destruct_type @SpecializedNaturalTransformation; simpl in *;
          fg_equal;
          symmetry;
            specialized_assumption idtac
    ).
  Defined.

  Definition TypeLimit_Property_Morphism (o' : @SliceCategory _ (TypeCat ^ C) F (DiagonalFunctor TypeCat C)) :
    Morphism
    (@SliceCategory _ (TypeCat ^ C) F (DiagonalFunctor TypeCat C)) o'
    (existT _ TypeLimit_Object TypeLimit_Morphism).
    exists (TypeLimit_Property_Morphism_mor _).
    abstract nt_eq.
  Defined.

  Definition TypeLimit : Limit F.
    Transparent Object Morphism Compose Identity.
    exists (existT _ TypeLimit_Object TypeLimit_Morphism).
    hnf; intros.
    exists (TypeLimit_Property_Morphism _).
    abstract (
      unfold TypeLimit_Property_Morphism, TypeLimit_Property_Morphism_mor; simpl in *;
        repeat (hnf in *; intros; simpl in *);
          simpl_eq;
          trivial;
            repeat (apply functional_extensionality_dep; intro; try simpl_eq);
              destruct_sig;
              rewrite LeftIdentityNaturalTransformation in *;
                subst;
                  unfold Morphism;
                    trivial
    ).
  Defined.
End TypeLimits.
