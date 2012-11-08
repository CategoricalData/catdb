Require Import JMeq.
Require Export SpecializedCategory Functor SigTCategory.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Local Infix "==" := JMeq.

Section sig_sigT_obj_mor.
  Context `(A : @SpecializedCategory objA).
  Variable Pobj : objA -> Prop.
  Variable Pmor : forall s d : sig Pobj, A.(Morphism) (proj1_sig s) (proj1_sig d) -> Type.

  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d', forall m1 m2, @Pmor d d' m1 -> @Pmor s d m2 -> @Pmor s d' (Compose (C := A) m1 m2).

  Hypothesis P_Associativity : forall o1 o2 o3 o4 m1 m2 m3 m1' m2' m3',
    @Pcompose o1 o2 o4 _ m1 (@Pcompose o2 o3 o4 m3 m2 m3' m2') m1' ==
    @Pcompose o1 o3 o4 m3 _ m3' (@Pcompose o1 o2 o3 m2 m1 m2' m1').

  Hypothesis P_LeftIdentity : forall a b f f',
    @Pcompose a b b _ f (@Pidentity b) f' ==
    f'.

  Hypothesis P_RightIdentity : forall a b f f',
    @Pcompose a a b f _ f' (@Pidentity a) ==
    f'.

  Definition SpecializedCategory_sig_sigT : @SpecializedCategory (sig Pobj).
    match goal with
      | [ |- @SpecializedCategory ?obj ] =>
        refine (@Build_SpecializedCategory obj
          (fun s d => sigT (@Pmor s d))
          (fun x => existT _ (Identity (C := A) (proj1_sig x)) (Pidentity x))
          (fun s d d' m1 m2 => existT _ (Compose (C := A) (projT1 m1) (projT1 m2)) (Pcompose (projT2 m1) (projT2 m2)))
          _
          _
          _
        )
    end;
    abstract (intros; simpl_eq; auto with category).
  Defined.

  Let sig_of_sigT' (A : Type) (P : A -> Prop) (X : sigT P) := exist P (projT1 X) (projT2 X).
  Let sigT_of_sig' (A : Type) (P : A -> Prop) (X : sig P) := existT P (proj1_sig X) (proj2_sig X).

  Let Pmor' (s d : sigT Pobj) : A.(Morphism) (projT1 s) (projT1 d) -> Type := @Pmor (sig_of_sigT' s) (sig_of_sigT' d).
  Let Pidentity' x : @Pmor' x x (Identity (C := A) _) := Pidentity (sig_of_sigT' x).
  Let Pcompose' s d d' : forall m1 m2, @Pmor' d d' m1 -> @Pmor' s d m2 -> @Pmor' s d' (Compose (C := A) m1 m2)
    := @Pcompose (sig_of_sigT' s) (sig_of_sigT' d) (sig_of_sigT' d').
  Let P_Associativity' o1 o2 o3 o4 m1 m2 m3 m1' m2' m3' :
    @Pcompose' o1 o2 o4 _ m1 (@Pcompose' o2 o3 o4 m3 m2 m3' m2') m1' ==
    @Pcompose' o1 o3 o4 m3 _ m3' (@Pcompose' o1 o2 o3 m2 m1 m2' m1')
    := P_Associativity m1' m2' m3'.
  Let P_LeftIdentity' a b f f' :
    @Pcompose' a b b _ f (@Pidentity' b) f' ==
    f'
    := P_LeftIdentity f'.
  Let P_RightIdentity' a b f f' :
    @Pcompose' a a b f _ f' (@Pidentity' a) ==
    f'
    := P_RightIdentity f'.

  Let SpecializedCategory_sig_sigT_as_sigT : @SpecializedCategory (sigT Pobj).
    eapply (@SpecializedCategory_sigT _ A
      Pobj
      Pmor'
      Pidentity'
      Pcompose'
    );
    trivial.
  Defined.

  Definition sig_sigT_functor_sigT_MorphismOf (s d  : {x | Pobj x}) (m : sigT (Pmor s d)) : sigT (Pmor' s d).
    subst_body; destruct s, d; simpl in *; eta_red; exact m.
  Defined.

  Definition sig_sigT_functor_sigT : SpecializedFunctor SpecializedCategory_sig_sigT SpecializedCategory_sig_sigT_as_sigT.
    refine (Build_SpecializedFunctor SpecializedCategory_sig_sigT SpecializedCategory_sig_sigT_as_sigT
      (fun x => x)
      (@sig_sigT_functor_sigT_MorphismOf)
      _
      _
    );
    abstract (intros; simpl; destruct_sig; reflexivity).
  Defined.

  Definition sigT_functor_sig_sigT_MorphismOf (s d : sigT Pobj) (m : sigT (Pmor' s d)) : sigT (Pmor s d).
    subst_body; destruct s, d; simpl in *; eta_red; exact m.
  Defined.

  Definition sigT_functor_sig_sigT : SpecializedFunctor SpecializedCategory_sig_sigT_as_sigT SpecializedCategory_sig_sigT.
    refine (Build_SpecializedFunctor SpecializedCategory_sig_sigT_as_sigT SpecializedCategory_sig_sigT
      (fun x => x)
      (@sigT_functor_sig_sigT_MorphismOf)
      _
      _
    );
    abstract (intros; simpl; destruct_sig; reflexivity).
  Defined.

  Lemma sig_sigT_sigT_compat :
    ComposeFunctors sig_sigT_functor_sigT sigT_functor_sig_sigT = IdentityFunctor _ /\
    ComposeFunctors sigT_functor_sig_sigT sig_sigT_functor_sigT = IdentityFunctor _.
    split; functor_eq; destruct_sig; reflexivity.
  Qed.

  Definition proj1_functor_sig_sigT : SpecializedFunctor SpecializedCategory_sig_sigT A
    := ComposeFunctors projT1_functor sig_sigT_functor_sigT.
End sig_sigT_obj_mor.
