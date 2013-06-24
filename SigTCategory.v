Require Import FunctionalExtensionality JMeq.
Require Export Category Functor.
Require Import Common Notations FunctorAttributes FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Local Ltac faithful_t :=
  repeat (unfold Object in *; simpl in *; subst;
          match goal with
            | _ => intro
            | _ => progress trivial
            | [ |- _ = _ ] => (apply functional_extensionality_dep; intro)
            | _ => progress simpl_eq
            | [ H : _ = _ |- _ ] => fg_equal_in H
            (*| [ |- projT2 ?a == projT2 ?b ] =>
              (cut (projT1 a = projT1 b); [ (*generalize a b*) | faithful_t ](*;
               intros [] [] ?*))*)
            | _ => progress JMeq_eq
          end).

Section sigT_obj_mor.
  Variable A : Category.
  Variable Pobj : A -> Type.
  Variable Pmor : forall s d : sigT Pobj, A.(Morphism) (projT1 s) (projT1 d) -> Type.

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

  Definition Category_sigT : Category.
    refine (@Build_Category
              (sigT Pobj)
              (fun s d => sigT (@Pmor s d))
              (fun x => existT _ (Identity (C := A) (projT1 x)) (Pidentity x))
              (fun s d d' m1 m2 => existT _ (Compose (C := A) (projT1 m1) (projT1 m2)) (Pcompose (projT2 m1) (projT2 m2)))
              _
              _
              _
           );
    abstract (intros; simpl_eq; auto with category).
  Defined.

  Definition projT1_functor : Functor Category_sigT A
    := Build_Functor Category_sigT A
                                (@projT1 _ _)
                                (fun _ _ => @projT1 _ _)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).
End sigT_obj_mor.

Arguments projT1_functor {A Pobj Pmor Pidentity Pcompose P_Associativity P_LeftIdentity P_RightIdentity}.

Section sigT_obj.
  Variable A : Category.
  Variable Pobj : A -> Type.

  Definition Category_sigT_obj : Category.
    refine (@Build_Category
              (sigT Pobj)
              (fun s d => A.(Morphism) (projT1 s) (projT1 d))
              (fun x => Identity (C := A) (projT1 x))
              (fun s d d' m1 m2 => Compose (C := A) m1 m2)
              _
              _
              _
           );
    abstract (intros; destruct_sig; simpl; auto with category).
  Defined.

  Definition projT1_obj_functor : Functor Category_sigT_obj A
    := Build_Functor Category_sigT_obj A
                                (@projT1 _ _)
                                (fun s d m => m)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Definition Category_sigT_obj_as_sigT : Category.
    refine (@Category_sigT A Pobj (fun _ _ _ => unit) (fun _ => tt) (fun _ _ _ _ _ _ _ => tt) _ _ _);
    abstract (simpl; intros; trivial).
  Defined.

  Definition sigT_functor_obj : Functor Category_sigT_obj_as_sigT Category_sigT_obj
    := Build_Functor Category_sigT_obj_as_sigT Category_sigT_obj
                                (fun x => x)
                                (fun _ _ => @projT1 _ _)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Definition sigT_functor_obj_inv : Functor Category_sigT_obj Category_sigT_obj_as_sigT
    := Build_Functor Category_sigT_obj Category_sigT_obj_as_sigT
                                (fun x => x)
                                (fun _ _ m => existT _ m tt)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Lemma sigT_obj_eq : ComposeFunctors sigT_functor_obj sigT_functor_obj_inv = IdentityFunctor _ /\ ComposeFunctors sigT_functor_obj_inv sigT_functor_obj = IdentityFunctor _.
    split; functor_eq; hnf in *; destruct_type @sigT; f_equal; trivial.
  Qed.

  Lemma sigT_obj_compat : ComposeFunctors projT1_obj_functor sigT_functor_obj = projT1_functor.
    functor_eq.
  Qed.
End sigT_obj.

Arguments projT1_obj_functor {A Pobj}.

Section sigT_mor.
  Variable A : Category.
  Variable Pmor : forall s d, A.(Morphism) s d -> Type.

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

  Definition Category_sigT_mor : Category.
    refine (@Build_Category
              _
              (fun s d => sigT (@Pmor s d))
              (fun x => existT _ (Identity (C := A) x) (Pidentity x))
              (fun s d d' m1 m2 => existT _ (Compose (C := A) (projT1 m1) (projT1 m2)) (Pcompose (projT2 m1) (projT2 m2)))
              _
              _
              _
           );
    abstract (intros; simpl_eq; auto with category).
  Defined.

  Definition projT1_mor_functor : Functor Category_sigT_mor A.
    refine (Build_Functor Category_sigT_mor A
      (fun x => x)
      (fun s d m => projT1 m)
      _
      _
    );
    intros; reflexivity.
  Defined.

  Definition Category_sigT_mor_as_sigT : Category.
    apply (@Category_sigT A (fun _ => unit) (fun s d => @Pmor (projT1 s) (projT1 d)) (fun _ => Pidentity _) (fun _ _ _ _ _ m1 m2 => Pcompose m1 m2));
      abstract (intros; trivial).
  Defined.

  Definition sigT_functor_mor : Functor Category_sigT_mor_as_sigT Category_sigT_mor.
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor C D
          (@projT1 _ _)
          (fun _ _ => @id _)
          _
          _
        )
    end;
    simpl; intros; reflexivity.
  Defined.

  Definition sigT_functor_mor_inv : Functor Category_sigT_mor Category_sigT_mor_as_sigT.
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor C D
          (fun x => existT _ x tt)
          (fun _ _  => @id _)
          _
          _
        )
    end;
    abstract (simpl; intros; f_equal; trivial).
  Defined.

  Lemma sigT_mor_eq : ComposeFunctors sigT_functor_mor sigT_functor_mor_inv = IdentityFunctor _ /\ ComposeFunctors sigT_functor_mor_inv sigT_functor_mor = IdentityFunctor _.
    split; functor_eq; simpl_eq; trivial.
  Qed.

  Lemma sigT_mor_compat : ComposeFunctors projT1_mor_functor sigT_functor_mor = projT1_functor.
    functor_eq.
  Qed.
End sigT_mor.

Arguments projT1_mor_functor {A Pmor Pidentity Pcompose P_Associativity P_LeftIdentity P_RightIdentity}.
