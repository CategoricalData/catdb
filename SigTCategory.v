Require Import JMeq.
Require Export SpecializedCategory Functor.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Local Infix "==" := JMeq (at level 70).

Section sigT_obj_mor.
  Context `(A : @SpecializedCategory objA morA).
  Variable Pobj : objA -> Type.
  Variable Pmor : forall s d : sigT Pobj, morA (projT1 s) (projT1 d) -> Type.

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

  Hint Resolve Associativity LeftIdentity RightIdentity.

  Definition SpecializedCategory_sigT : @SpecializedCategory (sigT Pobj) (fun s d => sigT (@Pmor s d)).
    match goal with
      | [ |- @SpecializedCategory ?obj ?mor ] =>
        refine (@Build_SpecializedCategory obj mor
          (fun x => existT _ (Identity (C := A) (projT1 x)) (Pidentity x))
          (fun s d d' m1 m2 => existT _ (Compose (C := A) (projT1 m1) (projT1 m2)) (Pcompose (projT2 m1) (projT2 m2)))
          _
          _
          _
        )
    end;
    abstract (intros; simpl_eq; present_spcategory_all; trivial).
  Defined.

  Definition projT1_functor : SpecializedFunctor SpecializedCategory_sigT A.
    refine (Build_SpecializedFunctor SpecializedCategory_sigT A
      (fun x => projT1 x)
      (fun s d m => projT1 m)
      _
      _
    );
    intros; reflexivity.
  Defined.
End sigT_obj_mor.

Arguments projT1_functor {objA morA A Pobj Pmor Pidentity Pcompose P_Associativity P_LeftIdentity P_RightIdentity}.

Section sigT_obj.
  Context `(A : @SpecializedCategory objA morA).
  Variable Pobj : objA -> Type.

  Hint Resolve Associativity LeftIdentity RightIdentity.

  Definition SpecializedCategory_sigT_obj : @SpecializedCategory (sigT Pobj) (fun s d => morA (projT1 s) (projT1 d)).
    match goal with
      | [ |- @SpecializedCategory ?obj ?mor ] =>
        refine (@Build_SpecializedCategory obj mor
          (fun x => Identity (C := A) (projT1 x))
          (fun s d d' m1 m2 => Compose (C := A) m1 m2)
          _
          _
          _
        )
    end;
    abstract (
      intros; destruct_sig; simpl;
        present_spcategory_all;
        trivial
    ).
  Defined.

  Hint Resolve Associativity LeftIdentity RightIdentity.

  Definition projT1_obj_functor : SpecializedFunctor SpecializedCategory_sigT_obj A.
    refine (Build_SpecializedFunctor SpecializedCategory_sigT_obj A
      (fun x => projT1 x)
      (fun s d m => m)
      _
      _
    );
    intros; reflexivity.
  Defined.

  Definition SpecializedCategory_sigT_obj_as_sigT : @SpecializedCategory (sigT Pobj) (fun s d => { _ : Morphism A (projT1 s) (projT1 d) & unit }).
    apply (@SpecializedCategory_sigT _ _ A Pobj (fun _ _ _ => unit) (fun _ => tt) (fun _ _ _ _ _ _ _ => tt));
      abstract (simpl; intros; trivial).
  Defined.

  Definition sigT_functor_obj : SpecializedFunctor SpecializedCategory_sigT_obj_as_sigT SpecializedCategory_sigT_obj.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (@id _)
          (fun _ _ => @projT1 _ _)
          _
          _
        )
    end;
    simpl; intros; reflexivity.
  Defined.

  Definition sigT_functor_obj_inv : SpecializedFunctor SpecializedCategory_sigT_obj SpecializedCategory_sigT_obj_as_sigT.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (@id _)
          (fun _ _ m => existT _ m tt)
          _
          _
        )
    end;
    abstract (simpl; intros; f_equal; trivial).
  Defined.

  Lemma sigT_obj_eq : ComposeFunctors sigT_functor_obj sigT_functor_obj_inv = IdentityFunctor _ /\ ComposeFunctors sigT_functor_obj_inv sigT_functor_obj = IdentityFunctor _.
    Local Transparent Morphism.
    split; functor_eq; simpl_eq; trivial.
  Qed.

  Lemma sigT_obj_compat : ComposeFunctors projT1_obj_functor sigT_functor_obj = projT1_functor.
    functor_eq.
  Qed.
End sigT_obj.

Arguments projT1_obj_functor {objA morA A Pobj}.

Section sigT_mor.
  Context `(A : @SpecializedCategory objA morA).
  Variable Pmor : forall s d, morA s d -> Type.

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

  Hint Resolve Associativity LeftIdentity RightIdentity.

  Definition SpecializedCategory_sigT_mor : @SpecializedCategory objA (fun s d => sigT (@Pmor s d)).
    match goal with
      | [ |- @SpecializedCategory ?obj ?mor ] =>
        refine (@Build_SpecializedCategory obj mor
          (fun x => existT _ (Identity (C := A) x) (Pidentity x))
          (fun s d d' m1 m2 => existT _ (Compose (C := A) (projT1 m1) (projT1 m2)) (Pcompose (projT2 m1) (projT2 m2)))
          _
          _
          _
        )
    end;
    abstract (intros; simpl_eq; present_spcategory_all; trivial).
  Defined.

  Definition projT1_mor_functor : SpecializedFunctor SpecializedCategory_sigT_mor A.
    refine (Build_SpecializedFunctor SpecializedCategory_sigT_mor A
      (fun x => x)
      (fun s d m => projT1 m)
      _
      _
    );
    intros; reflexivity.
  Defined.

  Definition SpecializedCategory_sigT_mor_as_sigT : @SpecializedCategory (sigT (fun _ : objA => unit)) (fun s d => sigT (@Pmor (projT1 s) (projT1 d))).
    apply (@SpecializedCategory_sigT _ _ A _ (fun s d => @Pmor (projT1 s) (projT1 d)) (fun _ => Pidentity _) (fun _ _ _ _ _ m1 m2 => Pcompose m1 m2));
      abstract (intros; trivial).
  Defined.

  Definition sigT_functor_mor : SpecializedFunctor SpecializedCategory_sigT_mor_as_sigT SpecializedCategory_sigT_mor.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (@projT1 _ _)
          (fun _ _ => @id _)
          _
          _
        )
    end;
    simpl; intros; reflexivity.
  Defined.

  Definition sigT_functor_mor_inv : SpecializedFunctor SpecializedCategory_sigT_mor SpecializedCategory_sigT_mor_as_sigT.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (fun x => existT _ x tt)
          (fun _ _  => @id _)
          _
          _
        )
    end;
    abstract (simpl; intros; f_equal; trivial).
  Defined.

  Lemma sigT_mor_eq : ComposeFunctors sigT_functor_mor sigT_functor_mor_inv = IdentityFunctor _ /\ ComposeFunctors sigT_functor_mor_inv sigT_functor_mor = IdentityFunctor _.
    Local Transparent Object.
    split; functor_eq; simpl_eq; trivial.
  Qed.

  Lemma sigT_mor_compat : ComposeFunctors projT1_mor_functor sigT_functor_mor = projT1_functor.
    functor_eq.
  Qed.
End sigT_mor.

Arguments projT1_mor_functor {objA morA A Pmor Pidentity Pcompose P_Associativity P_LeftIdentity P_RightIdentity}.
