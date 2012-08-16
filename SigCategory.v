Require Import JMeq.
Require Export SpecializedCategory Functor.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Local Infix "==" := JMeq.

Section sig_obj_mor.
  Context `(A : @SpecializedCategory objA morA).
  Variable Pobj : objA -> Prop.
  Variable Pmor : forall s d : sig Pobj, morA (proj1_sig s) (proj1_sig d) -> Prop.

  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d', forall m1 m2, @Pmor d d' m1 -> @Pmor s d m2 -> @Pmor s d' (Compose (C := A) m1 m2).

  Hint Resolve Associativity LeftIdentity RightIdentity.

  Definition SpecializedCategory_sig : @SpecializedCategory (sig Pobj) (fun s d => sig (@Pmor s d)).
    match goal with
      | [ |- @SpecializedCategory ?obj ?mor ] =>
        refine (@Build_SpecializedCategory obj mor
          (fun x => exist _ (Identity (C := A) (proj1_sig x)) (Pidentity x))
          (fun s d d' m1 m2 => exist _ (Compose (proj1_sig m1) (proj1_sig m2)) (Pcompose (proj2_sig m1) (proj2_sig m2)))
          _
          _
          _
        )
    end;
    abstract (intros; simpl_eq; present_spcategory_all; trivial).
  Defined.

  Definition proj1_sig_functor : SpecializedFunctor SpecializedCategory_sig A.
    refine (Build_SpecializedFunctor SpecializedCategory_sig A
      (fun x => proj1_sig x)
      (fun s d m => proj1_sig m)
      _
      _
    );
    intros; reflexivity.
  Defined.
End sig_obj_mor.

Arguments proj1_sig_functor {objA morA A Pobj Pmor Pidentity Pcompose}.

Section sig_obj.
  Context `(A : @SpecializedCategory objA morA).
  Variable Pobj : objA -> Prop.

  Hint Resolve Associativity LeftIdentity RightIdentity.

  Definition SpecializedCategory_sig_obj : @SpecializedCategory (sig Pobj) (fun s d => morA (proj1_sig s) (proj1_sig d)).
    match goal with
      | [ |- @SpecializedCategory ?obj ?mor ] =>
        refine (@Build_SpecializedCategory obj mor
          (fun x => Identity (C := A) (proj1_sig x))
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

  Definition proj1_sig_obj_functor : SpecializedFunctor SpecializedCategory_sig_obj A.
    refine (Build_SpecializedFunctor SpecializedCategory_sig_obj A
      (fun x => proj1_sig x)
      (fun s d m => m)
      _
      _
    );
    intros; reflexivity.
  Defined.

  Definition SpecializedCategory_sig_obj_as_sig : @SpecializedCategory (sig Pobj) (fun s d => { _ : morA (proj1_sig s) (proj1_sig d) | True }).
    apply (@SpecializedCategory_sig _ _ A Pobj (fun _ _ _ => True) (fun _ => I) (fun _ _ _ _ _ _ _ => I));
      abstract (simpl; intros; trivial).
  Defined.

  Definition sig_functor_obj : SpecializedFunctor SpecializedCategory_sig_obj_as_sig SpecializedCategory_sig_obj.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (@id _)
          (fun _ _ => @proj1_sig _ _)
          _
          _
        )
    end;
    simpl; intros; reflexivity.
  Defined.

  Definition sig_functor_obj_inv : SpecializedFunctor SpecializedCategory_sig_obj SpecializedCategory_sig_obj_as_sig.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (@id _)
          (fun _ _ m => exist _ m I)
          _
          _
        )
    end;
    abstract (simpl; intros; f_equal; trivial).
  Defined.

  Lemma sig_obj_eq : ComposeFunctors sig_functor_obj sig_functor_obj_inv = IdentityFunctor _ /\ ComposeFunctors sig_functor_obj_inv sig_functor_obj = IdentityFunctor _.
    split; functor_eq; simpl_eq; trivial.
  Qed.

  Lemma sig_obj_compat : ComposeFunctors proj1_sig_obj_functor sig_functor_obj = proj1_sig_functor.
    functor_eq.
  Qed.
End sig_obj.

Arguments proj1_sig_obj_functor {objA morA A Pobj}.

Section sig_mor.
  Context `(A : @SpecializedCategory objA morA).
  Variable Pmor : forall s d, morA s d -> Prop.

  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d', forall m1 m2, @Pmor d d' m1 -> @Pmor s d m2 -> @Pmor s d' (Compose (C := A) m1 m2).

  Hint Resolve Associativity LeftIdentity RightIdentity.

  Definition SpecializedCategory_sig_mor : @SpecializedCategory objA (fun s d => sig (@Pmor s d)).
    match goal with
      | [ |- @SpecializedCategory ?obj ?mor ] =>
        refine (@Build_SpecializedCategory obj mor
          (fun x => exist _ (Identity (C := A) x) (Pidentity x))
          (fun s d d' m1 m2 => exist _ (Compose (proj1_sig m1) (proj1_sig m2)) (Pcompose (proj2_sig m1) (proj2_sig m2)))
          _
          _
          _
        )
    end;
    abstract (intros; simpl_eq; present_spcategory_all; trivial).
  Defined.

  Definition proj1_sig_mor_functor : SpecializedFunctor SpecializedCategory_sig_mor A.
    refine (Build_SpecializedFunctor SpecializedCategory_sig_mor A
      (fun x => x)
      (fun s d m => proj1_sig m)
      _
      _
    );
    intros; reflexivity.
  Defined.

  Definition SpecializedCategory_sig_mor_as_sig : @SpecializedCategory (sig (fun _ : objA => True)) (fun s d => sig (@Pmor (proj1_sig s) (proj1_sig d))).
    apply (@SpecializedCategory_sig _ _ A _ (fun s d => @Pmor (proj1_sig s) (proj1_sig d)) (fun _ => Pidentity _) (fun _ _ _ _ _ m1 m2 => Pcompose m1 m2));
      abstract (intros; trivial).
  Defined.

  Definition sig_functor_mor : SpecializedFunctor SpecializedCategory_sig_mor_as_sig SpecializedCategory_sig_mor.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (@proj1_sig _ _)
          (fun _ _ => @id _)
          _
          _
        )
    end;
    simpl; intros; reflexivity.
  Defined.

  Definition sig_functor_mor_inv : SpecializedFunctor SpecializedCategory_sig_mor SpecializedCategory_sig_mor_as_sig.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (fun x => exist _ x I)
          (fun _ _  => @id _)
          _
          _
        )
    end;
    abstract (simpl; intros; f_equal; trivial).
  Defined.

  Lemma sig_mor_eq : ComposeFunctors sig_functor_mor sig_functor_mor_inv = IdentityFunctor _ /\ ComposeFunctors sig_functor_mor_inv sig_functor_mor = IdentityFunctor _.
    split; functor_eq; simpl_eq; trivial.
  Qed.

  Lemma sig_mor_compat : ComposeFunctors proj1_sig_mor_functor sig_functor_mor = proj1_sig_functor.
    functor_eq.
  Qed.
End sig_mor.

Arguments proj1_sig_mor_functor {objA morA A Pmor Pidentity Pcompose}.
