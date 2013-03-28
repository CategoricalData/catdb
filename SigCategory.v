Require Import JMeq FunctionalExtensionality.
Require Export SpecializedCategory Functor.
Require Import Common Notations FunctorAttributes.

Set Implicit Arguments.

Generalizable All Variables.

Local Infix "==" := JMeq.

Local Ltac faithful_t :=
  repeat (unfold Object in *; simpl in *;
          match goal with
            | _ => intro
            | _ => progress trivial
            | [ |- _ = _ ] => (apply functional_extensionality_dep; intro)
            | _ => progress simpl_eq
            | [ H : _ = _ |- _ ] => fg_equal_in H
          end).

Section sig_obj_mor.
  Context `(A : @SpecializedCategory objA).
  Variable Pobj : objA -> Prop.
  Variable Pmor : forall s d : sig Pobj, A.(Morphism) (proj1_sig s) (proj1_sig d) -> Prop.
  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d', forall m1 m2, @Pmor d d' m1 -> @Pmor s d m2 -> @Pmor s d' (Compose (C := A) m1 m2).

  Definition SpecializedCategory_sig : @SpecializedCategory (sig Pobj).
    match goal with
      | [ |- @SpecializedCategory ?obj ] =>
        refine (@Build_SpecializedCategory obj
          (fun s d => sig (@Pmor s d))
          (fun x => exist _ _ (Pidentity x))
          (fun s d d' m1 m2 => exist _ _ (Pcompose (proj2_sig m1) (proj2_sig m2)))
          _
          _
          _
        )
    end;
    abstract (intros; simpl_eq; auto with category).
  Defined.

  Definition proj1_sig_functor : SpecializedFunctor SpecializedCategory_sig A
    := Build_SpecializedFunctor SpecializedCategory_sig A
                                (@proj1_sig _ _)
                                (fun s d => @proj1_sig _ _)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Lemma proj1_sig_functor_faithful : FunctorFaithful proj1_sig_functor.
    faithful_t.
  Qed.
End sig_obj_mor.

Arguments proj1_sig_functor {objA A Pobj Pmor Pidentity Pcompose}.

Section sig_obj.
  Context `(A : @SpecializedCategory objA).
  Variable Pobj : objA -> Prop.

  Definition SpecializedCategory_sig_obj : @SpecializedCategory (sig Pobj).
    match goal with
      | [ |- @SpecializedCategory ?obj ] =>
        refine (@Build_SpecializedCategory obj
          (fun s d => A.(Morphism) (proj1_sig s) (proj1_sig d))
          (fun x => Identity (C := A) (proj1_sig x))
          (fun s d d' m1 m2 => Compose (C := A) m1 m2)
          _
          _
          _
        )
    end;
    abstract (intros; destruct_sig; simpl; auto with category).
  Defined.

  Definition proj1_sig_obj_functor : SpecializedFunctor SpecializedCategory_sig_obj A
    := Build_SpecializedFunctor SpecializedCategory_sig_obj A
                                (@proj1_sig _ _)
                                (fun s d m => m)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Definition SpecializedCategory_sig_obj_as_sig : @SpecializedCategory (sig Pobj)
    := @SpecializedCategory_sig _ A Pobj (fun _ _ _ => True) (fun _ => I) (fun _ _ _ _ _ _ _ => I).

  Definition sig_functor_obj : SpecializedFunctor SpecializedCategory_sig_obj_as_sig SpecializedCategory_sig_obj
    := Build_SpecializedFunctor SpecializedCategory_sig_obj_as_sig SpecializedCategory_sig_obj
                                (fun x => x)
                                (fun _ _ => @proj1_sig _ _)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Definition sig_functor_obj_inv : SpecializedFunctor SpecializedCategory_sig_obj SpecializedCategory_sig_obj_as_sig
    := Build_SpecializedFunctor SpecializedCategory_sig_obj SpecializedCategory_sig_obj_as_sig
                                (fun x => x)
                                (fun _ _ m => exist _ m I)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Lemma sig_obj_eq : ComposeFunctors sig_functor_obj sig_functor_obj_inv = IdentityFunctor _ /\ ComposeFunctors sig_functor_obj_inv sig_functor_obj = IdentityFunctor _.
    split; functor_eq; destruct_sig; destruct_head True; reflexivity.
  Qed.

  Lemma sig_obj_compat : ComposeFunctors proj1_sig_obj_functor sig_functor_obj = proj1_sig_functor.
    functor_eq.
  Qed.

  Lemma proj1_sig_obj_functor_faithful : FunctorFaithful proj1_sig_obj_functor.
    faithful_t.
  Qed.
End sig_obj.

Arguments proj1_sig_obj_functor {objA A Pobj}.

Section sig_mor.
  Context `(A : @SpecializedCategory objA).
  Variable Pmor : forall s d, A.(Morphism) s d -> Prop.

  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d', forall m1 m2, @Pmor d d' m1 -> @Pmor s d m2 -> @Pmor s d' (Compose (C := A) m1 m2).

  Definition SpecializedCategory_sig_mor : @SpecializedCategory objA.
    match goal with
      | [ |- @SpecializedCategory ?obj ] =>
        refine (@Build_SpecializedCategory obj
          (fun s d => sig (@Pmor s d))
          (fun x => exist _ (Identity (C := A) x) (Pidentity x))
          (fun s d d' m1 m2 => exist _ (Compose (proj1_sig m1) (proj1_sig m2)) (Pcompose (proj2_sig m1) (proj2_sig m2)))
          _
          _
          _
        )
    end;
    abstract (intros; simpl_eq; auto with category).
  Defined.

  Definition proj1_sig_mor_functor : SpecializedFunctor SpecializedCategory_sig_mor A
    := Build_SpecializedFunctor SpecializedCategory_sig_mor A
                                (fun x => x)
                                (fun s d => @proj1_sig _ _)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Definition SpecializedCategory_sig_mor_as_sig : @SpecializedCategory (sig (fun _ : objA => True))
    := @SpecializedCategory_sig _ A _ (fun s d => @Pmor (proj1_sig s) (proj1_sig d)) (fun _ => Pidentity _) (fun _ _ _ _ _ m1 m2 => Pcompose m1 m2).

  Definition sig_functor_mor : SpecializedFunctor SpecializedCategory_sig_mor_as_sig SpecializedCategory_sig_mor
    := Build_SpecializedFunctor SpecializedCategory_sig_mor_as_sig SpecializedCategory_sig_mor
                                (@proj1_sig _ _)
                                (fun _ _ m => m)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Definition sig_functor_mor_inv : SpecializedFunctor SpecializedCategory_sig_mor SpecializedCategory_sig_mor_as_sig
    := Build_SpecializedFunctor SpecializedCategory_sig_mor SpecializedCategory_sig_mor_as_sig
                                (fun x => exist _ x I)
                                (fun _ _ m => m)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Lemma sig_mor_eq : ComposeFunctors sig_functor_mor sig_functor_mor_inv = IdentityFunctor _ /\ ComposeFunctors sig_functor_mor_inv sig_functor_mor = IdentityFunctor _.
    split; functor_eq; destruct_sig; destruct_head True; reflexivity.
  Qed.

  Lemma sig_mor_compat : ComposeFunctors proj1_sig_mor_functor sig_functor_mor = proj1_sig_functor.
    functor_eq.
  Qed.

  Lemma proj1_sig_mor_functor_faithful : FunctorFaithful proj1_sig_mor_functor.
    faithful_t.
  Qed.
End sig_mor.

Arguments proj1_sig_mor_functor {objA A Pmor Pidentity Pcompose}.
