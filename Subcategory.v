Require Export SpecializedCategory.
Require Import Common.

Set Implicit Arguments.

Local Transparent Object Morphism.

Section Subcategory.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Variable Pobj : objC -> Prop.
  Let obj := sig Pobj.
  Let obj2objC (x : obj) := proj1_sig x.
  Local Coercion obj2objC : obj >-> objC.

  Variable Pmor : forall s d : obj, morC s d -> Prop.

  Let mor (s d : obj) := sig (Pmor s d).
  Let mor2morC s d (m : mor s d) := proj1_sig m.
  Local Coercion mor2morC : mor >-> morC.

  Hypothesis Pmor_compose : forall s d d' (m1 : mor d d') (m2 : mor s d), Pmor _ _ (Compose (C := C) m1 m2).
  Hypothesis Pmor_identity : forall x : obj, Pmor _ _ (Identity (C := C) x).

  Definition Subcategory_Compose s d d'(m1 : mor d d') (m2 : mor s d) : mor s d'
    := exist _ (Compose (C := C) m1 m2) (Pmor_compose _ _).

  Definition Subcategory_Identity x : mor x x
    := exist _ (Identity (C := C) x) (Pmor_identity _).

  Definition Subcategory : @SpecializedCategory obj mor.
    refine {| Compose' := @Subcategory_Compose;
      Identity' := @Subcategory_Identity
    |};
    abstract (
      intros; unfold Subcategory_Compose, Subcategory_Identity;
        simpl_eq;
        t_with t'
    ).
  Defined.
End Subcategory.

Section FullSubcategory.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Variable Pobj : objC -> Prop.
  Let obj := sig Pobj.
  Let obj2objC (x : obj) := proj1_sig x.
  Local Coercion obj2objC : obj >-> objC.

  Let Pmor (s d : obj) (_ : morC s d) := True.

  Definition FullSubcategory' := Subcategory C Pmor (fun _ _ _ _ _ => I) (fun _ => I).

  Definition FullSubcategory : @SpecializedCategory obj (fun s d => morC s d).
    refine (@Build_SpecializedCategory obj (fun s d => morC s d)
      (fun x => proj1_sig (FullSubcategory'.(Identity') x))
      (fun s d d' m1 m2 => proj1_sig (FullSubcategory'.(Compose') _ _ _ (exist _ m1 I) (exist _ m2 I)))
      _
      _
      _
    );
    subst_body;
    abstract (intros; simpl; t_with t').
  Defined.
End FullSubcategory.

Section WideSubcategory.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Let Pobj := (fun _ : objC => True).
  Let obj := sig Pobj.
  Let obj2objC (x : obj) := proj1_sig x.
  Local Coercion obj2objC : obj >-> objC.

  Variable Pmor : forall s d : objC, morC s d -> Prop.
  Let Pmor' : forall s d : obj, morC s d -> Prop := Pmor.

  Let mor (s d : objC) := sig (@Pmor s d).
  Let mor2morC s d (m : mor s d) := proj1_sig m.
  Local Coercion mor2morC : mor >-> morC.

  Let mor' (s d : obj) := sig (@Pmor' s d).
  Let mor'2morC s d (m : mor' s d) := proj1_sig m.
  Local Coercion mor'2morC : mor' >-> morC.

  Hypothesis Pmor_compose : forall s d d' (m1 : mor d d') (m2 : mor s d), Pmor (Compose (C := C) m1 m2).
  Hypothesis Pmor_identity : forall x : objC, Pmor (Identity (C := C) x).

  Let Pmor_compose' : forall s d d' (m1 : mor' d d') (m2 : mor' s d), Pmor' _ _ (Compose (C := C) m1 m2) := Pmor_compose.
  Let Pmor_identity' : forall x : obj, Pmor' _ _ (Identity (C := C) x) := Pmor_identity.

  Definition WideSubcategory' := Subcategory C Pmor' Pmor_compose' Pmor_identity'.

  Definition WideSubcategory : @SpecializedCategory obj mor'.
    refine (@Build_SpecializedCategory obj mor'
      (fun x => WideSubcategory'.(Identity') x)
      (fun s d d' m1 m2 => WideSubcategory'.(Compose') _ _ _ m1 m2)
      _
      _
      _
    );
    subst_body;
    abstract (intros; autorewrite with core; reflexivity).
  Defined.
End WideSubcategory.
