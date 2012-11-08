Require Export SpecializedCategory.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Section Subcategory.
  Context `(C : @SpecializedCategory objC).

  Variable Pobj : objC -> Prop.
  Let obj := sig Pobj.
  Let obj2objC (x : obj) := proj1_sig x.
  Local Coercion obj2objC : obj >-> objC.

  Variable Pmor : forall s d : obj, C.(Morphism) s d -> Prop.

  Let mor (s d : obj) := sig (Pmor s d).
  Let mor2morC s d (m : mor s d) := proj1_sig m.
  Local Coercion mor2morC : mor >-> Morphism.

  Hypothesis Pmor_compose : forall s d d' (m1 : mor d d') (m2 : mor s d), Pmor _ _ (Compose (C := C) m1 m2).
  Hypothesis Pmor_identity : forall x : obj, Pmor _ _ (Identity (C := C) x).

  Definition Subcategory_Compose s d d'(m1 : mor d d') (m2 : mor s d) : mor s d'
    := exist _ (Compose (C := C) m1 m2) (Pmor_compose _ _).

  Definition Subcategory_Identity x : mor x x
    := exist _ (Identity (C := C) x) (Pmor_identity _).

  Definition Subcategory : @SpecializedCategory obj.
    refine {|
      Morphism' := mor;
      Compose' := @Subcategory_Compose;
      Identity' := @Subcategory_Identity
    |};
    abstract (
        intros; unfold Subcategory_Compose, Subcategory_Identity;
        simpl_eq;
        auto with morphism
      ).
  Defined.
End Subcategory.

Section FullSubcategory.
  Context `(C : @SpecializedCategory objC).

  Variable Pobj : objC -> Prop.
  Let obj := sig Pobj.
  Let obj2objC (x : obj) := proj1_sig x.
  Local Coercion obj2objC : obj >-> objC.

  Let Pmor (s d : obj) (_ : C.(Morphism) s d) := True.

  Definition FullSubcategory' := Subcategory C Pmor (fun _ _ _ _ _ => I) (fun _ => I).

  Definition FullSubcategory : @SpecializedCategory obj.
    refine (@Build_SpecializedCategory obj (fun s d => C.(Morphism) s d)
      (fun x => proj1_sig (FullSubcategory'.(Identity') x))
      (fun s d d' m1 m2 => proj1_sig (FullSubcategory'.(Compose') _ _ _ (exist _ m1 I) (exist _ m2 I)))
      _
      _
      _
    );
    subst_body;
    abstract (intros; simpl; auto with morphism).
  Defined.
End FullSubcategory.

Section WideSubcategory.
  Context `(C : @SpecializedCategory objC).

  Let Pobj := (fun _ : objC => True).
  Let obj := sig Pobj.
  Let obj2objC (x : obj) := proj1_sig x.
  Local Coercion obj2objC : obj >-> objC.

  Variable Pmor : forall s d : objC, C.(Morphism) s d -> Prop.
  Let Pmor' : forall s d : obj, C.(Morphism) s d -> Prop := Pmor.

  Let mor (s d : objC) := sig (@Pmor s d).
  Let mor2morC s d (m : mor s d) := proj1_sig m.
  Local Coercion mor2morC : mor >-> Morphism.

  Let mor' (s d : obj) := sig (@Pmor' s d).
  Let mor'2morC s d (m : mor' s d) := proj1_sig m.
  Local Coercion mor'2morC : mor' >-> Morphism.

  Hypothesis Pmor_compose : forall s d d' (m1 : mor d d') (m2 : mor s d), Pmor _ _ (Compose (C := C) m1 m2).
  Hypothesis Pmor_identity : forall x : objC, Pmor _ _ (Identity (C := C) x).

  Let Pmor_compose' : forall s d d' (m1 : mor' d d') (m2 : mor' s d), Pmor' _ _ (Compose (C := C) m1 m2) := Pmor_compose.
  Let Pmor_identity' : forall x : obj, Pmor' _ _ (Identity (C := C) x) := Pmor_identity.

  Definition WideSubcategory' := Subcategory C Pmor' Pmor_compose' Pmor_identity'.

  Definition WideSubcategory : @SpecializedCategory obj.
    refine (@Build_SpecializedCategory obj mor'
      (fun x => WideSubcategory'.(Identity') x)
      (fun s d d' m1 m2 => WideSubcategory'.(Compose') _ _ _ m1 m2)
      _
      _
      _
    );
    subst_body;
    abstract (intros; autorewrite with morphism; reflexivity).
  Defined.
End WideSubcategory.
