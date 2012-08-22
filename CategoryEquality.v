Require Import ProofIrrelevance JMeq.
Require Export Category FEqualDep.
Require Import Common Notations StructureEquality SpecializedCategory.

Set Implicit Arguments.

Generalizable All Variables.

Local Infix "==" := JMeq.

Section Categories_Equal.
  Lemma Categories_Equal : forall (A B : Category),
    Object A = Object B
    -> Morphism A == Morphism B
    -> @Identity _ A == @Identity _ B
    -> @Compose _ A == @Compose _ B
    -> A = B.
    unfold Object, Morphism, Identity, Compose; intros;
      destruct_type @Category; destruct_type @SpecializedCategory; simpl in *;
        subst_body; repeat subst.
    repeat f_equal; apply proof_irrelevance.
  Qed.

  Lemma SmallCategories_Equal : forall (A B : SmallCategory),
    SObject A = SObject B
    -> Morphism A == Morphism B
    -> @Identity _ A == @Identity _ B
    -> @Compose _ A == @Compose _ B
    -> A = B.
    unfold SObject, Morphism, Identity, Compose; intros;
      destruct_type @SmallCategory; destruct_type @SmallSpecializedCategory; simpl in *;
        subst_body; repeat (subst; JMeq_eq).
    repeat f_equal; apply proof_irrelevance.
  Qed.

  Lemma LocallySmallCategories_Equal : forall (A B : LocallySmallCategory),
    LSObject A = LSObject B
    -> Morphism A == Morphism B
    -> @Identity _ A == @Identity _ B
    -> @Compose _ A == @Compose _ B
    -> A = B.
    unfold LSObject, Morphism, Identity, Compose; intros;
      destruct_type @LocallySmallCategory; destruct_type @LocallySmallSpecializedCategory; simpl in *;
        subst_body; repeat (subst; JMeq_eq).
    repeat f_equal; apply proof_irrelevance.
  Qed.
End Categories_Equal.

Ltac cat_eq_step_with tac :=
  structures_eq_step_with_tac
  ltac:(apply SmallCategories_Equal || apply LocallySmallCategories_Equal || apply Categories_Equal)
  tac.

Ltac cat_eq_with tac := repeat cat_eq_step_with tac.

Ltac cat_eq_step := cat_eq_step_with idtac.
Ltac cat_eq := cat_eq_with idtac.

Section RoundtripCat.
  Context `(C : @SpecializedCategory obj).
  Variable C' : Category.

  Lemma SpecializedCategory_Category_SpecializedCategory_Id : ((C : Category) : SpecializedCategory _) = C.
    spcat_eq.
  Qed.

  Lemma Category_SpecializedCategory_Category_Id : ((C' : SpecializedCategory _) : Category) = C'.
    cat_eq.
  Qed.
End RoundtripCat.

Hint Rewrite @SpecializedCategory_Category_SpecializedCategory_Id @Category_SpecializedCategory_Category_Id.

Section RoundtripLSCat.
  Context `(C : @LocallySmallSpecializedCategory obj).
  Variable C' : LocallySmallCategory.

  Lemma LocallySmall_SpecializedCategory_Category_SpecializedCategory_Id : ((C : LocallySmallCategory) : LocallySmallSpecializedCategory _) = C.
    spcat_eq.
  Qed.

  Lemma LocallySmall_Category_SpecializedCategory_Category_Id : ((C' : LocallySmallSpecializedCategory _) : LocallySmallCategory) = C'.
    cat_eq.
  Qed.
End RoundtripLSCat.

Hint Rewrite @LocallySmall_SpecializedCategory_Category_SpecializedCategory_Id LocallySmall_Category_SpecializedCategory_Category_Id.

Section RoundtripSCat.
  Context `(C : @SmallSpecializedCategory obj).
  Variable C' : SmallCategory.

  Lemma Small_SpecializedCategory_Category_SpecializedCategory_Id : ((C : SmallCategory) : SmallSpecializedCategory _) = C.
    spcat_eq.
  Qed.

  Lemma Small_Category_SpecializedCategory_Category_Id : ((C' : SmallSpecializedCategory _) : SmallCategory) = C'.
    cat_eq.
  Qed.
End RoundtripSCat.

Hint Rewrite @Small_SpecializedCategory_Category_SpecializedCategory_Id Small_Category_SpecializedCategory_Category_Id.
