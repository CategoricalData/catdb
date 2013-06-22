Require Import ProofIrrelevance JMeq.
Require Export Category FEqualDep.
Require Import Common Notations StructureEquality SpecializedCategory.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Section Categories_Equal.
  Lemma Category_eq : forall (A B : Category),
    Object A = Object B
    -> Morphism A == Morphism B
    -> @Identity A == @Identity B
    -> @Compose A == @Compose B
    -> A = B.
    unfold Object, Morphism, Identity, Compose; intros;
    destruct_type @Category; destruct_type @SpecializedCategory; simpl in *;
    subst_body; repeat subst.
    repeat f_equal; apply proof_irrelevance.
  Qed.

  Lemma SmallCategory_eq : forall (A B : SmallCategory),
    Object A = Object B
    -> Morphism A == Morphism B
    -> @Identity A == @Identity B
    -> @Compose A == @Compose B
    -> A = B.
    unfold Object, Morphism, Identity, Compose; intros;
    destruct_type @SmallCategory; destruct_type @SmallSpecializedCategory; simpl in *;
    subst_body; repeat (subst; JMeq_eq).
    repeat f_equal; apply proof_irrelevance.
  Qed.

  Lemma LocallySmallCategory_eq : forall (A B : LocallySmallCategory),
    Object A = Object B
    -> Morphism A == Morphism B
    -> @Identity A == @Identity B
    -> @Compose A == @Compose B
    -> A = B.
    unfold Object, Morphism, Identity, Compose; intros;
    destruct_type @LocallySmallCategory; destruct_type @LocallySmallSpecializedCategory; simpl in *;
    subst_body; repeat (subst; JMeq_eq).
    repeat f_equal; apply proof_irrelevance.
  Qed.
End Categories_Equal.

Ltac cat_eq_step_with tac :=
  structures_eq_step_with_tac
  ltac:(apply SmallCategory_eq || apply LocallySmallCategory_eq || apply Category_eq)
  tac.

Ltac cat_eq_with tac := repeat cat_eq_step_with tac.

Ltac cat_eq_step := cat_eq_step_with idtac.
Ltac cat_eq := cat_eq_with idtac.

Section RoundtripCat.
  Context `(C : SpecializedCategory).
  Variable C' : Category.

  Lemma SpecializedCategory_Category_SpecializedCategory_Id : ((C : Category) : SpecializedCategory) = C.
    spcat_eq.
  Qed.

  Lemma Category_SpecializedCategory_Category_Id : ((C' : SpecializedCategory) : Category) = C'.
    cat_eq.
  Qed.
End RoundtripCat.

Hint Rewrite @SpecializedCategory_Category_SpecializedCategory_Id @Category_SpecializedCategory_Category_Id : category.

Section RoundtripLSCat.
  Context `(C : @LocallySmallSpecializedCategory).
  Variable C' : LocallySmallCategory.

  Lemma LocallySmall_SpecializedCategory_Category_SpecializedCategory_Id : ((C : LocallySmallCategory) : LocallySmallSpecializedCategory) = C.
    spcat_eq.
  Qed.

  Lemma LocallySmall_Category_SpecializedCategory_Category_Id : ((C' : LocallySmallSpecializedCategory) : LocallySmallCategory) = C'.
    cat_eq.
  Qed.
End RoundtripLSCat.

Hint Rewrite @LocallySmall_SpecializedCategory_Category_SpecializedCategory_Id LocallySmall_Category_SpecializedCategory_Category_Id : category.

Section RoundtripSCat.
  Context `(C : @SmallSpecializedCategory).
  Variable C' : SmallCategory.

  Lemma Small_SpecializedCategory_Category_SpecializedCategory_Id : ((C : SmallCategory) : SmallSpecializedCategory) = C.
    spcat_eq.
  Qed.


  Lemma Small_Category_SpecializedCategory_Category_Id : ((C' : SmallSpecializedCategory) : SmallCategory) = C'.
    cat_eq.
  Qed.
End RoundtripSCat.

Hint Rewrite @Small_SpecializedCategory_Category_SpecializedCategory_Id Small_Category_SpecializedCategory_Category_Id : category.
