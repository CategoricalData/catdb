Require Import ProofIrrelevance JMeq.
Require Export Category FEqualDep.
Require Import Common StructureEquality SpecializedCategory.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

Section Categories_Equal.
  Lemma Categories_Equal : forall (A B : Category),
    Object A = Object B
    -> Morphism A == Morphism B
    -> @Identity _ _ A == @Identity _ _ B
    -> @Compose _ _ A == @Compose _ _ B
    -> A = B.
    Transparent Object Morphism Identity Compose.
    unfold Identity, Compose, Morphism, Object.
    intros.
    destruct_type @Category; destruct_type @SpecializedCategory; simpl in *;
      repeat subst; repeat f_equal; apply proof_irrelevance.
  Qed.

  Lemma SmallCategories_Equal : forall (A B : SmallCategory),
    SObject A = SObject B
    -> SMorphism A == SMorphism B
    -> @Identity _ _ A == @Identity _ _ B
    -> @Compose _ _ A == @Compose _ _ B
    -> A = B.
    Transparent SObject SMorphism Object Morphism Identity Compose.
    unfold Identity, Compose, Morphism, Object, SObject, SMorphism.
    intros.
    destruct_type @SmallCategory; hnf in *; destruct_type @SpecializedCategory; simpl in *;
      repeat subst; repeat f_equal; apply proof_irrelevance.
  Qed.

  Lemma LocallySmallCategories_Equal : forall (A B : LocallySmallCategory),
    LSObject A = LSObject B
    -> LSMorphism A == LSMorphism B
    -> @Identity _ _ A == @Identity _ _ B
    -> @Compose _ _ A == @Compose _ _ B
    -> A = B.
    Transparent LSObject LSMorphism Object Morphism Identity Compose.
    unfold Identity, Compose, Morphism, Object, LSObject, LSMorphism.
    intros.
    destruct_type @LocallySmallCategory; hnf in *; destruct_type @SpecializedCategory; simpl in *;
      repeat subst; repeat f_equal; apply proof_irrelevance.
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
  Variable obj : Type.
  Variable mor : obj -> obj -> Type.
  Variable C : SpecializedCategory mor.
  Variable C' : Category.

  Lemma SpecializedCategory_Category_SpecializedCategory_Id : ((C : Category) : SpecializedCategory _) = C.
    spcat_eq.
  Qed.

  Lemma Category_SpecializedCategory_Category_Id : ((C' : SpecializedCategory _) : Category) = C'.
    cat_eq.
  Qed.
End RoundtripCat.

Hint Rewrite SpecializedCategory_Category_SpecializedCategory_Id Category_SpecializedCategory_Category_Id.

Section RoundtripLSCat.
  Variable obj : Type.
  Variable mor : obj -> obj -> Set.
  Variable C : LocallySmallSpecializedCategory mor.
  Variable C' : LocallySmallCategory.

  Lemma LocallySmall_SpecializedCategory_Category_SpecializedCategory_Id : ((C : LocallySmallCategory) : LocallySmallSpecializedCategory _) = C.
    spcat_eq.
  Qed.

  Lemma LocallySmall_Category_SpecializedCategory_Category_Id : ((C' : LocallySmallSpecializedCategory _) : LocallySmallCategory) = C'.
    cat_eq.
  Qed.
End RoundtripLSCat.

Hint Rewrite LocallySmall_SpecializedCategory_Category_SpecializedCategory_Id LocallySmall_Category_SpecializedCategory_Category_Id.

Section RoundtripSCat.
  Variable obj : Set.
  Variable mor : obj -> obj -> Set.
  Variable C : SmallSpecializedCategory mor.
  Variable C' : SmallCategory.

  Lemma Small_SpecializedCategory_Category_SpecializedCategory_Id : ((C : SmallCategory) : SmallSpecializedCategory _) = C.
    spcat_eq.
  Qed.

  Lemma Small_Category_SpecializedCategory_Category_Id : ((C' : SmallSpecializedCategory _) : SmallCategory) = C'.
    cat_eq.
  Qed.
End RoundtripSCat.

Hint Rewrite Small_SpecializedCategory_Category_SpecializedCategory_Id Small_Category_SpecializedCategory_Category_Id.
