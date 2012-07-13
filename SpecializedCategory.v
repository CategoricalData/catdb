Require Import ProofIrrelevance.
Require Import Common StructureEquality.

Set Implicit Arguments.

Record SpecializedCategory (obj : Type) (Morphism : obj -> obj -> Type) := {
  Identity' : forall o, Morphism o o;
  Compose' : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d';

  Associativity' : forall o1 o2 o3 o4 (m1 : Morphism o1 o2) (m2 : Morphism o2 o3) (m3 : Morphism o3 o4),
    Compose' (Compose' m3 m2) m1 = Compose' m3 (Compose' m2 m1);
  LeftIdentity' : forall a b (f : Morphism a b), Compose' (Identity' b) f = f;
  RightIdentity' : forall a b (f : Morphism a b), Compose' f (Identity' a) = f
}.

Definition LocallySmallSpecializedCategory (obj : Type) (mor : obj -> obj -> Set) := SpecializedCategory mor.
Definition SmallSpecializedCategory (obj : Set) (mor : obj -> obj -> Set) := SpecializedCategory mor.
Identity Coercion LocallySmallSpecializedCategory_SpecializedCategory_Id : LocallySmallSpecializedCategory >-> SpecializedCategory.
Identity Coercion SmallSpecializedCategory_LocallySmallSpecializedCategory_Id : SmallSpecializedCategory >-> SpecializedCategory.

Section Categories_Equal.
  Lemma SpecializedCategories_Equal obj mor : forall (C D : @SpecializedCategory obj mor),
    @Identity' _ _ C = @Identity' _ _ D
    -> @Compose' _ _ C = @Compose' _ _ D
    -> C = D.
    destruct C, D; repeat rewrite unfold_Object, unfold_Morphism in *; simpl in *; intros; firstorder; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.
End Categories_Equal.

Ltac spcat_eq_step_with tac := structures_eq_step_with SpecializedCategories_Equal tac.

Ltac spcat_eq_with tac := repeat spcat_eq_step_with tac.

Ltac spcat_eq_step := spcat_eq_step_with idtac.
Ltac spcat_eq := spcat_eq_with idtac.
