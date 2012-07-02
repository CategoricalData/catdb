Require Import JMeq ProofIrrelevance FunctionalExtensionality.
Require Export Category.
Require Import Common CategoryEquality FEqualDep.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

(**
   Quoting Wikipedia:
   A category [C] is called small if both ob(C) and hom(C) are
   actually sets and not proper classes, and large otherwise.

   I don't impose this restriction, because I want to see if I
   can make it work with just saying that the objects and morphisms
   of a small category are no larger than the objects and morphisms
   of a (large) category.
   *)
Record SmallCategory := {
  SObject :> Type;
  SMorphism : SObject -> SObject -> Type;

  SIdentity : forall o, SMorphism o o;
  SCompose : forall s d d', SMorphism d d' -> SMorphism s d -> SMorphism s d';

  SAssociativity : forall o1 o2 o3 o4 (m1 : SMorphism o1 o2) (m2 : SMorphism o2 o3) (m3 : SMorphism o3 o4),
    SCompose (SCompose m3 m2) m1 = SCompose m3 (SCompose m2 m1);
  SLeftIdentity : forall a b (f : SMorphism a b), SCompose (SIdentity b) f = f;
  SRightIdentity : forall a b (f : SMorphism a b), SCompose f (SIdentity a) = f
}.

Implicit Arguments SCompose [s s0 d d'].
Implicit Arguments SIdentity [s].

Hint Rewrite SLeftIdentity SRightIdentity.

Hint Resolve SAssociativity SLeftIdentity SRightIdentity.

Section SmallCat2Cat.
  Variable C : SmallCategory.

  Definition smallcat2cat : Category.
    refine {| Object := @SObject C;
      Morphism := @SMorphism C;
      Compose := @SCompose C
    |}; auto.
  Defined.
End SmallCat2Cat.

Coercion smallcat2cat : SmallCategory >-> Category.

Section Categories_Equal.
  Lemma SmallCategories_Equal : forall (A B : SmallCategory),
    SObject A = SObject B
    -> SMorphism A == SMorphism B
    -> @SIdentity A == @SIdentity B
    -> @SCompose A == @SCompose B
    -> A = B.
    destruct A, B; simpl; intros; repeat subst;
      f_equal; reflexivity || apply proof_irrelevance.
  Qed.
End Categories_Equal.

Ltac scat_eq_step_with tac := intros; simpl;
  match goal with
    | _ => reflexivity
    | [ |- @eq SmallCategory _ _ ] => apply SmallCategories_Equal
    | [ |- (fun _ : ?A => _) == _ ] => apply (@functional_extensionality_dep_JMeq A); intro
    | [ |- (fun _ : ?A => _) = _ ] => apply (@functional_extensionality_dep A); intro
    | [ |- (forall _ : ?A, _) = _ ] => apply (@forall_extensionality_dep A); intro
    | [ |- _ = _ ] => apply proof_irrelevance
    | _ => tac
  end; repeat simpl; JMeq_eq.

Ltac scat_eq_with tac := repeat scat_eq_step_with tac.

Ltac scat_eq_step := scat_eq_step_with idtac.
Ltac scat_eq := scat_eq_with idtac.
