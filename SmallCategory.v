Require Import ProofIrrelevance JMeq.
Require Export Category.
Require Import Common CategoryEquality StructureEquality FEqualDep.

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

Arguments SCompose [s s0 d d'] _ _.
Arguments SIdentity [s] o.

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

Ltac scat_eq_step_with tac := structures_eq_step_with SmallCategories_Equal tac.

Ltac scat_eq_with tac := repeat scat_eq_step_with tac.

Ltac scat_eq_step := scat_eq_step_with idtac.
Ltac scat_eq := scat_eq_with idtac.

(* build a small category from a category *)
Ltac scat_from_cat_obj_mor cat obj mor :=
(* unfold [Identity] and [Compose] and also turn [cat] into [Build_Category _], if we can *)
  let cat' := eval hnf in cat in
    let ident := eval cbv beta iota zeta delta [Identity] in (@Identity cat') in
      let compose := eval cbv beta iota zeta delta [Compose] in (@Compose cat') in
        match goal with
          | [ |- SmallCategory ] =>
            eapply (@Build_SmallCategory
              obj
              mor
              (ident : forall o : obj, mor o o)
              (compose : forall s d d' : obj, mor d d' -> mor s d -> mor s d')
            ) || fail 1;
            try abstract (
              intros; (
                simpl_do do_rewrite (@LeftIdentity cat') ||
                simpl_do do_rewrite (@RightIdentity cat') ||
                  simpl_do do_rewrite (@Associativity cat')
              );
              reflexivity
            )
          | [ |- _ ] => assert SmallCategory; scat_from_cat_obj_mor cat obj mor
        end.

Ltac scat_from_cat_obj cat obj :=
(* unfold [Morphism] and also turn [cat] into [Build_Category _], if we can *)
  let cat' := eval hnf in cat in
    let mor := eval cbv beta iota zeta delta [Morphism] in (@Morphism cat') in
      match type of SMorphism with
        | (forall s : SmallCategory, SObject s -> SObject s -> ?T) =>
          scat_from_cat_obj_mor cat obj (mor : obj -> obj -> T)
        | _ =>
          scat_from_cat_obj_mor cat obj (mor : obj -> obj -> _)
      end.

Ltac scat_from_cat cat :=
(* unfold [Object] and also turn [cat] into [Build_Category _], if we can *)
  let cat' := eval hnf in cat in
    let objType :=
      match type of SObject with
        | (SmallCategory -> ?T) => T
        | _ => type of (@Object cat')
      end in
      let obj := eval cbv beta iota zeta delta [Object] in (@Object cat') in
        scat_from_cat_obj cat' (obj : objType).
