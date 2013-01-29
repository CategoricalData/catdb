Require Import FunctionalExtensionality.
Require Export MonoidalCategory SetCategory.
Require Import Common SetCategoryProductFunctor.

Set Implicit Arguments.

Generalizable All Variables.

(* There is a category [Set], where the objects are sets and the morphisms are set morphisms *)
Section CSet.
  Local Ltac build_set_cat :=
    match goal with
      | [ |- SpecializedCategory ?obj ] =>
        refine (@Build_SpecializedCategory obj
          (fun s d => s -> d)
          (fun _ => (fun x => x))
          (fun _ _ _ f g => (fun x => f (g x)))
          _
          _
          _
        )
    end;
    abstract (firstorder; etransitivity; eauto with morphism; t).
    Print MonoidalCategory.

    Local Ltac t :=
      repeat (reflexivity
                || (progress (simpl in *; repeat intro))
                || (apply functional_extensionality_dep; intro)
                || (destruct_head prod)
                || (destruct_head unit)).

    Local Ltac inst_1 :=
      match goal with | [ |- appcontext[?E] ] => is_evar E;
                                                let H := fresh in
                                                first [ assert (H : E = (fun xyz => (fst (fst xyz), (snd (fst xyz), snd xyz)))) by reflexivity
                                                      | assert (H : E = (fun xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz)))) by reflexivity ];
                                                  clear H
      end.

    Local Ltac inst_2 :=
      match goal with | [ |- appcontext[?E] ] => is_evar E;
                                                let H := fresh in
                                                first [ assert (H : E = (fun _ xyz => (fst (fst xyz), (snd (fst xyz), snd xyz)))) by reflexivity
                                                      | assert (H : E = (fun _ xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz)))) by reflexivity ];
                                                  clear H
      end.

    Local Ltac inst_nt :=
      match goal with | [ |- appcontext[?E] ] => is_evar E;
                                                match type of E with
                                                  | SpecializedNaturalTransformation ?F ?G =>
                                                    let A := fresh in
                                                    let B := fresh in
                                                    let H := fresh in
                                                    evar_evar_Type A;
                                                      evar_evar_Type B;
                                                      assert (H : E = Build_SpecializedNaturalTransformation F G A B) by reflexivity;
                                                      clear H
                                                end
      end;
      simpl in *.

    Local Ltac build_associator :=
      repeat intro; hnf; intros;
      destruct_head @prod; simpl;
      repeat esplit;
      repeat inst_nt; simpl in *; instantiate;
      repeat inst_1;
      repeat inst_2;
      clear;
      simpl in *;
      abstract t.

    (*Definition TypeAssociator_NT : SpecializedNaturalTransformation (TriMonoidalProductL TypeProductFunctor)
                                                                    (TriMonoidalProductR TypeProductFunctor).
      build_associator.
    Defined.*)
    Definition TypeAssociator : NaturalIsomorphism (TriMonoidalProductL TypeProductFunctor)
                                                   (TriMonoidalProductR TypeProductFunctor).
      repeat intro; hnf; intros;
      destruct_head @prod; simpl;
      repeat esplit;
      repeat inst_nt; simpl in *; instantiate;
      repeat inst_1;
      repeat inst_2;
      clear;
      simpl in *.
      admit.
      admit.
      Grab Existential Variables. (* Anomaly: type_of: variable x unbound. Please report. *)
      admit.
      subst_body; simpl; abstract t.
    Defined.

      eauto with monoidal_set_category_hints.

      apply functional_extensionality_dep; intro.
      destruct_head prod.
      trivial.

      simpl in *.
      clear.
      clear.
      inst_2.
      repeat match goal with | [ |- appcontext[?E] ] => is_evar E;
                                                       let H := fresh in
                                                       first [ assert (H : E = (fun xyz => (fst (fst xyz), (snd (fst xyz), snd xyz)))) by reflexivity
                                                             | assert (H : E = (fun xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz)))) by reflexivity ];
                                                         clear H
             end.
      match goal with | [ |- appcontext[?E] ] => is_evar E;
                                                let H := fresh in
                                                first [ assert (H : E = (fun _ xyz => (fst (fst xyz), (snd (fst xyz), snd xyz)))) by reflexivity
                                                      | assert (H : E = (fun _ xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz)))) by reflexivity ];
                                                  clear H
      end.

      repeat esplit.
      repeat intro; hnf; intros;
      destruct_head @prod; simpl;
      repeat esplit.
      simpl in *.
      clear.
      repeat match goal with
               | [ |- appcontext[?E] ] => is_evar E; let H := fresh in set (H := E)
             end.
      simpl in *.
      repeat match goal with | [ H : _ |- _ ] => revert H end.

      Local Ltac t :=
        match goal with
          | [ |- appcontext[?E] ] => is_evar E;
                                    let H := fresh in
                                    first [ assert (H : E = (fun _ xyz => (fst (fst xyz), (snd (fst xyz), snd xyz)))) by reflexivity
                                          | assert (H : E = (fun _ xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz)))) by reflexivity
                                          | assert (H : E = (fun xyz => (fst (fst xyz), (snd (fst xyz), snd xyz)))) by reflexivity
                                          | assert (H : E = (fun xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz)))) by reflexivity ];
                                      clear H
        end.

      Goal forall T0 T1 T : Type,
           exists (H : T0 * (T1 * T) -> T0 * T1 * T) (H0 : forall c : Type * Type * Type,
                                                             fst (fst c) * snd (fst c) * snd c ->
                                                             fst (fst c) * (snd (fst c) * snd c)),
             (fun x : T0 * T1 * T => H (H0 (T0, T1, T) x)) = (fun x : T0 * T1 * T => x).
      intros; repeat esplit.
      try t.
      build_associator.
      reflexivity.
      exists TypeAssociator_NT.
      build_associator.
    Defined.

    Local Ltac build_unitor :=
      simpl; repeat intro; hnf;
      esplit;
      try first [ instantiate (1 := fun _ => @snd _ _)
                | instantiate (1 := fun _ => @fst _ _)
                | instantiate (1 := fun x => (tt, x))
                | instantiate (1 := fun x => (x, tt)) ];
      simpl;
      try abstract eauto.


    Definition TypeLeftUnitor_NT : NaturalTransformation (LeftUnitorFunctor TypeProductFunctor unit)
                                                         (IdentityFunctor TypeCat).
      build_unitor.
    Defined.
    Definition TypeLeftUnitor : NaturalIsomorphism (LeftUnitorFunctor TypeProductFunctor unit)
                                                   (IdentityFunctor TypeCat).
      exists TypeLeftUnitor_NT.
      build_unitor.
    Defined.

    Definition TypeRightUnitor_NT : NaturalTransformation (RightUnitorFunctor TypeProductFunctor unit)
                                                          (IdentityFunctor TypeCat).
      build_unitor.
    Defined.
    Definition TypeRightUnitor : NaturalIsomorphism (RightUnitorFunctor TypeProductFunctor unit)
                                                    (IdentityFunctor TypeCat).
      exists TypeRightUnitor_NT.
      build_unitor.
    Defined.

  Definition TypeMonoidalCat : MonoidalCategory Type.
    eexists TypeCat TypeProductFunctor _ TypeAssociator TypeLeftUnitor TypeRightUnitor;
    simpl; abstract reflexivity.
  Definition SetCat : @SpecializedCategory Set. build_set_cat. Defined.
  Definition PropCat : @SpecializedCategory Prop. build_set_cat. Defined.
End CSet.

Section SetCoercionsDefinitions.
  Context `(C : @SpecializedCategory objC).

  Definition SpecializedFunctorToProp := SpecializedFunctor C PropCat.
  Definition SpecializedFunctorToSet := SpecializedFunctor C SetCat.
  Definition SpecializedFunctorToType := SpecializedFunctor C TypeCat.

  Definition SpecializedFunctorFromProp := SpecializedFunctor PropCat C.
  Definition SpecializedFunctorFromSet := SpecializedFunctor SetCat C.
  Definition SpecializedFunctorFromType := SpecializedFunctor TypeCat C.
End SetCoercionsDefinitions.

Identity Coercion SpecializedFunctorToProp_Id : SpecializedFunctorToProp >-> SpecializedFunctor.
Identity Coercion SpecializedFunctorToSet_Id : SpecializedFunctorToSet >-> SpecializedFunctor.
Identity Coercion SpecializedFunctorToType_Id : SpecializedFunctorToType >-> SpecializedFunctor.
Identity Coercion SpecializedFunctorFromProp_Id : SpecializedFunctorFromProp >-> SpecializedFunctor.
Identity Coercion SpecializedFunctorFromSet_Id : SpecializedFunctorFromSet >-> SpecializedFunctor.
Identity Coercion SpecializedFunctorFromType_Id : SpecializedFunctorFromType >-> SpecializedFunctor.

Section SetCoercions.
  Context `(C : @SpecializedCategory objC).

  Local Ltac build_functor := hnf in *;
    match goal with
      | [ F : SpecializedFunctor _ _ |- SpecializedFunctor ?C ?D ] =>
        exact (Build_SpecializedFunctor C D
          F.(ObjectOf')
          F.(MorphismOf')
          F.(FCompositionOf')
          F.(FIdentityOf')
        )
    end.

  Definition SpecializedFunctorTo_Prop2Set (F : SpecializedFunctorToProp C) : SpecializedFunctorToSet C. build_functor. Defined.
  Definition SpecializedFunctorTo_Prop2Type (F : SpecializedFunctorToProp C) : SpecializedFunctorToType C. build_functor. Defined.
  Definition SpecializedFunctorTo_Set2Type (F : SpecializedFunctorToSet C) : SpecializedFunctorToType C. build_functor. Defined.

  Definition SpecializedFunctorFrom_Set2Prop (F : SpecializedFunctorFromSet C) : SpecializedFunctorFromProp C. build_functor. Defined.
  Definition SpecializedFunctorFrom_Type2Prop (F : SpecializedFunctorFromType C) : SpecializedFunctorFromProp C. build_functor. Defined.
  Definition SpecializedFunctorFrom_Type2Set (F : SpecializedFunctorFromType C) : SpecializedFunctorFromSet C. build_functor. Defined.
End SetCoercions.

Coercion SpecializedFunctorTo_Prop2Set : SpecializedFunctorToProp >-> SpecializedFunctorToSet.
Coercion SpecializedFunctorTo_Prop2Type : SpecializedFunctorToProp >-> SpecializedFunctorToType.
Coercion SpecializedFunctorTo_Set2Type : SpecializedFunctorToSet >-> SpecializedFunctorToType.
Coercion SpecializedFunctorFrom_Set2Prop : SpecializedFunctorFromSet >-> SpecializedFunctorFromProp.
Coercion SpecializedFunctorFrom_Type2Prop : SpecializedFunctorFromType >-> SpecializedFunctorFromProp.
Coercion SpecializedFunctorFrom_Type2Set : SpecializedFunctorFromType >-> SpecializedFunctorFromSet.

(* There is a category [Set*], where the objects are sets with a distinguished elements and the morphisms are set morphisms *)
Section PointedSet.
  Local Ltac build_pointed_set_cat :=
    match goal with
      | [ |- SpecializedCategory ?obj ] =>
        refine (@Build_SpecializedCategory obj
          (fun s d => (projT1 s) -> (projT1 d))
          (fun _ => (fun x => x))
          (fun _ _ _ f g => (fun x => f (g x)))
          _
          _
          _
        )
    end;
    abstract (firstorder; etransitivity; eauto; t).

  Local Ltac build_pointed_set_cat_projection :=
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (fun c => projT1 c)
          (fun s d (m : (projT1 s) -> (projT1 d)) => m)
          _
          _
        )
    end;
    abstract t.

  Definition PointedTypeCat : @SpecializedCategory { A : Type & A }. build_pointed_set_cat. Defined.
  Definition PointedTypeProjection : SpecializedFunctor PointedTypeCat TypeCat. build_pointed_set_cat_projection. Defined.
  Definition PointedSetCat : @SpecializedCategory { A : Set & A }. build_pointed_set_cat. Defined.
  Definition PointedSetProjection : SpecializedFunctor PointedSetCat SetCat. build_pointed_set_cat_projection. Defined.
  Definition PointedPropCat : @SpecializedCategory { A : Prop & A }. build_pointed_set_cat. Defined.
  Definition PointedPropProjection : SpecializedFunctor PointedPropCat PropCat. build_pointed_set_cat_projection. Defined.
End PointedSet.
