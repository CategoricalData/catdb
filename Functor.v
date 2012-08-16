Require Import JMeq ProofIrrelevance.
Require Export Notations SpecializedCategory Category.
Require Import Common StructureEquality FEqualDep.

Set Implicit Arguments.

Local Infix "==" := JMeq.

Section SpecializedFunctor.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of categories is known as a functor. Namely, given
     categories [C] and [C'], a (covariant) functor [F : C -> C'] is a rule that assigns to
     each object [A] of [C] an object [F A] of [C'] and to each map [m : A -> B] of [C] a map
     [F m : F A -> F B] of [C'] preserving composition and identity; that is,
     (1) [F (m' ○ m) = (F m') ○ (F m)] for maps [m : A -> B] and [m' : B -> C] of [C], and
     (2) [F (id A) = id (F A)] for any object [A] of [C], where [id A] is the identity morphism of [A].
     **)
  Record SpecializedFunctor := {
    ObjectOf' : objC -> objD;
    MorphismOf' : forall s d, morC s d -> morD (ObjectOf' s) (ObjectOf' d);
    FCompositionOf' : forall s d d' (m1 : morC s d) (m2: morC d d'),
      MorphismOf' (C.(Compose') _ _ _ m2 m1) = D.(Compose') _ _ _ (MorphismOf' m2) (MorphismOf' m1);
    FIdentityOf' : forall o, MorphismOf' (C.(Identity') o) = D.(Identity') (ObjectOf' o)
  }.
End SpecializedFunctor.

Bind Scope functor_scope with SpecializedFunctor.

Section FunctorInterface.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.

  Variable F : SpecializedFunctor C D.

  Definition ObjectOf : forall c, D := Eval cbv beta delta [ObjectOf'] in F.(ObjectOf'). (* [forall], so we can name it in [Arguments] *)
  Definition MorphismOf : forall (s d : C) (m : C.(Morphism) s d), D.(Morphism) (ObjectOf s) (ObjectOf d)
    := Eval cbv beta delta [MorphismOf'] in F.(MorphismOf').
  Definition FCompositionOf : forall (s d d' : C) (m1 : C.(Morphism) s d) (m2 : C.(Morphism) d d'),
    MorphismOf (Compose m2 m1) = Compose (MorphismOf m2) (MorphismOf m1)
    := F.(FCompositionOf').
  Definition FIdentityOf : forall (o : C), MorphismOf (Identity o) = Identity (ObjectOf o)
    := F.(FIdentityOf').
End FunctorInterface.

Global Coercion ObjectOf : SpecializedFunctor >-> Funclass.

Section Functor.
  Variable C D : Category.

  Definition Functor := SpecializedFunctor C D.
End Functor.

Bind Scope functor_scope with Functor.

Identity Coercion Functor_SpecializedFunctor_Id : Functor >-> SpecializedFunctor.
Definition GeneralizeFunctor objC morC C objD morD D (F : @SpecializedFunctor objC morC C objD morD D) : Functor C D := F.
Coercion GeneralizeFunctor : SpecializedFunctor >-> Functor.

Arguments SpecializedFunctor {objC morC} C {objD morD} D.
Arguments Functor C D.
Arguments ObjectOf {objC morC C objD morD D} F c : simpl nomatch.
Arguments MorphismOf {objC morC} [C] {objD morD} [D] F [s d] m : simpl nomatch.

Ltac present_obj_mor_obj_mor from to :=
  repeat match goal with
           | [ _ : appcontext[from ?obj ?mor ?obj' ?mor'] |- _ ] => change (from obj mor obj' mor') with (to obj mor obj' mor') in *
           | [ |- appcontext[from ?obj ?mor ?obj' ?mor'] ] => change (from obj mor obj' mor') with (to obj mor obj' mor') in *
         end.

Ltac present_spfunctor' := present_spcategory';
  present_obj_mor_obj_mor @ObjectOf' @ObjectOf; present_obj_mor_obj_mor @MorphismOf' @MorphismOf.
Ltac present_spfunctor := present_spcategory;
  present_obj_mor_obj_mor @ObjectOf' @ObjectOf; present_obj_mor_obj_mor @MorphismOf' @MorphismOf.

Section Functors_Equal.
  Lemma Functors_Equal objC morC C objD morD D : forall (F G : @SpecializedFunctor objC morC C objD morD D),
    ObjectOf F = ObjectOf G
    -> (ObjectOf F = ObjectOf G -> MorphismOf F == MorphismOf G)
    -> F = G.
    destruct F, G; simpl; intros; specialize_all_ways; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.

  Lemma Functors_JMeq objC morC C objD morD D objC' morC' C' objD' morD' D' :
    forall (F : @SpecializedFunctor objC morC C objD morD D) (G : @SpecializedFunctor objC' morC' C' objD' morD' D'),
      objC = objC'
      -> objD = objD'
      -> (objC = objC' -> morC == morC')
      -> (objD = objD' -> morD == morD')
      -> (objC = objC' -> morC == morC' -> C == C')
      -> (objD = objD' -> morD == morD' -> D == D')
      -> (objC = objC' -> morC == morC' -> C == C' ->
        objD = objD' -> morD == morD' -> D == D' ->
        ObjectOf F == ObjectOf G)
      -> (objC = objC' -> morC == morC' -> C == C' ->
        objD = objD' -> morD == morD' -> D == D' ->
        ObjectOf F == ObjectOf G -> MorphismOf F == MorphismOf G)
      -> F == G.
    simpl; intros; subst objC' objD'; firstorder; subst morC' morD'; firstorder;
      JMeq_eq.
    repeat subst; JMeq_eq.
    apply Functors_Equal; intros; repeat subst; trivial.
  Qed.
End Functors_Equal.

Ltac functor_eq_step_with tac :=
  structures_eq_step_with_tac ltac:(apply Functors_Equal || apply Functors_JMeq) tac.

Ltac functor_eq_with tac := repeat functor_eq_step_with tac.

Ltac functor_eq_step := functor_eq_step_with idtac.
Ltac functor_eq := functor_eq_with idtac.

Section FunctorComposition.
  Variable objB : Type.
  Variable morB : objB -> objB -> Type.
  Variable B : SpecializedCategory morB.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.
  Variable objE : Type.
  Variable morE : objE -> objE -> Type.
  Variable E : SpecializedCategory morE.

  Hint Rewrite FCompositionOf FIdentityOf.

  Definition ComposeFunctors (G : SpecializedFunctor D E) (F : SpecializedFunctor C D) : SpecializedFunctor C E.
    refine {| ObjectOf' := (fun c => G (F c));
      MorphismOf' := (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
      |};
    abstract (
      present_spcategory; intros; simpl; repeat rewrite FCompositionOf; repeat rewrite FIdentityOf; reflexivity
    ).
    (* abstract t. *)
  Defined.
End FunctorComposition.

Section IdentityFunctor.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  (* There is an identity functor.  It does the obvious thing. *)
  Definition IdentityFunctor : SpecializedFunctor C C.
    refine {| ObjectOf' := (fun x => x);
      MorphismOf' := (fun _ _ x => x)
    |};
    abstract t.
  Defined.
End IdentityFunctor.

Section IdentityFunctorLemmas.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.

  Hint Unfold ComposeFunctors IdentityFunctor ObjectOf MorphismOf.

  Lemma LeftIdentityFunctor (F : SpecializedFunctor D C) : ComposeFunctors (IdentityFunctor _) F = F.
    functor_eq.
  Qed.

  Lemma RightIdentityFunctor (F : SpecializedFunctor C D) : ComposeFunctors F (IdentityFunctor _) = F.
    functor_eq.
  Qed.
End IdentityFunctorLemmas.

Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor.
Hint Immediate @LeftIdentityFunctor @RightIdentityFunctor.

Section FunctorCompositionLemmas.
  Variable objB : Type.
  Variable morB : objB -> objB -> Type.
  Variable B : SpecializedCategory morB.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.
  Variable objE : Type.
  Variable morE : objE -> objE -> Type.
  Variable E : SpecializedCategory morE.

  Lemma ComposeFunctorsAssociativity (F : SpecializedFunctor B C) (G : SpecializedFunctor C D) (H : SpecializedFunctor D E) :
    ComposeFunctors (ComposeFunctors H G) F = ComposeFunctors H (ComposeFunctors G F).
    functor_eq.
  Qed.
End FunctorCompositionLemmas.
