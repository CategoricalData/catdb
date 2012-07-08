Require Import JMeq ProofIrrelevance.
Require Export SpecializedCategory.
Require Import Common StructureEquality FEqualDep.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

Section Functor.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
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

  Section FunctorInterface.
    Variable F : SpecializedFunctor.

    Definition ObjectOf : forall c, D := F.(ObjectOf'). (* [forall], so we can name it in [Arguments] *)
    Definition MorphismOf : forall (s d : C) (m : C.(Morphism) s d), D.(Morphism) (ObjectOf s) (ObjectOf d) := F.(MorphismOf').
    Definition FCompositionOf : forall (s d d' : C) (m1 : C.(Morphism) s d) (m2 : C.(Morphism) d d'),
      MorphismOf (Compose m2 m1) = Compose (MorphismOf m2) (MorphismOf m1)
      := F.(FCompositionOf').
    Definition FIdentityOf : forall (o : C), MorphismOf (Identity o) = Identity (ObjectOf o)
      := F.(FIdentityOf').
  End FunctorInterface.
End Functor.

Global Coercion ObjectOf : SpecializedFunctor >-> Funclass.

Ltac present_obj_mor_obj_mor from to :=
  repeat match goal with
           | [ _ : appcontext[from ?obj ?mor ?obj' ?mor'] |- _ ] => change (from obj mor obj' mor') with (to obj mor obj' mor') in *
           | [ |- appcontext[from ?obj ?mor ?obj' ?mor'] ] => change (from obj mor obj' mor') with (to obj mor obj' mor') in *
         end.

Ltac present_spfunctor := present_spcategory;
  present_obj_mor_obj_mor @ObjectOf' @ObjectOf; present_obj_mor_obj_mor @MorphismOf' @MorphismOf.

Arguments SpecializedFunctor {objC morC objD morD} C D.
Arguments ObjectOf {objC morC objD morD C D} F c.
Arguments MorphismOf {objC morC objD morD} [C D] F [s d] m.

Section Functors_Equal.
  Lemma SpecializedFunctors_Equal objC morC objD morD : forall C D (F G : @SpecializedFunctor objC morC objD morD C D),
    ObjectOf F = ObjectOf G
    -> (ObjectOf F = ObjectOf G -> MorphismOf F == MorphismOf G)
    -> F = G.
    destruct F, G; simpl; intros; specialize_all_ways; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.

  Lemma SpecializedFunctors_JMeq objC morC objD morD objC' morC' objD' morD' :
    forall C D C' D' (F : @SpecializedFunctor objC morC objD morD C D) (G : @SpecializedFunctor objC' morC' objD' morD' C' D'),
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
    apply SpecializedFunctors_Equal; intros; repeat subst; trivial.
  Qed.
End Functors_Equal.

Ltac spfunctor_eq_step_with tac :=
  try structures_eq_step_with SpecializedFunctors_Equal tac;
    try structures_eq_step_with SpecializedFunctors_JMeq tac.

Ltac spfunctor_eq_with tac := repeat spfunctor_eq_step_with tac.

Ltac spfunctor_eq_step := spfunctor_eq_step_with idtac.
Ltac spfunctor_eq := spfunctor_eq_with idtac.

Section FunctorComposition.
  Variable objB : Type.
  Variable morB : objB -> objB -> Type.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable objE : Type.
  Variable morE : objE -> objE -> Type.
  Variable B : SpecializedCategory morB.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable E : SpecializedCategory morE.

  Hint Rewrite FCompositionOf FIdentityOf.

  Definition ComposeSpecializedFunctors (G : SpecializedFunctor D E) (F : SpecializedFunctor C D) : SpecializedFunctor C E.
    refine {| ObjectOf' := (fun c => G (F c));
      MorphismOf' := (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
      |};
    abstract (
      present_spcategory; intros; simpl; repeat rewrite FCompositionOf; repeat rewrite FIdentityOf; reflexivity
    ).
    (* abstract t. *)
  Defined.
End FunctorComposition.

Section Category.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.

  (* There is an identity functor.  It does the obvious thing. *)
  Definition IdentitySpecializedFunctor : SpecializedFunctor C C.
    refine {| ObjectOf' := (fun x => x);
      MorphismOf' := (fun _ _ x => x)
    |};
    abstract t.
  Defined.

  Hint Unfold ComposeSpecializedFunctors IdentitySpecializedFunctor ObjectOf MorphismOf.

  Lemma LeftIdentitySpecializedFunctor (F : SpecializedFunctor D C) : ComposeSpecializedFunctors IdentitySpecializedFunctor F = F.
    spfunctor_eq.
  Qed.

  Lemma RightIdentitySpecializedFunctor (F : SpecializedFunctor C D) : ComposeSpecializedFunctors F IdentitySpecializedFunctor = F.
    spfunctor_eq.
  Qed.
End Category.

Section FunctorCompositionLemmas.
  Variable objB : Type.
  Variable morB : objB -> objB -> Type.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable objE : Type.
  Variable morE : objE -> objE -> Type.
  Variable B : SpecializedCategory morB.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable E : SpecializedCategory morE.

  Lemma ComposeSpecializedFunctorsAssociativity (F : SpecializedFunctor B C) (G : SpecializedFunctor C D) (H : SpecializedFunctor D E) :
    ComposeSpecializedFunctors (ComposeSpecializedFunctors H G) F = ComposeSpecializedFunctors H (ComposeSpecializedFunctors G F).
    spfunctor_eq.
  Qed.
End FunctorCompositionLemmas.
