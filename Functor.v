Require Import JMeq ProofIrrelevance.
Require Export Category.
Require Import Common StructureEquality FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Local Infix "==" := JMeq (at level 70).

Local Open Scope morphism_scope.

Section Functor.
  Context `{C : Category}.
  Context `{D : Category}.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of categories is known as a functor. Namely, given
     categories [C] and [C'], a (covariant) functor [F : C -> C'] is a rule that assigns to
     each object [A] of [C] an object [F A] of [C'] and to each map [m : A -> B] of [C] a map
     [F m : F A -> F B] of [C'] preserving composition and identity; that is,
     (1) [F (m' ○ m) = (F m') ○ (F m)] for maps [m : A -> B] and [m' : B -> C] of [C], and
     (2) [F (id A) = id (F A)] for any object [A] of [C], where [id A] is the identity morphism of [A].
     **)
  Class Functor := {
    ObjectOf :> @CObject C -> @CObject D;
    MorphismOf : forall s d, Morphism s d -> Morphism (ObjectOf s) (ObjectOf d);
    FCompositionOf : forall s d d' (m1 : Morphism s d) (m2 : Morphism d d'),
      MorphismOf _ _ (m2 o m1) = (MorphismOf _ _ m2) o (MorphismOf _ _ m1);
    FIdentityOf : forall x,
      MorphismOf _ _ (Identity x) = Identity (ObjectOf x)
  }.
End Functor.

Arguments ObjectOf {C D} Functor x.
Arguments MorphismOf {C D} Functor [s d] m.

Section Specialized.
  Context `(C : @SpecializedCategory objC morC).
  Context `(D : @SpecializedCategory objD morD).

  Record SpecializedFunctor := {
    ObjectOf' :> objC -> objD;
    MorphismOf' : forall s d, morC s d -> morD (ObjectOf' s) (ObjectOf' d);
    FCompositionOf' : forall s d d' (m1 : morC s d) (m2: morC d d'),
      MorphismOf' (C.(Compose') _ _ _ m2 m1) = D.(Compose') _ _ _ (MorphismOf' m2) (MorphismOf' m1);
    FIdentityOf' : forall x, MorphismOf' (C.(Identity') x) = D.(Identity') (ObjectOf' x)
  }.

  Variable F : SpecializedFunctor.

  Global Instance GeneralizeFunctor : @Functor C D :=
    { ObjectOf := ObjectOf' F; MorphismOf := MorphismOf' F; FCompositionOf := FCompositionOf' F; FIdentityOf := FIdentityOf' F }.
End Specialized.

Coercion GeneralizeFunctor : SpecializedFunctor >-> Functor.

Section MkSpecialized.
  Context `(F : @Functor C D).

  Definition SpecializeFunctor : SpecializedFunctor C D.
    refine {| ObjectOf' := @ObjectOf C D F; MorphismOf' := @MorphismOf C D F |};
      present_spcategory; apply FCompositionOf || apply FIdentityOf.
  Defined.
End MkSpecialized.

Coercion SpecializeFunctor : Functor >-> SpecializedFunctor.

Delimit Scope functor_scope with functor.
Bind Scope functor_scope with SpecializedFunctor.
Bind Scope functor_scope with Functor.

Section Functors_Equal.
  Lemma Functors_Equal C D : forall (F G : @Functor C D),
    @ObjectOf _ _ F = @ObjectOf _ _ G
    -> (@ObjectOf _ _ F = @ObjectOf _ _ G -> @MorphismOf _ _ F == @MorphismOf _ _ G)
    -> F = G.
    destruct F, G; simpl; intros; specialize_all_ways; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.

  Lemma SpecializedFunctors_Equal objC morC C objD morD D : forall (F G : @SpecializedFunctor objC morC C objD morD D),
    ObjectOf' F = ObjectOf' G
    -> (ObjectOf' F = ObjectOf' G -> MorphismOf' F == MorphismOf' G)
    -> F = G.
    destruct F, G; simpl; intros; specialize_all_ways; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.

  Lemma Functors_JMeq C D C' D' :
    forall (F : @Functor C D) (G : @Functor C' D'),
      C = C'
      -> D = D'
      -> (C = C' -> D = D' -> @ObjectOf _ _ F == @ObjectOf _ _ G)
      -> (C = C' -> D = D' -> @ObjectOf _ _ F == @ObjectOf _ _ G
        -> @MorphismOf _ _ F == @MorphismOf _ _ G)
      -> F == G.
    simpl; intros; intuition; subst;
      JMeq_eq.
    apply Functors_Equal; intros; repeat subst; trivial.
  Qed.

  Lemma SpecializedFunctors_JMeq objC morC C objD morD D objC' morC' C' objD' morD' D' :
    forall (F : @SpecializedFunctor objC morC C objD morD D) (G : @SpecializedFunctor objC' morC' C' objD' morD' D'),
      objC = objC'
      -> objD = objD'
      -> (objC = objC' -> morC == morC')
      -> (objD = objD' -> morD == morD')
      -> (objC = objC' -> morC == morC' -> C == C')
      -> (objD = objD' -> morD == morD' -> D == D')
      -> (objC = objC' -> morC == morC' -> C == C' ->
        objD = objD' -> morD == morD' -> D == D' ->
        ObjectOf' F == ObjectOf' G)
      -> (objC = objC' -> morC == morC' -> C == C' ->
        objD = objD' -> morD == morD' -> D == D' ->
        ObjectOf' F == ObjectOf' G -> MorphismOf' F == MorphismOf' G)
      -> F == G.
    simpl; intros; intuition; repeat subst;
      JMeq_eq.
    apply SpecializedFunctors_Equal; intros; repeat subst; trivial.
  Qed.
End Functors_Equal.

Ltac functor_eq_step_with tac :=
  structures_eq_step_with_tac ltac:(apply Functors_Equal || apply Functors_JMeq || apply SpecializedFunctors_Equal || apply SpecializedFunctors_JMeq) tac.

Ltac functor_eq_with tac := repeat functor_eq_step_with tac.

Ltac functor_eq_step := functor_eq_step_with idtac.
Ltac functor_eq := functor_eq_with idtac.

Section FunctorComposition.
  Hint Rewrite @FCompositionOf @FIdentityOf.

  Definition ComposeFunctors C D E (G : @Functor D E) (F : @Functor C D) : @Functor C E.
    refine {| ObjectOf := (fun c => G (F c));
      MorphismOf := (fun _ _ m => MorphismOf G (MorphismOf F m))
    |};
    abstract (intros; autorewrite with core; reflexivity).
  Defined.

  Lemma ComposeFunctorsAssociativity B C D E (F : @Functor B C) (G : @Functor C D) (H : @Functor D E) :
    ComposeFunctors H (ComposeFunctors G F) = ComposeFunctors (ComposeFunctors H G) F.
    functor_eq.
  Qed.
End FunctorComposition.

Instance FunctorsComposable : Composable := {
  Object := { obj : Type & { mor : obj -> obj -> Type & SpecializedCategory mor } };
  Morphism := (fun s d => @Functor (projT2 (projT2 s)) (projT2 (projT2 d)));
  Compose := (fun _ _ _ m1 m2 => @ComposeFunctors _ _ _ m1 m2);
  Associativity := (fun _ _ _ _ F G H => @ComposeFunctorsAssociativity _ _ _ _ F G H)
}.

Check fun C D E (F : @Functor C D) (G : @Functor D E) => G o F.

admit.
Defined.
       }.

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
