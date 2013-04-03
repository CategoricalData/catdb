Require Import Setoid JMeq ProofIrrelevance FunctionalExtensionality.
Require Export Notations SpecializedCategory Category.
Require Import Common StructureEquality FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Local Infix "==" := JMeq.

(**
 * Quoting from the lecture notes for 18.705, Commutative Algebra:
 *
 *  A map of categories is known as a functor. Namely, given
 *  categories [C] and [C'], a (covariant) functor [F : C -> C'] is a rule that assigns to
 *  each object [A] of [C] an object [F A] of [C'] and to each map [m : A -> B] of [C] a map
 *  [F m : F A -> F B] of [C'] preserving composition and identity; that is,
 *  (1) [F (m' ○ m) = (F m') ○ (F m)] for maps [m : A -> B] and [m' : B -> C] of [C], and
 *  (2) [F (id A) = id (F A)] for any object [A] of [C], where [id A] is the identity morphism of [A].
 **)

Section ComputationalFunctor.
  Context `(C : @ComputationalCategory objC).
  Context `(D : @ComputationalCategory objD).

  Record ComputationalFunctor :=
    {
      ObjectOf :> objC -> objD;
      MorphismOf : forall {s d}, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d)
    }.
End ComputationalFunctor.

Bind Scope functor_scope with ComputationalFunctor.

Class IsSpecializedFunctor `{@IsSpecializedCategory objC C} `{@IsSpecializedCategory objD D} (F : ComputationalFunctor C D) : Prop :=
  {
    FCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
                       MorphismOf F (Compose m2 m1) = Compose (MorphismOf F m2) (MorphismOf F m1);
    FIdentityOf : forall x : objC, MorphismOf F (Identity x) = Identity (F x)
  }.

Record SpecializedFunctor `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD) :=
  Build_SpecializedFunctor' {
      UnderlyingCFunctor :> ComputationalFunctor C D;
      UnderlyingCFunctor_IsSpecializedFunctor :> IsSpecializedFunctor UnderlyingCFunctor
    }.

Hint Extern 0 (IsSpecializedFunctor _) => solve [ apply UnderlyingCFunctor_IsSpecializedFunctor ].

Existing Instance UnderlyingCFunctor_IsSpecializedFunctor.

Ltac specialized_functor_is_specialized :=
  solve [ apply UnderlyingCFunctor_IsSpecializedFunctor ].

Section Functor.
  Variable C D : Category.

  Definition Functor := SpecializedFunctor C D.
End Functor.

Bind Scope functor_scope with SpecializedFunctor.
Bind Scope functor_scope with Functor.

Section SpecializedFunctorInterface.
  Definition Build_SpecializedFunctor
             `(C : @SpecializedCategory objC)
             `(D : @SpecializedCategory objD)
             (ObjectOf : C -> D)
             (MorphismOf : forall s d (m : Morphism C s d),
                             Morphism D (ObjectOf s) (ObjectOf d))
             (FCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
                                 MorphismOf _ _ (Compose m2 m1) = Compose (MorphismOf _ _ m2) (MorphismOf _ _ m1))
             (FIdentityOf : forall x : C, MorphismOf _ _ (Identity x) = Identity (ObjectOf x))
  : SpecializedFunctor C D
    := Eval hnf in
        let F := (@Build_ComputationalFunctor _ C _ D
                                              ObjectOf
                                              MorphismOf) in
        @Build_SpecializedFunctor' _ C _ D
                                   F
                                   (@Build_IsSpecializedFunctor _ C _
                                                                _ D _
                                                                F
                                                                FCompositionOf
                                                                FIdentityOf).
End SpecializedFunctorInterface.

Create HintDb functor discriminated.

Identity Coercion Functor_SpecializedFunctor_Id : Functor >-> SpecializedFunctor.
Definition GeneralizeFunctor objC C objD D (F : @SpecializedFunctor objC C objD D) : Functor C D := F.
Coercion GeneralizeFunctor : SpecializedFunctor >-> Functor.

(* try to always unfold [GeneralizeFunctor]; it's in there
   only for coercions *)
Arguments GeneralizeFunctor [objC C objD D] F / .
Hint Extern 0 => unfold GeneralizeFunctor : category functor.

Arguments SpecializedFunctor {objC} C {objD} D.
Arguments Functor C D.
Arguments ObjectOf {objC%type C%category objD%type D%category} F%functor c%object : rename.
Arguments MorphismOf {objC%type} [C%category] {objD%type} [D%category] F%functor [s%object d%object] m%morphism : rename.

Hint Resolve @FCompositionOf @FIdentityOf : category functor.
Hint Rewrite @FIdentityOf using eauto with typeclass_instances : category.
Hint Rewrite @FIdentityOf using eauto with typeclass_instances : functor.
(** TODO(jgross): Try to figure out [rewrite_db functor; typeclasses eauto]. *)

Local Ltac rewrite_functor :=
  repeat (simpl; (split || intro)); simpl;
  repeat setoid_rewrite FCompositionOf;
  repeat setoid_rewrite FIdentityOf;
  eauto with typeclass_instances.

Ltac functor_hideProofs :=
  repeat match goal with
           | [ |- context[{|
                             FCompositionOf := ?pf0;
                             FIdentityOf := ?pf1
                           |}] ] =>
             hideProofs pf0 pf1
         end.

Ltac functor_tac_abstract_trailing_props F tac :=
  let H := fresh in
  pose F as H; revert H; clear; intro H; clear H;
  let F' := (eval hnf in (UnderlyingCFunctor F)) in
  let F'H := constr:(UnderlyingCFunctor_IsSpecializedFunctor F) in
  let F'' := (let F'' := eval simpl in F' in F'') in
  let FT := type of F in
  let CD := (match eval hnf in FT with
               | @SpecializedFunctor ?objC ?C ?objD ?D =>
                 constr:(C, D)
             end) in
  let C := constr:(fst CD) in
  let D := constr:(snd CD) in
  refine (@Build_SpecializedFunctor' _ C _ D
                                     F''
                                     _);
    abstract exact F'H.

Ltac functor_abstract_trailing_props F := functor_tac_abstract_trailing_props F ltac:(fun F' => F').
Ltac functor_simpl_abstract_trailing_props F := functor_tac_abstract_trailing_props F ltac:(fun F' => let F'' := eval simpl in F' in F'').

Section Functors_Equal.
  Lemma SpecializedFunctor_eq objC C objD D
  : forall (F G : @SpecializedFunctor objC C objD D),
      UnderlyingCFunctor F = UnderlyingCFunctor G
      -> F = G.
    intros; destruct_head @SpecializedFunctor;
    simpl in *; repeat subst;
    f_equal; apply proof_irrelevance.
  Qed.

  Lemma Functor_eq' objC C objD D : forall (F G : @SpecializedFunctor objC C objD D),
                                      ObjectOf F = ObjectOf G
                                      -> MorphismOf F == MorphismOf G
                                      -> F = G.
    intros; apply SpecializedFunctor_eq;
    destruct_head @SpecializedFunctor; destruct_head @ComputationalFunctor;
    simpl in *; repeat subst;
    reflexivity.
  Qed.

  Lemma Functor_eq objC C objD D :
    forall (F G : @SpecializedFunctor objC C objD D),
      (forall x, ObjectOf F x = ObjectOf G x)
      -> (forall s d m, MorphismOf F (s := s) (d := d) m == MorphismOf G (s := s) (d := d) m)
      -> F = G.
    intros; cut (ObjectOf F = ObjectOf G); intros; try apply Functor_eq';
    destruct_head @SpecializedFunctor; destruct_head @ComputationalFunctor;
    simpl in *; repeat subst;
    try apply eq_JMeq;
    repeat (apply functional_extensionality_dep; intro); trivial;
    try apply JMeq_eq; trivial.
  Qed.

  Lemma Functor_JMeq objC C objD D objC' C' objD' D' :
    forall (F : @SpecializedFunctor objC C objD D) (G : @SpecializedFunctor objC' C' objD' D'),
      objC = objC'
      -> objD = objD'
      -> C == C'
      -> D == D'
      -> ObjectOf F == ObjectOf G
      -> MorphismOf F == MorphismOf G
      -> F == G.
    simpl; intros; intuition; repeat subst;
    destruct_head @SpecializedFunctor; destruct_head @ComputationalFunctor;
    simpl in *;
    repeat subst; JMeq_eq;
    f_equal; apply proof_irrelevance.
  Qed.
End Functors_Equal.

Ltac functor_eq_step_with tac :=
  structures_eq_step_with_tac ltac:((apply SpecializedFunctor_eq; reflexivity)
                                      || apply Functor_eq
                                      || apply Functor_JMeq)
                                     tac.

Ltac functor_eq_with tac := repeat functor_eq_step_with tac.

Ltac functor_eq_step := functor_eq_step_with idtac.
Ltac functor_eq := functor_hideProofs; functor_eq_with idtac.

Ltac functor_tac_abstract_trailing_props_with_equality_do tac F thm :=
  let F' := (eval hnf in (UnderlyingCFunctor F)) in
  let F'H := constr:(UnderlyingCFunctor_IsSpecializedFunctor F) in
  let HT := type of F'H in
  let F'' := (tac F') in
  let H := fresh in
  let FT := type of F in
  pose F'' as H;
    hnf in H;
    revert H; clear; intro H; clear H;
    assert (H : HT) by abstract exact F'H;
    match eval hnf in FT with
      | @SpecializedFunctor ?objC ?C ?objD ?D =>
        (exists (@Build_SpecializedFunctor' objC C objD D
                                            F''
                                            F'H))
    end;
    expand; abstract (apply thm; reflexivity) || (apply thm; try reflexivity).

Ltac functor_tac_abstract_trailing_props_with_equality tac :=
  pre_abstract_trailing_props;
  match goal with
    | [ |- { F0 : SpecializedFunctor _ _ | F0 = ?F } ] =>
      functor_tac_abstract_trailing_props_with_equality_do tac F @Functor_eq'
    | [ |- { F0 : SpecializedFunctor _ _ | F0 == ?F } ] =>
      functor_tac_abstract_trailing_props_with_equality_do tac F @Functor_JMeq
  end.
Ltac functor_abstract_trailing_props_with_equality := functor_tac_abstract_trailing_props_with_equality ltac:(fun F' => F').
Ltac functor_simpl_abstract_trailing_props_with_equality := functor_tac_abstract_trailing_props_with_equality ltac:(fun F' => let F'' := eval simpl in F' in F'').


Section FunctorComposition.
  Section computational.
    Context `(C : @ComputationalCategory objC).
    Context `(D : @ComputationalCategory objD).
    Context `(E : @ComputationalCategory objE).

    Definition ComposeComputationalFunctors (G : ComputationalFunctor D E) (F : ComputationalFunctor C D) : ComputationalFunctor C E
      := Build_ComputationalFunctor C E
                                    (fun c => G (F c))
                                    (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m)).
  End computational.

  Section is_specialized.
    Context `(HC : @IsSpecializedCategory objC C).
    Context `(HD : @IsSpecializedCategory objD D).
    Context `(HE : @IsSpecializedCategory objE E).

    Global Instance ComposeIsSpecializedFunctors `(@IsSpecializedFunctor _ D HD _ E HE G) `(@IsSpecializedFunctor _ C HC _ D HD F)
    : IsSpecializedFunctor (ComposeComputationalFunctors (C := C) (D := D) (E := E) G F).
    Proof.
      rewrite_functor.
    Qed.
  End is_specialized.

  Section specialized.
    Context `(C : @SpecializedCategory objC).
    Context `(D : @SpecializedCategory objD).
    Context `(E : @SpecializedCategory objE).

    Definition ComposeFunctors (G : SpecializedFunctor D E) (F : SpecializedFunctor C D) : SpecializedFunctor C E
      := {| UnderlyingCFunctor := ComposeComputationalFunctors G F |}.
  End specialized.
End FunctorComposition.

Section IdentityFunctor.
  (** There is an identity functor.  It does the obvious thing. *)
  Section computational.
    Context `(C : @ComputationalCategory objC).

    Definition IdentityComputationalFunctor : ComputationalFunctor C C
      := Build_ComputationalFunctor C C
                                    (fun x => x)
                                    (fun _ _ m => m).
  End computational.

  Section is_specialized.
    Context `(HC : @IsSpecializedCategory objC C).

    Global Instance IdentityIsSpecializedFunctor
    : IsSpecializedFunctor (IdentityComputationalFunctor C).
    Proof.
      rewrite_functor.
    Qed.
  End is_specialized.

  Section specialized.
    Context `(C : @SpecializedCategory objC).

    Definition IdentityFunctor : SpecializedFunctor C C
      := {| UnderlyingCFunctor := IdentityComputationalFunctor C |}.
  End specialized.
End IdentityFunctor.

Section IdentityFunctorLemmas.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Lemma LeftIdentityFunctor (F : SpecializedFunctor D C) : ComposeFunctors (IdentityFunctor _) F = F.
    apply SpecializedFunctor_eq.
    destruct_head @SpecializedFunctor; destruct_head @ComputationalFunctor;
    expand.
    reflexivity.
  Qed.

  Lemma RightIdentityFunctor (F : SpecializedFunctor C D) : ComposeFunctors F (IdentityFunctor _) = F.
    apply SpecializedFunctor_eq.
    destruct_head @SpecializedFunctor; destruct_head @ComputationalFunctor;
    expand.
    reflexivity.
  Qed.
End IdentityFunctorLemmas.

Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor using typeclasses eauto : category.
Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor using typeclasses eauto : functor.
Hint Immediate @LeftIdentityFunctor @RightIdentityFunctor : category functor.

Section FunctorCompositionLemmas.
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).

  Lemma ComposeFunctorsAssociativity (F : SpecializedFunctor B C) (G : SpecializedFunctor C D) (H : SpecializedFunctor D E) :
    ComposeFunctors (ComposeFunctors H G) F = ComposeFunctors H (ComposeFunctors G F).
    apply SpecializedFunctor_eq.
    destruct_head @SpecializedFunctor; destruct_head @ComputationalFunctor;
    expand.
    reflexivity.
  Qed.
End FunctorCompositionLemmas.

Hint Resolve @ComposeFunctorsAssociativity : category functor.
