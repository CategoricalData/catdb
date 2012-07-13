Require Import JMeq ProofIrrelevance.
Require Export SpecializedCategory Category.
Require Import Common StructureEquality FEqualDep.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

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

Section Functor.
  Variable C D : Category.

  Definition Functor := SpecializedFunctor C D.

  Section FunctorInterface.
    Variable F : Functor.

    Definition ObjectOf : forall c, D := Eval cbv beta delta [ObjectOf'] in F.(ObjectOf'). (* [forall], so we can name it in [Arguments] *)
    Definition MorphismOf : forall (s d : C) (m : C.(Morphism) s d), D.(Morphism) (ObjectOf s) (ObjectOf d)
      := Eval cbv beta delta [MorphismOf'] in F.(MorphismOf').
    Definition FCompositionOf : forall (s d d' : C) (m1 : C.(Morphism) s d) (m2 : C.(Morphism) d d'),
      MorphismOf _ _ (Compose m2 m1) = Compose (MorphismOf _ _ m2) (MorphismOf _ _ m1)
      := F.(FCompositionOf').
    Definition FIdentityOf : forall (o : C), MorphismOf _ _ (Identity o) = Identity (ObjectOf o)
      := F.(FIdentityOf').
  End FunctorInterface.
End Functor.

Identity Coercion Functor_SpecializedFunctor_Id : Functor >-> SpecializedFunctor.
Definition GeneralizeFunctor objC morC C objD morD D (F : @SpecializedFunctor objC morC C objD morD D) : Functor C D := F : Functor C D.
Arguments GeneralizeFunctor [objC morC C objD morD D] F /.
Coercion GeneralizeFunctor : SpecializedFunctor >-> Functor.
Coercion ObjectOf : Functor >-> Funclass.

Ltac present_obj_mor_obj_mor from to :=
  repeat match goal with
           | [ _ : appcontext[from ?obj ?mor ?C ?obj' ?mor' ?C'] |- _ ] => change (from obj mor C obj' mor' C') with (to C C') in *
           | [ |- appcontext[from ?obj ?mor ?C ?obj' ?mor' ?C'] ] => change (from obj mor C obj' mor' C') with (to C C') in *
         end.

Ltac present_spfunctor' := present_spcategory';
  present_obj_mor_obj_mor @ObjectOf' @ObjectOf; present_obj_mor_obj_mor @MorphismOf' @MorphismOf.
Ltac present_spfunctor := present_spcategory;
  present_obj_mor_obj_mor @ObjectOf' @ObjectOf; present_obj_mor_obj_mor @MorphismOf' @MorphismOf.

Arguments SpecializedFunctor {objC morC} C {objD morD} D.
Arguments Functor C D.
Arguments ObjectOf [C D] F c : simpl nomatch.
Arguments MorphismOf [C D] F [s d] m : simpl nomatch.

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
  Variables B C D E : Category.

  Hint Rewrite FCompositionOf FIdentityOf.

  Definition ComposeFunctors (G : Functor D E) (F : Functor C D) : Functor C E.
    refine {| ObjectOf' := (fun c => G (F c));
      MorphismOf' := (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
      |};
(*    abstract ( *)
    intros; present_spcategory; simpl in *.
    Set Printing All.
    generalize dependent (@Build_Category (Object C) (Morphism C) (UnderlyingCategory C)).
    Lemma baz : forall (X Y : Type) (f : X -> Y), (fun x => f x) = f.
      intros X Y f.
      change (fun x => f x) with f.
      reflexivity.
    Qed.

    Print Assumptions baz.
    Inductive focus (T : Type) : Type := focused : T -> focus T.
    Definition typeOf T (f : focus T) := match f with focused A => A end.
    assert (C' := focused (@Build_Category (Object C) (Morphism C) (UnderlyingCategory C))).

    change (@Build_Category (Object C) (Morphism C) (UnderlyingCategory C)) with (typeOf C').
    change (@Build_Category (Object C) (Morphism C) (UnderlyingCategory C)) with C'.
    unfold Object, Morphism, UnderlyingCategory in C'.
    simpl in C'.

    sanitize_spcategory.

    Record foo := { bar : Type }.
    Lemma baz : forall (f : foo), Build_foo (bar f) = f.
      intro f.
      unfold bar.
      Require Import ProofIrrelevance Eqdep.
      Print eq_rect_eq.
      Goal forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : @eq U p p),
       @eq (Q p) x (@eq_rect U p Q x p h).
        intros.
        unfold eq_rect.
        destruct h.
        change (@eq (Q p) x match h in (@eq _ _ y) return (Q y) with
               | eq_refl => x
               end) with (match h in (@eq _ _ y) return Prop with
               | eq_refl => @eq (Q p) x x
               end).
      Goal forall (A B : Type) (a : A) (A (pf : a = a)
      change (Build_foo match f return Type with
                      | Build_foo bar => bar
                      end) with (match f return foo with
                      | Build_foo bar => bar
                      end).
      change (match f return foo with | Build_foo bar => Build_foo bar end) with (match f return foo with | foo' => foo' end).
      change (match f return foo with | foo' => foo' end) with f.
      (*change (Build_foo (bar f)) with f. (* Error: Not convertible. *)*)
      destruct f; simpl; reflexivity.
    Qed.
    Goal
    Print baz.
    Eval simpl in fun f : foo =>
match f as f0 return (@eq foo (Build_foo (bar f0)) f0) with
| Build_foo bar0 => @eq_refl foo (Build_foo bar0)
end.


      unfold bar.
      cbv iota.
      change (Build_foo match f return Type with
                      | Build_foo bar => bar
                      end) with (match f return foo with
                      | Build_foo bar => Build_foo bar
                      end).

    simultaneous_rewrite Category_eta.
    change (@Build_Category (Object C) (Morphism C) (UnderlyingCategory C)) with C in *.
    match goal with
      | [ |- appcontext[@Build_Category (Object ?C) (Morphism ?C) (UnderlyingCategory ?C)] ] => progress change (@Build_Category (Object C) (Morphism C) (UnderlyingCategory C)) with C in *
    end.

    rewrite FCompositionOf.
    repeat rewrite FCompositionOf; repeat rewrite FIdentityOf; simpl in *. reflexivity
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

Section FunctorCompositionLemmas.
  Variables B C D E : Category.

  Lemma ComposeFunctorsAssociativity (F : Functor B C) (G : Functor C D) (H : Functor D E) :
    ComposeFunctors (ComposeFunctors H G) F = ComposeFunctors H (ComposeFunctors G F).
    functor_eq.
  Qed.
End FunctorCompositionLemmas.
