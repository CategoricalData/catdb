Require Import JMeq ProofIrrelevance.
Require Export Functor.
Require Import Common StructureEquality FEqualDep.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

Section SpecializedNaturalTransformation.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.
  Variables F G : SpecializedFunctor C D.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of functors is known as a natural transformation. Namely, given two functors
     [F : C -> D], [G : C -> D], a natural transformation [T: F -> G] is a collection of maps
     [T A : F A -> G A], one for each object [A] of [C], such that [(T B) ○ (F m) = (G m) ○ (T A)]
     for every map [m : A -> B] of [C]; that is, the following diagram is commutative:

           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    G m     V
     G A --------> G B
     **)
  Record SpecializedNaturalTransformation := {
    ComponentsOf' : forall c, morD (F.(ObjectOf') c) (G.(ObjectOf') c);
    Commutes' : forall s d (m : morC s d),
      D.(Compose') _ _ _ (ComponentsOf' d) (F.(MorphismOf') _ _ m) = D.(Compose') _ _ _ (G.(MorphismOf') _ _ m) (ComponentsOf' s)
  }.
End SpecializedNaturalTransformation.

Section NaturalTransformation.
  Variable C D : Category.
  Variable F G : Functor C D.

  Definition NaturalTransformation := SpecializedNaturalTransformation F G.

  Section NaturalTransformationInterface.
    Variable T : NaturalTransformation.

    Definition ComponentsOf : forall c : C, D.(Morphism) (F c) (G c) := Eval cbv beta delta [ComponentsOf'] in T.(ComponentsOf').
    Definition Commutes : forall (s d : C) (m : C.(Morphism) s d),
      Compose (ComponentsOf d) (F.(MorphismOf) m) = Compose (G.(MorphismOf) m) (ComponentsOf s)
      := T.(Commutes').
  End NaturalTransformationInterface.
End NaturalTransformation.

Arguments ComponentsOf [C D F G] T c : simpl nomatch.
Global Coercion ComponentsOf : NaturalTransformation >-> Funclass.

Identity Coercion NaturalTransformation_SpecializedNaturalTransformation_Id : NaturalTransformation >-> SpecializedNaturalTransformation.
Definition GeneralizeNaturalTransformation objC morC C objD morD D F G (T : @SpecializedNaturalTransformation objC morC C objD morD D F G) :
  NaturalTransformation F G := T.
Global Coercion GeneralizeNaturalTransformation : SpecializedNaturalTransformation >-> NaturalTransformation.

Ltac present_spnt' := present_spcategory'; present_spfunctor';
  present_obj_mor_obj_mor @ComponentsOf' @ComponentsOf;
  present_spcategory'.
Ltac present_spnt := present_spcategory; present_spfunctor;
  present_obj_mor_obj_mor @ComponentsOf' @ComponentsOf;
  present_spcategory(*;
  repeat match goal with
           | [ H : appcontext[@ObjectOf (@Object ?obj ?mor ?C)] |- _ ] => change (@Object obj mor C) with obj in H
           | [ H : appcontext[@ObjectOf _ _ (@Object ?obj ?mor ?C)] |- _ ] => change (@Object obj mor C) with obj in H
           | [ |- appcontext[@ObjectOf (@Object ?obj ?mor ?C)] ] => change (@Object obj mor C) with obj
           | [ |- appcontext[@ObjectOf _ _ (@Object ?obj ?mor ?C)] ] => change (@Object obj mor C) with obj
           | [ H : appcontext[@MorphismOf (@Object ?obj ?mor ?C)] |- _ ] => change (@Object obj mor C) with obj in H
           | [ H : appcontext[@MorphismOf _ _ (@Object ?obj ?mor ?C)] |- _ ] => change (@Object obj mor C) with obj in H
           | [ |- appcontext[@MorphismOf (@Object ?obj ?mor ?C)] ] => change (@Object obj mor C) with obj
           | [ |- appcontext[@MorphismOf _ _ (@Object ?obj ?mor ?C)] ] => change (@Object obj mor C) with obj
         end*).

Section NaturalTransformations_Equal.
  Lemma NaturalTransformations_Equal objC morC C objD morD D F G :
    forall (T U : @SpecializedNaturalTransformation objC morC C objD morD D F G),
    ComponentsOf T = ComponentsOf U
    -> T = U.
    destruct T, U; simpl; intros; repeat subst;
      f_equal; reflexivity || apply proof_irrelevance.
  Qed.

  Lemma NaturalTransformations_JMeq objC morC C objD morD D objC' morC' C' objD' morD' D' :
    forall F G F' G'
      (T : @SpecializedNaturalTransformation objC morC C objD morD D F G) (U : @SpecializedNaturalTransformation objC' morC' C' objD' morD' D' F' G'),
      objC = objC'
      -> objD = objD'
      -> (objC = objC' -> morC == morC')
      -> (objD = objD' -> morD == morD')
      -> (objC = objC' -> morC == morC' -> C == C')
      -> (objD = objD' -> morD == morD' -> D == D')
      -> (objC = objC' -> morC == morC' -> C == C' ->
        objD = objD' -> morD == morD' -> D == D' ->
        F == F')
      -> (objC = objC' -> morC == morC' -> C == C' ->
        objD = objD' -> morD == morD' -> D == D' ->
        G == G')
      -> (objC = objC' -> morC == morC' -> C == C' ->
        objD = objD' -> morD == morD' -> D == D' ->
        F == F' -> G == G' -> ComponentsOf T == ComponentsOf U)
      -> T == U.
    simpl; intros; subst objC' objD'; firstorder; subst morC' morD'; firstorder;
      JMeq_eq.
    repeat subst; JMeq_eq.
    apply NaturalTransformations_Equal; intros; repeat subst; trivial.
  Qed.
End NaturalTransformations_Equal.

Ltac nt_eq_step_with tac :=
  structures_eq_step_with_tac ltac:(apply NaturalTransformations_Equal || apply NaturalTransformations_JMeq) tac.

Ltac nt_eq_with tac := repeat nt_eq_step_with tac.

Ltac nt_eq_step := nt_eq_step_with idtac.
Ltac nt_eq := nt_eq_with idtac.

Section NaturalTransformationComposition.
  Variables C D : Category.
  Variables F F' : Functor C D.

  Hint Resolve Commutes f_equal f_equal2.
  Hint Rewrite Associativity.

  (*
     We have the diagram
          F
     C -------> D
          |
          |
          | T
          |
          V
     C -------> D
          F'
          |
          | T'
          |
          V
     C ------> D
          F''

     And we want the commutative diagram
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    F' m    V
     F' A -------> F' B
      |            |
      |            |
      | T' A       | T' B
      |            |
      V    F'' m   V
     F'' A ------> F'' B

  *)

  Definition NTComposeT (F'' : Functor C D) (T' : NaturalTransformation F' F'') (T : NaturalTransformation F F') :
    NaturalTransformation F F''.
    refine {| ComponentsOf' := (fun c => Compose (T' c) (T c)) |};
      abstract (intros; present_spnt; etransitivity; try_associativity ltac:(rewrite Commutes; reflexivity)).
  Defined.

  (*
     We have the diagram
          F          G
     C -------> D -------> E
          |          |
          |          |
          | T        | U
          |          |
          V          V
     C -------> D -------> E
          F'         G'

     And we want the commutative diagram
             G (F m)
     G (F A) -------> G (F B)
        |                |
        |                |
        | U (T A)        | U (T B)
        |                |
        V     G' (F' m)  V
     G' (F' A) -----> G' (F' B)

  *)
  (* XXX TODO: Automate this better *)

  Hint Rewrite Commutes.
  Hint Resolve f_equal2.
  Hint Extern 1 (_ = _) => apply FCompositionOf.

  Lemma FCompositionOf2 : forall (C D : Category)
    (F : Functor C D) x y z u (m1 : C.(Morphism) x z) (m2 : C.(Morphism) y x) (m3 : D.(Morphism) u _),
    Compose (MorphismOf F m1) (Compose (MorphismOf F m2) m3) = Compose (MorphismOf F (Compose m1 m2)) m3.
    intros; symmetry; try_associativity eauto.
  Qed.

  Hint Rewrite FCompositionOf2.

  Definition NTComposeF E (G G' : Functor D E) (U : NaturalTransformation G G') (T : NaturalTransformation F F'):
    NaturalTransformation (ComposeFunctors G F) (ComposeFunctors G' F').
    refine (Build_SpecializedNaturalTransformation (ComposeFunctors G F) (ComposeFunctors G' F')
      (fun c => Compose (G'.(MorphismOf) (T c)) (U (F c)))
      _);
    abstract (simpl; intros; present_spnt; autorewrite with core in *; trivial).
  Defined.
End NaturalTransformationComposition.

Section IdentityNaturalTransformation.
  Variables C D : Category.
  Variable F : Functor C D.

  (* There is an identity natrual transformation. *)
  Definition IdentityNaturalTransformation : NaturalTransformation F F.
    refine {| ComponentsOf' := (fun c => Identity (F c))
      |};
    abstract (present_spnt; t).
  Defined.

  Hint Resolve LeftIdentity RightIdentity.

  Lemma LeftIdentityNaturalTransformation (F' : Functor C D) (T : NaturalTransformation F' F) :
    NTComposeT IdentityNaturalTransformation T = T.
    nt_eq; auto.
  Qed.

  Lemma RightIdentityNaturalTransformation (F' : SpecializedFunctor C D) (T : SpecializedNaturalTransformation F F') :
    NTComposeT T IdentityNaturalTransformation = T.
    nt_eq; auto.
  Qed.
End IdentityNaturalTransformation.

Hint Rewrite LeftIdentityNaturalTransformation RightIdentityNaturalTransformation.
