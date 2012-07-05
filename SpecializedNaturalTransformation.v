Require Import JMeq ProofIrrelevance.
Require Export SpecializedFunctor.
Require Import Common StructureEquality.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

Section Categories_NaturalTransformation.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
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

  Section SpecializedNaturalTransformationInterface.
    Variable T : SpecializedNaturalTransformation.

    Definition ComponentsOf : forall c : C, D.(Morphism) (F c) (G c) := T.(ComponentsOf').
    Definition Commutes : forall (s d : C) (m : C.(Morphism) s d),
      Compose (ComponentsOf d) (F.(MorphismOf) m) = Compose (G.(MorphismOf) m) (ComponentsOf s)
      := T.(Commutes').
  End SpecializedNaturalTransformationInterface.
End Categories_NaturalTransformation.

Global Coercion ComponentsOf : SpecializedNaturalTransformation >-> Funclass.

Ltac present_spnt := present_spcategory; present_spfunctor;
  present_obj_mor_obj_mor @ComponentsOf' @ComponentsOf.

Section NaturalTransformations_Equal.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variables F G : SpecializedFunctor C D.

  Lemma SpecializedNaturalTransformations_Equal : forall (T U : SpecializedNaturalTransformation F G),
    ComponentsOf T = ComponentsOf U
    -> T = U.
    destruct T, U; simpl; intros; repeat subst;
      f_equal; reflexivity || apply proof_irrelevance.
  Qed.
End NaturalTransformations_Equal.

Ltac spnt_eq_step_with tac := structures_eq_step_with SpecializedNaturalTransformations_Equal tac.

Ltac spnt_eq_with tac := repeat spnt_eq_step_with tac.

Ltac spnt_eq_step := spnt_eq_step_with idtac.
Ltac spnt_eq := spnt_eq_with idtac.

Section NaturalTransformationComposition.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable objE : Type.
  Variable morE : objE -> objE -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable E : SpecializedCategory morE.
  Variables F F' F'' : SpecializedFunctor C D.
  Variables G G' : SpecializedFunctor D E.

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

  Definition SPNTComposeT (T' : SpecializedNaturalTransformation F' F'') (T : SpecializedNaturalTransformation F F') :
    SpecializedNaturalTransformation F F''.
    refine {| ComponentsOf' := (fun c => Compose (T' c) (T c)) |};
      (* XXX TODO: Find a way to get rid of [m] in the transitivity call *)
      abstract (intros; transitivity (Compose (T' _) (Compose (MorphismOf F' m) (T _))); try_associativity eauto).
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

  Lemma FCompositionOf2 : forall objC morC objD morD (C : @SpecializedCategory objC morC) (D : @SpecializedCategory objD morD)
    (F : SpecializedFunctor C D) x y z u (m1 : C.(Morphism) x z) (m2 : C.(Morphism) y x) (m3 : D.(Morphism) u _),
    Compose (MorphismOf F m1) (Compose (MorphismOf F m2) m3) = Compose (MorphismOf F (Compose m1 m2)) m3.
    intros; symmetry; try_associativity eauto.
  Qed.

  Hint Rewrite FCompositionOf2.

  Definition SPNTComposeF (U : SpecializedNaturalTransformation G G') (T : SpecializedNaturalTransformation F F'):
    SpecializedNaturalTransformation (ComposeSpecializedFunctors G F) (ComposeSpecializedFunctors G' F').
    refine (Build_SpecializedNaturalTransformation (ComposeSpecializedFunctors G F) (ComposeSpecializedFunctors G' F')
      (fun c => Compose (G'.(MorphismOf) (T.(ComponentsOf) c)) (U.(ComponentsOf) (F c)))
      _). abstract (simpl; intros; autorewrite with core in *; trivial).
  Defined.
End NaturalTransformationComposition.

Section IdentityNaturalTransformation.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable F : SpecializedFunctor C D.

  (* There is an identity natrual transformation. *)
  Definition IdentitySpecializedNaturalTransformation : SpecializedNaturalTransformation F F.
    refine {| ComponentsOf' := (fun c => Identity (F c))
      |};
    abstract t.
  Defined.

  Hint Resolve LeftIdentity RightIdentity.

  Lemma LeftIdentitySpecializedNaturalTransformation (F' : SpecializedFunctor C D) (T : SpecializedNaturalTransformation F' F) :
    SPNTComposeT IdentitySpecializedNaturalTransformation T = T.
    spnt_eq; auto.
  Qed.

  Lemma RightIdentitySpecializedNaturalTransformation (F' : SpecializedFunctor C D) (T : SpecializedNaturalTransformation F F') :
    SPNTComposeT T IdentitySpecializedNaturalTransformation = T.
    spnt_eq; auto.
  Qed.
End IdentityNaturalTransformation.

Hint Rewrite LeftIdentitySpecializedNaturalTransformation RightIdentitySpecializedNaturalTransformation.
