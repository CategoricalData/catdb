Require Import ProofIrrelevance JMeq.
Require Export Functor FEqualDep.
Require Import Common StructureEquality.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

Section Categories_NaturalTransformation.
  Variable C D : Category.
  Variable F G : Functor C D.

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
  Record NaturalTransformation := {
    ComponentsOf :> forall c : C.(Object), Morphism _ (F c) (G c);
    Commutes : forall s d (m : Morphism C s d),
      Compose (ComponentsOf d) (F.(MorphismOf) m) = Compose (G.(MorphismOf) m) (ComponentsOf s)
  }.
End Categories_NaturalTransformation.

Section NaturalTransformations_Equal.
  Lemma NaturalTransformations_Equal C D (F G : Functor C D) : forall (T U : NaturalTransformation F G),
    ComponentsOf T = ComponentsOf U
    -> T = U.
    destruct T, U; simpl; intros; repeat subst;
      f_equal; reflexivity || apply proof_irrelevance.
  Qed.

  Lemma NaturalTransformations_JMeq C D C' D' (F G : Functor C D) (F' G' : Functor C' D') (T : NaturalTransformation F G) (U : NaturalTransformation F' G') :
    C = C'
    -> D = D'
    -> (C = C' -> D = D' -> F == F')
    -> (C = C' -> D = D' -> G == G')
    -> (C = C' -> D = D' -> F == F' -> G == G' -> ComponentsOf T == ComponentsOf U)
    -> T == U.
    intros; repeat subst; firstorder; repeat subst;
      destruct T, U; simpl in *; intros; repeat subst;
        JMeq_eq;
        f_equal; apply proof_irrelevance.
  Qed.
End NaturalTransformations_Equal.

Ltac nt_eq_step_with tac :=
  structures_eq_step_with_tac ltac:(apply NaturalTransformations_Equal || apply NaturalTransformations_JMeq) tac.

Ltac nt_eq_with tac := repeat nt_eq_step_with tac.

Ltac nt_eq_step := nt_eq_step_with idtac.
Ltac nt_eq := nt_eq_with idtac.

Section NaturalTransformationComposition.
  Variable C D E : Category.
  Variable F F' F'' : Functor C D.
  Variable G G' : Functor D E.

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

  Definition NTComposeT (T' : NaturalTransformation F' F'') (T : NaturalTransformation F F') :
    NaturalTransformation F F''.
    refine {| ComponentsOf := (fun c => Compose (T' c) (T c)) |};
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
  Hint Resolve FCompositionOf.

  Lemma FCompositionOf2 : forall C D (F : Functor C D) x y z u (m1 : C.(Morphism) x z) (m2 : C.(Morphism) y x) (m3 : D.(Morphism) u _),
    Compose (MorphismOf F m1) (Compose (MorphismOf F m2) m3) = Compose (MorphismOf F (Compose m1 m2)) m3.
    intros; try_associativity eauto.
  Qed.

  Hint Rewrite FCompositionOf2.

  Definition NTComposeF (U : NaturalTransformation G G') (T : NaturalTransformation F F'):
    NaturalTransformation (ComposeFunctors G F) (ComposeFunctors G' F').
    refine (Build_NaturalTransformation (ComposeFunctors G F) (ComposeFunctors G' F')
      (fun c => Compose (G'.(MorphismOf) (T.(ComponentsOf) c)) (U.(ComponentsOf) (F c)))
      _). abstract (simpl; intros; autorewrite with core in *; trivial).
  Defined.
End NaturalTransformationComposition.

Section IdentityNaturalTransformation.
  Variable C D : Category.
  Variable F : Functor C D.

  (* There is an identity natrual transformation. *)
  Definition IdentityNaturalTransformation : NaturalTransformation F F.
    refine {| ComponentsOf := (fun c => Identity (F c))
      |};
    abstract t.
  Defined.

  Hint Resolve LeftIdentity RightIdentity.

  Lemma LeftIdentityNaturalTransformation (F' : Functor C D) (T : NaturalTransformation F' F) :
    NTComposeT IdentityNaturalTransformation T = T.
    nt_eq; auto.
  Qed.

  Lemma RightIdentityNaturalTransformation (F' : Functor C D) (T : NaturalTransformation F F') :
    NTComposeT T IdentityNaturalTransformation = T.
    nt_eq; auto.
  Qed.
End IdentityNaturalTransformation.

Hint Rewrite LeftIdentityNaturalTransformation RightIdentityNaturalTransformation.
