Require Import FunctionalExtensionality ProofIrrelevance.
Require Export SmallCategory Functor NaturalTransformation FEqualDep.
Require Import Common.

Set Implicit Arguments.

Section Categories_NaturalTransformation.
  Variable C : SmallCategory.
  Variable D : Category.
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
  Record SmallNaturalTransformation := {
    SComponentsOf :> forall c : C.(SObject), Morphism _ (F c) (G c);
    SCommutes : forall s d (m : Morphism C s d),
      Compose (SComponentsOf d) (F.(MorphismOf) m) = Compose (G.(MorphismOf) m) (SComponentsOf s)
  }.
End Categories_NaturalTransformation.

Section SmallNaturalTransformations_Equal.
  Variable C : SmallCategory.
  Variable D : Category.
  Variables F G : Functor C D.

  Lemma SmallNaturalTransformations_Equal : forall (T U : SmallNaturalTransformation F G),
    SComponentsOf T = SComponentsOf U
    -> T = U.
    destruct T, U; simpl; intros; repeat subst;
      f_equal; reflexivity || apply proof_irrelevance.
  Qed.
End SmallNaturalTransformations_Equal.

Ltac snt_eq_step_with tac := intros; simpl;
  match goal with
    | _ => reflexivity
    | [ |- @eq (@SmallNaturalTransformation _ _ _ _) _ _ ] => apply SmallNaturalTransformations_Equal
    | [ |- (fun _ : ?A => _) = _ ] => apply (@functional_extensionality_dep A); intro
    | [ |- (forall _ : ?A, _) = _ ] => apply (@forall_extensionality_dep A); intro
    | [ |- _ = _ ] => apply proof_irrelevance
    | _ => tac
  end; repeat simpl.

Ltac snt_eq_with tac := repeat snt_eq_step_with tac.

Ltac snt_eq_step := snt_eq_step_with idtac.
Ltac snt_eq := snt_eq_with idtac.

Section Small2Large.
  Variable C : SmallCategory.
  Variable D : Category.
  Variable F G : Functor C D.

  Definition NaturalTransformationOnSmall := NaturalTransformation F G.

  Definition SmallNaturalTransformation2NaturalTransformation (T : SmallNaturalTransformation F G) : NaturalTransformation F G.
    refine {| ComponentsOf := (fun c : C.(Object) => T.(SComponentsOf) c); Commutes := T.(SCommutes) |}.
  Defined.

  Definition NaturalTransformation2SmallNaturalTransformation (T : NaturalTransformationOnSmall) : SmallNaturalTransformation F G.
    refine {| SComponentsOf := (fun c : C.(SObject) => T.(ComponentsOf) c); SCommutes := T.(Commutes) |}.
  Defined.
End Small2Large.

Arguments NaturalTransformationOnSmall {C D F G}.

Coercion SmallNaturalTransformation2NaturalTransformation : SmallNaturalTransformation >-> NaturalTransformation.
Identity Coercion NaturalTransformationOnSmall_NaturalTransformation_Id : NaturalTransformationOnSmall >-> NaturalTransformation.
Coercion NaturalTransformation2SmallNaturalTransformation : NaturalTransformationOnSmall >-> SmallNaturalTransformation.

Section Small2Large2Small_RoundTrip.
  Variable C : SmallCategory.
  Variable D : Category.
  Variables F G : Functor C D.
  Variable T : SmallNaturalTransformation F G.
  Variable T' : NaturalTransformation F G.

  Lemma SmallNaturalTransformation2NaturalTransformation2SmallNaturalTransformationId :
    NaturalTransformation2SmallNaturalTransformation (SmallNaturalTransformation2NaturalTransformation T) = T.
    snt_eq.
  Qed.

  Lemma NaturalTransformation2SmallNaturalTransformation2NaturalTransformationId :
    SmallNaturalTransformation2NaturalTransformation (NaturalTransformation2SmallNaturalTransformation T') = T'.
    nt_eq.
  Qed.
End Small2Large2Small_RoundTrip.

Hint Rewrite SmallNaturalTransformation2NaturalTransformation2SmallNaturalTransformationId NaturalTransformation2SmallNaturalTransformation2NaturalTransformationId.
Hint Resolve NaturalTransformation2SmallNaturalTransformation SmallNaturalTransformation2NaturalTransformation.

Definition SNTComposeT C D F F' F'' (T' : @SmallNaturalTransformation C D F' F'') (T : @SmallNaturalTransformation C D F F') :
    SmallNaturalTransformation F F''
    := NTComposeT T' T : NaturalTransformationOnSmall.
Definition SNTComposeF C D E F F' G G' (U : @SmallNaturalTransformation D E G G') (T : @SmallNaturalTransformation C D F F'):
    SmallNaturalTransformation (ComposeFunctors G F) (ComposeFunctors G' F')
    := NTComposeF U T : NaturalTransformationOnSmall.
Definition IdentitySmallNaturalTransformation C D F : @SmallNaturalTransformation C D F F
  := IdentityNaturalTransformation F : NaturalTransformationOnSmall.

Lemma LeftIdentitySmallNaturalTransformation C D F F' (T : @SmallNaturalTransformation C D F' F) :
    SNTComposeT (IdentitySmallNaturalTransformation _) T = T.
  snt_eq; autorewrite with core; auto.
Qed.

Lemma RightIdentitySmallNaturalTransformation C D F F' (T : @SmallNaturalTransformation C D F F') :
    SNTComposeT T (IdentitySmallNaturalTransformation _) = T.
  snt_eq; autorewrite with core; auto.
Qed.

Hint Unfold SNTComposeT SNTComposeF IdentitySmallNaturalTransformation.
Hint Rewrite LeftIdentitySmallNaturalTransformation RightIdentitySmallNaturalTransformation.
