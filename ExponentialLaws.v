Require Import JMeq FunctionalExtensionality ProofIrrelevance.
Require Export FunctorCategory SumCategory ProductCategory Functor.
Require Import Common NatCategory FEqualDep InitialTerminalCategory.
Require Import FunctorProduct ProductInducedFunctors FunctorialComposition.
Require Import SumInducedFunctors CanonicalStructureSimplification.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Hint Immediate
      TerminalCategoryFunctorUnique InitialCategoryFunctorUnique
      InitialCategoryFunctor'Unique.
Local Hint Resolve Functor_eq Functor_JMeq NaturalTransformation_eq
      NaturalTransformation_JMeq eq_JMeq.

Section Law0.
  Variable C : Category.

  Definition ExponentialLaw0Functor : Functor (C ^ 0) 1
    := FunctorTo1 _.
  Definition ExponentialLaw0Functor_Inverse : Functor 1 (C ^ 0)
    := FunctorFrom1 (C ^ 0) (FunctorFrom0 _).

  Lemma ExponentialLaw0
  : ComposeFunctors ExponentialLaw0Functor ExponentialLaw0Functor_Inverse
    = IdentityFunctor _
    /\ ComposeFunctors ExponentialLaw0Functor_Inverse ExponentialLaw0Functor
       = IdentityFunctor _.
  Proof.
    split; auto.
    apply Functor_eq; auto;
    nt_eq; auto;
    destruct_head_hnf Empty_set.
  Qed.
End Law0.

Section Law0'.
  Variable C : Category.
  Variable c : C.

  Definition ExponentialLaw0'Functor : Functor (0 ^ C) 0
    := Build_Functor (0 ^ C) 0
                                (fun F => F c)
                                (fun s d m => match (s c) with end)
                                (fun x _ _ _ _ => match (x c) with end)
                                (fun x => match (x c) with end).

  Definition ExponentialLaw0'Functor_Inverse : Functor 0 (0 ^ C)
    := FunctorFrom0 _.

  Lemma ExponentialLaw0'
  : ComposeFunctors ExponentialLaw0'Functor ExponentialLaw0'Functor_Inverse
    = IdentityFunctor _
    /\
    ComposeFunctors ExponentialLaw0'Functor_Inverse ExponentialLaw0'Functor
    = IdentityFunctor _.
  Proof.
    split; auto;
    apply Functor_eq; simpl; intros; expand; auto.
    match goal with
        [ |- context[match ?E with end] ] => solve [ case E ]
    end.
  Qed.
End Law0'.

Section Law1.
  Variable C : Category.

  Definition ExponentialLaw1Functor : Functor (C ^ 1) C
    := Build_Functor (C ^ 1) C
                                (fun F => F tt)
                                (fun s d m => m tt)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Definition ExponentialLaw1Functor_Inverse_MorphismOf
             s d (m : Morphism C s d)
  : Morphism (C ^ 1)
             (FunctorFrom1 _ s)
             (FunctorFrom1 _ d).
  Proof.
    hnf.
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
                                            (fun _ => m)
                                            _)
    end;
      simpl;
      abstract (
          intros; autorewrite with morphism;
          reflexivity
        ).
  Defined.

  Global Arguments ExponentialLaw1Functor_Inverse_MorphismOf / _ _ _.

  Definition ExponentialLaw1Functor_Inverse : Functor C (C ^ 1).
  Proof.
    refine (Build_Functor
              C (C ^ 1)
              (@FunctorFrom1 _)
              ExponentialLaw1Functor_Inverse_MorphismOf
              _
              _
           );
    abstract nt_eq.
  Defined.

  Lemma ExponentialLaw1
  : ComposeFunctors ExponentialLaw1Functor ExponentialLaw1Functor_Inverse
    = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw1Functor_Inverse ExponentialLaw1Functor
    = IdentityFunctor _.
  Proof.
    abstract (
        split; repeat (functor_eq || nt_eq);
        destruct_head_hnf @eq;
        destruct_head_hnf unit;
        trivial;
        rewrite FIdentityOf;
        trivial
      ).
  Qed.
End Law1.

Section Law1'.
  Variable C : Category.

  Definition ExponentialLaw1'Functor : Functor (1 ^ C) 1
    := FunctorTo1 _.

  Definition ExponentialLaw1'Functor_Inverse : Functor 1 (1 ^ C).
  Proof.
    refine (Build_Functor
              1 (1 ^ C)
              (fun _ => FunctorTo1 _)
              (fun s d m => Build_NaturalTransformation
                              (FunctorTo1 C) (FunctorTo1 C)
                              (fun _ => Identity (C := 1) tt)
                              (fun _ _ _ => eq_refl))
              _
              _
           );
    abstract nt_eq.
  Defined.

  Lemma ExponentialLaw1'
  : ComposeFunctors ExponentialLaw1'Functor ExponentialLaw1'Functor_Inverse
    = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw1'Functor_Inverse ExponentialLaw1'Functor
    = IdentityFunctor _.
  Proof.
    split; auto.
    apply Functor_eq; auto;
    nt_eq; auto.
  Qed.
End Law1'.

Section Law2.
  Variable D : Category.
  Variable C1 : Category.
  Variable C2 : Category.

  Definition ExponentialLaw2Functor
  : Functor (D ^ (C1 + C2)) ((D ^ C1) * (D ^ C2))
    := FunctorProduct (FunctorialComposition C1 (C1 + C2) D ⟨ - , inl_Functor _ _ ⟩)
                      (FunctorialComposition C2 (C1 + C2) D ⟨ - , inr_Functor _ _ ⟩).

  Definition ExponentialLaw2Functor_Inverse
  : Functor ((D ^ C1) * (D ^ C2)) (D ^ (C1 + C2)).
  Proof.
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor
                  C D
                  (fun FG => sum_Functor (fst FG) (snd FG))
                  (fun _ _ m => sum_Functor_Functorial (fst m) (snd m))
                  _
                  _)
    end;
    simpl in *;
    abstract (
        nt_eq; intros;
        destruct_head_hnf @prod;
        destruct_head_hnf @sum;
        reflexivity
      ).
  Defined.


  Lemma ExponentialLaw2
  : ComposeFunctors ExponentialLaw2Functor ExponentialLaw2Functor_Inverse
    = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw2Functor_Inverse ExponentialLaw2Functor
    = IdentityFunctor _.
  Proof.
    abstract (repeat
                match goal with
                  | _ => reflexivity
                  | _ => split
                  | _ => progress (simpl in *; intros; trivial)
                  | _ => progress repeat subst
                  | _ => progress destruct_head_hnf @Empty_set
                  | _ => progress simpl_eq
                  | _ => progress apply Functor_eq
                  | _ => progress nt_eq
                  | _ => progress rsimplify_morphisms
                  | _ => progress destruct_head_hnf @sum
                  | _ => progress rewrite FIdentityOf
                end).
  Qed.
End Law2.

Section Law3.
  Variable C1 : Category.
  Variable C2 : Category.
  Variable D : Category.

  Definition ExponentialLaw3Functor
  : Functor ((C1 * C2) ^ D) (C1 ^ D * C2 ^ D).
    let F := match goal with | [ |- Functor ?F ?G ] => constr:(F) end in
    let G := match goal with | [ |- Functor ?F ?G ] => constr:(G) end in
    refine (Build_Functor
              F G
              (fun H => (ComposeFunctors fst_Functor H,
                         ComposeFunctors snd_Functor H))
              (fun s d m =>
                 (MorphismOf (FunctorialComposition D (C1 * C2) C1)
                             (s := (_, _))
                             (d := (_, _))
                             (Identity (C := _ ^ _) fst_Functor, m),
                  MorphismOf (FunctorialComposition D (C1 * C2) C2)
                             (s := (_, _))
                             (d := (_, _))
                             (Identity (C := _ ^ _) snd_Functor, m)))
              _
              _
           );
    abstract (
        intros;
        simpl;
        simpl_eq;
        apply NaturalTransformation_eq;
        simpl; intros;
        rsimplify_morphisms;
        reflexivity
      ).
  Defined.

  Definition ExponentialLaw3Functor_Inverse
  : Functor (C1 ^ D * C2 ^ D) ((C1 * C2) ^ D).
    let FG := (match goal with
                   [ |- Functor ?F ?G ] => constr:(F, G)
               end) in
    refine (Build_Functor
              (fst FG) (snd FG)
              (fun H => FunctorProduct
                          (@fst_Functor (C1 ^ D) (C2 ^ D) H)
                          (@snd_Functor (C1 ^ D) (C2 ^ D) H))
              (fun _ _ m => FunctorProductFunctorial (fst m) (snd m))
              _
              _);
      abstract (
          simpl; intros;
          simpl_eq;
          nt_eq
        ).
  Defined.


  Lemma ExponentialLaw3
  : ComposeFunctors ExponentialLaw3Functor ExponentialLaw3Functor_Inverse
    = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw3Functor_Inverse ExponentialLaw3Functor
    = IdentityFunctor _.
  Proof.
    abstract (
        repeat
          match goal with
            | _ => reflexivity
            | _ => split
            | _ => progress (simpl; intros; trivial)
            | _ => progress repeat subst
            | _ => progress JMeq_eq
            | _ => progress simpl_eq
            | _ => progress apply Functor_eq
            | _ => progress apply NaturalTransformation_JMeq
            | _ => rsimplify_morphisms
          end
      ).
  Qed.
End Law3.

Section Law4.
  Variable C1 : Category.
  Variable C2 : Category.
  Variable D : Category.

  Section functor.
    Local Ltac do_exponential4 := intros; simpl;
      repeat (simpl;
        match goal with
          | _ => reflexivity
          | _ => rewrite !FCompositionOf
          | _ => rewrite !FIdentityOf
          | _ => rewrite !LeftIdentity
          | _ => rewrite !RightIdentity
          | _ => try_associativity ltac:(rewrite !Commutes)
          | _ => rewrite ?Associativity; apply f_equal
          | _ => rewrite <- ?Associativity; apply f_equal2; try reflexivity; []
        end).

    Definition ExponentialLaw4Functor_ObjectOf : ((D ^ C1) ^ C2)%category -> (D ^ (C1 * C2))%category.
    Proof.
      intro F; hnf in F |- *.
      match goal with
        | [ |- Functor ?C ?D ] =>
          refine (Build_Functor C D
            (fun c1c2 => F (snd c1c2) (fst c1c2))
            (fun s1s2 d1d2 m1m2 => Compose ((F (snd d1d2)).(MorphismOf) (fst m1m2)) ((F.(MorphismOf) (snd m1m2)) (fst s1s2)))
            _
            _
          )
      end;
      abstract do_exponential4.
    Defined.

    Definition ExponentialLaw4Functor_MorphismOf s d (m : Morphism ((D ^ C1) ^ C2) s d) :
      Morphism (D ^ (C1 * C2)) (ExponentialLaw4Functor_ObjectOf s) (ExponentialLaw4Functor_ObjectOf d).
    Proof.
      exists (fun c => (m (snd c)) (fst c));
        abstract (
          do_exponential4;
          match goal with
            | [ |- Compose (ComponentsOf ?T ?x) (ComponentsOf ?U _) = Compose (ComponentsOf ?T' _) (ComponentsOf ?U' _) ] =>
              cut (Compose T U = Compose T' U');
                [ let H := fresh in intro H; simpl in H;
                  exact (f_equal (fun T => ComponentsOf T (fst s0)) H)
                  | rewrite Commutes; reflexivity
                ]
          end
        ).
    Defined.

    Definition ExponentialLaw4Functor : Functor ((D ^ C1) ^ C2) (D ^ (C1 * C2)).
    Proof.
      match goal with
        | [ |- Functor ?C ?D ] =>
          refine (Build_Functor C D
            ExponentialLaw4Functor_ObjectOf
            ExponentialLaw4Functor_MorphismOf
            _
            _
          )
      end;
      abstract nt_eq.
    Defined.
  End functor.

  Section inverse.
    Local Ltac do_exponential4_inverse := intros; simpl;
      repeat (simpl;
        match goal with
          | _ => reflexivity
          | _ => rewrite <- !FCompositionOf
          | _ => rewrite !FIdentityOf
          | _ => rewrite !LeftIdentity
          | _ => rewrite !RightIdentity
          | _ => try_associativity ltac:(rewrite !Commutes)
          | _ => rewrite ?Associativity; apply f_equal
          | _ => rewrite <- ?Associativity; apply f_equal2; try reflexivity; []
        end).


    Section ObjectOf.
      Variable F : Functor (C1 * C2) D.

      Definition ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf : C2 -> (D ^ C1)%category.
      Proof.
        intro c2.
        hnf.
        match goal with
          | [ |- Functor ?C ?D ] =>
            refine (Build_Functor C D
              (fun c1 => F (c1, c2))
              (fun s1 d1 m1 => F.(MorphismOf) (s := (s1, c2)) (d := (d1, c2)) (m1, Identity c2))
              _
              _
            )
        end;
        abstract do_exponential4_inverse.
      Defined.

      Definition ExponentialLaw4Functor_Inverse_ObjectOf_MorphismOf s d (m : Morphism C2 s d) :
        Morphism (D ^ C1) (ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf s) (ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf d).
      Proof.
        exists (fun c => F.(MorphismOf) (s := (c, s)) (d := (c, d)) (Identity c, m));
          abstract do_exponential4_inverse.
      Defined.

      Definition ExponentialLaw4Functor_Inverse_ObjectOf : ((D ^ C1) ^ C2)%category.
      Proof.
        hnf.
        match goal with
          | [ |- Functor ?C ?D ] =>
            refine (Build_Functor C D
              ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf
              ExponentialLaw4Functor_Inverse_ObjectOf_MorphismOf
              _
              _
            )
        end;
        abstract (nt_eq; do_exponential4_inverse).
      Defined.
    End ObjectOf.

    Section MorphismOf.
      Definition ExponentialLaw4Functor_Inverse_MorphismOf_ComponentsOf s d (m : Morphism (D ^ (C1 * C2)) s d) :
        forall c, Morphism (D ^ C1) ((ExponentialLaw4Functor_Inverse_ObjectOf s) c) ((ExponentialLaw4Functor_Inverse_ObjectOf d) c).
      Proof.
        intro c;
          exists (fun c' => m (c', c));
            abstract do_exponential4_inverse.
      Defined.

      Definition ExponentialLaw4Functor_Inverse_MorphismOf s d (m : Morphism (D ^ (C1 * C2)) s d) :
        Morphism ((D ^ C1) ^ C2) (ExponentialLaw4Functor_Inverse_ObjectOf s) (ExponentialLaw4Functor_Inverse_ObjectOf d).
      Proof.
        exists (ExponentialLaw4Functor_Inverse_MorphismOf_ComponentsOf m);
          abstract (nt_eq; do_exponential4_inverse).
      Defined.
    End MorphismOf.

    Arguments ExponentialLaw4Functor_Inverse_MorphismOf_ComponentsOf / _ _ _ _.

    Definition ExponentialLaw4Functor_Inverse : Functor (D ^ (C1 * C2)) ((D ^ C1) ^ C2).
    Proof.
      match goal with
        | [ |- Functor ?C ?D ] =>
          refine (Build_Functor C D
            ExponentialLaw4Functor_Inverse_ObjectOf
            ExponentialLaw4Functor_Inverse_MorphismOf
            _
            _
          )
      end;
      abstract nt_eq.
    Defined.
  End inverse.

  Lemma ExponentialLaw4
  : ComposeFunctors ExponentialLaw4Functor ExponentialLaw4Functor_Inverse
    = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw4Functor_Inverse ExponentialLaw4Functor
    = IdentityFunctor _.
  Proof.
    abstract (repeat match goal with
                       | _ => reflexivity
                       | _ => split
                       | _ => intro
                       | _ => progress (simpl in *; intros; subst; trivial)
                       | _ => apply eq_JMeq
                       | _ => apply Functor_eq
                       | _ => apply NaturalTransformation_eq
                       | _ => apply NaturalTransformation_JMeq
                       | _ => progress destruct_head prod

                       | _ => rewrite <- !FCompositionOf
                       | _ => rewrite !FIdentityOf
                       | _ => rewrite !LeftIdentity
                       | _ => rewrite !RightIdentity
                     end).
  Qed.
End Law4.
