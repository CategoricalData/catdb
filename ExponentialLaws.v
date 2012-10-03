Require Import FunctionalExtensionality ProofIrrelevance.
Require Export FunctorCategory SumCategory ProductCategory Functor.
Require Import Common NatCategory FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Section Law0.
  Context `(C : @SpecializedCategory objC).

  Definition ExponentialLaw0Functor : SpecializedFunctor (C ^ 0) 1
    :=
    Build_SpecializedFunctor (C ^ 0) 1
    (fun _ => tt)
    (fun _ _ _ => eq_refl)
    (fun _ _ _ _ _ => eq_refl)
    (fun _ => eq_refl).

  Definition ExponentialLaw0Functor_Inverse_ObjectOf : (1 -> C ^ 0)%category.
  Proof.
    intro x; clear x.
    refine (Build_SpecializedFunctor 0 C
      (fun x => match x with end)
      (fun s d m => match s with end)
      _
      _
    );
    abstract (
      let x := fresh in intro x; case x
    ).
  Defined.

  Global Arguments ExponentialLaw0Functor_Inverse_ObjectOf / _.

  Definition ExponentialLaw0Functor_Inverse_MorphismOf s d (m : Morphism 1 s d) :
    Morphism (C ^ 0) (ExponentialLaw0Functor_Inverse_ObjectOf s) (ExponentialLaw0Functor_Inverse_ObjectOf d)
    := Build_SpecializedNaturalTransformation (ExponentialLaw0Functor_Inverse_ObjectOf s) (ExponentialLaw0Functor_Inverse_ObjectOf d)
    (fun c => match c with end)
    (fun s' d' m' => match s' return _ with end).

  Arguments ExponentialLaw0Functor_Inverse_MorphismOf / _ _ _.

  Definition ExponentialLaw0Functor_Inverse : SpecializedFunctor 1 (C ^ 0).
  Proof.
    refine (Build_SpecializedFunctor 1 (C ^ 0)
      ExponentialLaw0Functor_Inverse_ObjectOf
      ExponentialLaw0Functor_Inverse_MorphismOf
      _
      _
    );
    present_spcategory;
    abstract (
      intros;
        nt_eq;
        apply functional_extensionality_dep;
          let x := fresh in intro x; destruct x
    ).
  Defined.

  Lemma ExponentialLaw0 : ComposeFunctors ExponentialLaw0Functor ExponentialLaw0Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw0Functor_Inverse ExponentialLaw0Functor = IdentityFunctor _.
  Proof.
    split; functor_eq; try f_equal;
      functor_eq;
      nt_eq;
      hnf in *;
        repeat subst;
          trivial;
            repeat (apply functional_extensionality_dep; intro);
              destruct_head_hnf sum;
              destruct_head_hnf Empty_set;
              destruct_head_hnf unit;
              destruct_head_hnf @eq;
              try reflexivity;
                functor_eq;
                nt_eq;
                repeat (apply functional_extensionality_dep; intro);
                  repeat (apply functional_extensionality_dep_JMeq; intros);
                    destruct_head_hnf Empty_set.
  Qed.
End Law0.

Section Law0'.
  Context `(C : @SpecializedCategory objC).
  Variable c : objC.

  Definition ExponentialLaw0'Functor : SpecializedFunctor (0 ^ C) 0
    := Build_SpecializedFunctor (0 ^ C) 0
    (fun F => F c)
    (fun s d m => match (s c) with end)
    (fun x _ _ _ _ => match (x c) with end)
    (fun x => match (x c) with end).

  Definition ExponentialLaw0'Functor_Inverse : SpecializedFunctor 0 (0 ^ C)
    := Build_SpecializedFunctor 0 (0 ^ C)
    (fun x => match x with end)
    (fun s d m => match s with end)
    (fun x _ _ _ _ => match x with end)
    (fun x => match x with end).

  Lemma ExponentialLaw0' : ComposeFunctors ExponentialLaw0'Functor ExponentialLaw0'Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw0'Functor_Inverse ExponentialLaw0'Functor = IdentityFunctor _.
  Proof.
    split; functor_eq; destruct_head_hnf Empty_set;
      match goal with
        | [ x : _ |- _ ] => solve [ let H := fresh in pose proof (x c) as H; case H ]
      end.
  Qed.
End Law0'.

Section Law1.
  Context `(C : @SpecializedCategory objC).

  Definition ExponentialLaw1Functor : SpecializedFunctor (C ^ 1) C
    := Build_SpecializedFunctor (C ^ 1) C
    (fun F => F tt)
    (fun s d m => m tt)
    (fun _ _ _ _ _ => eq_refl)
    (fun _ => eq_refl).

  Definition ExponentialLaw1Functor_Inverse_ObjectOf : C -> (C ^ 1)%category.
  Proof.
    refine (fun c => Build_SpecializedFunctor 1 C
      (fun _ => c)
      (fun _ _ _ => Identity c)
      _
      _
    );
    present_spcategory;
    abstract (
      intros; auto
    ).
  Defined.

  Global Arguments ExponentialLaw1Functor_Inverse_ObjectOf / _.

  Definition ExponentialLaw1Functor_Inverse_MorphismOf s d (m : Morphism C s d) :
    Morphism (C ^ 1) (ExponentialLaw1Functor_Inverse_ObjectOf s) (ExponentialLaw1Functor_Inverse_ObjectOf d).
  Proof.
    hnf.
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun _ => m)
          _
        )
    end;
    simpl; present_spnt;
      abstract (
        intros; autorewrite with core;
          reflexivity
      ).
  Defined.

  Global Arguments ExponentialLaw1Functor_Inverse_MorphismOf / _ _ _.

  Definition ExponentialLaw1Functor_Inverse : SpecializedFunctor C (C ^ 1).
  Proof.
    refine (Build_SpecializedFunctor C (C ^ 1)
      ExponentialLaw1Functor_Inverse_ObjectOf
      ExponentialLaw1Functor_Inverse_MorphismOf
      _
      _
    );
    abstract nt_eq.
  Defined.

  Lemma ExponentialLaw1 : ComposeFunctors ExponentialLaw1Functor ExponentialLaw1Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw1Functor_Inverse ExponentialLaw1Functor = IdentityFunctor _.
  Proof.
    split; functor_eq; try f_equal;
      nt_eq;
      functor_eq;
      hnf in *; destruct_head_hnf sum; destruct_head_hnf Empty_set; destruct_head_hnf unit;
        repeat subst;
          trivial;
            match goal with
              | [ H : _ = _ |- _ ] => destruct H; subst_body; try rewrite FIdentityOf
            end;
            reflexivity.
  Qed.
End Law1.

Section Law1'.
  Context `(C : @SpecializedCategory objC).

  Let FunctorTo1 `(D : @SpecializedCategory objD) : SpecializedFunctor D 1
    := Build_SpecializedFunctor D 1
    (fun _ => tt)
    (fun _ _ _ => eq_refl)
    (fun _ _ _ _ _ => eq_refl)
    (fun _ => eq_refl).


  Definition ExponentialLaw1'Functor : SpecializedFunctor (1 ^ C) 1 := FunctorTo1 _.

  Definition ExponentialLaw1'Functor_Inverse : SpecializedFunctor 1 (1 ^ C).
  Proof.
    refine (Build_SpecializedFunctor 1 (1 ^ C)
      (fun _ => FunctorTo1 _)
      (fun s d m => Build_SpecializedNaturalTransformation (FunctorTo1 C) (FunctorTo1 C)
        (fun _ => Identity (C := 1) tt)
        (fun _ _ _ => eq_refl)
      )
      _
      _
    );
    abstract nt_eq.
  Defined.

  Lemma ExponentialLaw1' : ComposeFunctors ExponentialLaw1'Functor ExponentialLaw1'Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw1'Functor_Inverse ExponentialLaw1'Functor = IdentityFunctor _.
  Proof.
    split; functor_eq; try f_equal;
      nt_eq;
      functor_eq;
      hnf in *; destruct_head sum; destruct_head Empty_set; destruct_head unit; destruct_head @eq;
        repeat subst; subst_body;
          unfold Object;
            trivial;
              repeat match goal with
                       | _ => reflexivity
                       | [ H : _ |- _ ] => clear H
                       | [ |- context[@eq unit ?a ?b] ] => progress (case a; case b)
                       | [ |- JMeq.JMeq eq_refl ?x ] => progress destruct x
                       | _ => destruct_head_hnf @SpecializedNaturalTransformation; simpl in *
                     end.
  Qed.
End Law1'.

Section Law2.
  Context `(D : @SpecializedCategory objD).
  Context `(C1 : @SpecializedCategory objC1).
  Context `(C2 : @SpecializedCategory objC2).

  Section functor.
    Eval unfold Object in ((D ^ (C1 + C2)) -> ((D ^ C1) * (D ^ C2)))%category.
    Let ExponentialLaw2Functor_ObjectOf_ObjectOf_1 (F : SpecializedFunctor (C1 + C2) D) :
      C1 -> D
      := fun x => F (inl x).
    Let ExponentialLaw2Functor_ObjectOf_ObjectOf_2 (F : SpecializedFunctor (C1 + C2) D) :
      C2 -> D
      := fun x => F (inr x).

    Definition ExponentialLaw2Functor_ObjectOf_MorphismOf_1 (F : SpecializedFunctor (C1 + C2) D)
      s d (m : Morphism C1 s d) :
      Morphism D (ExponentialLaw2Functor_ObjectOf_ObjectOf_1 F s) (ExponentialLaw2Functor_ObjectOf_ObjectOf_1 F d)
      := F.(MorphismOf) (s := inl _) (d := inl _) m.
    Definition ExponentialLaw2Functor_ObjectOf_MorphismOf_2 (F : SpecializedFunctor (C1 + C2) D)
      s d (m : Morphism C2 s d) :
      Morphism D (ExponentialLaw2Functor_ObjectOf_ObjectOf_2 F s) (ExponentialLaw2Functor_ObjectOf_ObjectOf_2 F d)
      := F.(MorphismOf) (s := inr _) (d := inr _) m.

    Arguments ExponentialLaw2Functor_ObjectOf_MorphismOf_1 / _ _ _ _.
    Arguments ExponentialLaw2Functor_ObjectOf_MorphismOf_2 / _ _ _ _.

    Definition ExponentialLaw2Functor_ObjectOf : SpecializedFunctor (C1 + C2) D -> (SpecializedFunctor C1 D) * (SpecializedFunctor C2 D).
    Proof.
      intro F.
      match goal with
        | [ |- prod (SpecializedFunctor ?C1 ?D) (SpecializedFunctor ?C2 ?D) ] =>
          refine (Build_SpecializedFunctor C1 D
            (ExponentialLaw2Functor_ObjectOf_ObjectOf_1 F)
            (ExponentialLaw2Functor_ObjectOf_MorphismOf_1 F)
            _
            _
            ,
            Build_SpecializedFunctor C2 D
            (ExponentialLaw2Functor_ObjectOf_ObjectOf_2 F)
            (ExponentialLaw2Functor_ObjectOf_MorphismOf_2 F)
            _
            _
          )
      end;
      simpl; subst_body; simpl; present_spcategory;
        abstract (
          intros; simpl;
            try rewrite <- FCompositionOf;
              try rewrite <- FIdentityOf;
                trivial
        ).
    Defined.

    Definition ExponentialLaw2Functor_MorphismOf_ComponentsOf_1 s d (m : Morphism (D ^ (C1 + C2)) s d) :
      forall c : C1,
        Morphism D ((fst (ExponentialLaw2Functor_ObjectOf s)) c) ((fst (ExponentialLaw2Functor_ObjectOf d)) c)
        := fun c => m (inl c).
    Definition ExponentialLaw2Functor_MorphismOf_ComponentsOf_2 s d (m : Morphism (D ^ (C1 + C2)) s d) :
      forall c : C2,
        Morphism D ((snd (ExponentialLaw2Functor_ObjectOf s)) c) ((snd (ExponentialLaw2Functor_ObjectOf d)) c)
        := fun c => m (inr c).

    Global Arguments ExponentialLaw2Functor_MorphismOf_ComponentsOf_1 _ _ _ _ /.
    Global Arguments ExponentialLaw2Functor_MorphismOf_ComponentsOf_2 _ _ _ _ /.

    Definition ExponentialLaw2Functor_MorphismOf s d
      (m : Morphism (D ^ (C1 + C2)) s d) :
      Morphism ((D ^ C1) * (D ^ C2)) (ExponentialLaw2Functor_ObjectOf s) (ExponentialLaw2Functor_ObjectOf d).
    Proof.
      hnf; unfold FunctorCategory, Morphism.
      match goal with
        | [ |- prod (SpecializedNaturalTransformation ?F1 ?G1) (SpecializedNaturalTransformation ?F2 ?G2) ] =>
          refine (Build_SpecializedNaturalTransformation F1 G1
            (@ExponentialLaw2Functor_MorphismOf_ComponentsOf_1 s d m)
            _
            ,
            Build_SpecializedNaturalTransformation F2 G2
            (@ExponentialLaw2Functor_MorphismOf_ComponentsOf_2 s d m)
            _
          )
      end;
      present_spfunctor; simpl; subst_body; simpl;
        abstract (
          intros; simpl;
            auto
        ).
    Defined.

    Definition ExponentialLaw2Functor : SpecializedFunctor (D ^ (C1 + C2)) ((D ^ C1) * (D ^ C2)).
    Proof.
      match goal with
        | [ |- SpecializedFunctor ?C ?D ] =>
          refine (Build_SpecializedFunctor C D
            ExponentialLaw2Functor_ObjectOf
            ExponentialLaw2Functor_MorphismOf
            _
            _
          )
      end;
      present_spnt; intros;
        abstract (intros; simpl; simpl_eq; nt_eq).
    Defined.
  End functor.

  Section inverse.
    Let ExponentialLaw2Functor_Inverse_ObjectOf_ObjectOf (F : SpecializedFunctor C1 D * SpecializedFunctor C2 D) :
      C1 + C2 -> D
      := (fun x => match x with
                     | inl x' => (fst F) x'
                     | inr x' => (snd F) x'
                   end).

    Definition ExponentialLaw2Functor_Inverse_ObjectOf_MorphismOf (F : SpecializedFunctor C1 D * SpecializedFunctor C2 D)
      s d (m : Morphism (C1 + C2) s d) :
      Morphism D (ExponentialLaw2Functor_Inverse_ObjectOf_ObjectOf F s) (ExponentialLaw2Functor_Inverse_ObjectOf_ObjectOf F d)
      := match (s, d) as sd
           return
           (Morphism (C1 + C2) (fst sd) (snd sd) ->
             D.(Morphism)
             match (fst sd) with
               | inl x' => (fst F) x'
               | inr x' => (snd F) x'
             end
             match (snd sd) with
               | inl x' => (fst F) x'
               | inr x' => (snd F) x'
             end)
           with
           | (inl s', inl d') => MorphismOf (fst F) (s := s') (d := d')
           | (inr s', inr d') => MorphismOf (snd F) (s := s') (d := d')
           | _ => (fun x => match x with end)
         end m.

    Arguments ExponentialLaw2Functor_Inverse_ObjectOf_MorphismOf / _ _ _ _.

    Definition ExponentialLaw2Functor_Inverse_ObjectOf : SpecializedFunctor C1 D * SpecializedFunctor C2 D -> SpecializedFunctor (C1 + C2) D.
    Proof.
      intro F.
      match goal with
        | [ |- SpecializedFunctor ?C ?D ] =>
          refine (Build_SpecializedFunctor C D
            (ExponentialLaw2Functor_Inverse_ObjectOf_ObjectOf F)
            (ExponentialLaw2Functor_Inverse_ObjectOf_MorphismOf F)
            _
            _
          )
      end;
      abstract (
        simpl in *; subst_body; simpl in *;
          destruct_hypotheses;
          repeat (let H := fresh in intro H; destruct H; simpl in *);
            intros; destruct_type Empty_set; present_spcategory;
              auto
      ).
    Defined.

    Definition ExponentialLaw2Functor_Inverse_MorphismOf_ComponentsOf (s d : Object ((D ^ C1) * (D ^ C2)))
      (m : Morphism ((D ^ C1) * (D ^ C2)) s d) :
      forall (c : Object (C1 + C2)),
        Morphism D ((ExponentialLaw2Functor_Inverse_ObjectOf s) c) ((ExponentialLaw2Functor_Inverse_ObjectOf d) c)
        := (fun c => match c as c'
                       return
                       (Morphism D
                         match c' with
                           | inl x' => (fst s) x'
                           | inr x' => (snd s) x'
                         end
                         match c' with
                           | inl x' => (fst d) x'
                           | inr x' => (snd d) x'
                         end)
                       with
                       | inl o => (fst m) o
                       | inr o => (snd m) o
                     end).

    Definition ExponentialLaw2Functor_Inverse_MorphismOf (s d : Object ((D ^ C1) * (D ^ C2)))
      (m : Morphism ((D ^ C1) * (D ^ C2)) s d) :
      Morphism (D ^ (C1 + C2)) (ExponentialLaw2Functor_Inverse_ObjectOf s) (ExponentialLaw2Functor_Inverse_ObjectOf d).
    Proof.
      hnf.
      match goal with
        | [ |- SpecializedNaturalTransformation ?F ?G ] =>
          refine (Build_SpecializedNaturalTransformation F G
            (@ExponentialLaw2Functor_Inverse_MorphismOf_ComponentsOf s d m)
            _
          )
      end;
      abstract (
        present_spfunctor; repeat (let H := fresh in intro H; destruct H);
          simpl in *;
            intros;
              auto
      ).
    Defined.

    Definition ExponentialLaw2Functor_Inverse : SpecializedFunctor ((D ^ C1) * (D ^ C2)) (D ^ (C1 + C2)).
    Proof.
      match goal with
        | [ |- SpecializedFunctor ?C ?D ] =>
          refine (Build_SpecializedFunctor C D
            ExponentialLaw2Functor_Inverse_ObjectOf
            ExponentialLaw2Functor_Inverse_MorphismOf
            _
            _
          )
      end;
      simpl in *; present_spnt;
        repeat (let H := fresh in intro H; destruct H);
          simpl in *;
            nt_eq;
            simpl in *;
              apply functional_extensionality_dep; let H := fresh in intro H; destruct H;
                unfold ExponentialLaw2Functor_Inverse_MorphismOf, ExponentialLaw2Functor_Inverse_MorphismOf_ComponentsOf, ExponentialLaw2Functor_Inverse_ObjectOf_ObjectOf;
                  simpl in *;
                    reflexivity.
    Defined.
  End inverse.

  Lemma ExponentialLaw2 : ComposeFunctors ExponentialLaw2Functor ExponentialLaw2Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw2Functor_Inverse ExponentialLaw2Functor = IdentityFunctor _.
  Admitted.
End Law2.

Section Law3.
  Context `(C1 : @SpecializedCategory objC1).
  Context `(C2 : @SpecializedCategory objC2).
  Context `(D : @SpecializedCategory objD).

  Definition ExponentialLaw3Functor : SpecializedFunctor ((C1 * C2) ^ D) (C1 ^ D * C2 ^ D).
  Admitted.

  Definition ExponentialLaw3Functor_Inverse : SpecializedFunctor (C1 ^ D * C2 ^ D) ((C1 * C2) ^ D).
  Admitted.

  Lemma ExponentialLaw3 : ComposeFunctors ExponentialLaw3Functor ExponentialLaw3Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw3Functor_Inverse ExponentialLaw3Functor = IdentityFunctor _.
  Admitted.
End Law3.

Section Law4.
  Context `(C1 : @SpecializedCategory objC1).
  Context `(C2 : @SpecializedCategory objC2).
  Context `(D : @SpecializedCategory objD).

  Definition ExponentialLaw4Functor : SpecializedFunctor ((D ^ C1) ^ C2) (D ^ (C1 * C2)).
  Admitted.

  Definition ExponentialLaw4Functor_Inverse : SpecializedFunctor (D ^ (C1 * C2)) ((D ^ C1) ^ C2).
  Admitted.

  Lemma ExponentialLaw4 : ComposeFunctors ExponentialLaw4Functor ExponentialLaw4Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw4Functor_Inverse ExponentialLaw4Functor = IdentityFunctor _.
  Admitted.
End Law4.
