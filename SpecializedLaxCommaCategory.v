Require Import ProofIrrelevance JMeq.
Require Export Category Functor ProductCategory NaturalTransformation SpecializedCommaCategory.
Require Import Common ComputableCategory FEqualDep CanonicalStructureSimplification DefinitionSimplification.
Require Import TypeclassSimplification. (* This must come after canonical structure simplification for things to work. *)

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Local Open Scope category_scope.

Section LaxSliceSpecializedCategory.
  Let Cat := ComputableCategory (fun x => x).
  Variables A B : SpecializedCategory.
  Let C := Cat.
  Variable S : SpecializedFunctor A C.
  Variable T : SpecializedFunctor B C.

  (** Quoting David Spivak:
     David: ok
       so an object of [FC ⇓ D] is a pair [(X, G)], where [X] is a
       finite category (or a small category or whatever you wanted)
       and [G : X --> D] is a functor.
       a morphism in [FC ⇓ D] is a ``natural transformation diagram''
       (as opposed to a commutative diagram, in which the natural
       transformation would be ``identity'')
       so a map in [FC ⇓ D] from [(X, G)] to [(X', G')] is a pair
       [(F, α)] where [F : X --> X'] is a functor and
       [α : G --> G' ○ F] is a natural transformation
       and the punchline is that there is a functor
       [colim : FC ⇓ D --> D]
     David: consider for yourself the case where [F : X --> X'] is
       identity ([X = X']) and (separately) the case where
       [α : G --> G ○ F] is identity.
       the point is, you've already done the work to get this colim
       functor.
       because every map in [FC ⇓ D] can be written as a composition
       of two maps, one where the [F]-part is identity and one where
       the [α]-part is identity.
       and you've worked both of those cases out already.
       *)
  Local Notation LaxCommaSpecializedCategory_Object :=
    (CommaSpecializedCategory_Object S T).
  Local Notation LaxCommaSpecializedCategory_ObjectT :=
    (CommaSpecializedCategory_ObjectT S T).

  Record LaxCommaSpecializedCategory_Morphism (αβf α'β'f' : LaxCommaSpecializedCategory_Object) :=
    {
      LCCM_g : Morphism A (CCO_α αβf) (CCO_α α'β'f');
      LCCM_h : Morphism B (CCO_β αβf) (CCO_β α'β'f');
      LCCM_φ : SpecializedNaturalTransformation (Compose (MorphismOf T LCCM_h) (CCO_f αβf))
                                                (Compose (CCO_f α'β'f') (MorphismOf S LCCM_g))
    }.

  Definition LaxCommaSpecializedCategory_MorphismT (αβf α'β'f' : LaxCommaSpecializedCategory_ObjectT)
    := { gh : ((A.(Morphism) (fst (projT1 αβf)) (fst (projT1 α'β'f'))) * (B.(Morphism) (snd (projT1 αβf)) (snd (projT1 α'β'f'))))
                & (SpecializedNaturalTransformation (Compose (T.(MorphismOf) (snd gh)) (projT2 αβf))
                                                    (Compose (projT2 α'β'f') (S.(MorphismOf) (fst gh))))
       }.

  Global Identity Coercion LaxCommaSpecializedCategory_Morphism_Id : LaxCommaSpecializedCategory_MorphismT >-> sigT.
  Global Coercion sigT_of_LCCM αβf α'β'f' (gh : LaxCommaSpecializedCategory_Morphism αβf α'β'f')
  : LaxCommaSpecializedCategory_MorphismT αβf α'β'f'
    := existT (fun gh : Morphism (A * B) (projT1 αβf) (projT1 α'β'f')
               => SpecializedNaturalTransformation (Compose (MorphismOf T (snd gh)) (projT2 αβf))
                                                   (Compose (projT2 α'β'f') (MorphismOf S (fst gh))))
              (LCCM_g gh, LCCM_h gh)
              (LCCM_φ gh).
  Global Coercion LCCM_of_sigT αβf α'β'f' (gh : LaxCommaSpecializedCategory_MorphismT αβf α'β'f')
  : LaxCommaSpecializedCategory_Morphism αβf α'β'f'
    := Build_LaxCommaSpecializedCategory_Morphism
         αβf
         α'β'f'
         _
         _
         (projT2 gh).

  Global Arguments LCCM_of_sigT _ _ _ / .
  Global Arguments sigT_of_LCCM _ _ _ / .

  Lemma LaxCommaSpecializedCategory_Morphism_eq' αβf α'β'f'
        (gh g'h' : LaxCommaSpecializedCategory_Morphism αβf α'β'f')
  : forall (Hg : LCCM_g gh = LCCM_g g'h')
           (Hh : LCCM_h gh = LCCM_h g'h'),
      match Hg in (_ = g), Hh in (_ = h)
            return SpecializedNaturalTransformation (Compose (MorphismOf T h) _)
                                                    (Compose _ (MorphismOf S g))
      with
        | eq_refl, eq_refl => LCCM_φ gh
      end = LCCM_φ g'h'
      -> gh = g'h'.
  Proof.
    destruct gh, g'h'; simpl.
    repeat (let H := fresh in intro H; destruct H).
    reflexivity.
  Defined.

  Lemma LaxCommaSpecializedCategory_Morphism_eq αβf α'β'f'
        (gh g'h' : LaxCommaSpecializedCategory_Morphism αβf α'β'f')
  : LCCM_g gh = LCCM_g g'h'
    -> LCCM_h gh = LCCM_h g'h'
    -> LCCM_φ gh == LCCM_φ g'h'
    -> gh = g'h'.
  Proof.
    destruct gh, g'h'; simpl.
    intros; repeat subst.
    reflexivity.
  Qed.

  Lemma LaxCommaSpecializedCategory_Morphism_JMeq αβf0 α'β'f'0 αβf1 α'β'f'1
        (gh : LaxCommaSpecializedCategory_Morphism αβf0 αβf1)
        (g'h' : LaxCommaSpecializedCategory_Morphism α'β'f'0 α'β'f'1)
  : αβf0 = α'β'f'0
    -> αβf1 = α'β'f'1
    -> LCCM_g gh == LCCM_g g'h'
    -> LCCM_h gh == LCCM_h g'h'
    -> LCCM_φ gh == LCCM_φ g'h'
    -> gh == g'h'.
  Proof.
    destruct gh, g'h'; simpl.
    intros; repeat subst.
    reflexivity.
  Qed.

  Definition LaxCommaSpecializedCategory_Compose s d d'
             (gh : LaxCommaSpecializedCategory_Morphism d d') (g'h' : LaxCommaSpecializedCategory_Morphism s d)
  : LaxCommaSpecializedCategory_Morphism s d'.
  Proof.
    exists (Compose (LCCM_g gh) (LCCM_g g'h')) (Compose (LCCM_h gh) (LCCM_h g'h')).
    let F := match goal with |- SpecializedNaturalTransformation ?F ?G => constr:(F) end in
    let G := match goal with |- SpecializedNaturalTransformation ?F ?G => constr:(G) end in
    let FC := match F with
                | appcontext[MorphismOf ?T (Compose (s := ?s) (d := ?d) (d' := ?d') ?m1 ?m2)]
                  => constr:(FCompositionOf T s d d' m2 m1)
              end in
    let GC := match G with
                | appcontext[MorphismOf ?T (Compose (s := ?s) (d := ?d) (d' := ?d') ?m1 ?m2)]
                  => constr:(FCompositionOf T s d d' m2 m1)
              end in
    refine (NTComposeT _ (NTComposeF (GeneralizedIdentityNaturalTransformation FC) (IdentityNaturalTransformation _)));
      refine (NTComposeT (NTComposeF (IdentityNaturalTransformation _) (GeneralizedIdentityNaturalTransformation (eq_sym GC))) _).
    change ComposeFunctors with (Compose (C := Cat)).
    unfold id in *.
    refine (NTComposeT _ (ComposeFunctorsAssociator1 _ _ _)).
    refine (NTComposeT (ComposeFunctorsAssociator1 _ _ _) _).
    change ComposeFunctors with (Compose (C := Cat)).
    refine (NTComposeT (NTComposeF (LCCM_φ gh) (IdentityNaturalTransformation _)) _).
    change ComposeFunctors with (Compose (C := Cat)).
    refine (NTComposeT (ComposeFunctorsAssociator2 _ _ _) _).
    change ComposeFunctors with (Compose (C := Cat)).
    refine (NTComposeF (IdentityNaturalTransformation _) (LCCM_φ g'h')).
  Defined.

  (*
  Let LaxCommaSpecializedCategory_pre_Compose' s d d'
             (gh : LaxCommaSpecializedCategory_Morphism d d') (g'h' : LaxCommaSpecializedCategory_Morphism s d)
  : LaxCommaSpecializedCategory_Morphism s d'.
  Proof.
    pose (LaxCommaSpecializedCategory_pre_Compose gh g'h') as m.
    exists (LCCM_g m) (LCCM_h m).
    assert (Hf : focus (LCCM_φ m)) by constructor;
      hnf in m; subst m; simpl in *.
    revert Hf; clear; intro Hf.
    unfold NTComposeT in Hf; simpl in *.
    let F := match goal with |- SpecializedNaturalTransformation ?F ?G => constr:(F) end in
    let G := match goal with |- SpecializedNaturalTransformation ?F ?G => constr:(G) end in
    let f := match type of Hf with | focus {| ComponentsOf := ?f ; Commutes := ?H |} => constr:(f) end in
    let H := match type of Hf with | focus {| ComponentsOf := ?f ; Commutes := ?H |} => constr:(H) end in
    refine (Build_SpecializedNaturalTransformation
              F G
              (fun x => ReifiedMorphismDenote
                          (ReifiedMorphismSimplify
                             (reified_morphism
                                (m := f x))))
              _);
      clear Hf;
      let s0 := fresh in
      let d0 := fresh in
      let m0 := fresh in
      intros s0 d0 m0;
        etransitivity; [ | etransitivity ];
        [ | revert s0 d0 m0; exact H | ];
        instantiate;
        simpl;
        rsimplify_morphisms;
        f_equal.
    Defined. *)

  (*Global Arguments LaxCommaSpecializedCategory_Compose _ _ _ _ _ / .*)

  Definition LaxCommaSpecializedCategory_Identity o : LaxCommaSpecializedCategory_Morphism o o.
    exists (Identity (CCO_α o)) (Identity (CCO_β o)).

    let F := match goal with |- SpecializedNaturalTransformation ?F ?G => constr:(F) end in
    let G := match goal with |- SpecializedNaturalTransformation ?F ?G => constr:(G) end in
    let FI := match F with
                | appcontext[MorphismOf ?T (Identity ?x)]
                  => constr:(FIdentityOf T x)
              end in
    let GI := match G with
                | appcontext[MorphismOf ?T (Identity ?x)]
                  => constr:(FIdentityOf T x)
              end in
    refine (NTComposeT _ (NTComposeF (GeneralizedIdentityNaturalTransformation FI) (IdentityNaturalTransformation _)));
      refine (NTComposeT (NTComposeF (IdentityNaturalTransformation _) (GeneralizedIdentityNaturalTransformation (eq_sym GI))) _).
    change ComposeFunctors with (Compose (C := Cat)).
    let F := match goal with |- SpecializedNaturalTransformation ?F ?G => constr:(F) end in
    let G := match goal with |- SpecializedNaturalTransformation ?F ?G => constr:(G) end in
    refine (Build_SpecializedNaturalTransformation F G
                                                   (fun c => Identity (F c))
                                                   _).
    clear; intros; unfold id in *; simpl in *.
    abstract (autorewrite with morphism; reflexivity).
  Defined.

  Global Arguments LaxCommaSpecializedCategory_Identity _ / .

  Local Ltac lax_comma_t :=
    intros;
    destruct_head LaxCommaSpecializedCategory_Morphism;
    simpl in *;
    simpl_eq;
    autorewrite with category;
    f_equal;
    try reflexivity.

  Local Ltac destruct_eq_refl_in_match :=
    repeat match goal with
             | [ |- appcontext[match ?E with eq_refl => _ end] ] => destruct E
           end.

  Local Ltac lax_comma_eq_t :=
    intros;
    destruct_head LaxCommaSpecializedCategory_Morphism;
    apply LaxCommaSpecializedCategory_Morphism_eq;
    simpl in *;
    [ rsimplify_morphisms; reflexivity
    | rsimplify_morphisms; reflexivity
    | ];
    repeat (nt_eq || functor_eq);
    simpl in *;
    subst;
    destruct_eq_refl_in_match;
    simpl in *;
    trivial.


  Lemma LaxCommaSpecializedCategory_Associativity o1 o2 o3 o4
        (m1 : LaxCommaSpecializedCategory_Morphism o1 o2)
        (m2 : LaxCommaSpecializedCategory_Morphism o2 o3)
        (m3 : LaxCommaSpecializedCategory_Morphism o3 o4)
  : LaxCommaSpecializedCategory_Compose (LaxCommaSpecializedCategory_Compose m3 m2) m1
    = LaxCommaSpecializedCategory_Compose m3 (LaxCommaSpecializedCategory_Compose m2 m1).
  Proof.
    intros;
    destruct_head LaxCommaSpecializedCategory_Morphism;
    apply LaxCommaSpecializedCategory_Morphism_eq;
    [ simpl; rsimplify_morphisms; reflexivity
    | simpl; rsimplify_morphisms; reflexivity
    | ];
    intros; try apply eq_JMeq;
    apply NaturalTransformation_JMeq; trivial;
    intros; subst; try apply eq_JMeq;
    try (simpl; apply Functor_eq; trivial; intros; subst; try apply eq_JMeq; simpl);
    autorewrite with morphism; try reflexivity.
    unfold LaxCommaSpecializedCategory_Compose.
    simpl.

    repeat rewrite Associativity.
    f_equal.
    progress f_equal.
    destruct_eq_refl_in_match.

    match goal with
    autorewrite with morphism.

    autorewrite with morphism; reflexivity.
    simpl.
    intros; try apply eq_JMeq;
    try (simpl; intros; apply Functor_eq; trivial);
    try apply eq_JMeq;
    try (simpl; intros; apply Functor_eq; trivial);
    try apply eq_JMeq;
    try (simpl; intros; apply Functor_eq; trivial);
    try apply eq_JMeq.
    simpl; intros; autorewrite with morphism; reflexivity.
    simpll.
    JMeq_eq.
    nt_eq.
    Time lax_comma_eq_t.
    r
    apply NaturalTransformation_eq.
    simpl in *.

    destruct_eq_refl_in_match.
    nt_eq.
    nt_eq.
    functor_eq.
    functor_eq.
    subst.
    JMeq_eq.
    Require Import CanonicalStructureSimplification.
    rsimplify_morphisms.
    trivial.
  Qed.

  Lemma LaxCommaSpecializedCategory_LeftIdentity : forall a b (f : LaxCommaSpecializedCategory_Morphism a b),
    LaxCommaSpecializedCategory_Compose (CommaSpecializedCategory_Identity b) f = f.
  Proof.
    abstract comma_eq_t.
  Qed.

  Lemma LaxCommaSpecializedCategory_RightIdentity : forall a b (f : LaxCommaSpecializedCategory_Morphism a b),
    LaxCommaSpecializedCategory_Compose f (CommaSpecializedCategory_Identity a) = f.
  Proof.
    abstract comma_eq_t.
  Qed.



  Definition LaxSliceSpecializedCategory_Compose
             s d d'
             (Fα : LaxSliceSpecializedCategory_Morphism d d')
             (F'α' : LaxSliceSpecializedCategory_Morphism s d)
  : LaxSliceSpecializedCategory_Morphism s d'.
    exists (ComposeFunctors (fst (projT1 Fα)) (fst (projT1 F'α')), tt).
    repeat match goal with
             | [ H : _ |- _ ] => unique_pose_with_body (fst (projT1 H))
             | [ H : _ |- _ ] => unique_pose_with_body (projT2 H)
           end; simpl in *.
    repeat match goal with
             | [ x : _, T : _ |- _ ] => unique_pose (NTComposeF T (IdentityNaturalTransformation x))
           end.
    match goal with
      | [ T0 : _, T1 : _ |- _ ] => eapply (NTComposeT _ (NTComposeT T0 T1))
    end.
    Grab Existential Variables.
    match goal with
      | [ C : _ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
      subst_body;
      intros; simpl;
      autorewrite with morphism;
      reflexivity
    ).
  Defined.

  Definition LaxSliceSpecializedCategory_Compose'' s d d' (Fα : LaxSliceSpecializedCategory_MorphismT d d') (F'α' : LaxSliceSpecializedCategory_MorphismT s d) :
    LaxSliceSpecializedCategory_MorphismT s d'.
    simpl_definition_by_tac_and_exact (@LaxSliceSpecializedCategory_Compose' s d d' Fα F'α') ltac:(unfold LaxSliceSpecializedCategory_Compose' in *).
  Defined.

  (* Then we clean up a bit with reduction. *)
  Definition LaxSliceSpecializedCategory_Compose s d d' (Fα : LaxSliceSpecializedCategory_MorphismT d d') (F'α' : LaxSliceSpecializedCategory_MorphismT s d) :
    LaxSliceSpecializedCategory_MorphismT s d'
    := Eval cbv beta iota zeta delta [LaxSliceSpecializedCategory_Compose''] in (@LaxSliceSpecializedCategory_Compose'' s d d' Fα F'α').

  Global Arguments LaxSliceSpecializedCategory_Compose _ _ _ _ _ /.

  Definition LaxSliceSpecializedCategory_Identity o : LaxSliceSpecializedCategory_MorphismT o o.
    exists (IdentityFunctor _, tt).
    eapply (NTComposeT _ (IdentityNaturalTransformation _)).
    Grab Existential Variables.
    match goal with
      | [ C : _ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
        intros; simpl;
        autorewrite with morphism;
        reflexivity
      ).
  Defined.

  Global Arguments LaxSliceSpecializedCategory_Identity _ /.

  Local Ltac lax_slice_t :=
    repeat (
      let H := fresh in intro H; destruct H; simpl in * |-
    );
    unfold projT1, projT2;
      try unfold LaxSliceSpecializedCategory_Compose at 1; try (symmetry; unfold LaxSliceSpecializedCategory_Compose at 1);
        try apply f_equal (* slow; ~ 3s / goal *);
          simpl_eq (* slow; ~ 4s / goal *);
          nt_eq (* slow; ~ 2s / goal *); clear_refl_eq;
          repeat rewrite ComposeFunctorsAssociativity;
            repeat rewrite LeftIdentityFunctor; repeat rewrite RightIdentityFunctor;
              repeat rewrite FIdentityOf;
                repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                  repeat rewrite Associativity;
                    try reflexivity;
                    subst;
                    trivial.

  Lemma LaxSliceSpecializedCategory_Associativity : forall (o1 o2 o3 o4 : LaxSliceSpecializedCategory_ObjectT)
    (m1 : LaxSliceSpecializedCategory_MorphismT o1 o2)
    (m2 : LaxSliceSpecializedCategory_MorphismT o2 o3)
    (m3 : LaxSliceSpecializedCategory_MorphismT o3 o4),
    LaxSliceSpecializedCategory_Compose
    (LaxSliceSpecializedCategory_Compose m3 m2) m1 =
    LaxSliceSpecializedCategory_Compose m3
    (LaxSliceSpecializedCategory_Compose m2 m1).
  Proof.
    abstract lax_slice_t.
  Qed.

  Lemma LaxSliceSpecializedCategory_LeftIdentity : forall (a b : LaxSliceSpecializedCategory_ObjectT)
    (f : LaxSliceSpecializedCategory_MorphismT a b),
    LaxSliceSpecializedCategory_Compose
    (LaxSliceSpecializedCategory_Identity b) f = f.
  Proof.
    abstract lax_slice_t.
  Qed.

  Lemma LaxSliceSpecializedCategory_RightIdentity : forall (a b : LaxSliceSpecializedCategory_ObjectT)
    (f : LaxSliceSpecializedCategory_MorphismT a b),
    LaxSliceSpecializedCategory_Compose
    f (LaxSliceSpecializedCategory_Identity a) = f.
  Proof.
    abstract lax_slice_t.
  Qed.

  Definition LaxSliceSpecializedCategory : SpecializedCategory.
    refine (@Build_SpecializedCategory
              LaxSliceSpecializedCategory_Object
              LaxSliceSpecializedCategory_Morphism
              LaxSliceSpecializedCategory_Identity
              LaxSliceSpecializedCategory_Compose
              _
              _
              _
           );
    abstract (
      repeat (
        let H := fresh in intro H; destruct H as [ ]; simpl in * |-
      );
      unfold LaxSliceSpecializedCategory_Morphism_Member, LaxSliceSpecializedCategory_Object_Member,
        Build_LaxSliceSpecializedCategory_Morphism', Build_LaxSliceSpecializedCategory_Object';
        apply f_equal;
          apply LaxSliceSpecializedCategory_Associativity ||
            apply LaxSliceSpecializedCategory_LeftIdentity ||
              apply LaxSliceSpecializedCategory_RightIdentity
    ).
  Defined.
End LaxSliceSpecializedCategory.

Hint Unfold LaxSliceSpecializedCategory_Compose LaxSliceSpecializedCategory_Identity : category.
Hint Constructors LaxSliceSpecializedCategory_Morphism LaxSliceSpecializedCategory_Object : category.

Section LaxCosliceSpecializedCategory.
  (* [Definition]s are not sort-polymorphic. *)

  Variable I : Type.
  Variable Index2Cat : I -> SpecializedCategory.

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Let Cat := ComputableCategory Index2Cat.

  Context `(C : SpecializedCategory).

  Record LaxCosliceSpecializedCategory_Object := { LaxCosliceSpecializedCategory_Object_Member :> { X : unit * I & SpecializedFunctor (snd X) C } }.

  Let SortPolymorphic_Helper (A T : Type) (Build_T : A -> T) := A.

  Definition LaxCosliceSpecializedCategory_ObjectT := Eval hnf in SortPolymorphic_Helper Build_LaxCosliceSpecializedCategory_Object.
  Global Identity Coercion LaxCosliceSpecializedCategory_Object_Id : LaxCosliceSpecializedCategory_ObjectT >-> sigT.
  Definition Build_LaxCosliceSpecializedCategory_Object' (mem : LaxCosliceSpecializedCategory_ObjectT) := Build_LaxCosliceSpecializedCategory_Object mem.
  Global Coercion Build_LaxCosliceSpecializedCategory_Object' : LaxCosliceSpecializedCategory_ObjectT >-> LaxCosliceSpecializedCategory_Object.

  Record LaxCosliceSpecializedCategory_Morphism (XG X'G' : LaxCosliceSpecializedCategory_ObjectT) := { LaxCosliceSpecializedCategory_Morphism_Member :>
    { F : unit * SpecializedFunctor (snd (projT1 X'G')) (snd (projT1 XG)) &
      SpecializedNaturalTransformation (ComposeFunctors (projT2 XG) (snd F)) (projT2 X'G')
    }
  }.

  Definition LaxCosliceSpecializedCategory_MorphismT (XG X'G' : LaxCosliceSpecializedCategory_ObjectT) :=
    Eval hnf in SortPolymorphic_Helper (@Build_LaxCosliceSpecializedCategory_Morphism XG X'G').
  Global Identity Coercion LaxCosliceSpecializedCategory_Morphism_Id : LaxCosliceSpecializedCategory_MorphismT >-> sigT.
  Definition Build_LaxCosliceSpecializedCategory_Morphism' XG X'G' (mem : @LaxCosliceSpecializedCategory_MorphismT XG X'G') :=
    @Build_LaxCosliceSpecializedCategory_Morphism _ _ mem.
  Global Coercion Build_LaxCosliceSpecializedCategory_Morphism' : LaxCosliceSpecializedCategory_MorphismT >-> LaxCosliceSpecializedCategory_Morphism.

  Global Arguments LaxCosliceSpecializedCategory_Object_Member _ : simpl nomatch.
  Global Arguments LaxCosliceSpecializedCategory_Morphism_Member _ _ _ : simpl nomatch.
  Global Arguments LaxCosliceSpecializedCategory_ObjectT /.
  Global Arguments LaxCosliceSpecializedCategory_MorphismT _ _ /.

  Definition LaxCosliceSpecializedCategory_Compose' s d d' (Fα : LaxCosliceSpecializedCategory_MorphismT d d') (F'α' : LaxCosliceSpecializedCategory_MorphismT s d) :
    LaxCosliceSpecializedCategory_MorphismT s d'.
    exists (tt, ComposeFunctors (snd (projT1 F'α')) (snd (projT1 Fα))).
    repeat match goal with
             | [ H : _ |- _ ] => unique_pose_with_body (snd (projT1 H))
             | [ H : _ |- _ ] => unique_pose_with_body (projT2 H)
           end; simpl in *.
    repeat match goal with
             | [ x : _, T : _ |- _ ] => unique_pose (NTComposeF T (IdentityNaturalTransformation x))
           end.
    match goal with
      | [ T0 : _, T1 : _ |- _ ] => eapply (NTComposeT (NTComposeT T0 T1) _)
    end.
    Grab Existential Variables.
    match goal with
      | [ C : _ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
      subst_body;
      intros; simpl;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
          reflexivity
    ).
  Defined.

  Definition LaxCosliceSpecializedCategory_Compose'' s d d' (Fα : LaxCosliceSpecializedCategory_MorphismT d d') (F'α' : LaxCosliceSpecializedCategory_MorphismT s d) :
    LaxCosliceSpecializedCategory_MorphismT s d'.
    simpl_definition_by_tac_and_exact (@LaxCosliceSpecializedCategory_Compose' s d d' Fα F'α') ltac:(unfold LaxCosliceSpecializedCategory_Compose' in *).
  Defined.

  (* Then we clean up a bit with reduction. *)
  Definition LaxCosliceSpecializedCategory_Compose s d d' (Fα : LaxCosliceSpecializedCategory_MorphismT d d') (F'α' : LaxCosliceSpecializedCategory_MorphismT s d) :
    LaxCosliceSpecializedCategory_MorphismT s d'
    := Eval cbv beta iota zeta delta [LaxCosliceSpecializedCategory_Compose''] in (@LaxCosliceSpecializedCategory_Compose'' s d d' Fα F'α').

  Global Arguments LaxCosliceSpecializedCategory_Compose _ _ _ _ _ /.

  Definition LaxCosliceSpecializedCategory_Identity o : LaxCosliceSpecializedCategory_MorphismT o o.
    exists (tt, IdentityFunctor _).
    eapply (NTComposeT _ (IdentityNaturalTransformation _)).
    Grab Existential Variables.
    match goal with
      | [ C : _ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
      intros; simpl;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
          reflexivity
    ).
  Defined.

  Global Arguments LaxCosliceSpecializedCategory_Identity _ /.

  Local Ltac lax_coslice_t :=
    repeat (
      let H := fresh in intro H; destruct H; simpl in * |-
    );
    unfold projT1, projT2;
      try unfold LaxCosliceSpecializedCategory_Compose at 1; try (symmetry; unfold LaxCosliceSpecializedCategory_Compose at 1);
        try apply f_equal (* slow; ~ 3s / goal *);
          simpl_eq (* slow; ~ 4s / goal *);
          nt_eq (* slow; ~ 2s / goal *); clear_refl_eq;
          repeat rewrite ComposeFunctorsAssociativity;
            repeat rewrite LeftIdentityFunctor; repeat rewrite RightIdentityFunctor;
              repeat rewrite FIdentityOf;
                repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                  repeat rewrite Associativity;
                    try reflexivity;
                    subst;
                    trivial.

  Lemma LaxCosliceSpecializedCategory_Associativity : forall (o1 o2 o3 o4 : LaxCosliceSpecializedCategory_ObjectT)
    (m1 : LaxCosliceSpecializedCategory_MorphismT o1 o2)
    (m2 : LaxCosliceSpecializedCategory_MorphismT o2 o3)
    (m3 : LaxCosliceSpecializedCategory_MorphismT o3 o4),
    LaxCosliceSpecializedCategory_Compose
    (LaxCosliceSpecializedCategory_Compose m3 m2) m1 =
    LaxCosliceSpecializedCategory_Compose m3
    (LaxCosliceSpecializedCategory_Compose m2 m1).
  Proof.
    abstract lax_coslice_t.
  Qed.

  Lemma LaxCosliceSpecializedCategory_LeftIdentity : forall (a b : LaxCosliceSpecializedCategory_ObjectT)
    (f : LaxCosliceSpecializedCategory_MorphismT a b),
    LaxCosliceSpecializedCategory_Compose
    (LaxCosliceSpecializedCategory_Identity b) f = f.
  Proof.
    abstract lax_coslice_t.
  Qed.

  Lemma LaxCosliceSpecializedCategory_RightIdentity : forall (a b : LaxCosliceSpecializedCategory_ObjectT)
    (f : LaxCosliceSpecializedCategory_MorphismT a b),
    LaxCosliceSpecializedCategory_Compose
    f (LaxCosliceSpecializedCategory_Identity a) = f.
  Proof.
    abstract lax_coslice_t.
  Qed.

  Definition LaxCosliceSpecializedCategory : SpecializedCategory.
    refine (@Build_SpecializedCategory
              LaxCosliceSpecializedCategory_Object
              LaxCosliceSpecializedCategory_Morphism
              LaxCosliceSpecializedCategory_Identity
              LaxCosliceSpecializedCategory_Compose
              _
              _
              _
           );
    abstract (
      repeat (
        let H := fresh in intro H; destruct H as [ ]; simpl in * |-
      );
      unfold LaxCosliceSpecializedCategory_Morphism_Member, LaxCosliceSpecializedCategory_Object_Member,
        Build_LaxCosliceSpecializedCategory_Morphism', Build_LaxCosliceSpecializedCategory_Object';
        apply f_equal;
          apply LaxCosliceSpecializedCategory_Associativity ||
            apply LaxCosliceSpecializedCategory_LeftIdentity ||
              apply LaxCosliceSpecializedCategory_RightIdentity
    ).
  Defined.
End LaxCosliceSpecializedCategory.

Hint Unfold LaxCosliceSpecializedCategory_Compose LaxCosliceSpecializedCategory_Identity : category.
Hint Constructors LaxCosliceSpecializedCategory_Morphism LaxCosliceSpecializedCategory_Object : category.
