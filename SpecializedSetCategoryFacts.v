Require Import Setoid ProofIrrelevance FunctionalExtensionality.
Require Export SetCategory DiscreteCategory EquivalenceSet EquivalenceClass Grothendieck EquivalenceRelationGenerator.
Require Import Common Limits Functor NaturalTransformation FunctorCategory.

Set Implicit Arguments.

Local Infix "*" := ProductCategory.
Local Notation "C ^ D" := (FunctorCategory D C).

Section InitialTerminal.
  Local Transparent Object Morphism.

  Hint Extern 1 (_ = _) => apply (@functional_extensionality_dep _); intro.

  Local Ltac t := repeat (hnf in *; simpl in *; intros; try destruct_exists; try destruct_to_empty_set); auto.

  Definition TypeCatEmptyInitial : @InitialObject _ _ TypeCat Empty_set. t. Defined.
  Definition TypeCatSingletonTerminal : @TerminalObject _ _ TypeCat unit. t. Defined.
  Definition SetCatEmptyInitial : @InitialObject _ _ SetCat Empty_set. t. Defined.
  Definition SetCatSingletonTerminal : @TerminalObject _ _ SetCat unit. t. Defined.
End InitialTerminal.

Section SetLimits.
  Local Transparent Object Morphism Identity Compose.

  Variable objC : Set.
  Variable morC : objC -> objC -> Set.
  Variable C : SmallSpecializedCategory morC.
  Variable F : SpecializedFunctor C SetCat.

  (* Quoting David:
     let F:C-->Set be a functor. An element of the limit is a collection of elements x_c,
     one for each c in C, such that under every arrow g: c-->c' in C, x_c is sent to x_{c'}.
     *)
  Definition SetLimit_Object : SetCat * TerminalCategory :=
    (
      { S : forall c : objC, F c | forall c c' (g : C.(Morphism) c c'), F.(MorphismOf) g (S c) = (S c') },
      tt
    ).

  Definition SetLimit_Morphism : SpecializedNaturalTransformation
    ((DiagonalFunctor SetCat C) (fst SetLimit_Object))
    ((SliceCategory_Functor
      (FunctorCategory C SetCat) F) (snd SetLimit_Object)).
    simpl.
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun c : objC => (fun S => (proj1_sig S) c))
          _
        )
    end.
    abstract (
      simpl; intros;
        apply functional_extensionality_dep; intro;
          destruct_sig;
          t_with t'
    ).
  Defined.
Print SliceCategory .
  Definition SetLimit_Property_Morphism_mor (o' : @SliceCategory _ (SetCat ^ C) F (DiagonalFunctor SetCat C)) :
    Morphism (SetCat * TerminalCategory) (projT1 o')
    SetLimit_Object.
    refine (
      (fun x : (fst (projT1 o')) => exist _ (fun c : C => ComponentsOf (projT2 o') c x) _),
      tt
    ).
    abstract (
      simpl in *; intros;
        destruct_type @SpecializedNaturalTransformation; simpl in *;
          fg_equal;
          symmetry;
            specialized_assumption idtac
    ).
  Defined.

  Definition SetLimit_Property_Morphism (o' : @SliceCategory _ (SetCat ^ C) F (DiagonalFunctor SetCat C)) :
    Morphism
    (@SliceCategory _ (SetCat ^ C) F (DiagonalFunctor SetCat C)) o'
    (existT _ SetLimit_Object SetLimit_Morphism).
    exists (SetLimit_Property_Morphism_mor _).
    abstract nt_eq.
  Defined.

  Definition SetLimit : Limit F.
    Transparent Object Morphism Compose Identity.
    exists (existT _ SetLimit_Object SetLimit_Morphism).
    hnf; intros.
    exists (SetLimit_Property_Morphism _).
    abstract (
      unfold SetLimit_Property_Morphism, SetLimit_Property_Morphism_mor; simpl in *;
        repeat (hnf in *; intros; simpl in *);
          simpl_exist;
          apply injective_projections; simpl; trivial;
            repeat (apply functional_extensionality_dep; intro; try simpl_exist);
              destruct_sig;
              rewrite LeftIdentityNaturalTransformation in *;
                subst;
                  unfold Morphism;
                    trivial
    ).
  Defined.
End SetLimits.

Section TypeLimits.
  Local Transparent Object Morphism Identity Compose.

  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable F : SpecializedFunctor C TypeCat.

  (* Quoting David:
     let F:C-->Set be a functor. An element of the limit is a collection of elements x_c,
     one for each c in C, such that under every arrow g: c-->c' in C, x_c is sent to x_{c'}.
     *)
  Definition TypeLimit_Object : TypeCat * TerminalCategory :=
    (
      { S : forall c : objC, F c | forall c c' (g : C.(Morphism) c c'), F.(MorphismOf) g (S c) = (S c') },
      tt
    ).

  Definition TypeLimit_Morphism : SpecializedNaturalTransformation
    ((DiagonalFunctor TypeCat C) (fst TypeLimit_Object))
    ((SliceCategory_Functor
      (FunctorCategory C TypeCat) F) (snd TypeLimit_Object)).
    simpl.
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun c : objC => (fun S => (proj1_sig S) c))
          _
        )
    end.
    abstract (
      simpl; intros;
        apply functional_extensionality_dep; intro;
          destruct_sig;
          t_with t'
    ).
  Defined.

  Definition TypeLimit_Property_Morphism_mor (o' : @SliceCategory _ (TypeCat ^ C) F (DiagonalFunctor TypeCat C)) :
    Morphism (TypeCat * TerminalCategory) (projT1 o')
    TypeLimit_Object.
    refine (
      (fun x : (fst (projT1 o')) => exist _ (fun c : C => ComponentsOf (projT2 o') c x) _),
      tt
    ).
    abstract (
      simpl in *; intros;
        destruct_type @SpecializedNaturalTransformation; simpl in *;
          fg_equal;
          symmetry;
            specialized_assumption idtac
    ).
  Defined.

  Definition TypeLimit_Property_Morphism (o' : @SliceCategory _ (TypeCat ^ C) F (DiagonalFunctor TypeCat C)) :
    Morphism
    (@SliceCategory _ (TypeCat ^ C) F (DiagonalFunctor TypeCat C)) o'
    (existT _ TypeLimit_Object TypeLimit_Morphism).
    exists (TypeLimit_Property_Morphism_mor _).
    abstract nt_eq.
  Defined.

  Definition TypeLimit : Limit F.
    Transparent Object Morphism Compose Identity.
    exists (existT _ TypeLimit_Object TypeLimit_Morphism).
    hnf; intros.
    exists (TypeLimit_Property_Morphism _).
    abstract (
      unfold TypeLimit_Property_Morphism, TypeLimit_Property_Morphism_mor; simpl in *;
        repeat (hnf in *; intros; simpl in *);
          simpl_exist;
          apply injective_projections; simpl; trivial;
            repeat (apply functional_extensionality_dep; intro; try simpl_exist);
              destruct_sig;
              rewrite LeftIdentityNaturalTransformation in *;
                subst;
                  unfold Morphism;
                    trivial
    ).
  Defined.
End TypeLimits.

Section SetColimits.
  Local Transparent Object Morphism.

  Variable objC : Set.
  Variable morC : objC -> objC -> Set.
  Variable C : SmallSpecializedCategory morC.
  Variable F : SpecializedFunctor C SetCat.
  Let F' := (F : SpecializedFunctorToSet _) : SpecializedFunctorToType _.
  Set Printing Universes.

  Check { c : objC & F.(ObjectOf') c }.
  Definition SetColimit_Object_pre := SetGrothendieckPair F. (* { c : objC & F.(ObjectOf') c }.*)
  Definition SetColimit_Object_equiv_sig :=
    generateEquivalence (fun x y : SetColimit_Object_pre => inhabited (Morphism (CategoryOfElements F') x y)).
  Definition SetColimit_Object_equiv :=
    proj1_sig SetColimit_Object_equiv_sig.
  Definition SetColimit_Object_equiv_Equivalence :=
    proj2_sig SetColimit_Object_equiv_sig.

  Local Infix "~=" := SetColimit_Object_equiv (at level 70, no associativity).

  Hypothesis inhabited_dec : forall x y : SetColimit_Object_pre, {x ~= y} + {~(x ~= y)}.

  Definition SetColimit_Object : TerminalCategory * SetCat := (tt, EquivalenceSet SetColimit_Object_equiv).

  (* TODO: Automate better. *)
  Definition SetColimit_Morphism : Morphism (FunctorCategory C SetCat)
    ((SliceCategory_Functor
      (FunctorCategory C SetCat) F) (fst SetColimit_Object))
    ((DiagonalFunctor SetCat C) (snd SetColimit_Object)).
    Transparent Identity.
    hnf; simpl.
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
          (fun c : objC =>
            (fun S : F c =>
              setOf SetColimit_Object_equiv_Equivalence inhabited_dec
              (Build_SetGrothendieckPair F c S)
            )
          )
          _
        )
    end.
    abstract (
      simpl; intros; hnf;
        repeat (apply functional_extensionality_dep; intro);
          simpl;
            apply EquivalenceSet_forall__eq;
              intros; repeat (split; intros);
                clear_InSet;
                t_with t';
                match goal with
                  | [ m : _ |- _ ]
                    => apply gen_sym;
                      apply gen_underlying;
                        constructor; hnf; simpl;
                          exists m; reflexivity
                  | [ m : _ |- _ ]
                    => apply gen_underlying;
                      constructor; hnf; simpl;
                        exists m; reflexivity
                end
    ).
  Defined.

  Definition SetColimit_Property_Morphism_mor (o' : @CosliceCategory _ (SetCat ^ C) F (DiagonalFunctor SetCat C)) :
    Morphism (TerminalCategory * SetCat)
    SetColimit_Object (projT1 o').
  Print Colimit.
  Check InitialMorphism.
  Eval unfold InitialMorphism in  @InitialMorphism (SetCat ^ C) _ F (DiagonalFunctor SetCat C).
  Eval unfold InitialObject in {Aφ : @CosliceCategory _ (SetCat ^ C) F (DiagonalFunctor SetCat C) & InitialObject Aφ}.
  Eval simpl in {Aφ : @CosliceCategory _ (SetCat ^ C) F (DiagonalFunctor SetCat C) &
       forall o' : @CosliceCategory _ (SetCat ^ C) F (DiagonalFunctor SetCat C),
       {m : Morphism (@CosliceCategory _ (SetCat ^ C) F (DiagonalFunctor SetCat C)) Aφ o' |
       is_unique m}}.
    hnf; simpl.
    assert (EquivalenceSet SetColimit_Object_equiv -> snd (projT1 o')).
    destruct o' as [ [ ] ]; simpl in *.
    hnf in m.
    pose (m.(ComponentsOf')) as p; simpl in *.
    unfold SetColimit_Object_equiv, SetColimit_Object_equiv_sig, SetColimit_Object_pre.
    intro a.
    Print SetGrothendieckPair.
    assert (forall cFc c'Fc' : SetGrothendieckPair F, InSet a cFc -> InSet a c'Fc' ->
      p (SetGrothendieckC cFc) (SetGrothendieckX cFc) = p (SetGrothendieckC c'Fc') (SetGrothendieckX c'Fc')).
    intros.
    clear_InSet.
    unfold SetEquivalent in H1.
    match type of H1 with
      | appcontext[proj1_sig ?x] => assert (H2 := proj2_sig x)
    end.
    simpl in *.
    induction H1.
    destruct H.
    simpl in *.
    hnf in X.
    destruct X.
    present_spnt.
    rewrite <- e.

    unfold Equivalence in *.

 destruct (SetInhabited a).

  Definition SetColimit_Property_Morphism (o' : CosliceSpecializedCategory F (DiagonalFunctor SetCat C)) :
    Morphism
    (CosliceSpecializedCategory F (DiagonalFunctor SetCat C))
    (existT _ SetColimit_Object SetColimit_Morphism) o'.
    hnf; simpl.
    match goal with
      | [ |- @sig ?A ?P ] => assert (m : A)
    end.
    hnf. simpl.
    assert (Morphism SetCat (EquivalenceSet SetColimit_Object_equiv) (snd (projT1 o'))).
    hnf; simpl; intros.
    hnf in *; simpl in *.
    destruct o' as [ [ ] ].
    simpl in *.
    hnf in m.
    let t := type of m.(ComponentsOf') in let t' := eval simpl in t in idtac t'.



    refine (
      (fun x : (fst (projT1 o')) => exist _ (fun c : C => ComponentsOf (projT2 o') c x) _),
      tt
    ).

  Definition SetColimit : Colimit F.
    Transparent Object Morphism Compose Identity.
    hnf.
    exists (existT _ SetColimit_Object SetColimit_Morphism).
    hnf.
    hnf; intros.
    match goal with
      | [ |- @sigT ?A ?P ] => assert (Aφ : A)
    end.
    hnf.
    exists SetColimit_Object.
    exact SetColimit_Morphism.
    match goal with
      | [ |- @sigT ?A ?P ] => assert (αβ : A)
    end.
    unfold Object.
    exact (
      { l : SpecializedFunctor C PointedTypeCat | ComposeSpecializedFunctors PointedTypeProjection l = F },
      tt
    ).
    exists αβ.
    hnf; simpl.
    unfold SliceCategory, CommaSpecializedCategory.
    Set Printing All.
    unfold
    hnf.
    unfold Limit.
    unfold TerminalMorphism.
    unfold SliceCategory, TerminalObject, CommaSpecializedCategory.
    simpl.
End Limits.

Section DiscreteLimits.
  Variable O : Set.
  Variable eq_dec : forall a b : O, {a = b} + {a <> b}.
  Let D := DiscreteSmallCategory O eq_dec.

  Variable F : Functor D SetCat.

  Lemma eq_dec_refl' x : forall H, eq_dec x x <> right H.
    intro H; contradict H; reflexivity.
  Qed.

  Lemma eq_dec_refl_helper a b : (forall H, eq_dec a b <> right H) -> (exists H, eq_dec a b = left H).
    intro H.
    destruct (eq_dec a b) as [ e |  ].
    exists e; trivial.
    specialized_assumption ltac:(try tauto).
  Qed.

  Lemma eq_dec_refl x : exists H, eq_dec x x = left H.
    apply eq_dec_refl_helper; intro; firstorder.
  Qed.

  Lemma eq_dec_refl_use x A (a b : A) : (if eq_dec x x then a else b) = a.
    pose (eq_dec_refl x) as H.
    destruct H as [ ? H ].
    rewrite H.
    reflexivity.
  Qed.

(*  Lemma eq_dec_refl' x : forall H, ~eq_dec x x = right H.
    intro H; contradict H; reflexivity.
  Qed.
*)
  Definition DiscreteSetColimit : Colimit F.
    hnf; simpl.
    Print sigT.
    match goal with
      | [ |- { _ : { αβ : _ & SmallNaturalTransformation (@?F0 αβ) (@?G0 αβ) } & _ } ] =>
        let αβ := constr:((tt, { o : O & F o })) in
          refine (existT _
            (existT
              _
              αβ
              (Build_SmallNaturalTransformation _ _ (fun c : D => (fun Fc : F c => existT _ c Fc) : Morphism SetCat (F0 αβ c) (G0 αβ c)) _)
            )
            _
          )
    end.
    hnf; simpl in *; intro o'.
    destruct o' as [ [ [ ] S ] f ]; simpl in *.
    match goal with
      | [ |- @sig (@sig ?A ?P) ?P' ] =>
        let gh := constr:((tt, (fun oFo => f (projT1 oFo) (projT2 oFo)))) in
          cut (P gh);
            try (
              let x := fresh in intro x;
                let m := constr:(exist P gh x) in
                  exists m
            )
    end.
    hnf; simpl in *.
    intro x'.
    simultaneous_rewrite RightIdentitySmallNaturalTransformation; simpl in *.
    destruct x' as [ [ [ ] f' ] H' ].
    simpl in *.
    Lemma sig_equal A P (s s' : @sig A P) : proj1_sig s = proj1_sig s' -> s = s'.
      intros; destruct s, s'; simpl in *; subst; f_equal; apply proof_irrelevance.
    Qed.
    apply sig_equal; simpl in *.
    f_equal.
    repeat (apply functional_extensionality_dep; intro).
    destruct x; simpl in *.
    match goal with
      | [ H : _, H' : _ |- _ ] => rewrite <- H; rewrite <- H'; simpl; f_equal
    end.
    snt_eq.
    Grab Existential Variables.
    simpl in *; intros.
    subst D.
    repeat (apply functional_extensionality_dep; intro).
    match goal with
      | [ |- existT ?a ?b ?c = existT ?a ?b' ?c' ] => cut (b = b');
        try (let H := fresh in intro H; simultaneous_rewrite H || simultaneous_rewrite_rev H);
          f_equal
    end.
    generalize x.
    clear H0.
    generalize dependent x.
    generalize F; clear F.
    generalize m; clear m.
    unfold DiscreteSmallCategory.
    unfold Morphism.
    simpl.
    Eval simpl in Morphism
    {|
    SObject := O;
    SMorphism := fun s d : O => if eq_dec s d then unit else Empty_set;
    SIdentity := DiscreteCategory_Identity O eq_dec;
    SCompose := DiscreteCategory_Compose O eq_dec;
    SAssociativity := DiscreteSmallCategory_subproof O eq_dec;
    SLeftIdentity := DiscreteSmallCategory_subproof0 O eq_dec;
    SRightIdentity := DiscreteSmallCategory_subproof1 O eq_dec |} s s.
    unfold smallcat2cat in *.
    simpl in *.
    destruct F.
    simpl in *.
    clear F.
    generalize dependent eq_dec.
    clear eq_dec.
    intro.
    pattern (eq_dec s s).
    generalize
    destruct (eq_dec s s).
    destruct m.
    destruct F.
    simpl in *.
    simpl in *.
    match (eq_dec s s) with
      | left _ => assert H
      | right ?H => contradict H
    end.
    contradict (
    destruct (eq_dec s d); tauto || assumption || symmetry; assumption.
    match goal with
      | [ H : context[eq_dec ?a ?a] |- _ ] => generalize dependent H; destruct (eq_dec a a)
    end.
    rewrite <- H1.
    rewrite <- H'.
    simpl.
    f_equal.
    Require Import DefinitionSimplification.
    rewrite sigT_eta.
    match goal with
    match goal with
      | [ |- @sigT (@sigT ?A ?P) ?P' ] =>
        let αβ := constr:((tt, { o : O & F o })) in
          cut (P αβ);
            try (
              let x := fresh in intro x;
                let Aφ := constr:(existT P αβ x) in
                  exists Aφ(*
                  cut (P' Aφ);
                    try (
                      let y := fresh in intro y;
                        exact (existT P' Aφ y)
                    )*)
            )
    end.
    Focus 2.
    hnf; simpl in *.
    Print SmallNaturalTransformation.
    Set Printing All.
    Eval simpl in forall c : D, Morphism SetCat (F c) ((Build_Functor (smallcat2cat D) SetCat
        (fun _ : O =>
         @sigT O (fun o : O => @ObjectOf (smallcat2cat D) SetCat F o))
        (fun (s d : O)
           (_ : match eq_dec s d return Set with
                | left _ => unit
                | right _ => Empty_set
                end)
           (x : @sigT O (fun o : O => @ObjectOf (smallcat2cat D) SetCat F o)) =>
         x)
        (diagonal_functor_object_of_subproof SetCat D
           (@sigT O (fun o : O => @ObjectOf (smallcat2cat D) SetCat F o)))
        (diagonal_functor_object_of_subproof0 SetCat D
           (@sigT O (fun o : O => @ObjectOf (smallcat2cat D) SetCat F o)))) c).
    Unset Printing All.
    Eval simpl in forall c : O,
       @ObjectOf (smallcat2cat D) SetCat F c ->
       @sigT O (fun o : O => @ObjectOf (smallcat2cat D) SetCat F o).
    match goal with
      | [ |- SmallNaturalTransformation ?F ?G ] =>
        refine (Build_SmallNaturalTransformation _ _ (fun c : D => (fun Fc : F c => existT _ c Fc) : Morphism SetCat (F c) (G c)) _)
    end.
    intros; simpl; repeat (apply functional_extensionality_dep; intro).
    match goal with
      | [ |- existT ?a ?b ?c = existT ?a ?b' ?c' ] => cut (b = b');
        try (let H := fresh in intro H; simultaneous_rewrite H || simultaneous_rewrite_rev H);
          f_equal
    end.
    admit.
    subst D; simpl in *.
    destruct (eq_dec s d); tauto || symmetry; assumption.
    destruct D; simpl in *.
    hnf; simpl in *. intros o'.
    destruct o' as [ [ [ ] S ] f ]; simpl in *.
    match goal with
      | [ |- @sig (@sig ?A ?P) ?P' ] =>
        let gh := constr:((tt, (fun oFo => f (projT1 oFo) (projT2 oFo)))) in
          cut (P gh);
            try (
              let x := fresh in intro x;
                let m := constr:(exist P gh x) in
                  exists m
            )
    end.
    hnf; simpl in *.
    intro x'.
    simultaneous_rewrite RightIdentitySmallNaturalTransformation; simpl in *.
    destruct x' as [ [ [ ] f' ] H' ].
    simpl in *.
    match goal with
      | [ |- exist ?a ?b ?c = exist ?a ?b' ?c' ] => cut (b = b');
        try (let H := fresh in intro H; simultaneous_rewrite H || simultaneous_rewrite_rev H);
          f_equal
    end.
    Require Import ProofIrrelevance FunctionalExtensionality.
    admit.
    apply functional_extensionality_dep; intro.
    destruct x; simpl in *.
    rewrite <- H1.
    rewrite <- H'.
    simpl.
    f_equal.
    Require Import DefinitionSimplification.
    rewrite sigT_eta.
    match goal with
      | [ |- existT ?a ?b ?c = existT ?a ?b' ?c' ] => assert (b = b')
    end.

    admit.
    let H := fresh in intro H; simultaneous_rewrite_rev H.
    cut (x = (projT1 (H x o))).


    simpl.
    intro H5. simpl in H5. rewrite <- H5.

rewrite RightIdentitySmallNaturalTransformation in *; simpl in *.

    apply
    assert (H' = eq_refl _).
    intro H5.
    generalize dependent (tt, f').
    simultaneous_rewrite H5.

    intro x.
    let αβ := constr:((tt, { o : O & F o })) in
      let Aφ := constr:(existT _ αβ x) in
        idtac Aφ.
      (
      (tt, {o : O & F o})
H.
    exact (
    reflexivity.
        idtac A; idtac P; idtac P'
        let Aφ := fresh in evar (Aφ : @sigT A P);
          let
    end.
    refine (existT _ (existT _ (tt, { o : O & F o }) _) _).
    hnf; simpl; intro o'.
    destruct o' as [ [ [ ] S ] f ].
    simpl in *.
    refine (exist _ (exist _ (tt, fun oFo => f (projT1 oFo) (projT2 oFo)) _ ) _).
    hnf; simpl; intros x'.
    destruct x' as [ [ [ ] S' ] f' ].
    simpl.
    match goal with
      | [ |- exist ?a ?b ?c = exist ?a ?b' ?c' ] => cut (b = b');
        try (let H := fresh in intro H; simultaneous_rewrite H || simultaneous_rewrite_rev H);
          f_equal
    end.
    Require Import ProofIrrelevance FunctionalExtensionality.
    apply proof_irrelevance.
    rewrite RightIdentitySmallNaturalTransformation in *; simpl in *.
    apply functional_extensionality_dep; intro.
    subst.
    simpl.
    destruct x.
    simpl.
    f_equal.
    subst D.
    unfold DiscreteSmallCategory in *.
    simpl in *.
    unfold smallcat2cat in *.
    simpl in *.
    autorewrite with core.
    simpl in *.
    unfold ObjectOf, Object in *.
    unfold SComponentsOf in *.
    simpl in *.
    unfold smallcat2cat, ObjectOf in *; simpl in *.
    apply f_equal3.
    destruct x.
    simpl.
    intro H1. simultaneous_rewrite  H1.
    apply f_equal2


    unfold Limit.
    unfold
End DiscreteLimits.


(*Require Import Common FunctionalExtensionality.
Set Implicit Arguments.


Section EpiMono.
  Definition compose {A B C : Type} (f : B -> C) (g : A -> B) := (fun x => f (g x)).

  Variables S : Type.
  Hypothesis eq_dec : forall a b : S, {a = b} + {a <> b}.

  Lemma MonoInj B (f : B -> S) :
    (forall A (g g' : A -> B), (compose f g) = (compose f g') -> g = g')
    -> (forall x y : B, f x = f y -> x = y).
    intros H x y fxfy.
    unfold compose in *; simpl in *; fg_equal.
    apply (fun H' => H bool (fun b => if b then x else y) (fun _ => y) H' true).
    apply functional_extensionality_dep.
    intro b; destruct b; trivial.
  Qed.

  Lemma EpiSurj A (f : A -> S) :
    (forall C (g g' : S -> C), (compose g f) = (compose g' f) -> g = g')
    -> (forall x : S, exists y : A, f y = x).
    intro H.
    assert (H' := fun x H' => H bool (fun y => if eq_dec x y then true else false) (fun y => true) H').
    clear H.
    unfold compose in *; simpl in *; fg_equal.

    let H'T := type of H' in cut (~~H'T).
    clear H'; intro H.
    contradict H
    cut (~(~H')).
    contradict H'.
    intro x.
    pose (H bool (fun y => if eq_dec_B x y then true else false) (fun y => true)); simpl in *.
    fg_equal.
*)
