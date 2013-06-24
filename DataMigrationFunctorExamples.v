Require Import JMeq.
Require Export String.
Require Export DataMigrationFunctors PathsCategory PathsCategoryFunctors.
Require Import Notations Common Limits SetLimits SetColimits FEqualDep FunctorCategory DefinitionSimplification SetLimits SetColimits CommaCategory CommaCategoryFunctors.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope type_scope.

Section helpers.
  Definition eq_dec (T : Type) := forall a b : T, {a = b} + {a <> b}.

  Theorem JMeq_type_mismatch_absurd A (a : A) B (b : B) : A <> B -> @JMeq A a B b -> False.
    intros H0 H1;
    destruct H1;
    intuition.
  Qed.

  Lemma type_neq_helper (A B : Type) (a : A) : (forall b : B, JMeq a b -> False) -> A <> B.
    intros H0 H1.
    subst.
    specialize (H0 a); intuition.
  Qed.


(*
  Section path_eq_dec.
    Variable V : Type.
    Variable E : V -> V -> Type.
    Hypothesis Veq_dec : eq_dec V.
    Hypothesis Eeq_dec : forall s d, eq_dec (E s d).

    Inductive paths_eq (s : V) : forall d (p : path E s d) d' (p' : path E s d'), Prop :=
      | noedges_eq : paths_eq NoEdges NoEdges
      | addedge_eq : forall s' (p p' : path E s s') d (e : E s' d), paths_eq p p' -> paths_eq (AddEdge p e) (AddEdge p' e).

    Definition paths_eq_dec' s d (p : path E s d) d' (p' : path E s d') : {paths_eq p p'} + {paths_eq p p' -> False}.
      destruct (Veq_dec d d'); subst.
      - induction p.
        + induction p'.
          * solve [ left; constructor ].
          * right. intro H. destruct H.
solve [ (left; congruence) || (right; apply eq_JMeq; discriminate) ].
      Focus 2.

    Definition mk_paths_eq s d (p p' : path E s d) : p = p' -> paths_eq p p'.
      intro H.
      subst.


    Definition path_JMeq_dec : forall s d (p : path E s d) d' (p' : path E s d'),
                                 {JMeq p p'} + {not (JMeq p p')}.
      intros s d.
      induction p.
      - induction p'.
        + solve [ (left; apply eq_JMeq; congruence) || (right; apply eq_JMeq; discriminate) ].
        + right. intro.
          admit.
      - induction p'.
        + admit.
        + destruct

          destruct H.
      solve [ (left; apply eq_JMeq; congruence) || (right; apply eq_JMeq; discriminate) ].

      left
                                 eq_dec (path E s d).
      unfold eq_dec.
      intro s.
      induction a.


  Definition path_eq_dec V E (Veq : eq_dec V) (Eeq : forall s d : V, eq_dec (E s d)) (s d : V) : eq_dec (path E s d).
    destruc
    hnf; induction a.

    Focus 2.
    induction b.
    solve [ (left; congruence) || (right; discriminate) ].

    pose Eeq.
    hnf in e.

  Lemma noedges_not_JMeq_other_dest V (E : V -> V -> Type) (x s : V) :
    x <> s -> forall d (p : path E s d), JMeq (@NoEdges V E x) p -> False.
    intros H0 d p H1.
    hnf in *.



  Inductive unit' : Set := tt'.

  Goal unit <> unit'.
  intro.
  assert (JMeq tt tt').
  generalize tt tt'; rewrite H; repeat (let x := fresh in intro x; destruct x); reflexivity.
  apply (@JMeq_type_mismatch_absurd _ _ _ _ _ .
  subst H.
  rewrite H.
  generalize tt.
  rewrite H.
  subst.
  Goal unit <> Empty_set.
  intro.
  assert Empty_set.
  rewrite <- H.
  constructor.
  destruct H0.
  Qed.

  Lemma first_neq_implies_path_types_JMeq_absurd V E (s d s' d' : V) p0 p1 :
    s <> s' -> @JMeq (path E s d) p0 (path E s' d') p1 -> False.
    intros H0 H1; eapply (JMeq_type_mismatch_absurd _ H1).
    Grab Existential Variables.
    intro; hnf in *.
    inversion H.
    apply H0.
    apply f_equal in H.
    congruence.
    discriminate.
 *)
End helpers.

Local Ltac make_inductive_eq_dec :=
  match goal with
    | [ |- eq_dec ?T ] =>
      intros ? ?; destruct_head T;
        solve [ (left; congruence) || (right; discriminate) ]
  end.


Ltac make_an_edge E s d hyp :=
  let Etype' := constr:(E s d) in
  let Etype := (eval simpl in Etype') in
  assert (hyp : E s d) by constructor || fail "There is no edge of type" Etype "from" s "to" d.

Ltac find_an_edge_no_cleanup E s d cont :=
  let e := fresh "e" in
  make_an_edge E s d e;
    cont e.

Ltac find_an_edge E s d cont :=
  find_an_edge_no_cleanup E s d ltac:(fun e => cont e; destruct e).

Ltac find_the_edge_no_cleanup E s d cont :=
  let Etype' := constr:(E s d) in
  let Etype := (eval simpl in Etype') in
  let e := fresh "e" in
  let e' := fresh "e'" in
  make_an_edge E s d e;
    pose proof e as e';
    (destruct e' as [ ] || fail "There are multiple edges of type" Etype "from" s "to" d);
    cont e.

Ltac find_the_edge E s d cont :=
  find_the_edge_no_cleanup E s d ltac:(fun e => cont e; destruct e).

Ltac find_a_path' E s d cont node_eq_dec check_node :=
  (find_an_edge
     E s d
     ltac:(fun e => let p := constr:(AddEdge NoEdges e) in
                    cont p))
    || idtac.

Ltac find_a_path E s d node_eq_dec cont :=
  find_a_path' E s d cont node_eq_dec ltac:(fun n => idtac).

Ltac find_the_path' E s d cont node_eq_dec check_node :=
  (find_the_edge
     E s d
     ltac:(fun e => let p := constr:(AddEdge NoEdges e) in
                    cont p))
    || idtac.

Ltac find_the_path E s d node_eq_dec cont :=
  find_the_path' E s d cont node_eq_dec ltac:(fun n => idtac).

Ltac eliminate_useless_paths_functor_cases_then tac :=
  present_spcategory;
  match goal with
    | [ |- forall s d : ?fromObjectType,
             ?fromEdgeType s d ->
             Morphism ?toCategory (@?Fs s) (@?Fd d) ] =>
      let s := fresh "s" in
      let d := fresh "d" in
      let m := fresh "m" in
      intros s d m;
        let toObject := constr:(Fs s) in
        let toObjectType := type of toObject in
        let toEdge := constr:(Morphism toCategory (Fs s) (Fd d)) in
        let toEdgeType := type of toEdge in
        destruct_head fromObjectType; simpl in *;
        destruct_head fromEdgeType; simpl in *;
        hnf;
        tac toObjectType toCategory
    | _ => fail 2 "Goal should be of the form [forall s d : ?T, ?EdgeType s d -> ?Morphism ?D (@?F0 s) (?@F1 d)]."
  end.

Ltac eliminate_useless_paths_functor_cases := eliminate_useless_paths_functor_cases_then ltac:(fun _ _ => idtac).

Ltac fill_unique_paths_functor' make_object_eq_dec  :=
  eliminate_useless_paths_functor_cases_then
    ltac:(fun toObjectType toCategory =>
            let toObject_eq_dec := fresh "toObject_eq_dec" in
            (assert (toObject_eq_dec : eq_dec toObjectType) by (abstract make_object_eq_dec)
                                                                 || fail 1 "Failed to construct decision procedure for equality of" toObjectType "by" make_object_eq_dec);
          match goal with
            | [ |- path ?E ?s ?d ] =>
              try find_the_path E s d toObject_eq_dec ltac:(fun p => exact p)
            | [ |- ?G ] => fail 2 "Morphisms in" toCategory "are not paths, but look like" G
          end
         ).

Ltac fill_unique_paths_functor := fill_unique_paths_functor' ltac:(idtac; make_inductive_eq_dec).


Section FunctorialDataMigration.
  Section Example22.
    Inductive C_Objects_Ex22 : Set := SSN_Ex22_C | FirstName_Ex22_C | LastName_Ex22_C | Salary_Ex22_C | T1_Ex22_C | T2_Ex22_C.
    Inductive D_Objects_Ex22 : Set := SSN_Ex22_D | FirstName_Ex22_D | LastName_Ex22_D | Salary_Ex22_D | U_Ex22_D.
    Inductive E_Objects_Ex22 : Set := SSN_Ex22_E | FirstName_Ex22_E | LastName_Ex22_E | V_Ex22_E.

    Example C_Edges_Ex22 (s d : C_Objects_Ex22) : Set :=
      match (s, d) with
        | (T1_Ex22_C, SSN_Ex22_C) => unit
        | (T1_Ex22_C, FirstName_Ex22_C) => unit
        | (T1_Ex22_C, LastName_Ex22_C) => unit

        | (T2_Ex22_C, FirstName_Ex22_C) => unit
        | (T2_Ex22_C, LastName_Ex22_C) => unit
        | (T2_Ex22_C, Salary_Ex22_C) => unit

        | _ => Empty_set
      end.

    Example D_Edges_Ex22 (s d : D_Objects_Ex22) : Set :=
      match (s, d) with
        | (U_Ex22_D, SSN_Ex22_D) => unit
        | (U_Ex22_D, FirstName_Ex22_D) => unit
        | (U_Ex22_D, LastName_Ex22_D) => unit
        | (U_Ex22_D, Salary_Ex22_D) => unit
        | _ => Empty_set
      end.

    Example E_Edges_Ex22 (s d : E_Objects_Ex22) : Set :=
      match (s, d) with
        | (V_Ex22_E, SSN_Ex22_E) => unit
        | (V_Ex22_E, FirstName_Ex22_E) => unit
        | (V_Ex22_E, LastName_Ex22_E) => unit
        | _ => Empty_set
      end.

    Example C_Category_Ex22 : Category := PathsCategory C_Edges_Ex22.
    Example D_Category_Ex22 : Category := PathsCategory D_Edges_Ex22.
    Example E_Category_Ex22 : Category := PathsCategory E_Edges_Ex22.

    Example F_Functor_Ex22_ObjectOf (x : C_Objects_Ex22) : D_Objects_Ex22 :=
      match x with
        | SSN_Ex22_C => SSN_Ex22_D
        | FirstName_Ex22_C => FirstName_Ex22_D
        | LastName_Ex22_C => LastName_Ex22_D
        | Salary_Ex22_C => Salary_Ex22_D
        | T1_Ex22_C => U_Ex22_D
        | T2_Ex22_C => U_Ex22_D
      end.

    Example G_Functor_Ex22_ObjectOf (x : E_Objects_Ex22) : D_Objects_Ex22 :=
      match x with
        | SSN_Ex22_E => SSN_Ex22_D
        | FirstName_Ex22_E => FirstName_Ex22_D
        | LastName_Ex22_E => LastName_Ex22_D
        | V_Ex22_E => U_Ex22_D
      end.

    Example F_Functor_Ex22 : Functor C_Category_Ex22 D_Category_Ex22.
    Proof.
      apply (@FunctorFromPaths _ _ _ _ F_Functor_Ex22_ObjectOf).
      fill_unique_paths_functor.
    Defined.

    Example G_Functor_Ex22 : Functor E_Category_Ex22 D_Category_Ex22.
    Proof.
      apply (@FunctorFromPaths _ _ _ _ G_Functor_Ex22_ObjectOf).
      fill_unique_paths_functor.
    Defined.

    Inductive SSN := SSN_intro : string -> SSN.
    Inductive FirstName := FirstName_intro : string -> FirstName.
    Inductive LastName := LastName_intro : string -> LastName.
    Inductive Salary := Salary_intro : nat -> Salary.

    Section Example221.
      Inductive Id_Ex221 := x11_Ex221 | x12_Ex221 | x13_Ex221.

      Definition δ_Functor_Ex221_ObjectOf (x : D_Objects_Ex22) : Set :=
        match x with
          | SSN_Ex22_D => SSN
          | FirstName_Ex22_D => FirstName
          | LastName_Ex22_D => LastName
          | Salary_Ex22_D => Salary
          | U_Ex22_D => Id_Ex221
        end.

      Example  δ_Functor_Ex221 : Functor D_Category_Ex22 SetCat.
      Proof.
        apply (@FunctorFromPaths _ _ _ _ δ_Functor_Ex221_ObjectOf).
        eliminate_useless_paths_functor_cases;
          intro id;
          match goal with
            | [ |- SSN ] =>
              constructor;
                exact (match id with
                         | x11_Ex221 => "101-22-0411"%string
                         | x12_Ex221 => "220-39-7479"%string
                         | x13_Ex221 => "775-33-2819"%string
                       end)
            | [ |- FirstName ] =>
              constructor;
                exact (match id with
                         | x11_Ex221 => "David"%string
                         | x12_Ex221 => "Bertrand"%string
                         | x13_Ex221 => "Alan"%string
                       end)
            | [ |- LastName ] =>
              constructor;
                exact (match id with
                         | x11_Ex221 => "Hilbert"%string
                         | x12_Ex221 => "Russell"%string
                         | x13_Ex221 => "Turing"%string
                       end)
            | [ |- Salary ] =>
              constructor;
                exact (match id with
                         | x11_Ex221 => 150
                         | x12_Ex221 => 200
                         | x13_Ex221 => 200
                       end)
          end.
      Defined.

      Eval compute in (ObjectOf ((PullbackAlong C_Category_Ex22 D_Category_Ex22 SetCat F_Functor_Ex22) δ_Functor_Ex221)).

      Section Δ_F__δ__T1_Ex221_cleanup.
        Example Δ_F__δ__T1_Ex221' :=
          Eval compute in (fun d e =>
                             (@MorphismOf _ _ _ _
                                          ((PullbackAlong C_Category_Ex22 D_Category_Ex22 SetCat F_Functor_Ex22)
                                             δ_Functor_Ex221)
                                          T1_Ex22_C
                                          d
                                          (AddEdge NoEdges e))).

        Example Δ_F__δ__T1_Ex221_with_type' : {T : Set & T }
          := Eval compute in @existT _ _ _ Δ_F__δ__T1_Ex221'.

        Let Δ_F__δ__T1_Ex221_DE_Type : Set.
          match eval compute in (projT1 Δ_F__δ__T1_Ex221_with_type') with
            | forall d : ?D, @?E d -> _ => exact { d : D & E d }
          end.
        Defined.

        Let Δ_F__δ__T1_Ex221_D_Type : Set.
          match eval compute in (projT1 Δ_F__δ__T1_Ex221_with_type') with
            | forall d : ?D, @?E d -> _ => exact D
          end.
        Defined.

        Example Δ_F__δ__T1_Ex221_with_type'' (d : Δ_F__δ__T1_Ex221_D_Type) : {T : Set & T }.
        Proof.
          assert (H : focus Δ_F__δ__T1_Ex221_DE_Type) by constructor; unfold Δ_F__δ__T1_Ex221_DE_Type in *; hnf in d.
          repeat match type of H with
                   | appcontext G[unit] => let x := fresh in
                                           evar (x : Set);
                                             let G' := context G[x] in
                                             clear H;
                                               assert (H : G') by constructor;
                                               subst x
                 end;
            repeat match type of H with
                     | appcontext G[Empty_set] => let G' := context G[unit] in
                                                  clear H;
                                                    assert (H : G') by constructor
                   end;
            match type of H with
              | focus ({ d0 : _ & @?f d0 }) => let P := fresh in pose (f d) as P; exists P; subst P; simpl; clear H;
                                                                 pose d as d'; destruct d; try solve [ constructor ];
                                                                 let g := fresh in pose (Δ_F__δ__T1_Ex221' d' tt) as g; compute in *;
                                                                                   exact g
            end.
        Defined.
      End Δ_F__δ__T1_Ex221_cleanup.

      Section Δ_F__δ__T2_Ex221_cleanup.
        Example Δ_F__δ__T2_Ex221' :=
          Eval compute in (fun d e =>
                             (@MorphismOf _ _ _ _
                                          ((PullbackAlong C_Category_Ex22 D_Category_Ex22 SetCat F_Functor_Ex22)
                                             δ_Functor_Ex221)
                                          T2_Ex22_C
                                          d
                                          (AddEdge NoEdges e))).

        Example Δ_F__δ__T2_Ex221_with_type' : {T : Set & T }
          := Eval compute in @existT _ _ _ Δ_F__δ__T2_Ex221'.

        Let Δ_F__δ__T2_Ex221_DE_Type : Set.
          match eval compute in (projT1 Δ_F__δ__T2_Ex221_with_type') with
            | forall d : ?D, @?E d -> _ => exact { d : D & E d }
          end.
        Defined.

        Let Δ_F__δ__T2_Ex221_D_Type : Set.
          match eval compute in (projT1 Δ_F__δ__T2_Ex221_with_type') with
            | forall d : ?D, @?E d -> _ => exact D
          end.
        Defined.

        Example Δ_F__δ__T2_Ex221_with_type'' (d : Δ_F__δ__T2_Ex221_D_Type) : {T : Set & T }.
        Proof.
          assert (H : focus Δ_F__δ__T2_Ex221_DE_Type) by constructor; unfold Δ_F__δ__T2_Ex221_DE_Type in *; hnf in d.
          repeat match type of H with
                   | appcontext G[unit] => let x := fresh in
                                           evar (x : Set);
                                             let G' := context G[x] in
                                             clear H;
                                               assert (H : G') by constructor;
                                               subst x
                 end;
            repeat match type of H with
                     | appcontext G[Empty_set] => let G' := context G[unit] in
                                                  clear H;
                                                    assert (H : G') by constructor
                   end;
            match type of H with
              | focus ({ d0 : _ & @?f d0 }) => let P := fresh in pose (f d) as P; exists P; subst P; simpl; clear H;
                                                                 pose d as d'; destruct d; try solve [ constructor ];
                                                                 let g := fresh in pose (Δ_F__δ__T2_Ex221' d' tt) as g; compute in *;
                                                                                   exact g
            end.
        Defined.
      End Δ_F__δ__T2_Ex221_cleanup.

      Example Δ_F__δ__T1_Ex221 := Eval compute in (fun d => projT2 (Δ_F__δ__T1_Ex221_with_type'' d)).
      Example Δ_F__δ__T2_Ex221 := Eval compute in (fun d => projT2 (Δ_F__δ__T2_Ex221_with_type'' d)).

      Example Δ_F__δ__T1_Ex221_rev_T (x : Id_Ex221) (d : C_Objects_Ex22) : Type.
      Proof.
        pose (Δ_F__δ__T1_Ex221 d) as f;
        destruct d; compute in *;
        (specialize (f x); let t := type of f in exact t) || exact unit.
      Defined.

      Example Δ_F__δ__T1_Ex221_rev' (x : Id_Ex221) (d : C_Objects_Ex22) : Δ_F__δ__T1_Ex221_rev_T x d.
      Proof.
        pose (Δ_F__δ__T1_Ex221 d) as f;
        destruct d; compute in *; exact (f x) || exact tt.
      Defined.

      Example Δ_F__δ__T1_Ex221_rev'' x d := Eval compute in Δ_F__δ__T1_Ex221_rev' x d.

      Let typeof {T} (_ : T) := T.

      Example Δ_F__δ__T1_Ex221_rev''' x d : typeof (Δ_F__δ__T1_Ex221_rev'' x d).
      Proof.
        pose (Δ_F__δ__T1_Ex221_rev'' x d) as f;
        compute in *; destruct x; compute in *; destruct d; compute in *;
        exact f.
      Defined.

      Example Δ_F__δ__T1_Ex221_rev x d := Eval compute in Δ_F__δ__T1_Ex221_rev''' x d.

      Print Δ_F__δ__T1_Ex221_rev.

      Print Δ_F__δ__T1_Ex221.
      Print Δ_F__δ__T2_Ex221.
    End Example221.

    Section Example222.
      Inductive T1_Id_Ex222 := x11_Ex222 | x12_Ex222 | x13_Ex222.
      Inductive T2_Id_Ex222 := y1_Ex222 | y2_Ex222 | y3_Ex222 | y4_Ex222.

      Definition γ_Functor_Ex222_ObjectOf (x : C_Objects_Ex22) : Set :=
        match x with
          | SSN_Ex22_C => SSN
          | FirstName_Ex22_C => FirstName
          | LastName_Ex22_C => LastName
          | Salary_Ex22_C => Salary
          | T1_Ex22_C => T1_Id_Ex222
          | T2_Ex22_C => T2_Id_Ex222
        end.

      Example γ_Functor_Ex222 : Functor C_Category_Ex22 SetCat.
      Proof.
        apply (@FunctorFromPaths _ _ _ _ γ_Functor_Ex222_ObjectOf).
        eliminate_useless_paths_functor_cases;
          intro id;
          match type of id with
            | T1_Id_Ex222 =>
              match goal with
                | [ |- SSN ] =>
                  constructor;
                    exact (match id with
                             | x11_Ex222 => "101-22-0411"%string
                             | x12_Ex222 => "220-39-7479"%string
                             | x13_Ex222 => "775-33-2819"%string
                           end)
                | [ |- FirstName ] =>
                  constructor;
                    exact (match id with
                             | x11_Ex222 => "David"%string
                             | x12_Ex222 => "Bertrand"%string
                             | x13_Ex222 => "Bertrand"%string
                           end)
                | [ |- LastName ] =>
                  constructor;
                    exact (match id with
                             | x11_Ex222 => "Hilbert"%string
                             | x12_Ex222 => "Russell"%string
                             | x13_Ex222 => "Russell"%string
                           end)
              end
            | T2_Id_Ex222 =>
              match goal with
                | [ |- FirstName ] =>
                  constructor;
                    exact (match id with
                             | y1_Ex222 => "David"%string
                             | y2_Ex222 => "Bertrand"%string
                             | y3_Ex222 => "Bertrand"%string
                             | y4_Ex222 => "Alan"%string
                           end)
                | [ |- LastName ] =>
                  constructor;
                    exact (match id with
                             | y1_Ex222 => "Hilbert"%string
                             | y2_Ex222 => "Russell"%string
                             | y3_Ex222 => "Russell"%string
                             | y4_Ex222 => "Turning"%string
                           end)
                | [ |- Salary ] =>
                  constructor;
                    exact (match id with
                             | y1_Ex222 => 150
                             | y2_Ex222 => 200
                             | y3_Ex222 => 225
                             | y4_Ex222 => 200
                           end)
              end
          end.
      Defined.

      Check (@RightPushforwardAlong C_Category_Ex22
                                    D_Category_Ex22
                                    TypeCat
                                    F_Functor_Ex22
                                    (fun (g : FunctorToType _) d => @TypeLimit
                                                                                 _
                                                                                 _
                                                                                 (RightPushforwardAlong_pre_Functor
                                                                                    C_Category_Ex22
                                                                                    D_Category_Ex22
                                                                                    TypeCat
                                                                                    F_Functor_Ex22
                                                                                    (g : FunctorToType _)
                                                                                    d))).

      Let U_Ex22_D_ex := Eval hnf in (ObjectOf (@RightPushforwardAlong C_Category_Ex22
                                                                       D_Category_Ex22
                                                                       TypeCat
                                                                       F_Functor_Ex22
                                                                       (fun (g : FunctorToType _) d => @TypeLimit
                                                                                                                    _
                                                                                                                    _
                                                                                                                    (RightPushforwardAlong_pre_Functor
                                                                                                                       C_Category_Ex22
                                                                                                                       D_Category_Ex22
                                                                                                                       TypeCat
                                                                                                                       F_Functor_Ex22
                                                                                                                       (g : FunctorToType _)
                                                                                                                       d)))
                                               ((γ_Functor_Ex222 : FunctorToSet _) : FunctorToType _)
                                               U_Ex22_D).

      Let Π_F__γ := (@RightPushforwardAlong C_Category_Ex22
                                            D_Category_Ex22
                                            TypeCat
                                            F_Functor_Ex22
                                            (fun (g : FunctorToType _) d => @TypeLimit
                                                                                         _
                                                                                         _
                                                                                         (RightPushforwardAlong_pre_Functor
                                                                                            C_Category_Ex22
                                                                                            D_Category_Ex22
                                                                                            TypeCat
                                                                                            F_Functor_Ex22
                                                                                            (g : FunctorToType _)
                                                                                            d)))
                      ((γ_Functor_Ex222 : FunctorToSet _) : FunctorToType _).

      Section Π_F__γ__T1_Ex222_cleanup.
        Example Π_F__γ__U_Ex222' :=
          Eval hnf in (@ObjectOf _ _ _ _
                                 Π_F__γ
                                 U_Ex22_D).

        Example Π_F__γ__U_Ex222'' :=
          Eval cbv beta iota zeta delta [Π_F__γ__U_Ex222'
                                           Object
                                           C_Edges_Ex22
                                           SliceCategory_Functor
                                           RightPushforwardAlong_pre_Functor
                                           γ_Functor_Ex222] in Π_F__γ__U_Ex222'.

        Arguments Π_F__γ__U_Ex222'' /.

                  Example Π_F__γ__U_Ex222''' := Eval simpl in Π_F__γ__U_Ex222''.

        Set Printing Coercions.
        Let typeof {T} (_ : T) := T.

        Example Π_F__γ__U_Ex222'''' : typeof Π_F__γ__U_Ex222'''.
        Proof.
          subst_body; hnf.
          assert (f : focus Π_F__γ__U_Ex222''') by constructor.
          unfold Π_F__γ__U_Ex222''' in f.
          simpl in f.
          unfold CommaCategory_ObjectT in *; simpl in *.
          unfold γ_Functor_Ex222_ObjectOf in *.
          simpl in *.
          unfold F_Functor_Ex22_ObjectOf in *.
          match type of f with
            | focus ?f' => exact f'
          end.
        Defined.

        Example Π_F__γ__U_Ex222''''' : Type.
        Proof.
          assert (f : focus Π_F__γ__U_Ex222'''') by constructor.
          unfold Π_F__γ__U_Ex222'''' in f; revert f.
          subst_body; hnf.
          intro f.
          match type of f with
            | focus ({ S0 : forall c : CommaCategory_Object ?A ?B, @?C c |
                       @?D S0 }) =>
              clear f; assert (f : focus ({ S0 : forall c : CommaCategory_ObjectT A B,
                                                   C (Build_CommaCategory_Object A B c) |
                                            D (fun c => S0 (CommaCategory_Object_Member c)) }))
                       by constructor;
              unfold CommaCategory_ObjectT in f; simpl in f
          end.
          match type of f with
            | focus ({ S0 : ?ST |
                       forall (c c' : CommaCategory_Object ?A ?B)
                              (g : CommaCategory_Morphism (CommaCategory_Object_Member c)
                                                                     (CommaCategory_Object_Member c')),
                         @?D S0 c c' g }) =>
              clear f; assert (f : focus { S0 : ST |
                                           forall (c c' : CommaCategory_ObjectT A B)
                                                  (g : CommaCategory_MorphismT c c'),
                                             D S0
                                               (Build_CommaCategory_Object A B c)
                                               (Build_CommaCategory_Object A B c')
                                               (Build_CommaCategory_Morphism c c' g) })
                       by constructor;
              unfold CommaCategory_ObjectT, CommaCategory_MorphismT in f;
              simpl in f
          end.
          match type of f with
            | focus ({ S0 : forall c : { ab : unit * ?B & @?C ab }, @?D c |
                       @?E S0 }) =>
              clear f; assert (f : focus ({ S0 : forall (b : B) (c : C (tt, b)),
                                                   D (existT _ (tt, b) c) |
                                            E (fun c => S0 (snd (projT1 c)) (projT2 c)) }))
                       by constructor;
              simpl in f
          end.
          match type of f with
            | focus ({ S0 : ?ST |
                       forall (c c' : ?C)
                              (g : { ab : unit * @?B c c' | @?D c c' ab }),
                         @?E S0 c c' g }) =>
              clear f; assert (f : focus { S0 : ST |
                                           forall (c c' : C)
                                                  (g : B c c')
                                                  (gp : D c c' (tt, g)),
                                             E S0
                                               c
                                               c'
                                               (existT _ (tt, g) gp)
                              })
                       by constructor;
              simpl in f
          end.
          match type of f with
            | focus ({ S0 : ?ST |
                       forall (c c' : { ab : unit * ?B & @?C ab }),
                         @?D S0 c c' }) =>
              clear f; assert (f : focus { S0 : ST |
                                           forall (b b' : B)
                                                  (c : C (tt, b))
                                                  (c' : C (tt, b')),
                                             D S0
                                               (existT _ (tt, b) c)
                                               (existT _ (tt, b') c')
                              })
                       by constructor;
              simpl in f
          end.
          repeat match type of f with
                   | appcontext G [fun x : ?T => match x with tt => ?R end] =>
                     clear f; let f' := context G[fun x : T => R] in
                              assert (f : f') by constructor;
                                simpl in f
                 end.
          (*repeat match type of f with
                   | appcontext G [match _ with
                                     | SSN_Ex22_C => Empty_set
                                     | FirstName_Ex22_C => Empty_set
                                     | LastName_Ex22_C => Empty_set
                                     | Salary_Ex22_C => Empty_set
                                     | T1_Ex22_C => Empty_set
                                     | T2_Ex22_C => Empty_set
                                   end] =>
                     clear f; let f' := context G[Empty_set] in
                              assert (f : f') by constructor;
                                simpl in f
                 end.*)
          unfold C_Edges_Ex22 in f; simpl in f.
          (*repeat match type of f with
                   | appcontext G [fun x : ?E => _] =>
                     match eval hnf in E with
                       | Empty_set =>
                         let T := fresh in
                         let F := fresh "Empty_set_func" in
                         evar (T : Type);
                           pose (fun x : E => match x return T with end) as F;
                           subst T;
                           clear f; let f' := context G[F] in
                                    assert (f : f') by constructor;
                                      simpl in f
                     end
                 end.*)
          repeat match type of f with
                   | appcontext G [fun x : Empty_set => @?t x] =>
                     match type of t with
                       | Empty_set -> ?t' =>
                         let F := fresh "Empty_set_func" in
                         pose (fun x : Empty_set => match x return t' with end) as F;
                             clear f; let f' := context G[F] in
                                      assert (f : f') by constructor;
                                        simpl in f
                     end
                 end.
          (*repeat match type of f with
                   | appcontext G [fun x : Empty_set => _] =>
                     let T := fresh in
                     let F := fresh "Empty_set_func" in
                     evar (T : Type);
                       pose (fun x : Empty_set => match x return T with end) as F;
                       subst T;
                       clear f; let f' := context G[F] in
                                assert (f : f') by constructor;

                                  simpl in f
                 end;
            subst_body.*)
          (*repeat match type of f with
                   | appcontext G [fun x : ?E => _] =>
                     pose E;
                     match eval hnf in E with
                       | Empty_set =>
                         let T := fresh in
                         let F := fresh "Empty_set_func" in
                         evar (T : Type);
                           pose (fun x : E => match x return T with end) as F;
                           subst T;
                           clear f; let f' := context G[F] in
                                    assert (f : f') by constructor;
                                      simpl in f
                     end
                 end.*)
          match type of f with
            | focus ?T => let rtn := fresh in pose T as rtn; exact rtn
          end.
        Defined.

        Example Π_F__γ__U_Ex222'''''' := Eval hnf in Π_F__γ__U_Ex222'''''.

        Example Π_F__γ__U_Ex222''''''_Obj : Set.
        Proof.
          assert (f : focus (Π_F__γ__U_Ex222'''''')) by constructor; unfold Π_F__γ__U_Ex222'''''' in f;
          revert f; clear; intro f.
          unfold F_Functor_Ex22_ObjectOf in *.
          match type of f with
            | focus { S0 : ?T | _ } => exact T
          end.
        Defined.

        Example Π_F__γ__U_Ex222''''''_Proof (o : Π_F__γ__U_Ex222''''''_Obj) : Prop.
        Proof.
          assert (f : focus (Π_F__γ__U_Ex222'''''')) by constructor; unfold Π_F__γ__U_Ex222'''''' in f;
          hnf in o;
          revert f o; clear; intros zf o.
          match type of f with
            | focus { S0 : ?T | @?Pf' S0 } => exact (Pf' o)
          end.
        Defined.

        Eval hnf in Π_F__γ__U_Ex222''''''_Obj.
        Print Π_F__γ__U_Ex222''''''.
        Example Π_F__γ__U_Ex222_MorphismOf' (x : D_Objects_Ex22) (m : path D_Edges_Ex22 U_Ex22_D x)
          := Eval hnf in (@MorphismOf _ _ _ _
                                      Π_F__γ
                                      U_Ex22_D
                                      x m).

        Example Π_F__γ__U_Ex222_MorphismOf'' x m : typeof (@Π_F__γ__U_Ex222_MorphismOf' x m).
        Proof.
          assert (f : focus (@Π_F__γ__U_Ex222_MorphismOf' x m)) by constructor;
          unfold Π_F__γ__U_Ex222_MorphismOf' in *; revert f; clear; intro f.
          simpl in f.
          hnf in x, m.

          revert


        Print Π_F__γ__U_Ex222''''''.
(*
        Goal forall x : Π_F__γ__U_Ex222'''', True.
        clear.
        intro x.
        hnf in x.
        destruct x.
        simpl in *.
        match type of x with
          | forall c : CommaCategory_Object ?A ?B, @?f c =>
            assert (x' : forall c : CommaCategory_ObjectT A B,
                      f (Build_CommaCategory_Object A B c))
        end.
        admit.
        match type of e with
          | forall (c c' : CommaCategory_Object ?A ?B) (g : CommaCategory_Morphism (CommaCategory_Object_Member c)
               (CommaCategory_Object_Member c')),
              @?f c c' g =>
            clear e; assert (e : forall (c c' : CommaCategory_ObjectT A B) (g : CommaCategory_MorphismT c c'),
                                    f (Build_CommaCategory_Object A B c) (Build_CommaCategory_Object A B c')
                                      (Build_CommaCategory_Morphism c c' g)) by admit
        end.
        match type of x with
          | forall c : CommaCategory_Object ?A ?B, @?f c =>
            match type of e with
              | appcontext e'[x] =>
                let e'' := context e'[fun c : CommaCategory_Object A B => x' (CommaCategory_Object_Member c)] in
                assert (e''' : e'') by admit
            end
        end.
        clear e.
        rename e''' into e'.
        simpl in *.
        match type of x with
          | forall c : CommaCategory_Object ?A ?B, @?f c =>
            repeat match type of e' with
                     | appcontext e''[x] =>
                       let e''' := context e''[fun c : CommaCategory_Object A B => x' (CommaCategory_Object_Member c)] in
                       clear e'; assert (e' : e''') by admit
                   end
        end.
        clear x.
        rename x' into x, e' into e.
        simpl in *.
        compute in x.
        unfold CommaCategory_ObjectT in e; simpl in *.
        unfold CommaCategory_MorphismT in *; simpl in *.
        Print existT.
        Print exist.
        match type of e with
          | forall (c c' : { ab : unit * ?A & @?B ab }) (g : { ab : unit * @?C c c' | @?D c c' ab }), @?E c c' g =>
            rename e into e'; pose proof (fun (c c' : { a : A & B (tt, a) })
                                              (g : { a : C (existT _ (tt, projT1 c) (projT2 c))
                                                           (existT _ (tt, projT1 c') (projT2 c')) |
                                                     D (existT _ (tt, projT1 c) (projT2 c))
                                                       (existT _ (tt, projT1 c') (projT2 c'))
                                                       (tt, a) })
                                          => e' (existT _ (tt, projT1 c) (projT2 c))
                                                (existT _ (tt, projT1 c') (projT2 c'))
                                                (exist _ (tt, proj1_sig g) (proj2_sig g))) as e; clear e'; simpl in *
        end.
        match type of x with
          | forall (c : { ab : unit * ?A & @?B ab }), _ =>
            rename x into x'; pose proof (fun c : { a : A & B (tt, a) } => x' (existT _ (tt, projT1 c) (projT2 c))) as x; simpl in *
        end.
        assert (H : x' = (fun c => x (existT _ (snd (projT1 c)) (projT2 c)))) by admit;
          rewrite H in e; clear H; clear x'; simpl in *.
        pose proof (fun ca ce c'a c'e ge gpf => e (existT _ ca (AddEdge NoEdges ce)) (existT _ c'a (AddEdge NoEdges c'e)) (exist _ (AddEdge NoEdges ge) gpf)) as e'; simpl in *.
        compute in e'.
        clear e.
        pose (fun a p => x (existT _ a p)) as x'; simpl in *.
        repeat match type of e' with
               | appcontext e''[x] =>
                 let e''' := context e''[fun c => (fun a p => x (existT _ a p)) (projT1 c) (projT2 c)] in
                 clear e'; assert (e' : e''') by admit;
                 change (fun a p => x (existT _ a p)) with x' in e'
             end.
        clearbody x'.
        clear x.
        compute in *.
        rename x' into x, e' into e.
        compute in *.
        let t := type of x in evar (x' : t).
        refine (x' = _).
        instantiate (1 := refine _).
        refine
        pose (fun ca ce => (x ca (AddEdge NoEdges ce))) as f;
          simpl in f.
        clear f.
        change (@AddEdge) with (fun V E s d d' => @AddEdge V E s d d') in e.
        match goal with
          | [ f := (fun ca ce => x ca (@?p ca ce)) |- _ ] =>  pose (fun ca ce =>
        end.

        clear x.
        change (x ?ca (AddEdge
        pose (fun ap => x (projT1 ap) (projT2 ap)) as x'; simpl in *.
        pose (fun a e => x a (AddEdge NoEdges e)) as x'; simpl in *.
        let t := type of x in let t' := type of x' in assert (FOOBAR : t).
        intro a;
          pose (x' a) as x'';
          destruct a; simpl;
          intro p; try apply (x'' tt); admit.
        Show Proof.
        Show Proof.
        pose
        intro p.
        intros a p.
        pose p as p'.
        destruct p as [ p'' | p'' ].
        admit.
        pose a as a'; destruct a.
        destruct
        apply (x' a y).
        destruct
        Ltac rep_con e x x' :=
             match e with
               | appcontext e'[x] =>
                 let e'' := context e'[x'] in
                 match e'' with
                   | appcontext e'''[AddEdge NoEdges] =>
                     let e'''' := context e'''[fun u => u] in
                     rep_con e'''' x x'
                 end
               | _ => e
             end.
        let e' := type of e in let e'' := rep_con e' x x' in assert (e''' : e'') by admit.


        Check x'.
        let t := type of x in
        assert t.
        Goal forall (x' : forall a : C_Objects_Ex22,
       match
         match a with
         | SSN_Ex22_C => SSN_Ex22_D
         | FirstName_Ex22_C => FirstName_Ex22_D
         | LastName_Ex22_C => LastName_Ex22_D
         | Salary_Ex22_C => Salary_Ex22_D
         | T1_Ex22_C => U_Ex22_D
         | T2_Ex22_C => U_Ex22_D
         end
       with
       | SSN_Ex22_D => unit
       | FirstName_Ex22_D => unit
       | LastName_Ex22_D => unit
       | Salary_Ex22_D => unit
       | U_Ex22_D => Empty_set
       end ->
       match a with
       | SSN_Ex22_C => SSN
       | FirstName_Ex22_C => FirstName
       | LastName_Ex22_C => LastName
       | Salary_Ex22_C => Salary
       | T1_Ex22_C => T1_Id_Ex222
       | T2_Ex22_C => T2_Id_Ex222
       end), forall a : C_Objects_Ex22,
   path
     (fun s d : D_Objects_Ex22 =>
      match s with
      | SSN_Ex22_D => Empty_set
      | FirstName_Ex22_D => Empty_set
      | LastName_Ex22_D => Empty_set
      | Salary_Ex22_D => Empty_set
      | U_Ex22_D =>
          match d with
          | SSN_Ex22_D => unit
          | FirstName_Ex22_D => unit
          | LastName_Ex22_D => unit
          | Salary_Ex22_D => unit
          | U_Ex22_D => Empty_set
          end
      end) U_Ex22_D
     match a with
     | SSN_Ex22_C => SSN_Ex22_D
     | FirstName_Ex22_C => FirstName_Ex22_D
     | LastName_Ex22_C => LastName_Ex22_D
     | Salary_Ex22_C => Salary_Ex22_D
     | T1_Ex22_C => U_Ex22_D
     | T2_Ex22_C => U_Ex22_D
     end ->
   match a with
   | SSN_Ex22_C => SSN
   | FirstName_Ex22_C => FirstName
   | LastName_Ex22_C => LastName
   | Salary_Ex22_C => Salary
   | T1_Ex22_C => T1_Id_Ex222
   | T2_Ex22_C => T2_Id_Ex222
   end.
        clear.
        intros x' a p.
        refine match p with
                 | AddEdge _ _ _ e => x' a _
                 | _ => _
               end.
        Focus 2.


        Show Proof.
        Show Proof.
        Show Proof.
        intros a p.
        Show Proof.
        evar (x'' : t).

 assert (H : x = x'') by admit; rewrite H in e; clear H.
        assert (H : forall a e, x a (AddEdge NoEdges e) = x' a e) by reflexivity.
        compute in e.
        clearbody x'.
        compute in
        setoid_rewrite H in e.
        match type of x' with
          | forall (a : ?A) (e : @?E a), _ =>
            pose E as E0
        end.

            assert (H : x = (fun a p => match p with
                                          | AddEdge _ _ NoEdges e0 => x' a (e0 : E0 a)
                                          | _ => x a p
                                        end)).
        change (x ?a0 (AddEdge NoEdges ?e0)) with (x' a0 e0) in e.
        pose
        change (x'
        match type of x' with
          | forall (a : ?A) (p : @?P a), _ =>
            change x' with (fun (a : A) (p : P a) => (fun (p' : P a) (a' : A) => x' a' p') p a) in e'
        end.

        pose proof (fun a p => x (existT _ a p)) as x'; simpl in *.
        simpl in *.
        clear x e.

        compute in e.
        assert (forall
        c : CommaCategory_ObjectT
              {|
              ObjectOf := fun _ : unit => U_Ex22_D;
              MorphismOf := fun _ _ _ : unit => NoEdges;
              FCompositionOf' := SliceCategory_Functor_subproof
                                   D_Category_Ex22 U_Ex22_D;
              FIdentityOf' := SliceCategory_Functor_subproof0
                                D_Category_Ex22 U_Ex22_D |} F_Functor_Ex22,
      match snd (projT1 ( c)) with
      | SSN_Ex22_C => SSN
      | FirstName_Ex22_C => FirstName
      | LastName_Ex22_C => LastName
      | Salary_Ex22_C => Salary
      | T1_Ex22_C => T1_Id_Ex222
      | T2_Ex22_C => T2_Id_Ex222
      end).
*)
        Eval hnf in (@ObjectOf _ _ _ _
                               Π_F__γ
                               SSN_Ex22_D).


        Require Import InitialTerminalCategory ChainCategory DiscreteCategoryFunctors.

        Definition F objC (C : Category) : Functor C TerminalCategory.
          clear.
          eexists; intros; simpl; eauto.
          Grab Existential Variables.
          intros; simpl; eauto.
          intros; simpl; eauto.
        Defined.

        Let Π_F_C objC (C : @Category) := Eval hnf in
                             (@RightPushforwardAlong C
                                                     (TerminalCategory : Category)
                                                     TypeCat
                                                     (@F objC C)
                                                     (fun (g : FunctorToType _) d => @TypeLimit
                                                                                                  _
                                                                                                  _
                                                                                                  (RightPushforwardAlong_pre_Functor
                                                                                                     C
                                                                                                     (TerminalCategory : Category)
                                                                                                     TypeCat
                                                                                                     (@F objC C)
                                                                                                     (g : FunctorToType _)
                                                                                                     d))).

        Let Π_F_C'_ObjectOf C := Eval hnf in @ObjectOf _ _ _ _ (@Π_F_C objC C).
        Let Π_F_C'_MorphismOf C := Eval simpl in @MorphismOf _ _ _ _ (@Π_F_C objC C).

        Require Import ProofIrrelevance.

        Definition Functor_01_0 : Functor [0] [1].
          clear.
          eexists (fun _ => exist _ 0 _) _;
            intros; compute; try apply proof_irrelevance.
          Grab Existential Variables.
          intros; compute; trivial.
          intros; compute; constructor; trivial.
        Defined.

        Definition Functor_01_1 : Functor [0] [1].
          clear.
          eexists (fun _ => exist _ 1 _) _;
            intros; compute; try apply proof_irrelevance.
          Grab Existential Variables.
          intros; compute; trivial.
          intros; compute; constructor; trivial.
        Defined.

        Let Π_F_01_F F := Eval hnf in
                           (@RightPushforwardAlong ([0] : Category)
                                                   ([1] : Category)
                                                   TypeCat
                                                   F
                                                   (fun (g : FunctorToType _) d => @TypeLimit
                                                                                                _
                                                                                                _
                                                                                                (RightPushforwardAlong_pre_Functor
                                                                                                   ([0] : Category)
                                                                                                   ([1] : Category)
                                                                                                   TypeCat
                                                                                                   F
                                                                                                   (g : FunctorToType _)
                                                                                                   d))).

        Example Π_F_01_F_ObjectOf (F : Functor [0] [1]) (x : Functor [0] TypeCat) := Eval hnf in (@ObjectOf _ _ _ _ (Π_F_01_F F) x).
        Example Π_F_01_F_MorphismOf (F : Functor [0] [1]) (s d : Functor [0] TypeCat) m m' := Eval simpl in (@MorphismOf _ _ _ _ (Π_F_01_F F) s d m m').

        Example Π_F_01_F_ObjectOf_ObjectOf F x (x' : [1]%category) := Eval hnf in (@Π_F_01_F_ObjectOf F x x').
        Example Π_F_01_F_ObjectOf_MorhismOf F x s d (m : Morphism [1] s d) := Eval simpl in (MorphismOf (@Π_F_01_F_ObjectOf F x) m).

        Example Π_F_01_F_ObjectOf_ObjectOf F x x' : typeof (@Π_F_01_F_ObjectOf_ObjectOf F x x').
        Proof.
          clear.
          pose (Π_F_01_F_ObjectOf_ObjectOf F x x') as f.
          hnf in *;
            simpl in *; unfold Object in *; simpl in *.
          match goal with
            | [ f := { S0 : forall c : CommaCategory_Object ?A ?B, @?C c |
                       @?D S0 } |- _ ] =>
              clear f; pose ({ S0 : forall c : CommaCategory_ObjectT A B, C (Build_CommaCategory_Object A B c) |
                               D (fun c => S0 (CommaCategory_Object_Member c)) }) as f; unfold CommaCategory_ObjectT in *;
              simpl in *
          end.
          match goal with
            | [ f := { S0 : ?ST |
                       forall (c c' : CommaCategory_Object ?A ?B)
                              (g : CommaCategory_Morphism (CommaCategory_Object_Member c)
                                                                     (CommaCategory_Object_Member c')),
                         @?D S0 c c' g } |- _ ] =>
              clear f; pose ({ S0 : ST |
                               forall (c c' : CommaCategory_ObjectT A B)
                                      (g : CommaCategory_MorphismT c c'),
                                 D S0
                                   (Build_CommaCategory_Object A B c)
                                   (Build_CommaCategory_Object A B c')
                                   (Build_CommaCategory_Morphism c c' g) }) as f;
              unfold CommaCategory_ObjectT, CommaCategory_MorphismT in f;
              simpl in f
          end.
          exact f.
        Defined.

        Example Π_F_01_F_ObjectOf_ObjectOf (F : Functor [0] [1]) (x : Functor [0] TypeCat) (x' : [1]%category) :
          typeof (Π_F_01_F_ObjectOf_ObjectOf F x x').
        Proof.
          hnf in *; simpl in *.
          assert (Hf : focus (Π_F_01_F_ObjectOf_ObjectOf F x x')) by constructor.
          unfold Π_F_01_F_ObjectOf_ObjectOf in Hf; simpl in Hf.
          revert Hf; clear; intro.
          unfold CommaCategory_ObjectT, CommaCategory_MorphismT in Hf.
          simpl in Hf.
          match type of Hf with
            | focus ({ S0 : forall c : { ab : unit * ?A & @?B ab },
                              @?C c |
                       @?D S0 }) =>
              clear Hf; assert (Hf : focus ({ S0 : forall (ca : A) (cb : B (tt, ca)),
                                                     C (existT _ (tt, ca) cb) |
                                              D (fun c => S0 (snd (projT1 c)) (projT2 c)) })) by constructor;
              simpl in Hf
          end.
          match type of Hf with
            | focus ({ S0 : ?ST |
                       forall (c c' : { ab : unit * ?A & @?B ab }),
                         @?C S0 c c' }) =>
              clear Hf; assert (Hf : focus ({ S0 : ST |
                                              forall (ca : A) (cb : B (tt, ca))
                                                     (c'a : A) (c'b : B (tt, c'a)),
                                                C S0
                                                  (existT _ (tt, ca) cb)
                                                  (existT _ (tt, c'a) c'b)
                                           })) by constructor;
              simpl in Hf
          end.
          match type of Hf with
            | focus ({ S0 : ?ST |
                       forall ca cb c'a c'b
                              (g : { gh : unit * (@?A ca cb c'a c'b) | @?B ca cb c'a c'b gh }),
                         @?C S0 ca cb c'a c'b g }) =>
              clear Hf;
                assert (Hf : focus ({ S0 : ST |
                                      forall ca cb c'a c'b
                                             (g : A ca cb c'a c'b)
                                             (gpf : B ca cb c'a c'b (tt, g)),
                                        C S0 ca cb c'a c'b (exist _ (tt, g) gpf) })) by constructor;
                simpl in Hf
          end.
          match type of Hf with
            | focus ?T => exact T
          end.
        Defined.

        Arguments Π_F_01_F_ObjectOf_ObjectOf / .

        Require Import FunctionalExtensionality.

        Definition f_to_functor_MorphismOf (f : [0]%category -> TypeCat) s d (m : Morphism [0] s d) : f s -> f d.
          revert m; clear; intro; clear m;
          destruct s as [ [ ] ];
          match goal with
            | [ H : S _ <= 0 |- _ ] => exfalso; revert H; clear; intro; solve [ intuition ] || fail 1
            | _ => idtac
          end;
          destruct d as [ [ ] ];
          match goal with
            | [ H : S _ <= 0 |- _ ] => exfalso; revert H; clear; intro; solve [ intuition ] || fail 1
            | _ => idtac
          end;
          repeat match goal with
                   | [ H : 0 <= 0 |- _ ] => assert (H = le_n 0) by (apply proof_irrelevance); subst H
                 end;
          exact (@id _).
        Defined.

        Definition f_to_functor (f : [0]%category -> TypeCat) : Functor [0] TypeCat.
        Proof.
          revert f; clear; intro.
          exists f (f_to_functor_MorphismOf f); intros; simpl; destruct_sig; simpl in *;
          repeat match goal with
                   | [ H : nat |- _ ] =>
                     destruct H;
                       match goal with
                         | [ H : S _ <= 0 |- _ ] => exfalso; revert H; clear; intro; solve [ intuition ] || fail 1
                         | _ => idtac
                       end
                 end;
            repeat match goal with
                     | [ H : 0 <= 0 |- _ ] => assert (H = le_n 0) by (apply proof_irrelevance); subst H
                   end;
            compute;
            repeat match goal with
                     | [ |- context[match ?f with _ => _ end] ] => destruct f
                   end; try reflexivity.
        Defined.
      End Π_F__γ__T1_Ex222_cleanup.
    End Example222.
  End Example22.
End FunctorialDataMigration.
Arguments Π_F_01_F_ObjectOf_ObjectOf / .
Arguments Functor_01_0 / .
Arguments f_to_functor / .
Definition foo  f := Eval simpl in (@Π_F_01_F_ObjectOf_ObjectOf Functor_01_1 (f_to_functor f)).
Let typeof {T} (_ : T) := T.
Eval compute in typeof foo.
Require Import ExtrOcamlString.
Require Import ExtrOcamlBasic.
Extraction Δ_F__δ__T1_Ex221_rev.
Extraction foo.
Extraction Π_F__γ__U_Ex222''''''.
Extraction path.
        Example F01_0 (f : [0]%category -> TypeCat) : Type.
        Proof.
          pose (@Π_F_01_F_ObjectOf_ObjectOf Functor_01_0 (f_to_functor f)) as f'.
          hnf in *; revert f'; clear; intro.
          simpl in *.

          unfold f_to_functor_MorphismOf in *.
          simpl in *.
          revert f';
        Goal Type.
        pose (@Π_F_01_F_ObjectOf_ObjectOf Functor_01_0) as f; hnf in f; unfold typeof in f; simpl in f; revert f; clear; intro.
        unfold MorphismOf in f; simpl in f.
        apply f.
        assert (f' : [0]%category -> TypeCat) by admit.

        Goal forall x y : @Π_F_01_F_ObjectOf_ObjectOf Functor_01_0, x = y.

          Set Printing All.

 }) =>
              clear Hf; assert (Hf : focus ({ S0 : forall (ca : A) (cb : B (tt, ca)),
                                                     C (existT _ (tt, ca) cb) |
                                              D (fun c => S0 (snd (projT1 c)) (projT2 c)) })) by constructor;
              simpl in Hf
          end.
                                end.

          unfold ObjectOf in f; simpl in *.
          unfold MorphismOf in f; simpl in f.
          compute in f.
          simpl in *.
        Print Π_F_01_F_ObjectOf_ObjectOf.
          match goal with
            | [ f := { S0 : ?ST |
                       forall (c c' : ?C)
                              (g : CommaCategory_Morphism c c'),
                         @?D S0 c c' g } |- _ ] =>
              clear f; pose ({ S0 : ST |
                               forall (c c' : C)
                                      (g : CommaCategory_MorphismT (Build_CommaCategory_Object c) (CommaCategory_Object_Member c')),
                                 D S0 c c' (Build_CommaCategory_Morphism c c' g) }) (*as f;
              unfold CommaCategory_MorphismT in f; simpl in * *)
          end.
                                                                      c')),


                         @?D S0 c c' g
                              (g : CommaCategory_Morphism (CommaCategory_Object_Member c)
                                                                     (CommaCategory_Object_Member c')),

                        D (exist _ (Build_CommaCategory_Object A B (proj1_sig S0)) (proj2_sig S0))
                          (Build_CommaCategory_Object A' B' c)
                          (Build_CommaCategory_Object A' B' c')
                          (Build_CommaCategory_Morphism (Build_CommaCategory_Object A' B' c)
                                                                   (Build_CommaCategory_Object A' B' c')
                                                                   g) }) as f'

          compute in f.

        Print Π_F_01_F_ObjectOf.

        Example Π_F_C'_ObjectOf C g : typeof (@Π_F_C'_ObjectOf C g).
        Proof.
          pose (@Π_F_C'_ObjectOf C g) as f; hnf in f |- *; revert f; clear; intro.
          hnf in *.
          unfold Object in *.
          simpl in *.
          unfold RightPushforwardAlong_pre_Functor, RightPushforwardAlong_ObjectOf_MorphismOf,
            InducedLimitFunctors.InducedLimitFunctor_MorphismOf, LimitFunctorTheorems.InducedLimitMap, NTComposeT, NTComposeF in *;
            simpl in *.
        Print Π_F_C'_ObjectOf.
        Example Π_F_C' C : typeof (@Π_F_C objC C).
        pose (Π_F_C C) as Π_F_C''.
        hnf in Π_F_C'' |- *.
        revert Π_F_C''; clear; intro.

        clear Π_F_C typeof.
        clear
        clear Π_F_C'
        compute in Π_F_C''.

        ((γ_Functor_Ex222 : FunctorToSet _) : FunctorToType _).

        Goal Π_F__γ__U_Ex222''''.
        hnf.
        subst_body.
        eexists.
        intros.
        destruct_head @CommaCategory_Object.
        simpl in *.
        destruct_sig.
        simpl in *.
        destruct_head prod.
        simpl in *.
        destruct_head unit.
        destruct_head @CommaCategory_Morphism.
        simpl in *.
        destruct_sig; destruct_head prod; destruct_head unit; simpl in *.
        destruct c0; simpl in *.
        - destruct c; simpl in *.
          compute in *.
          destruct p1.
          unfold concatenate in e.

          + induction p0.
            destruct_head C_Objects_Ex22;
              simpl in *.

            CommaCategory_Object
              {|
                ObjectOf := fun _ : unit => U_Ex22_D;
                MorphismOf := fun _ _ _ : unit => NoEdges;
                FCompositionOf' := SliceCategory_Functor_subproof
                                     D_Category_Ex22 U_Ex22_D;
                FIdentityOf' := SliceCategory_Functor_subproof0
                                  D_Category_Ex22 U_Ex22_D |} F_Functor_Ex22.

            Example Π_F__γ__U_Ex222''''' : Type.
            Proof.
              evar (A : Type).
              assert (forall a b : Π_F__γ__U_Ex222'''', a = b).
              - intros a b; hnf in *.
                destruct a as [ x e ].
                simpl in *.
                pose proof (fun c : CommaCategory_ObjectT _ _ => x c) as x'; simpl in x'.
                move x' at top.
                compute in x'.
                pose proof (fun (c c' : CommaCategory_ObjectT _ _) (g : CommaCategory_MorphismT _ _) => e c c' g) as e'.
                move e' at top; simpl in e'.
                unfold CommaCategory_ObjectT, CommaCategory_MorphismT in e'; simpl in e'.
                unfold C_Edges_Ex22, D_Edges_Ex22 in *; simpl in *.
                pattern x in e'.
                Check e'.
                pose proof (existT _ x' e') as a0.
                pattern x in a0.
                Check a0.
                match type of e' with
                  | (fun _ => _) _ => idtac (* pose proof (existT _ x' (f x')) as a*)
                end.
                move a at top.
                pattern
                  Ltac x_to_x' T2 x x' :=
                  match T2 with
                    | appcontext T2'[x] =>
                      let T2'' := context T2'[x'] in
                      x_to_x' T2'' x x'
                    | _ => T2
                  end.
                match type of a with
                  | { _ : ?T1 & ?T2 } =>
                    let T2' := x_to_x' T2 x x' in
                    pose T2' as a'; move a' at top
                end.
                pattern x' in a'.
                let t := type of a in
                assert (t = A) by (subst A; reflexivity).
                assert (
                    intros
                      pose Π_F__γ__U_Ex222'''' as f'.
                    hnf in *.
                    assert (f = f') by reflexivity.
                    destruct f.

                    Eval hnf in Π_F__γ__U_Ex222''''.


                    change (CommaCategory_Object_Member ?x) with x in *.
                    match goal with
                      | [ f := context G'[let (x) := ?y in x] |- _ ] => idtac
                    end.
                    change (let (x) := ?y in x) with y in *.
                    unfold C_Objects_Ex22 in *.
                    simpl in f.
                    change (CommaCategory_Object ?A ?B) with (CommaCategory_ObjectT A B) in f.

                    Check (CommaCategory_ObjectT _ _ : CommaCategory_Object
                                                                    {|
                                                                      ObjectOf := fun _ : unit => U_Ex22_D;
                                                                      MorphismOf := fun _ _ _ : unit => NoEdges;
                                                                      FCompositionOf' := SliceCategory_Functor_subproof
                                                                                           D_Category_Ex22 U_Ex22_D;
                                                                      FIdentityOf' := SliceCategory_Functor_subproof0
                                                                                        D_Category_Ex22 U_Ex22_D |} F_Functor_Ex22).
                    unfold CommaCategory_Object.
                    unfold Object, C_Edges_Ex22 in f.

                    Print Π_F__γ__U_Ex222'.
                    d
                      (AddEdge NoEdges e)).

                Example Π_F__γ__T1_Ex222_with_type' : {T : Set & T }
                  := Eval compute in @existT _ _ _ Π_F__γ__T1_Ex222'.

                Let Π_F__γ__T1_Ex222_DE_Type : Set.
                  match eval compute in (projT1 Π_F__γ__T1_Ex222_with_type') with
                    | forall d : ?D, @?E d -> _ => exact { d : D & E d }
                  end.
                Defined.

                Let Π_F__γ__T1_Ex222_D_Type : Set.
                  match eval compute in (projT1 Π_F__γ__T1_Ex222_with_type') with
                    | forall d : ?D, @?E d -> _ => exact D
                  end.
                Defined.

                Example Π_F__γ__T1_Ex222_with_type'' (d : Π_F__γ__T1_Ex222_D_Type) : {T : Set & T }.
                Proof.
                  assert (H : focus Π_F__γ__T1_Ex222_DE_Type) by constructor; unfold Π_F__γ__T1_Ex222_DE_Type in *; hnf in d.
                  repeat match type of H with
                           | appcontext G[unit] => let x := fresh in
                                                   evar (x : Set);
                                                     let G' := context G[x] in
                                                     clear H;
                                                       assert (H : G') by constructor;
                                                       subst x
                         end;
                    repeat match type of H with
                             | appcontext G[Empty_set] => let G' := context G[unit] in
                                                          clear H;
                                                            assert (H : G') by constructor
                           end;
                    match type of H with
                      | focus ({ d0 : _ & @?f d0 }) => let P := fresh in pose (f d) as P; exists P; subst P; simpl; clear H;
                                                                         pose d as d'; destruct d; try solve [ constructor ];
                                                                         let g := fresh in pose (Π_F__γ__T1_Ex222' d' tt) as g; compute in *;
                                                                                           exact g
                    end.
                Defined.
      End Π_F__γ__T1_Ex222_cleanup.

      Section Π_F__γ__T2_Ex222_cleanup.
        Example Π_F__γ__T2_Ex222' :=
          Eval compute in (fun d e =>
                             (@MorphismOf _ _ _ _
                                          ((PullbackAlong C_Category_Ex22 D_Category_Ex22 SetCat F_Functor_Ex22)
                                             γ_Functor_Ex222)
                                          T2_Ex22_C
                                          d
                                          (AddEdge NoEdges e))).

        Example Π_F__γ__T2_Ex222_with_type' : {T : Set & T }
          := Eval compute in @existT _ _ _ Π_F__γ__T2_Ex222'.

        Let Π_F__γ__T2_Ex222_DE_Type : Set.
          match eval compute in (projT1 Π_F__γ__T2_Ex222_with_type') with
            | forall d : ?D, @?E d -> _ => exact { d : D & E d }
          end.
        Defined.

        Let Π_F__γ__T2_Ex222_D_Type : Set.
          match eval compute in (projT1 Π_F__γ__T2_Ex222_with_type') with
            | forall d : ?D, @?E d -> _ => exact D
          end.
        Defined.

        Example Π_F__γ__T2_Ex222_with_type'' (d : Π_F__γ__T2_Ex222_D_Type) : {T : Set & T }.
        Proof.
          assert (H : focus Π_F__γ__T2_Ex222_DE_Type) by constructor; unfold Π_F__γ__T2_Ex222_DE_Type in *; hnf in d.
          repeat match type of H with
                   | appcontext G[unit] => let x := fresh in
                                           evar (x : Set);
                                             let G' := context G[x] in
                                             clear H;
                                               assert (H : G') by constructor;
                                               subst x
                 end;
            repeat match type of H with
                     | appcontext G[Empty_set] => let G' := context G[unit] in
                                                  clear H;
                                                    assert (H : G') by constructor
                   end;
            match type of H with
              | focus ({ d0 : _ & @?f d0 }) => let P := fresh in pose (f d) as P; exists P; subst P; simpl; clear H;
                                                                 pose d as d'; destruct d; try solve [ constructor ];
                                                                 let g := fresh in pose (Π_F__γ__T2_Ex222' d' tt) as g; compute in *;
                                                                                   exact g
            end.
        Defined.
      End Π_F__γ__T2_Ex222_cleanup.

      Example Π_F__γ__T1_Ex222 := Eval compute in (fun d => projT2 (Π_F__γ__T1_Ex222_with_type'' d)).
      Example Π_F__γ__T2_Ex222 := Eval compute in (fun d => projT2 (Π_F__γ__T2_Ex222_with_type'' d)).

      Print Π_F__γ__T1_Ex222.
      Print Π_F__γ__T2_Ex222.


    End Example222.

  End Example22.
End FunctorialDataMigration.
