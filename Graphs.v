Require Import FunctionalExtensionality.
Require Export Functor SetCategory Cat FunctorCategory Paths.
Require Import Common FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section GraphObj.
  Variable C : Category.

  Inductive GraphIndex := GraphIndexSource | GraphIndexTarget.

  Definition GraphIndex_Morphism (a b : GraphIndex) : Set :=
    match (a, b) with
      | (GraphIndexSource, GraphIndexSource) => unit
      | (GraphIndexTarget, GraphIndexTarget) => unit
      | (GraphIndexTarget, GraphIndexSource) => Empty_set
      | (GraphIndexSource, GraphIndexTarget) => GraphIndex
    end.

  Global Arguments GraphIndex_Morphism a b /.

  Definition GraphIndex_Compose s d d' (m1 : GraphIndex_Morphism d d') (m2 : GraphIndex_Morphism s d) :
    GraphIndex_Morphism s d'.
    destruct s, d, d'; simpl in *; trivial.
  Defined.

  Definition GraphIndexingCategory : Category.
    refine (@Build_Category GraphIndex
                                       GraphIndex_Morphism
                                       (fun x => match x with GraphIndexSource => tt | GraphIndexTarget => tt end)
                                       GraphIndex_Compose
                                       _
                                       _
                                       _);
    abstract (
        intros; destruct_type GraphIndex; simpl in *; destruct_type Empty_set; trivial
      ).
  Defined.

  Definition UnderlyingGraph_ObjectOf x :=
    match x with
      | GraphIndexSource => { sd : C * C & C.(Morphism) (fst sd) (snd sd) }
      | GraphIndexTarget => Object C
    end.

  Global Arguments UnderlyingGraph_ObjectOf x /.

  Definition UnderlyingGraph_MorphismOf s d (m : Morphism GraphIndexingCategory s d) :
    UnderlyingGraph_ObjectOf s -> UnderlyingGraph_ObjectOf d :=
    match (s, d) as sd return
      Morphism GraphIndexingCategory (fst sd) (snd sd) ->
      UnderlyingGraph_ObjectOf (fst sd) -> UnderlyingGraph_ObjectOf (snd sd)
      with
      | (GraphIndexSource, GraphIndexSource) => fun _ => @id _
      | (GraphIndexSource, GraphIndexTarget) => fun m' =>
        match m' with
          | GraphIndexSource => fun sdm => fst (projT1 sdm)
          | GraphIndexTarget => fun sdm => snd (projT1 sdm)
        end
      | (GraphIndexTarget, GraphIndexSource) => fun m' => match m' with end
      | (GraphIndexTarget, GraphIndexTarget) => fun _ => @id _
    end m.

  Definition UnderlyingGraph : Functor GraphIndexingCategory TypeCat.
  Proof.
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor C D
          UnderlyingGraph_ObjectOf
          UnderlyingGraph_MorphismOf
          _
          _
        )
    end;
    abstract (
      unfold UnderlyingGraph_MorphismOf; simpl; intros;
        destruct_type GraphIndex;
        autorewrite with morphism;
        trivial; try destruct_to_empty_set
    ).
  Defined.
End GraphObj.

Section GraphFunctor.
  Let UnderlyingGraphFunctor_ObjectOf (C : Cat) : Functor GraphIndexingCategory TypeCat :=
    UnderlyingGraph C.

  Local Ltac t :=
    intros; destruct_head_hnf GraphIndex;
      repeat match goal with
               | [ H : Empty_set |- _ ] => destruct H
               | _  => reflexivity
               | _ => progress destruct_head GraphIndex; simpl in *
               | _ => progress repeat (apply functional_extensionality_dep; intro)
               | _ => progress simpl_eq
               | _ => progress destruct_sig; simpl in *
             end.

  Definition UnderlyingGraphFunctor_MorphismOf C D (F : Morphism Cat C D) :
    Morphism (TypeCat ^ GraphIndexingCategory) (UnderlyingGraph C) (UnderlyingGraph D).
  Proof.
    exists (fun c => match c as c return (UnderlyingGraph C) c -> (UnderlyingGraph D) c with
                       | GraphIndexSource => fun sdm => existT _ (F (fst (projT1 sdm)), F (snd (projT1 sdm))) (F.(MorphismOf) (projT2 sdm))
                       | GraphIndexTarget => ObjectOf F
                     end);
    abstract t.
  Defined.

  Definition UnderlyingGraphFunctor : Functor Cat (TypeCat ^ GraphIndexingCategory).
  Proof.
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor C D
          UnderlyingGraphFunctor_ObjectOf
          UnderlyingGraphFunctor_MorphismOf
          _
          _
        )
    end;
    abstract (
      repeat match goal with
               | _ => progress simpl in *
               | _ => progress functor_eq
               | _ => progress nt_eq
               | _ => progress t
               | _ => progress unfold ComponentsOf
               | [ |- appcontext[match ?x with _ => _ end] ] => destruct x
             end
    ).
  Defined.
End GraphFunctor.

Section FreeCategory.
  Variable F : Functor GraphIndexingCategory TypeCat.

  Let vertices := F GraphIndexTarget.

  Hint Rewrite concatenate_p_noedges concatenate_noedges_p concatenate_associative.

  Definition FreeCategory : Category.
  Proof.
    refine (@Build_Category
              vertices
              _
              (@NoEdges _ _)
              (fun s d d' m m' => @concatenate _ _ s d d' m' m)
              _
              _
              _
           );
    intros; autorewrite with core; reflexivity.
    Grab Existential Variables.
  (* what goes here, of type [vertices -> vertices -> Type]? *)
  (* morphisms are paths *)
  Admitted.
End FreeCategory.
