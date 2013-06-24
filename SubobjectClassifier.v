Require Export Pullback Limits.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section subobject_classifier.
  (** Quoting Wikipedia:

    For the general definition, we start with a category [C] that has
    a terminal object, which we denote by [1]. The object [Ω] of [C]
    is a subobject classifier for [C] if there exists a morphism [m :
    1 → Ω] with the following property: for each monomorphism [j : U →
    X] there is a unique morphism [χj : X → Ω] such that the following
    commutative diagram:

    [[
        U ----> 1
        |       |
      j |       | m
        ↓       ↓
        X ----> Ω
           χj
    ]]

    is a pullback diagram — that is, [U] is the limit of the diagram:

    [[
                1
                |
                | m
                ↓
        X ----> Ω
           χj
    ]]

    The morphism [χj] is then called the classifying morphism for the
    subobject represented by [j].
   *)

  (** Quoting nCatLab:

   Definition 1. In a category [C] with finite limits, a subobject
   classifier is a monomorphism [true : * → Ω] out of the terminal
   object, such that for every monomorphism [U → X] in [C] there is a unique
   morphism [χU : X → Ω] such that there is a pullback diagram

   [[
        U ----> *
        |       |
        |       | true
        ↓       ↓
        X ----> Ω
           χU
   ]]

   See for instance (MacLane-Moerdijk, p. 22).
   *)

  Variable C : Category.

  Local Reserved Notation "'Ω'".

  Record SubobjectClassifier :=
    {
      SubobjectClassifierOne : TerminalObject C where "1" := (TerminalObject_Object SubobjectClassifierOne);
      ObjectOfTruthValues : C where "'Ω'" := ObjectOfTruthValues;
      TrueValue : C.(Morphism) 1 Ω;
      TrueIsMonomorphism : IsMonomorphism TrueValue;
      SubobjectClassifyingMap : forall U X (j : C.(Morphism) U X),
                                  IsMonomorphism j
                                  -> { χj : Morphism C X Ω &
                                                     { H : Compose χj j =
                                                           Compose TrueValue (TerminalObject_Morphism SubobjectClassifierOne U)
                                                                   & IsPullbackGivenMorphisms
                                                                   X 1 Ω
                                                                   χj TrueValue
                                                                   U j
                                                                   (TerminalObject_Morphism SubobjectClassifierOne U)
                                                                   H } }
    }.
End subobject_classifier.
