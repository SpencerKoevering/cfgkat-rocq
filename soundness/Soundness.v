Require Import Stdlib.Logic.Classical.
From Stdlib Require Import Lists.List.
Import ListNotations.

From CFGKAT.Soundness Require Export BooleanAlgebraSoundness.
From CFGKAT.Semantics Require Export TransitionFunction.
From CFGKAT.Soundness Require Export AssignmentLaws.
From CFGKAT.Soundness Require Export GuardLaws.
From CFGKAT.Soundness Require Export SequenceLaws.
From CFGKAT.Soundness Require Export LoopLaws.
From CFGKAT.Soundness Require Export CongruenceLaws.
From CFGKAT.Soundness Require Export ContextualAxioms.
From CFGKAT.Syntax Require Export Axioms.

Local Open Scope cfgkat_scope.

Definition C7_solution
  (E F : label_environment CFGKATExpression)
  : Prop :=
  forall l body,
    E l = Some body ->
    F |- goto l == body -| F.

Definition C7_side_condition
  (E F : label_environment CFGKATExpression)
  : Prop :=
  (forall l, label_in_dom E l <-> label_in_dom F l) /\
  C7_solution E F /\
  (forall l l' body target,
    E l = Some body ->
    E l' = Some target ->
    guarded l' body).

Lemma EqC7_from_side_condition
  (E F : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  :
  C7_side_condition E F ->
  F |- e == e -| E.
Proof.
  intros [Hdom [Hsol Hguard]].
  apply EqC7.
  - exact Hdom.
  - exact Hguard.
  - exact Hsol.
Qed.

Lemma strong_equiv_no_goto :
  forall E F e,
    (forall k, ~ contains_goto k e) ->
    E |- e == e -| F.
Proof.
  intros E F e Hno.
  change (cfgkat_equiv (E, e) (F, e)).
  transitivity (empty_label_context, e).
  - replace E with (empty_label_context + E)
      by (apply label_env_cup_empty_l).
    apply EqC3.
    intros l _.
    split.
    + intros k body H; discriminate.
    + exact (Hno l).
  - apply EqSym.
    replace F with (empty_label_context + F)
      by (apply label_env_cup_empty_l).
    apply EqC3.
    intros l _.
    split.
    + intros k body H; discriminate.
    + exact (Hno l).
Qed.

Theorem CFGKATEquiv_sound :
  forall E e f F,
    E |- e == f -| F ->
    forall i,
      (e, i) ~[lift E, lift F] (f, i).
Proof.
  intros E e f F H.
  induction H; intro i.
  - eapply CFGKATCongruenceRefl_sound; eauto.
  - eapply CFGKATCongruenceSym_sound; eauto.
  - eapply CFGKATCongruenceTrans_sound; eauto.
  - eapply G1_sound; eauto.
  - eapply G2_sound; eauto.
  - eapply G3_sound; eauto.
  - eapply G4_sound; eauto.
  - eapply G5_sound; eauto.
  - eapply S1_sound; eauto.
  - eapply S2_sound; eauto.
  - eapply S3_sound; eauto.
  - eapply S4_sound; eauto.
  - eapply S5_sound; eauto.
  - eapply S6_sound; eauto.
  - eapply S7_sound; eauto.
  - eapply S8_sound; eauto.
  - eapply S9_sound; eauto.
  - eapply L1_sound; eauto.
  - eapply L2_sound; eauto.
  - eapply L3_sound; eauto.
  - eapply L4_sound; eauto.
  - eapply L5_sound; eauto.
  - eapply L6_sound; eauto.
  - eapply L7_sound; eauto.
  - eapply L8_sound; eauto.
  - eapply L9_sound; eauto.
  - eapply L10_sound; eauto.
  - eapply L11_sound.
    intro j.
    exact (IHCFGKATEquiv j).
  - eapply A1_sound; eauto.
  - eapply A2_sound; eauto.
  - eapply A3_sound; eauto.
  - eapply A4_sound; eauto.
  - eapply A5_sound; eauto.
  - eapply A6_sound; eauto.
  - eapply A7_sound; eauto.
  - eapply A8_sound; eauto.
  - eapply A9_sound; eauto.
  - eapply C1_sound; eauto.
  - eapply C2_sound; eauto.
  - eapply C3_sound; eauto.
  - eapply C4_sound; eauto.
  - eapply C5_sound; eauto.
  - eapply C6_sound; eauto.
  - eapply C7_sound; eauto.
  - eapply CFGKATCongruenceGuardedChoice_sound; eauto.
  - eapply CFGKATCongruenceBooleanChoice_sound; eauto.
  - eapply CFGKATCongruenceBooleanAssert_sound; eauto.
  - eapply CFGKATCongruenceBooleanLoop_sound; eauto.
  - eapply CFGKATCongruenceSequenceRight_sound; eauto.
  - eapply CFGKATCongruenceLoopSeqRight_sound; eauto.
  - eapply CFGKATCongruenceSequenceLeftEmpty_sound.
    apply IHCFGKATEquiv.
  - eapply CFGKATCongruenceLoopSeqLeftEmpty_sound.
    apply IHCFGKATEquiv.
  - eapply CFGKATCongruenceLoopBodyEmpty_sound.
    intro j.
    exact (IHCFGKATEquiv j).
  - eapply CFGKATCongruenceLoopBody_sound; eauto.
Qed.
