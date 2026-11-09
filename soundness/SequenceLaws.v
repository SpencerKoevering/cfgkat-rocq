Require Import Stdlib.Program.Equality.
Require Import Stdlib.Setoids.Setoid.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.Logic.ClassicalEpsilon.
Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.Arith.Arith.
From Stdlib Require Import Lists.List.
Import ListNotations.

From CFGKAT.Soundness Require Export GuardLaws.

Local Open Scope type_scope.

Record CFGKATDirectBisimulation := {
  cfgkat_direct_relation: cfgkat_states ExprAutEmpty ->
                          cfgkat_states ExprAutEmpty ->
                          Prop;
  cfgkat_direct_bisimulation_step:
    forall e1 e2 i1 i2 a,
      cfgkat_direct_relation (e1, i1) (e2, i2) ->
      lifted_relation cfgkat_direct_relation
                      (transition_output e1 a i1)
                      (transition_output e2 a i2);
}.

Program Definition direct_bisimulation_to_bisimulation
  (B: CFGKATDirectBisimulation) :
  CFGKATAutomatonBisimulation ExprAutEmpty ExprAutEmpty:= {|
  cfgkat_relation := cfgkat_direct_relation B;
|}.
Next Obligation.
  intros. simpl in H0, H1. destruct x1, x2.
  rewrite resolve_syntactic_empty_identity in H0, H1.
  rewrite transition_output_exact in H0, H1.
  subst. now apply cfgkat_direct_bisimulation_step.
Qed.

Record CFGKATLocalDirectBisimulation := {
  cfgkat_local_direct_relation: cfgkat_states ExprAutEmpty ->
                                cfgkat_states ExprAutEmpty ->
                                Prop;
  cfgkat_local_direct_left_to_right:
    forall e1 e2 i1 i2 a p x1',
      cfgkat_local_direct_relation (e1, i1) (e2, i2) ->
      transition_output e1 a i1 = CFGKATAutomatonNext p x1' ->
      exists x2',
        transition_output e2 a i2 = CFGKATAutomatonNext p x2' /\
        cfgkat_local_direct_relation x1' x2';
  cfgkat_local_direct_right_to_left:
    forall e1 e2 i1 i2 a p x2',
      cfgkat_local_direct_relation (e1, i1) (e2, i2) ->
      transition_output e2 a i2 = CFGKATAutomatonNext p x2' ->
      exists x1',
        transition_output e1 a i1 = CFGKATAutomatonNext p x1' /\
        cfgkat_local_direct_relation x1' x2';
  cfgkat_local_direct_step:
    forall e1 e2 i1 i2 a,
      cfgkat_local_direct_relation (e1, i1) (e2, i2) ->
      (forall q i'' e',
        transition_output e1 a i1 <>
        CFGKATAutomatonNext q (e', i'')) ->
      (forall q i'' e',
        transition_output e2 a i2 <>
        CFGKATAutomatonNext q (e', i'')) ->
      transition_output e1 a i1 = transition_output e2 a i2;
}.

Program Definition local_direct_bisimulation_to_bisimulation
  (B: CFGKATLocalDirectBisimulation) :
  CFGKATAutomatonBisimulation ExprAutEmpty ExprAutEmpty
:= direct_bisimulation_to_bisimulation {|
  cfgkat_direct_relation x1 x2 :=
    x1 = x2 \/ cfgkat_local_direct_relation B x1 x2;
|}.
Next Obligation.
  simpl. intros. destruct H.
  - inversion_clear H.
    destruct (transition_output e2 a i2); simpl;
    constructor; intuition.
  - destruct (classic (exists p i' e',
      transition_output e1 a i1 =
      CFGKATAutomatonNext p (e', i'))); [|
    destruct (classic (exists p i' e',
        transition_output e2 a i2 =
        CFGKATAutomatonNext p (e', i')))].
    + do 3 destruct H0.
      edestruct cfgkat_local_direct_left_to_right as [? [? ?]]; eauto.
      rewrite H0, H1. constructor. intuition.
    + do 3 destruct H1.
      edestruct cfgkat_local_direct_right_to_left as [? [? ?]]; eauto.
      rewrite H1, H2. constructor. intuition.
    + erewrite cfgkat_local_direct_step; eauto.
      * destruct (transition_output e2 a i2);
        now repeat constructor.
      * intros. do 3 eapply not_ex_all_not in H0. eauto.
      * intros. do 3 eapply not_ex_all_not in H1; eauto.
Qed.

Inductive S1Relation : cfgkat_states ExprAutEmpty ->
                       cfgkat_states ExprAutEmpty ->
                       Prop :=
| S1_refl :
    forall e, S1Relation e e
| S1_main :
    forall e f g i, S1Relation (e;;f;;g, i) (e;;(f;;g), i).

Program Definition S1_bisim := {|
  cfgkat_local_direct_relation := S1Relation;
|}.
Next Obligation.
  intros e f g i a p x1' Hrel.
  dependent destruction Hrel.
  - intros. eexists; intuition eauto.
    now constructor.
  - rewrite !transition_sequence in *.
    destruct (transition_output e0 a i);
      try discriminate; simpl.
    + rewrite transition_sequence; simpl.
      eexists. intuition eauto. constructor.
    + destruct s. simpl. intros.
      exists (c;; (f0;; g0), i0).
      inversion_clear H. intuition constructor.
Qed.
Next Obligation.
  intros e f g i a p x2' Hrel.
  dependent destruction Hrel.
  - intros. eexists. intuition eauto.
    now constructor.
  - rewrite !transition_sequence in *; simpl.
    destruct (transition_output e0 a i);
      try discriminate; simpl.
    + rewrite transition_sequence; simpl.
      eexists. intuition eauto. constructor.
    + destruct s. exists ((c;; f0);; g0, i0).
      inversion_clear H. intuition constructor.
Qed.
Next Obligation.
  intros e f g i a Hrel Hnot_left Hnot_right.
  dependent destruction Hrel; auto.
  rewrite !transition_sequence in *.
  destruct (transition_output e0 a i) eqn:?; firstorder.
  - simpl. now rewrite transition_sequence.
  - simpl in *. destruct s.
    exfalso. now eapply Hnot_left.
Qed.

Theorem S1_sound:
  forall e f g i,
    ((e;;f);;g, i) ~~ (e;;(f;;g), i).
Proof.
  unshelve eexists.
  - apply local_direct_bisimulation_to_bisimulation, S1_bisim.
  - simpl. intuition now constructor.
Qed.

Theorem S2_sound:
  forall e i,
    (0;;e, i) ~~ (0, i).
Proof.
  intros e i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_sequence.
  rewrite transition_assert.
  now destruct (eval_test_dec 0 a i).
Qed.

Theorem S3_sound:
  forall e i,
    (1;;e, i) ~~ (e, i).
Proof.
  intros e i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_sequence.
  rewrite transition_assert.
  now destruct (eval_test_dec 0 a i).
Qed.

Inductive S4Relation : CFGKATSyntConfiguration ->
                       CFGKATSyntConfiguration ->
                       Prop :=
| S4_refl :
    forall e, S4Relation e e
| S4_main :
    forall e i, S4Relation (e;;1, i) (e, i).

Program Definition S4_bisim := {|
  cfgkat_local_direct_relation := S4Relation;
|}.
Next Obligation.
  intros e1 e2 i1 i2 a p x1' Hrel.
  dependent destruction Hrel.
  - intros. eexists. intuition eauto. constructor.
  - rewrite transition_sequence.
    destruct (transition_output e2 a i2);
      try discriminate; simpl.
    + rewrite transition_assert.
      destruct (eval_test_dec 1 a i); discriminate.
    + destruct s. intros. inversion_clear H.
      eexists. intuition eauto. constructor.
Qed.
Next Obligation.
  intros e1 e2 i1 i2 a p x2' Hrel.
  dependent destruction Hrel.
  - intros. eexists. intuition eauto. constructor.
  - rewrite transition_sequence. intros.
    rewrite H. simpl. destruct x2'.
    eexists. intuition eauto. constructor.
Qed.
Next Obligation.
  intros e1 e2 i1 i2 a Hrel Hnot_left Hnot_right.
  dependent destruction Hrel; auto.
  rewrite transition_sequence.
  destruct (transition_output e2 a i2) eqn:?; auto; simpl.
  - rewrite transition_assert.
    destruct (eval_test_dec 1 a i); auto.
    now simpl in n.
  - exfalso. destruct s.
    eapply Hnot_right; eauto.
Qed.

Theorem S4_sound:
  forall e i,
    (e;;1, i) ~~ (e, i).
Proof.
  unshelve eexists.
  - apply local_direct_bisimulation_to_bisimulation, S4_bisim.
  - simpl. intuition now constructor.
Qed.

Theorem S5_sound:
  forall b c i,
    (test b;; test c, i) ~~ (test b and c, i).
Proof.
  intros b c i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_sequence.
  rewrite !transition_assert.
  destruct (eval_test_dec b a i); simpl sequence_output.
  - rewrite transition_assert.
    destruct (eval_test_dec c a i),
             (eval_test_dec (b and c) a i);
      simpl in *; intuition.
  - destruct (eval_test_dec (b and c) a i);
      simpl in *; intuition.
Qed.

Theorem S6_sound:
  forall e i,
    (return ;; e, i) ~~ (return, i).
Proof.
  intros e i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  now rewrite transition_sequence, transition_return.
Qed.

Theorem S7_sound:
  forall e i,
    (continue ;; e, i) ~~ (continue, i).
Proof.
  intros e i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  now rewrite transition_sequence, transition_continue.
Qed.

Theorem S8_sound:
  forall e i,
    (break ;; e, i) ~~ (break, i).
Proof.
  intros e i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  now rewrite transition_sequence, transition_break.
Qed.

Theorem S9_sound:
  forall e l i,
    (goto l ;; e, i) ~~ (goto l, i).
Proof.
  intros e l i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  now rewrite transition_sequence, transition_goto.
Qed.
