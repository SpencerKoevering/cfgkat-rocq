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

From CFGKAT.Soundness Require Export AssignmentLaws.
From CFGKAT.Semantics Require Export LoopInvariant.

Local Open Scope type_scope.

Theorem L1_sound:
  forall e i, (1 |>  e, i) ~~ (e, i).
Proof.
  intros e i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_loopseq.
  rewrite transition_assert.
  destruct (eval_test_dec 1); simpl in *; intuition.
Qed.

Theorem L2_sound:
  forall e i,
  (0 |>  e, i) ~~ (0, i).
Proof.
  intros e i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_loopseq.
  rewrite transition_assert.
  destruct (eval_test_dec 0); simpl in *; intuition.
Qed.

Theorem L3_sound:
  forall e i,
  (return |> e, i) ~~ (return, i).
Proof.
  intros e i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_loopseq.
  now rewrite transition_return.
Qed.

Theorem L4_sound:
  forall e i l,
  (goto l |> e, i) ~~ (goto l, i).
Proof.
  intros e i l.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_loopseq.
  now rewrite transition_goto.
Qed.

Theorem L5_sound:
  forall e i,
  (break |> e, i) ~~ (1, i).
Proof.
  intros e i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_loopseq.
  rewrite transition_assert.
  destruct (eval_test_dec 1); simpl in *; intuition.
  now rewrite transition_break.
Qed.

Theorem L6_sound:
  forall e i,
  (continue |> e, i) ~~ (e, i).
Proof.
  intros e i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_loopseq.
  now rewrite transition_continue.
Qed.

Inductive L7Relation : CFGKATSyntConfiguration ->
                       CFGKATSyntConfiguration ->
                       Prop :=
| L7_main :
    forall p f g i,
      L7Relation ((do p ;; f) |> g, i) (do p ;; (f |> g), i)
| L7_supp :
    forall f g i,
      L7Relation ((1 ;; f) |> g, i) (1 ;; (f |> g), i)
| L7_refl :
    forall s,
      L7Relation s s
.

Program Definition L7_bisim := {|
  cfgkat_local_direct_relation := L7Relation;
|}.
Next Obligation.
  intros e1 e2 i1 i2 a p x1' Hrel.
  dependent destruction Hrel.
  - rewrite transition_loopseq.
    rewrite !transition_sequence.
    rewrite !transition_action; simpl.
    intros. inversion_clear H.
    eexists. intuition eauto. constructor.
  - rewrite transition_loopseq.
    rewrite !transition_sequence.
    rewrite !transition_assert.
    destruct (eval_test_dec 1); simpl in *; intuition.
    rewrite transition_loopseq.
    eexists. intuition eauto. constructor.
  - eexists. intuition eauto. constructor.
Qed.
Next Obligation.
  intros e1 e2 i1 i2 a p x2' Hrel.
  dependent destruction Hrel.
  - rewrite transition_sequence.
    rewrite !transition_loopseq.
    rewrite transition_sequence.
    rewrite !transition_action; simpl.
    intros. inversion_clear H.
    eexists. intuition eauto. constructor.
  - rewrite transition_sequence.
    rewrite !transition_loopseq.
    rewrite transition_sequence.
    rewrite transition_assert.
    destruct (eval_test_dec 1); try now intuition.
    simpl. rewrite transition_loopseq.
    eexists. intuition eauto. constructor.
  - eexists. intuition eauto. constructor.
Qed.
Next Obligation.
  intros e1 e2 i1 i2 a Hrel.
  dependent destruction Hrel; auto.
  - rewrite transition_loopseq.
    rewrite !transition_sequence.
    rewrite !transition_action; simpl.
    intros Hnot_left Hnot_right.
    exfalso. eapply Hnot_left; eauto.
  - intros Hnot_left Hnot_right.
    rewrite !transition_loopseq.
    rewrite !transition_sequence.
    rewrite !transition_assert; simpl.
    destruct (transition_output f a i2) eqn:?; simpl;
    now rewrite transition_loopseq, Heqc.
Qed.

Theorem L7_sound:
  forall p f g i,
  ((do p ;; f) |> g, i) ~~ (do p ;; (f |> g), i).
Proof.
  unshelve eexists.
  - apply local_direct_bisimulation_to_bisimulation, L7_bisim.
  - simpl. intuition now constructor.
Qed.

Theorem L8_sound:
  forall x j f g i,
    ((assign j to x ;; f) |> g, i) ~~
    (assign j to x ;; (f |> g), i).
Proof.
  intros x j f g i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_loopseq.
  rewrite !transition_sequence.
  rewrite !transition_assign; simpl.
  now rewrite transition_loopseq.
Qed.

Theorem L9_sound:
  forall b e f g i,
    ((if b then e else f) |> g, i) ~~
    (if b then (e |> g) else (f |> g), i).
Proof.
  intros b e f g i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_loopseq.
  rewrite !transition_choice.
  rewrite !transition_loopseq.
  now destruct (eval_test_dec b).
Qed.

Theorem L10_sound:
  forall e b i,
  (while b do e, i) ~~ (if b then e |> while b do e else 1, i).
Proof.
  intros e b i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_choice.
  rewrite !transition_loop.
  rewrite !transition_loopseq.
  rewrite !transition_assert.
  destruct (eval_test_dec 1); simpl in *; intuition.
Qed.
