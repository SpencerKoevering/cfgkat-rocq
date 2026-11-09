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

From CFGKAT.Soundness Require Export SequenceLaws.

Local Open Scope type_scope.

Inductive A1Relation : cfgkat_states ExprAutEmpty ->
                       cfgkat_states ExprAutEmpty ->
                       Prop :=
| A1_main :
    forall x v p i,
      A1Relation (assign v to x;; do p, i)
                 (do p ;; assign v to x, i)
| A1_supp :
    forall x v i,
      A1Relation (1, update i x v)
                 (1 ;; assign v to x, i).

Program Definition A1_bisim := {|
  cfgkat_local_direct_relation := A1Relation;
|}.
Next Obligation.
  intros e1 e2 i1 i2 a p x1' Hrel.
  dependent destruction Hrel.
  - rewrite !transition_sequence.
    rewrite !transition_assign; simpl.
    rewrite !transition_action; simpl.
    intros. inversion_clear H.
    eexists. intuition eauto. constructor.
  - rewrite !transition_sequence.
    rewrite !transition_assert.
    destruct (eval_test_dec 1 a); simpl in *; intuition.
    discriminate.
Qed.
Next Obligation.
  intros e1 e2 i1 i2 a p x2' Hrel.
  dependent destruction Hrel.
  - rewrite !transition_sequence.
    rewrite !transition_assign; simpl.
    rewrite !transition_action; simpl.
    intros. inversion_clear H.
    eexists. intuition eauto. constructor.
  - rewrite !transition_sequence.
    rewrite !transition_assert.
    destruct (eval_test_dec 1 a); simpl in *; intuition.
    rewrite !transition_assign in H.
    discriminate.
Qed.
Next Obligation.
  intros e1 e2 i1 i2 a Hrel Hnot_left Hnot_right.
  dependent destruction Hrel.
  - exfalso. eapply Hnot_right.
    rewrite !transition_sequence.
    now rewrite !transition_action; simpl.
  - rewrite transition_sequence.
    rewrite !transition_assert.
    destruct (eval_test_dec 1 a); simpl; auto.
    now rewrite transition_assign.
Qed.

Theorem A1_sound:
  forall p x v i,
    (assign v to x ;; do p, i) ~~ (do p ;; assign v to x, i).
Proof.
  unshelve eexists.
  - apply local_direct_bisimulation_to_bisimulation, A1_bisim.
  - simpl. intuition now constructor.
Qed.

Inductive A2Relation : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop :=
| A2_main :
    forall x v i,
      A2Relation (assign v to x;; test x is v, i) (assign v to x, i).

Theorem A2_sound:
  forall x v i,
      (assign v to x;; test x is v, i) ~~
      (assign v to x, i).
Proof.
  intros x vi i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_sequence.
  rewrite !transition_assign; simpl.
  rewrite transition_assert.
  destruct (eval_test_dec (x is vi)); auto.
  contradict n; simpl.
  apply update_same.
Qed.

Theorem A3_sound:
  forall x v i,
    (test x is v ;; assign v to x, i) ~~ (test x is v, i).
Proof.
  intros x v i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_sequence.
  rewrite !transition_assert.
  destruct (eval_test_dec (x is v)); auto; simpl.
  rewrite transition_assign. f_equal.
  simpl in e. subst.
  apply update_noop.
Qed.

Theorem A4_sound:
  forall x v v' i,
    (assign v' to x ;; assign v to x, i) ~~ (assign v to x, i).
Proof.
  intros x v v' i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_sequence.
  rewrite !transition_assign; simpl.
  rewrite !transition_assign; simpl.
  f_equal. apply update_shadow.
Qed.

Theorem A5_sound:
  forall x v i,
    (assign v to x ;; return, i) ~~ (return, i).
Proof.
  intros x v i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_sequence.
  rewrite transition_assign; simpl.
  now rewrite !transition_return; simpl.
Qed.

Lemma test_indicator_free_update
  (x : IndicatorVariable)
  (b : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
  (v : IndicatorValue)
  :
  test_indicator_free x b ->
  (eval_test b a (update i x v) <-> eval_test b a i).
Proof.
  induction b; simpl; intro Hfree.
  - tauto.
  - rewrite update_other by
      (intro Hxy; apply Hfree; symmetry; exact Hxy).
    tauto.
  - tauto.
  - tauto.
  - destruct Hfree as [Hfree1 Hfree2].
    specialize (IHb1 Hfree1).
    specialize (IHb2 Hfree2).
    tauto.
  - destruct Hfree as [Hfree1 Hfree2].
    specialize (IHb1 Hfree1).
    specialize (IHb2 Hfree2).
    tauto.
  - specialize (IHb Hfree).
    tauto.
Qed.

Theorem A6_sound:
  forall x v e f i t,
    (assign v to x ;; (if (TPrim t) then e else f), i) ~~ (if (TPrim t) then assign v to x ;; e else assign v to x ;; f, i).
Proof.
  intros x v e f i t.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_choice.
  rewrite !transition_sequence.
  rewrite !transition_assign; simpl.
  rewrite transition_choice.
  pose proof (test_indicator_free_update x (prim t) a i v I) as Hfree.
  destruct (eval_test_dec (prim t) a (update i x v)) as [Hupdated | Hupdated];
    destruct (eval_test_dec (prim t) a i) as [Hinitial | Hinitial];
    destruct (atom_dec a t) as [Hat | Hnot];
    simpl in *;
    try tauto;
    try contradiction;
    reflexivity.
Qed.

Theorem A7_sound:
  forall x v i,
    (assign v to x ;; 0, i) ~~ (0, i).
Proof.
  intros x v i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_sequence.
  rewrite transition_assign; simpl.
  rewrite !transition_assert.
  now destruct (eval_test_dec 0).
Qed.

Theorem A8_sound:
  forall x x' v v' i,
    x <> x' ->
    (assign v' to x' ;; assign v to x, i) ~~
    (assign v to x ;; assign v' to x', i).
Proof.
  intros x x' v v' i Hneq.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite !transition_sequence.
  rewrite !transition_assign; simpl.
  rewrite !transition_assign; simpl.
  f_equal. extensionality y.
  destruct (Var_eq_dec x y).
  - subst. symmetry.
    rewrite update_other by intuition.
    now rewrite !update_same.
  - rewrite update_other by intuition.
    destruct (Var_eq_dec x' y).
    + subst. now rewrite !update_same.
    + now repeat rewrite update_other by intuition.
Qed.

Inductive A9Relation : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop :=
| A9_main :
    forall x x' v v' e f i,
      x <> x' -> A9Relation (assign v to x ;; if x' is v' then e else f, i) (if x' is v' then assign v to x ;; e else assign v to x ;; f, i)
| A9_refl :
    forall e,
      A9Relation e e
.

Theorem A9_sound:
  forall x x' v v' e f i,
  x <> x' ->
  (assign v to x ;; if x' is v' then e else f, i) ~~ (if x' is v' then assign v to x ;; e else assign v to x ;; f, i).
Proof.
  intros x x' v v' e f i Hneq.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_choice.
  rewrite !transition_sequence; simpl.
  rewrite transition_assign; simpl.
  rewrite transition_choice.
  destruct (eval_test_dec (x' is v')),
           (Val_eq_dec (i x') v'); try now intuition.
  - simpl in e0. contradict n.
    rewrite <- e0.
    now rewrite update_other.
  - contradict n. simpl.
    now rewrite update_other.
Qed.
