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

From CFGKAT.Semantics Require Export Bisimulation.
From CFGKAT.Semantics Require Export TransitionFunction.

Local Open Scope cfgkat_scope.

Lemma cfgkat_invariant_while_dynamics_reject :
  forall e b c i a,
    CFGKATL11Premise e (c and b) ->
    eval_test (c and b) a i ->
    CFGKATExpressionDynamics (while b do e, i) a CFGKATAutomatonReject.
Proof.
  intros e b c i a Hinv Hbc.
  set (N := fun s => exists j, s = (while b do e, j) /\
                               eval_test (c and b) a j).
  eapply rejecting_set_member_resolves_reject
    with (ys := []) (aut := CFGKATExpressionAutomaton) (N := N).
  - intros s [j [Hs Hbcj]].
    subst s. simpl in Hbcj.
    eapply cfgkat_l11_premise_stuck in Hinv as Hstuck; eauto.
    destruct (Hstuck j a Hbcj) as [Hbody_reject | [sigma [Hbody Hbc_sigma]]].
    + left. eapply CFGKATExpressionDynamicsLoopGuardTrue; intuition.
      now apply CFGKATExpressionDynamicsLoopSeqReject.
    + right. exists (while b do e, sigma). firstorder.
      * apply CFGKATSilentLoop; intuition.
        left. eapply cfgkat_dynamics_nonreject_finite; eauto.
        discriminate.
      * apply CFGKATSilentLoop; intuition.
        right. eapply cfgkat_dynamics_nonreject_finite; eauto.
        discriminate.
  - exists i; intuition.
Qed.

Inductive L11_relation
  (e : CFGKATExpression)
  (b c : CFGKATTest)
  : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop :=
| L11RelationLoop :
    forall i,
      L11_relation e b c
        (while b do (test (not c) ;; e), i)
        (while b do e, i)
| L11RelationLoopSeq :
    forall e' i,
      L11_relation e b c
        (e' |> while b do (test (not c) ;; e), i)
        (e' |> while b do e, i).

Local Lemma empty_resolved_expression_transition :
  forall s a zeta,
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [empty_syntactic_context])
      s a zeta <->
    CFGKATExpressionDynamics s a zeta.
Proof.
  intros s a zeta.
  apply resolve_syntactic_empty_identity.
Qed.

Local Lemma L11_left_body_dynamics :
  forall e c a i zeta,
    ~ eval_test c a i ->
    CFGKATExpressionDynamics (e, i) a zeta ->
    CFGKATExpressionDynamics (test (not c) ;; e, i) a zeta.
Proof.
  intros e c a i zeta Hnotc Hbody.
  rewrite transition_output_exact.
  rewrite transition_sequence.
  rewrite transition_assert.
  destruct (eval_test_dec (not c)); intuition; simpl.
  now apply transition_output_exact.
Qed.

Definition cfgkat_continuing_output
  {X: Type}
  (zeta: CFGKATAutomatonOutputs X)
:=
  match zeta with
  | CFGKATAutomatonAccept _ => True
  | CFGKATAutomatonContinue _ => True
  | _ => False
  end.

Definition cfgkat_floor
  (zeta: CFGKATAutomatonOutputs CFGKATSyntConfiguration)
:=
  match zeta with
  | CFGKATAutomatonBreak i => CFGKATAutomatonAccept i
  | _ => zeta
  end.

Lemma CFGKATExpressionDynamicsLoopSeqHalt :
  forall (a : Atom) (i : IndicatorAssignment)
         (e1 e2 : CFGKATExpression) zeta,
    cfgkat_halting_output zeta ->
    ~ cfgkat_continuing_output zeta ->
    CFGKATExpressionDynamics (e1, i) a zeta ->
    CFGKATExpressionDynamics (e1 |> e2, i) a (cfgkat_floor zeta).
Proof.
  intros.
  destruct zeta; simpl in *; try now intuition.
  - now apply CFGKATExpressionDynamicsLoopSeqReject.
  - now apply CFGKATExpressionDynamicsLoopSeqBreak.
  - now apply CFGKATExpressionDynamicsLoopSeqReturn.
  - now apply CFGKATExpressionDynamicsLoopSeqJump.
Qed.

Local Lemma L11_loop_strong_step_not_c :
  forall e b c i a,
    eval_test b a i ->
    ~ eval_test c a i ->
    CFGKATStrongStep
      CFGKATExpressionAutomaton CFGKATExpressionAutomaton
      [empty_syntactic_context] [empty_syntactic_context]
      (L11_relation e b c)
      a
      (while b do (test (not c) ;; e), i)
      (while b do e, i).
Proof.
  intros e b c i a Hb Hnotc.
  destruct (cfgkat_expression_dynamics_total (e, i) a)
    as [zeta Hbody].
  destruct (classic (cfgkat_halting_output zeta)); [
    destruct (classic (cfgkat_continuing_output zeta))|].
  - eapply cfgkat_dynamics_nonreject_finite in Hbody;
      try intro; subst; intuition.
    destruct zeta; try now intuition.
    + eapply CFGKATStrongStepSilent.
      * apply CFGKATSilentLoop with (sigma := i0); eauto.
        left.
        eapply CFGKATExpressionFiniteDynamicsSequenceSkip; eauto.
        now apply CFGKATExpressionFiniteDynamicsAssertTrue.
      * apply CFGKATSilentLoop; eauto.
        left; eauto.
      * apply L11RelationLoop.
    + eapply CFGKATStrongStepSilent.
      * apply CFGKATSilentLoop with (sigma := i0); eauto.
        right.
        eapply CFGKATExpressionFiniteDynamicsSequenceSkip; eauto.
        now apply CFGKATExpressionFiniteDynamicsAssertTrue.
      * apply CFGKATSilentLoop; eauto.
        right; eauto.
      * apply L11RelationLoop.
  - eapply CFGKATStrongStepHalt; swap 1 3.
    + apply empty_resolved_expression_transition.
      eapply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
      apply CFGKATExpressionDynamicsLoopSeqHalt; eauto.
    + apply empty_resolved_expression_transition.
      eapply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
      apply CFGKATExpressionDynamicsLoopSeqHalt; eauto.
      eapply L11_left_body_dynamics; eauto.
    + now destruct zeta.
  - destruct zeta; simpl in H; try now intuition.
    destruct s as [e' sigma].
    eapply CFGKATStrongStepNext.
    + apply empty_resolved_expression_transition.
      eapply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
      apply CFGKATExpressionDynamicsLoopSeqNext.
      eapply L11_left_body_dynamics; eauto.
    + apply empty_resolved_expression_transition.
      eapply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
      apply CFGKATExpressionDynamicsLoopSeqNext; eauto.
    + apply L11RelationLoopSeq.
Qed.

Local Lemma L11_loop_strong_step :
  forall e b c i a,
    CFGKATL11Premise e (c and b) ->
    CFGKATStrongStep
      CFGKATExpressionAutomaton CFGKATExpressionAutomaton
      [empty_syntactic_context] [empty_syntactic_context]
      (L11_relation e b c)
      a
      (while b do (test (not c) ;; e), i)
      (while b do e, i).
Proof.
  intros e b c i a Hinv.
  destruct (classic (eval_test b a i)) as [Hb | Hnotb].
  - destruct (classic (eval_test c a i)) as [Hc | Hnotc].
	    + eapply CFGKATStrongStepHalt
	        with (zeta := CFGKATAutomatonReject); try now intuition.
	      * apply empty_resolved_expression_transition.
	        eapply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
	        apply CFGKATExpressionDynamicsLoopSeqReject.
	        apply CFGKATExpressionDynamicsSequenceReject.
	        apply CFGKATExpressionDynamicsAssertFalse.
	        intuition.
	      * apply empty_resolved_expression_transition.
	        eapply cfgkat_invariant_while_dynamics_reject; eauto.
	        simpl; intuition.
    + eapply L11_loop_strong_step_not_c; eauto.
  - eapply CFGKATStrongStepHalt with
      (zeta := CFGKATAutomatonAccept i); try now intuition.
    + apply empty_resolved_expression_transition.
      apply CFGKATExpressionDynamicsLoopGuardFalse; eauto.
    + apply empty_resolved_expression_transition.
      apply CFGKATExpressionDynamicsLoopGuardFalse; eauto.
Qed.

Local Lemma L11_loopseq_strong_step :
  forall e b c e' i a,
    CFGKATStrongStep
      CFGKATExpressionAutomaton CFGKATExpressionAutomaton
      [empty_syntactic_context] [empty_syntactic_context]
      (L11_relation e b c)
      a
      (e' |> while b do (test (not c) ;; e), i)
      (e' |> while b do e, i).
Proof.
  intros e b c e' i a.
  destruct (cfgkat_expression_dynamics_total (e', i) a)
    as [zeta Hbody].
  destruct (classic (cfgkat_halting_output zeta)); [
    destruct (classic (cfgkat_continuing_output zeta))|].
  - destruct zeta; try now intuition.
    + eapply cfgkat_dynamics_nonreject_finite in Hbody;
        try discriminate.
      eapply CFGKATStrongStepSilent.
      * apply CFGKATSilentLoopSeq. left. eauto.
      * apply CFGKATSilentLoopSeq. left. eauto.
      * apply L11RelationLoop.
    + eapply cfgkat_dynamics_nonreject_finite in Hbody;
        try discriminate.
      eapply CFGKATStrongStepSilent.
      * apply CFGKATSilentLoopSeq. right. eauto.
      * apply CFGKATSilentLoopSeq. right. eauto.
      * apply L11RelationLoop.
  - eapply CFGKATStrongStepHalt
      with (zeta := cfgkat_floor zeta);
      simpl; try now intuition;
      apply empty_resolved_expression_transition;
      now apply CFGKATExpressionDynamicsLoopSeqHalt.
      now destruct zeta.
  - destruct zeta; simpl in *; try intuition discriminate.
    destruct s as [f sigma].
    eapply CFGKATStrongStepNext.
    + apply empty_resolved_expression_transition.
      apply CFGKATExpressionDynamicsLoopSeqNext; eauto.
    + apply empty_resolved_expression_transition.
      apply CFGKATExpressionDynamicsLoopSeqNext; eauto.
    + apply L11RelationLoopSeq.
Qed.

Program Definition L11_strong_bisimulation
  (e : CFGKATExpression)
  (b c : CFGKATTest)
  (Hprem: CFGKATL11Premise e (c and b))
:
  @CFGKATStrongBisimulation
    CFGKATExpressionAutomaton CFGKATExpressionAutomaton
    [empty_syntactic_context] [empty_syntactic_context]
:= {|
    cfgkat_strong_relation := L11_relation e b c;
|}.
Next Obligation.
  intros e b c Hprem x1 x2 a Hrel.
  inversion Hrel; subst.
  - apply L11_loop_strong_step; eauto.
  - apply L11_loopseq_strong_step.
Qed.

Theorem L11_sound:
  forall e b c i,
    CFGKATL11Premise e (c and b) ->
      (while b do e, i) ~~
      (while b do (test (not c) ;; e), i).
Proof.
  intros e b c i Hinv.
  unshelve eexists. eapply bisim_sym.
  - eapply (strong_bisim_to_bisim [empty_syntactic_context]
                                  [empty_syntactic_context]).
    eapply L11_strong_bisimulation; eauto.
  - simpl. apply L11RelationLoop.
Qed.
