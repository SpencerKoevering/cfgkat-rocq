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

From CFGKAT.Soundness Require Export BooleanAlgebraSoundness.
From CFGKAT.Soundness Require Export LoopLaws.

Local Open Scope type_scope.

Lemma lifted_relation_refl
  {X : Type}
  (R : X -> X -> Prop)
  :
  (forall x, R x x) ->
  forall zeta : CFGKATAutomatonOutputs X,
    lifted_relation R zeta zeta.
Proof.
  intros HR zeta.
  destruct zeta; constructor; auto.
Qed.

Program Definition bisim_refl
  {A : CFGKATAutomaton}
  (Hfunc : forall s,
      cfgkat_automaton_dynamics_functional
        (cfgkat_transitions A s))
  : CFGKATAutomatonBisimulation A A
:= {|
  cfgkat_relation := eq
|}.
Next Obligation.
  intros A Hfunc x y a zeta1 zeta2 Heq Hx Hy. subst.
  specialize (Hfunc y). enforce_functionality.
  now apply lifted_relation_refl.
Qed.

Theorem CFGKATCongruenceRefl_sound :
  forall E e i,
    (e, i) ~[lift E] (e, i).
Proof.
  intros E e i.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar.
  exists (bisim_refl (resolved_lift_functional E)).
  reflexivity.
Qed.

Theorem CFGKATCongruenceSym_sound :
  forall E F e f i j,
    (e, i) ~[lift E, lift F] (f, j) ->
    (f, j) ~[lift F, lift E] (e, i).
Proof.
  intros E F e f i j Hsound.
  destruct Hsound as [R HR].
  now exists (bisim_sym R).
Qed.

Program Definition bisim_trans
  {A B C : CFGKATAutomaton}
  (HtotalB : forall s,
      cfgkat_automaton_dynamics_total
        (cfgkat_transitions B s))
  (R1 : CFGKATAutomatonBisimulation A B)
  (R2 : CFGKATAutomatonBisimulation B C)
  : CFGKATAutomatonBisimulation A C := {|
  cfgkat_relation x z :=
    exists y, cfgkat_relation R1 x y /\
              cfgkat_relation R2 y z;
|}.
Next Obligation.
  intros A B C HtotalB R1 R2 x z a zeta1 zeta3 Hxz Hx Hz.
  destruct Hxz as [y [Hxy Hyz]].
  destruct (HtotalB y a) as [zeta2 Hy].
  pose proof (cfgkat_bisimulation_step R1 x y a zeta1 zeta2 Hxy Hx Hy)
    as H12.
  pose proof (cfgkat_bisimulation_step R2 y z a zeta2 zeta3 Hyz Hy Hz)
    as H23.
  inversion H12; subst;
  inversion H23; subst;
  constructor; eauto.
Qed.

Theorem CFGKATCongruenceTrans_sound :
  forall E F G e f g i j k,
    (e, i) ~[lift E, lift F] (f, j) ->
    (f, j) ~[lift F, lift G] (g, k) ->
    (e, i) ~[lift E, lift G] (g, k).
Proof.
  intros E F G e f g i j k Hleft Hright.
  destruct Hleft as [Rleft HRleft].
  destruct Hright as [Rright HRright].
  unshelve eexists.
  - eapply bisim_trans; eauto.
    apply resolved_lift_total.
  - exists (f, j). intuition.
Qed.

Lemma choice_left_dynamics_iff
  (b : CFGKATTest)
  (e e' : CFGKATExpression)
  (i : IndicatorAssignment)
  (a : Atom)
  :
  eval_test b a i ->
  forall r,
    CFGKATExpressionDynamics (if b then e else e', i) a r <->
    CFGKATExpressionDynamics (e, i) a r.
Proof.
  intros Hb r.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_choice.
  destruct (eval_test_dec b a i); intuition.
Qed.

Lemma choice_right_dynamics_iff
  (b : CFGKATTest)
  (e e' : CFGKATExpression)
  (i : IndicatorAssignment)
  (a : Atom)
  :
  ~ eval_test b a i ->
  forall r,
    CFGKATExpressionDynamics (if b then e else e', i) a r <->
    CFGKATExpressionDynamics (e', i) a r.
Proof.
  intros Hb r.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_choice.
  destruct (eval_test_dec b a i); intuition.
Qed.

Local Lemma resolved_choice_left_iff
  (E : label_environment CFGKATExpression)
  (b : CFGKATTest)
  (e e' : CFGKATExpression)
  (i : IndicatorAssignment)
  (a : Atom)
  :
  eval_test b a i ->
  forall r,
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      (if b then e else e', i) a r <->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      (e, i) a r.
Proof.
  intros Hb r.
  apply resolve_list_same_dynamics.
  now apply choice_left_dynamics_iff.
Qed.

Local Lemma resolved_choice_right_iff
  (E : label_environment CFGKATExpression)
  (b : CFGKATTest)
  (e e' : CFGKATExpression)
  (i : IndicatorAssignment)
  (a : Atom)
  :
  ~ eval_test b a i ->
  forall r,
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      (if b then e else e', i) a r <->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      (e', i) a r.
Proof.
  intros Hb r.
  apply resolve_list_same_dynamics.
  now apply choice_right_dynamics_iff.
Qed.

Lemma lifted_relation_mono
  {X Y : Type}
  (R S : X -> Y -> Prop)
  :
  (forall x y, R x y -> S x y) ->
  forall zeta1 zeta2,
    lifted_relation R zeta1 zeta2 ->
    lifted_relation S zeta1 zeta2.
Proof.
  intros HRS zeta1 zeta2 H.
  inversion H; subst; constructor; eauto.
Qed.

Program Definition automaton_bisimilarity_bisim
  {A B : CFGKATAutomaton}
  : CFGKATAutomatonBisimulation A B := {|
  cfgkat_relation := CFGKATAutomatonBisimilar A B
|}.
Next Obligation.
  intros A B x y a zeta1 zeta2 Hrel Hx Hy.
  destruct Hrel as [R HR].
  eapply lifted_relation_mono.
  + intros u v Huv.
    exists R; eauto.
  + eapply cfgkat_bisimulation_step; eauto.
Qed.

Inductive CFGKATCongruenceGuardedChoice_relation
  (E F : label_environment CFGKATExpression)
  (Hleft Hright: CFGKATAutomatonBisimulation
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift F)))
  :
  CFGKATSyntConfiguration ->
  CFGKATSyntConfiguration ->
  Prop
:=
| CFGKATCongruenceGuardedChoice_combine:
    forall b e1 e2 f1 f2 i,
      cfgkat_relation Hleft (e1, i) (f1, i) ->
      cfgkat_relation Hright (e2, i) (f2, i) ->
      CFGKATCongruenceGuardedChoice_relation
        E F Hleft Hright
        (if b then e1 else e2, i)
        (if b then f1 else f2, i)
| CFGKATCongruenceGuardedChoice_left:
    forall x1 x2,
      cfgkat_relation Hleft x1 x2 ->
      CFGKATCongruenceGuardedChoice_relation
        E F Hleft Hright x1 x2
| CFGKATCongruenceGuardedChoice_right:
    forall x1 x2,
      cfgkat_relation Hright x1 x2 ->
      CFGKATCongruenceGuardedChoice_relation
        E F Hleft Hright x1 x2
.

Program Definition CFGKATCongruenceGuardedChoice_bisim
  (E F : label_environment CFGKATExpression)
  (Hleft Hright: CFGKATAutomatonBisimulation
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift F)))
: CFGKATAutomatonBisimulation
      (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
      (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift F))
:= {|
  cfgkat_relation :=
    CFGKATCongruenceGuardedChoice_relation E F Hleft Hright;
|}.
Next Obligation.
  intros E F Hleft Hright [e i] [f j] a zeta1 zeta2 Hrel He Hf.
  simpl in zeta1, zeta2. dependent destruction Hrel.
  - destruct (eval_test_dec b a j).
    + apply resolved_choice_left_iff in He; eauto.
      apply resolved_choice_left_iff in Hf; eauto.
      eapply lifted_relation_mono with (R := cfgkat_relation Hleft).
      * apply CFGKATCongruenceGuardedChoice_left.
      * eapply cfgkat_bisimulation_step; eauto.
    + apply resolved_choice_right_iff in He; eauto.
      apply resolved_choice_right_iff in Hf; eauto.
      eapply lifted_relation_mono with (R := cfgkat_relation Hright).
      * apply CFGKATCongruenceGuardedChoice_right.
      * eapply cfgkat_bisimulation_step; eauto.
  - eapply lifted_relation_mono with (R := cfgkat_relation Hleft).
    * apply CFGKATCongruenceGuardedChoice_left.
    * eapply cfgkat_bisimulation_step; eauto.
  - eapply lifted_relation_mono with (R := cfgkat_relation Hright).
    * apply CFGKATCongruenceGuardedChoice_right.
    * eapply cfgkat_bisimulation_step; eauto.
Qed.

Theorem CFGKATCongruenceGuardedChoice_sound :
  forall E F e1 e2 f1 f2 b i,
    (e1, i) ~[lift E, lift F] (f1, i) ->
    (e2, i) ~[lift E, lift F] (f2, i) ->
    (if b then e1 else e2, i) ~[lift E, lift F]
    (if b then f1 else f2, i).
Proof.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar.
  intros E F e1 e2 f1 f2 b i Hleft Hright.
  destruct Hleft as [Rleft HRleft].
  destruct Hright as [Rright HRright].
  unshelve eexists.
  - apply CFGKATCongruenceGuardedChoice_bisim.
    + apply Rleft.
    + apply Rright.
  - apply CFGKATCongruenceGuardedChoice_combine; eauto.
Qed.

Theorem CFGKATCongruenceBooleanChoice_sound :
  forall e f b c,
    b =BA c ->
    forall i,
      (if b then e else f, i) ~~
      (if c then e else f, i).
Proof.
  intros e f b c Hba i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite !transition_choice.
  destruct (eval_test_dec b a i).
  - destruct (eval_test_dec c a i); auto.
    contradict n. eapply BA_leq_eval; eauto.
    now rewrite Hba.
  - destruct (eval_test_dec c a i); auto.
    contradict n. eapply BA_leq_eval; eauto.
    now rewrite Hba.
Qed.

Theorem CFGKATCongruenceBooleanAssert_sound :
  forall b c,
    b =BA c ->
    forall i,
      (test b, i) ~~
      (test c, i).
Proof.
  intros b c Hba i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite !transition_assert.
  destruct (eval_test_dec b a i).
  - destruct (eval_test_dec c a i); auto.
    contradict n. eapply BA_leq_eval; eauto.
    now rewrite Hba.
  - destruct (eval_test_dec c a i); auto.
    contradict n. eapply BA_leq_eval; eauto.
    now rewrite Hba.
Qed.

Inductive CFGKATCongruenceSequenceLeftEmpty_relation
  (Hhead: CFGKATAutomatonBisimulation ExprAutEmpty ExprAutEmpty)
  :
  cfgkat_states ExprAutEmpty ->
  cfgkat_states ExprAutEmpty ->
  Prop
:=
| CFGKATCongruenceSequenceLeftEmpty_combine:
    forall e f g i j,
      cfgkat_relation Hhead (e, i) (f, j) ->
      CFGKATCongruenceSequenceLeftEmpty_relation
        Hhead
        (e;; g, i) (f;; g, j)
| CFGKATCongruenceSequenceLeftEmpty_refl:
    forall x,
      CFGKATCongruenceSequenceLeftEmpty_relation
        Hhead x x
.

Program Definition bisimulation_to_direct_bisimulation
  (B: CFGKATAutomatonBisimulation ExprAutEmpty ExprAutEmpty)
: CFGKATDirectBisimulation := {|
  cfgkat_direct_relation := cfgkat_relation B;
|}.
Next Obligation.
  intros.
  eapply cfgkat_bisimulation_step; eauto.
  - now apply resolve_syntactic_empty_identity, transition_output_exact.
  - now apply resolve_syntactic_empty_identity, transition_output_exact.
Qed.

Lemma lifted_relation_transpose_halting
  {X: Type}
  (zeta1 zeta2 : CFGKATAutomatonOutputs X)
  (R : X -> X -> Prop)
:
  cfgkat_halting_output zeta1 ->
  lifted_relation R zeta1 zeta2 ->
  zeta1 = zeta2
.
Proof.
  intros Hhalting Hlift.
  destruct zeta1; try now inversion Hlift.
Qed.

Program Definition CFGKATCongruenceSequenceLeftEmpty_bisim
  (Hhead: CFGKATAutomatonBisimulation ExprAutEmpty ExprAutEmpty)
  : CFGKATAutomatonBisimulation ExprAutEmpty ExprAutEmpty
:= {|
  cfgkat_relation := CFGKATCongruenceSequenceLeftEmpty_relation Hhead;
|}.
Next Obligation.
  intros Hhead [e i] [f j] a zeta1 zeta2 ? ? ?.
  apply resolve_syntactic_empty_identity in H0, H1.
  apply transition_output_exact in H0, H1. subst.
  set (Hhead_direct := bisimulation_to_direct_bisimulation Hhead).
  dependent destruction H.
  - rewrite !transition_sequence.
    destruct (classic (transition_output e0 a i =
                         CFGKATAutomatonReject)); [|
    destruct (classic (cfgkat_halting_output
                        (transition_output e0 a i))) ].
    + eapply (cfgkat_direct_bisimulation_step Hhead_direct) in H.
      rewrite H0 in H. inversion H.
      rewrite H0. constructor.
    + erewrite lifted_relation_transpose_halting
        with (zeta1 := transition_output e0 a i); eauto.
      * apply lifted_relation_refl. constructor.
      * apply (cfgkat_direct_bisimulation_step Hhead_direct); eauto.
    + destruct (transition_output e0 a i) eqn:?;
        simpl in H1; try intuition. clear H0 H1.
      eapply (cfgkat_direct_bisimulation_step Hhead_direct)
        with (a := a) in H.
      rewrite Heqc in H. dependent destruction H.
      rewrite <- x. destruct s, y. simpl.
      now repeat constructor.
  - apply lifted_relation_refl. constructor.
Qed.

Theorem CFGKATCongruenceSequenceLeftEmpty_sound :
  forall e f g i j,
    (e, i) ~~ (f, j) ->
    (e ;; g, i) ~~ (f ;; g, j).
Proof.
  intros e f g i j [R HR]. unshelve eexists.
  - now apply CFGKATCongruenceSequenceLeftEmpty_bisim.
  - now constructor.
Qed.

Inductive CFGKATCongruenceLoopSeqLeftEmpty_relation
  (Hhead: CFGKATAutomatonBisimulation ExprAutEmpty ExprAutEmpty)
  :
  cfgkat_states ExprAutEmpty ->
  cfgkat_states ExprAutEmpty ->
  Prop
:=
| CFGKATCongruenceLoopSeqLeftEmpty_combine:
    forall e f g i j,
      cfgkat_relation Hhead (e, i) (f, j) ->
      CFGKATCongruenceLoopSeqLeftEmpty_relation
        Hhead
        (e |> g, i) (f |> g, j)
| CFGKATCongruenceLoopSeqLeftEmpty_refl:
    forall x,
      CFGKATCongruenceLoopSeqLeftEmpty_relation
        Hhead x x
.

Program Definition CFGKATCongruenceLoopSeqLeftEmpty_bisim
  (Hhead: CFGKATAutomatonBisimulation ExprAutEmpty ExprAutEmpty)
  : CFGKATAutomatonBisimulation ExprAutEmpty ExprAutEmpty := {|
  cfgkat_relation := CFGKATCongruenceLoopSeqLeftEmpty_relation Hhead;
|}.
Next Obligation.
  intros Hhead [e i] [f j] a zeta1 zeta2 ? ? ?.
  apply resolve_syntactic_empty_identity in H0, H1.
  apply transition_output_exact in H0, H1. subst.
  set (Hhead_direct := bisimulation_to_direct_bisimulation Hhead).
  dependent destruction H.
  - rewrite !transition_loopseq.
    destruct (classic (transition_output e0 a i =
                         CFGKATAutomatonReject)); [|
    destruct (classic (cfgkat_halting_output
                        (transition_output e0 a i))) ].
    + eapply (cfgkat_direct_bisimulation_step Hhead_direct) in H.
      rewrite H0 in H. inversion H.
      rewrite H0. constructor.
    + erewrite lifted_relation_transpose_halting
        with (zeta1 := transition_output e0 a i); eauto.
      * apply lifted_relation_refl. constructor.
      * apply (cfgkat_direct_bisimulation_step Hhead_direct); eauto.
    + destruct (transition_output e0 a i) eqn:?;
        simpl in H1; try intuition. clear H0 H1.
      eapply (cfgkat_direct_bisimulation_step Hhead_direct)
        with (a := a) in H.
      rewrite Heqc in H. dependent destruction H.
      rewrite <- x. destruct s, y. simpl.
      now repeat constructor.
  - apply lifted_relation_refl. constructor.
Qed.

Theorem CFGKATCongruenceLoopSeqLeftEmpty_sound :
  forall e f g i,
    (e, i) ~~ (f, i) ->
    (e |> g, i) ~~ (f |> g, i).
Proof.
  intros e f g i [R HR]. unshelve eexists.
  - now apply CFGKATCongruenceLoopSeqLeftEmpty_bisim.
  - now constructor.
Qed.

Inductive CFGKATCongruenceBooleanLoop_relation
  : CFGKATSyntConfiguration ->
    CFGKATSyntConfiguration ->
    Prop :=
| CFGKATCongruenceBooleanLoop_loop :
    forall e b c i,
      b =BA c ->
      CFGKATCongruenceBooleanLoop_relation
        (while b do e, i)
        (while c do e, i)
| CFGKATCongruenceBooleanLoop_loopseq :
    forall h e b c i,
      b =BA c ->
      CFGKATCongruenceBooleanLoop_relation
        (h |> while b do e, i)
        (h |> while c do e, i)
.

Lemma CFGKATExpressionDynamicsLoopHalt
  (a : Atom)
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (i : IndicatorAssignment)
  (zeta : CFGKATAutomatonOutputs (CFGKATExpression * IndicatorAssignment))
:
  CFGKATExpressionDynamics (e, i) a zeta ->
  ~ cfgkat_continuing_output zeta ->
  cfgkat_halting_output zeta ->
  eval_test b a i ->
  CFGKATExpressionDynamics (while b do e, i) a (cfgkat_floor zeta)
.
Proof.
  intros.
  apply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
  apply CFGKATExpressionDynamicsLoopSeqHalt; eauto.
Qed.

Program Definition CFGKATCongruenceBooleanLoop_bisim
  : @CFGKATStrongBisimulation
      CFGKATExpressionAutomaton
      CFGKATExpressionAutomaton
      [empty_syntactic_context]
      [empty_syntactic_context] := {|
  cfgkat_strong_relation := CFGKATCongruenceBooleanLoop_relation;
|}.
Next Obligation.
  intros. dependent destruction H.
  - destruct (eval_test_dec b a i);
    destruct (eval_test_dec c a i);
      try now (contradict n; eapply BA_leq_eval; eauto; now rewrite H).
    destruct (cfgkat_expression_dynamics_total (e, i) a) as [zeta Hzeta].
    destruct (classic (cfgkat_continuing_output zeta)); [|
    destruct (classic (cfgkat_halting_output zeta)) ].
    + destruct zeta; try now (simpl in H0; intuition).
      * eapply CFGKATStrongStepSilent; constructor; eauto;
        left; dependent destruction Hzeta; eauto.
      * eapply CFGKATStrongStepSilent; constructor; eauto;
        right; dependent destruction Hzeta; eauto.
    + eapply CFGKATStrongStepHalt with (zeta := cfgkat_floor zeta); eauto.
      * destruct zeta; eauto.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopHalt; eauto.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopHalt; eauto.
    + destruct zeta; try now (simpl in *; intuition).
      clear H0 H1. destruct s as [e' i'].
      eapply CFGKATStrongStepNext.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
        apply CFGKATExpressionDynamicsLoopSeqNext; eauto.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
        apply CFGKATExpressionDynamicsLoopSeqNext; eauto.
      * now constructor.
    + eapply CFGKATStrongStepHalt; swap 1 3.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopGuardFalse; eauto.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopGuardFalse; eauto.
      * now simpl.
  - destruct (cfgkat_expression_dynamics_total (h, i) a) as [zeta Hzeta].
    destruct (classic (cfgkat_continuing_output zeta)); [|
    destruct (classic (cfgkat_halting_output zeta)) ].
    + destruct zeta; try now (simpl in H0; intuition).
      * eapply CFGKATStrongStepSilent; constructor; eauto;
        left; dependent destruction Hzeta; eauto.
      * eapply CFGKATStrongStepSilent; constructor; eauto;
        right; dependent destruction Hzeta; eauto.
    + eapply CFGKATStrongStepHalt with (zeta := cfgkat_floor zeta); eauto.
      * destruct zeta; eauto.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopSeqHalt; eauto.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopSeqHalt; eauto.
    + destruct zeta; try now (simpl in *; intuition).
      clear H0 H1. destruct s as [h' i'].
      eapply CFGKATStrongStepNext.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopSeqNext; eauto.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopSeqNext; eauto.
      * now constructor.
Qed.

Theorem CFGKATCongruenceBooleanLoop_sound :
  forall e b c i,
    b =BA c ->
    (while b do e, i) ~~ (while c do e, i).
Proof.
  intros. unshelve eexists.
  - apply (strong_bisim_to_bisim [empty_syntactic_context]
                                 [empty_syntactic_context]).
    apply CFGKATCongruenceBooleanLoop_bisim.
  - now constructor.
Qed.

Inductive CFGKATCongruenceSequenceRight_relation
  (E F : label_environment CFGKATExpression)
  (Hleft Hright: CFGKATAutomatonBisimulation
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift F)))
:
  CFGKATSyntConfiguration ->
  CFGKATSyntConfiguration ->
  Prop
:=
| CFGKATCongruenceSequenceRight_combine:
    forall e f g i,
      (forall j, cfgkat_relation Hright (e, j) (f, j)) ->
      cfgkat_relation Hleft (g, i) (g, i) ->
      CFGKATCongruenceSequenceRight_relation
        E F Hleft Hright (g ;; e, i) (g ;; f, i)
| CFGKATCongruenceSequenceRight_left:
    forall x1 x2,
      cfgkat_relation Hleft x1 x2 ->
      CFGKATCongruenceSequenceRight_relation
        E F Hleft Hright x1 x2
| CFGKATCongruenceSequenceRight_right:
    forall x1 x2,
      cfgkat_relation Hright x1 x2 ->
      CFGKATCongruenceSequenceRight_relation
        E F Hleft Hright x1 x2.

Lemma sequence_accept_iff:
  forall g h i i' a,
    CFGKATExpressionDynamics (g, i) a (CFGKATAutomatonAccept i') ->
    forall r,
      CFGKATExpressionDynamics (g ;; h, i) a r <->
      CFGKATExpressionDynamics (h, i') a r.
Proof.
  intros g h i i' a Hg r. split.
  - intro Hseq.
    destruct (cfgkat_expression_dynamics_total (h, i') a) as [zeta Hzeta].
    rewrite cfgkat_expression_dynamics_functional; eauto.
    eapply CFGKATExpressionDynamicsSequenceSkip; eauto.
  - eapply CFGKATExpressionDynamicsSequenceSkip; eauto.
Qed.

Local Lemma sequence_resolved_accept_iff
  (E : label_environment CFGKATExpression)
  (g h : CFGKATExpression)
  (i i' : IndicatorAssignment)
  (a : Atom)
  :
  CFGKATExpressionDynamics (g, i) a (CFGKATAutomatonAccept i') ->
  forall r,
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E]) (g ;; h, i) a r <->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E]) (h, i') a r.
Proof.
  intros Haccept r. apply resolve_list_same_dynamics.
  intro r'. now apply sequence_accept_iff.
Qed.

Lemma sequence_jump_iff :
  forall g h h' i i' l a,
    CFGKATExpressionDynamics (g, i) a (CFGKATAutomatonJump l i') ->
    forall r,
      CFGKATExpressionDynamics (g ;; h, i) a r <->
      CFGKATExpressionDynamics (g ;; h', i) a r.
Proof.
  intros g h h' i i' l a Hg r. intuition.
  - destruct (cfgkat_expression_dynamics_total (h, i') a) as [zeta Hzeta].
    eapply CFGKATExpressionDynamicsSequenceJump with (e2 := h) in Hg as Hg'.
    rewrite cfgkat_expression_dynamics_functional; eauto.
    eapply CFGKATExpressionDynamicsSequenceJump; eauto.
  - destruct (cfgkat_expression_dynamics_total (h', i') a) as [zeta Hzeta].
    eapply CFGKATExpressionDynamicsSequenceJump with (e2 := h') in Hg as Hg'.
    rewrite cfgkat_expression_dynamics_functional; eauto.
    eapply CFGKATExpressionDynamicsSequenceJump; eauto.
Qed.

Local Lemma sequence_resolved_jump_iff
  (E : label_environment CFGKATExpression)
  (g h : CFGKATExpression)
  (i i' : IndicatorAssignment)
  (l : Label)
  (a : Atom)
  :
  CFGKATExpressionDynamics (g, i) a (CFGKATAutomatonJump l i') ->
  forall r,
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E]) (g ;; h, i) a r <->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E]) (g, i) a r.
Proof.
  intros Hjump r. apply resolve_list_same_dynamics. intro r'.
  rewrite sequence_jump_iff with (h' := test 1); eauto.
  intuition.
  - eapply CFGKATExpressionDynamicsSequenceJump in Hjump as Hjump'; eauto.
    erewrite cfgkat_expression_dynamics_functional; eauto.
  - erewrite cfgkat_expression_dynamics_functional
      with (zeta2 := CFGKATAutomatonJump l i'); eauto.
    now apply CFGKATExpressionDynamicsSequenceJump.
Qed.

Definition cfgkat_lifts_easy
  (zeta: CFGKATAutomatonOutputs CFGKATSyntConfiguration) :=
  match zeta with
  | CFGKATAutomatonReject => True
  | CFGKATAutomatonAccept _ => True
  | CFGKATAutomatonBreak _ => True
  | CFGKATAutomatonContinue _ => True
  | CFGKATAutomatonReturn => True
  | CFGKATAutomatonNext _ _ => True
  | _ => False
  end.

Lemma Hlift_easy (ys : list (environment CFGKATSyntConfiguration)):
  forall zeta,
  cfgkat_lifts_easy zeta ->
  forall aut x a,
    cfgkat_synt_transitions aut x a zeta ->
    cfgkat_transitions (resolve_list aut ys) x a zeta.
Proof.
  intros zeta Hzeta. destruct zeta; try (now simpl in *); intros.
  - now apply Hlift_reject.
  - now apply Hlift_accept.
  - now apply Hlift_break.
  - now apply Hlift_continue.
  - now apply Hlift_return.
  - now apply Hlift_next.
Qed.

Definition cfgkat_halts_sequence
  (zeta: CFGKATAutomatonOutputs CFGKATSyntConfiguration) :=
  match zeta with
  | CFGKATAutomatonReject => True
  | CFGKATAutomatonBreak _ => True
  | CFGKATAutomatonContinue _ => True
  | CFGKATAutomatonReturn => True
  | _ => False
  end.

Lemma CFGKATExpressionDynamicsSequenceHalt :
  forall a i e1 e2 zeta,
    cfgkat_halts_sequence zeta ->
    CFGKATExpressionDynamics (e1, i) a zeta ->
    CFGKATExpressionDynamics (e1 ;; e2, i) a zeta.
Proof.
  intros a i e1 e2 zeta Hzeta Hhead.
  destruct zeta; try now (simpl in Hzeta; intuition).
  - now apply CFGKATExpressionDynamicsSequenceReject.
  - now apply CFGKATExpressionDynamicsSequenceBreak.
  - now apply CFGKATExpressionDynamicsSequenceContinue.
  - now apply CFGKATExpressionDynamicsSequenceReturn.
Qed.

Lemma CFGKATCongruenceSequenceRight_cases
  (zeta: CFGKATAutomatonOutputs CFGKATSyntConfiguration):
  (exists i', zeta = CFGKATAutomatonAccept i') \/
  (exists l i', zeta = CFGKATAutomatonJump l i') \/
  (exists p s, zeta = CFGKATAutomatonNext p s) \/
  cfgkat_halts_sequence zeta.
Proof.
  destruct zeta; intuition repeat eexists.
Qed.

Program Definition CFGKATCongruenceSequenceRight_bisim
  (E F : label_environment CFGKATExpression)
  (Hleft Hright: CFGKATAutomatonBisimulation
    (resolve_list CFGKATExpressionAutomaton [lift E])
    (resolve_list CFGKATExpressionAutomaton [lift F]))
  : CFGKATAutomatonBisimulation
    (resolve_list CFGKATExpressionAutomaton [lift E])
    (resolve_list CFGKATExpressionAutomaton [lift F]) := {|
  cfgkat_relation := CFGKATCongruenceSequenceRight_relation E F Hleft Hright;
|}.
Next Obligation.
  intros. dependent destruction H.
  - destruct (cfgkat_expression_dynamics_total (g, i) a) as [zeta Hzeta].
    destruct (CFGKATCongruenceSequenceRight_cases zeta) as [? | [? | [? | ?]]].
    + destruct H3 as [i' ?]; subst.
      eapply lifted_relation_mono.
      * apply CFGKATCongruenceSequenceRight_right.
      * rewrite sequence_resolved_accept_iff in H1, H2; eauto.
        eapply (cfgkat_bisimulation_step Hright); eauto.
        apply H.
    + destruct H3 as [l [i' ?]]; subst.
      eapply lifted_relation_mono.
      * apply CFGKATCongruenceSequenceRight_left.
      * eapply (cfgkat_bisimulation_step Hleft); eauto;
        rewrite <- sequence_resolved_jump_iff; eauto.
    + destruct H3 as [p [[g' i'] ?]]; subst.
      erewrite (resolved_lift_functional F (g;; f, i))
        with (zeta1 := zeta2)
             (zeta2 := CFGKATAutomatonNext p (g';; f, i')); [
      erewrite (resolved_lift_functional E (g;; e, i))
        with (zeta1 := zeta1)
             (zeta2 := CFGKATAutomatonNext p (g';; e, i')) | |]; eauto.
      * constructor.
        apply CFGKATCongruenceSequenceRight_combine; auto.
        apply Hlift_next with (aut := CFGKATSyntacticExpressionAutomaton)
                              (ys := [lift E]) in Hzeta as Hzeta1.
        eapply (cfgkat_bisimulation_step Hleft)
          with (zeta2 := CFGKATAutomatonNext p (g', i')) in Hzeta1; eauto.
        -- now dependent destruction Hzeta1.
        -- now apply Hlift_next with (ys := [lift F]).
      * apply Hlift_next with (ys := [lift E]).
        now apply CFGKATExpressionDynamicsSequenceNext.
      * apply Hlift_next with (ys := [lift F]).
        now apply CFGKATExpressionDynamicsSequenceNext.
    + erewrite (resolved_lift_functional F (g;; f, i))
        with (zeta1 := zeta2) (zeta2 := zeta); [
      erewrite (resolved_lift_functional E (g;; e, i))
        with (zeta1 := zeta1) (zeta2 := zeta) | |]; eauto.
      * destruct zeta; try now simpl in H3; constructor.
      * apply Hlift_easy with (ys := [lift E]); try now simpl.
        -- now destruct zeta.
        -- now apply CFGKATExpressionDynamicsSequenceHalt.
      * apply Hlift_easy with (ys := [lift F]); try now simpl.
        -- now destruct zeta.
        -- now apply CFGKATExpressionDynamicsSequenceHalt.
  - eapply lifted_relation_mono.
    + apply CFGKATCongruenceSequenceRight_left.
    + eapply (cfgkat_bisimulation_step Hleft); eauto.
  - eapply lifted_relation_mono.
    + apply CFGKATCongruenceSequenceRight_right.
    + eapply (cfgkat_bisimulation_step Hright); eauto.
Qed.

Program Definition CFGKATBisimilarity
  {aut1 aut2: CFGKATAutomaton}
: CFGKATAutomatonBisimulation aut1 aut2
:= {| cfgkat_relation x y := exists B, cfgkat_relation B x y |}.
Next Obligation.
  intros. simpl in H. destruct H as [B HB].
  eapply lifted_relation_mono with (R := cfgkat_relation B).
  - intros. now exists B.
  - eapply (cfgkat_bisimulation_step B); eauto.
Qed.

Theorem CFGKATCongruenceSequenceRight_sound :
  forall E F e f g i,
    (forall i, (e, i) ~[lift E, lift F] (f, i)) ->
    (g, i) ~[lift E, lift F] (g, i) ->
    (g ;; e, i) ~[lift E, lift F] (g ;; f, i).
Proof.
  intros E F e f g i Htail Hprefix.
  unshelve eexists.
  - apply CFGKATCongruenceSequenceRight_bisim.
    + apply CFGKATBisimilarity.
    + apply CFGKATBisimilarity.
  - apply CFGKATCongruenceSequenceRight_combine.
    + intros. destruct (Htail j) as [B HB].
      now exists B.
    + apply Hprefix.
Qed.

Lemma sequence_same_forced_output :
  forall g h h' i a forced,
    (forall tail,
      CFGKATExpressionDynamics (g ;; tail, i) a forced) ->
    forall r,
      CFGKATExpressionDynamics (g ;; h, i) a r <->
      CFGKATExpressionDynamics (g ;; h', i) a r.
Proof.
  intros g h h' i a forced Hforced r.
  split; intro Hseq.
  - pose proof (Hforced h) as Hshort.
    erewrite cfgkat_dynamics_functional; eauto.
  - pose proof (Hforced h') as Hshort.
    erewrite cfgkat_dynamics_functional; eauto.
Qed.

Inductive CFGKATCongruenceLoopSeqRight_relation
  (E F : label_environment CFGKATExpression)
  (Hleft Hright: CFGKATAutomatonBisimulation
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift F)))
:
  CFGKATSyntConfiguration ->
  CFGKATSyntConfiguration ->
  Prop :=
| CFGKATCongruenceLoopSeqRight_combine:
    forall e f g i,
      (forall j, cfgkat_relation Hright (e, j) (f, j)) ->
      cfgkat_relation Hleft (g, i) (g, i) ->
      CFGKATCongruenceLoopSeqRight_relation
        E F Hleft Hright (g |> e, i) (g |> f, i)
| CFGKATCongruenceLoopSeqRight_left:
    forall x1 x2,
      cfgkat_relation Hleft x1 x2 ->
      CFGKATCongruenceLoopSeqRight_relation
        E F Hleft Hright x1 x2
| CFGKATCongruenceLoopSeqRight_right:
    forall x1 x2,
      cfgkat_relation Hright x1 x2 ->
      CFGKATCongruenceLoopSeqRight_relation
        E F Hleft Hright x1 x2
.

Definition cfgkat_halts_loopseq
  (zeta: CFGKATAutomatonOutputs CFGKATSyntConfiguration) :=
  match zeta with
  | CFGKATAutomatonReject => True
  | CFGKATAutomatonBreak _ => True
  | CFGKATAutomatonReturn => True
  | _ => False
  end.

Lemma CFGKATCongruenceLoopSeqRight_cases
  (zeta: CFGKATAutomatonOutputs CFGKATSyntConfiguration):
  cfgkat_continuing_output zeta \/
  (exists l i', zeta = CFGKATAutomatonJump l i') \/
  (exists p s, zeta = CFGKATAutomatonNext p s) \/
  cfgkat_halts_loopseq zeta.
Proof.
  destruct zeta; intuition repeat eexists.
Qed.

Local Lemma loopseq_resolved_accept_iff
  (E : label_environment CFGKATExpression)
  (g h : CFGKATExpression)
  (i i' : IndicatorAssignment)
  (a : Atom)
  :
  CFGKATExpressionDynamics (g, i) a (CFGKATAutomatonAccept i') ->
  forall r,
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E]) (g |> h, i) a r <->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E]) (h, i') a r.
Proof.
  intros r. apply resolve_list_same_dynamics.
  intro r'. now apply loopseq_accept_tail_dynamics.
Qed.

Local Lemma loopseq_resolved_continue_iff
  (E : label_environment CFGKATExpression)
  (g h : CFGKATExpression)
  (i i' : IndicatorAssignment)
  (a : Atom)
  :
  CFGKATExpressionDynamics (g, i) a (CFGKATAutomatonContinue i') ->
  forall r,
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E]) (g |> h, i) a r <->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E]) (h, i') a r.
Proof.
  intros r. apply resolve_list_same_dynamics.
  intro r'. now apply loopseq_continue_tail_dynamics.
Qed.

Lemma loopseq_jump_iff :
  forall g h h' i i' l a,
    CFGKATExpressionDynamics (g, i) a (CFGKATAutomatonJump l i') ->
    forall r,
      CFGKATExpressionDynamics (g |> h, i) a r <->
      CFGKATExpressionDynamics (g |> h', i) a r.
Proof.
  intros g h h' i i' l a Hg r.
  split; intro Hloop.
  - eapply CFGKATExpressionDynamicsLoopSeqJump in Hg as Hg'.
    erewrite cfgkat_dynamics_functional; eauto.
    now apply CFGKATExpressionDynamicsLoopSeqJump.
  - eapply CFGKATExpressionDynamicsLoopSeqJump in Hg as Hg'.
    erewrite cfgkat_dynamics_functional; eauto.
    now eapply CFGKATExpressionDynamicsLoopSeqJump.
Qed.

Local Lemma loopseq_resolved_jump_iff
  (E : label_environment CFGKATExpression)
  (g h : CFGKATExpression)
  (i i' : IndicatorAssignment)
  (l : Label)
  (a : Atom)
  :
  CFGKATExpressionDynamics (g, i) a (CFGKATAutomatonJump l i') ->
  forall r,
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E]) (g |> h, i) a r <->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E]) (g, i) a r.
Proof.
  intros Hjump r. apply resolve_list_same_dynamics. intro r'.
  rewrite loopseq_jump_iff with (h' := test 1); eauto.
  intuition.
  - eapply CFGKATExpressionDynamicsLoopSeqJump in Hjump as Hjump'.
    erewrite cfgkat_expression_dynamics_functional; eauto.
  - erewrite cfgkat_expression_dynamics_functional
      with (zeta2 := CFGKATAutomatonJump l i'); eauto.
    now apply CFGKATExpressionDynamicsLoopSeqJump.
Qed.

Program Definition CFGKATCongruenceLoopSeqRight_bisim
  (E F : label_environment CFGKATExpression)
  (Hleft Hright: CFGKATAutomatonBisimulation
    (resolve_list CFGKATExpressionAutomaton [lift E])
    (resolve_list CFGKATExpressionAutomaton [lift F]))
  : CFGKATAutomatonBisimulation
    (resolve_list CFGKATExpressionAutomaton [lift E])
    (resolve_list CFGKATExpressionAutomaton [lift F]) := {|
  cfgkat_relation := CFGKATCongruenceLoopSeqRight_relation E F Hleft Hright;
|}.
Next Obligation.
  intros.
  dependent destruction H.
  - destruct (CFGKATExpressionDynamics_total (g, i) a) as [zeta Hzeta].
    destruct (CFGKATCongruenceLoopSeqRight_cases zeta) as [? | [? | [? | ?]]].
    + eapply lifted_relation_mono.
      * apply CFGKATCongruenceLoopSeqRight_right.
      * destruct zeta; try now simpl in *; intuition.
        -- rewrite loopseq_resolved_accept_iff in H1, H2; eauto.
           now eapply (cfgkat_bisimulation_step Hright); eauto.
        -- rewrite loopseq_resolved_continue_iff in H1, H2; eauto.
           now eapply (cfgkat_bisimulation_step Hright); eauto.
    + destruct H3 as [l [i' ?]]; subst.
      eapply lifted_relation_mono.
      * apply CFGKATCongruenceLoopSeqRight_left.
      * eapply (cfgkat_bisimulation_step Hleft); eauto;
        rewrite <- loopseq_resolved_jump_iff; eauto.
    + destruct H3 as [p [[g' i'] ?]]; subst.
      erewrite (resolved_lift_functional F (g |> f, i))
        with (zeta1 := zeta2)
             (zeta2 := CFGKATAutomatonNext p (g' |> f, i')); [
      erewrite (resolved_lift_functional E (g |> e, i))
        with (zeta1 := zeta1)
             (zeta2 := CFGKATAutomatonNext p (g' |> e, i')) | |]; eauto.
      * constructor.
        apply CFGKATCongruenceLoopSeqRight_combine; auto.
        apply Hlift_next with (aut := CFGKATSyntacticExpressionAutomaton)
                              (ys := [lift E]) in Hzeta as Hzeta1.
        eapply (cfgkat_bisimulation_step Hleft)
          with (zeta2 := CFGKATAutomatonNext p (g', i')) in Hzeta1; eauto.
        -- now dependent destruction Hzeta1.
        -- now apply Hlift_next with (ys := [lift F]).
      * apply Hlift_next with (ys := [lift E]).
        now apply CFGKATExpressionDynamicsLoopSeqNext.
      * apply Hlift_next with (ys := [lift F]).
        now apply CFGKATExpressionDynamicsLoopSeqNext.
    + erewrite (resolved_lift_functional F (g |> f, i))
        with (zeta1 := zeta2) (zeta2 := cfgkat_floor zeta); [
      erewrite (resolved_lift_functional E (g |> e, i))
        with (zeta1 := zeta1) (zeta2 := cfgkat_floor zeta) | |]; eauto.
      * destruct zeta; try now simpl in H3; constructor.
      * apply Hlift_easy with (ys := [lift E]); try now simpl.
        -- now destruct zeta.
        -- apply CFGKATExpressionDynamicsLoopSeqHalt; now destruct zeta.
      * apply Hlift_easy with (ys := [lift F]); try now simpl.
        -- now destruct zeta.
        -- apply CFGKATExpressionDynamicsLoopSeqHalt; now destruct zeta.
  - eapply lifted_relation_mono.
    + apply CFGKATCongruenceLoopSeqRight_left.
    + eapply cfgkat_bisimulation_step; eauto.
  - eapply lifted_relation_mono.
    + apply CFGKATCongruenceLoopSeqRight_right.
    + eapply cfgkat_bisimulation_step; eauto.
Qed.

Theorem CFGKATCongruenceLoopSeqRight_sound :
  forall E F e f g i,
    (forall i, (e, i) ~[lift E, lift F] (f, i)) ->
    (g, i) ~[lift E, lift F] (g, i) ->
    (g |> e, i) ~[lift E, lift F] (g |> f, i).
Proof.
  intros E F e f g i Htail Hprefix.
  unshelve eexists.
  - apply CFGKATCongruenceLoopSeqRight_bisim.
    + apply CFGKATBisimilarity.
    + apply CFGKATBisimilarity.
  - apply CFGKATCongruenceLoopSeqRight_combine.
    + intros. destruct (Htail j) as [B HB].
      now exists B.
    + apply Hprefix.
Qed.

Lemma loopseq_same_forced_output :
  forall g h h' i a forced,
    (forall tail,
      CFGKATExpressionDynamics (g |> tail, i) a forced) ->
    forall r,
      CFGKATExpressionDynamics (g |> h, i) a r <->
      CFGKATExpressionDynamics (g |> h', i) a r.
Proof.
  intros g h h' i a forced Hforced r.
  split; intro Hloop.
  - pose proof (Hforced h) as Hshort.
    pose proof (cfgkat_dynamics_functional (g |> h) i a r forced
      Hloop Hshort) as Heq.
    subst r.
    apply Hforced.
  - pose proof (Hforced h') as Hshort.
    pose proof (cfgkat_dynamics_functional (g |> h') i a r forced
      Hloop Hshort) as Heq.
    subst r.
    apply Hforced.
Qed.

Inductive CFGKATCongruenceLoopBodyEmpty_relation
  (Hbody: CFGKATAutomatonBisimulation ExprAutEmpty ExprAutEmpty)
  :
  cfgkat_states ExprAutEmpty ->
  cfgkat_states ExprAutEmpty ->
  Prop
:=
| CFGKATCongruenceLoopBodyEmpty_combine:
    forall b e f i,
      (forall j, cfgkat_relation Hbody (e, j) (f, j)) ->
      CFGKATCongruenceLoopBodyEmpty_relation
        Hbody (while b do e, i) (while b do f, i)
| CFGKATCongruenceLoopBodyEmpty_refl:
    forall b e f g h i j,
      (forall k, cfgkat_relation Hbody (e, k) (f, k)) ->
      cfgkat_relation Hbody (g, i) (h, j) ->
      CFGKATCongruenceLoopBodyEmpty_relation
        Hbody (g |> while b do e, i) (h |> while b do f, j)
.

Local Lemma bisimulation_transpose_halting
  {aut: CFGKATAutomaton}
  (zeta1 zeta2 : CFGKATAutomatonOutputs (cfgkat_states aut))
  (B : CFGKATAutomatonBisimulation aut aut)
  (x1 x2: cfgkat_states aut)
  (a: Atom)
:
  cfgkat_transitions aut x1 a zeta1 ->
  cfgkat_transitions aut x2 a zeta2 ->
  cfgkat_relation B x1 x2 ->
  cfgkat_halting_output zeta1 ->
  zeta1 = zeta2
.
Proof.
  intros Hleft Hright Hrel Hhalting.
  eapply lifted_relation_transpose_halting; eauto.
  eapply (cfgkat_bisimulation_step B); eauto.
Qed.

Local Lemma bisimulation_transpose_step
  {aut1 aut2: CFGKATAutomaton}
  (zeta : CFGKATAutomatonOutputs (cfgkat_states aut2))
  (B : CFGKATAutomatonBisimulation aut1 aut2)
  (x1 x1': cfgkat_states aut1)
  (x2: cfgkat_states aut2)
  (a: Atom)
  (p: Action)
:
  cfgkat_transitions aut1 x1 a (CFGKATAutomatonNext p x1') ->
  cfgkat_transitions aut2 x2 a zeta ->
  cfgkat_relation B x1 x2 ->
  exists x2', zeta = CFGKATAutomatonNext p x2' /\
              cfgkat_relation B x1' x2'
.
Proof.
  intros Hleft Hright Hrel.
  eapply (cfgkat_bisimulation_step B) in Hrel; eauto.
  dependent destruction Hrel.
  eexists; intuition.
Qed.

Program Definition CFGKATCongruenceLoopBodyEmpty_bisim
  (Hbody: CFGKATAutomatonBisimulation ExprAutEmpty ExprAutEmpty)
  : @CFGKATStrongBisimulation
      CFGKATExpressionAutomaton
      CFGKATExpressionAutomaton
      [empty_syntactic_context]
      [empty_syntactic_context] := {|
  cfgkat_strong_relation := CFGKATCongruenceLoopBodyEmpty_relation Hbody;
|}.
Next Obligation.
  intros.
  set (Hbody_direct := bisimulation_to_direct_bisimulation Hbody).
  dependent destruction H.
  - destruct (eval_test_dec b a i).
    + destruct (cfgkat_expression_dynamics_total (e, i) a) as [zeta1 Hzeta1].
      destruct (cfgkat_expression_dynamics_total (f, i) a) as [zeta2 Hzeta2].
      pose proof (H i) as Hi.
      destruct (classic (cfgkat_continuing_output zeta1)); [|
      destruct (classic (cfgkat_halting_output zeta1)) ].
      * eapply bisimulation_transpose_halting
          with (zeta1 := zeta1) (zeta2 := zeta2) in Hi; subst;
          try apply resolve_syntactic_empty_identity; eauto.
        -- destruct zeta2; try (now simpl in *);
           eapply CFGKATStrongStepSilent; constructor; eauto;
           unfold cfgkat_loop_silent_body;
           dependent destruction Hzeta1;
           dependent destruction Hzeta2; eauto.
        -- destruct zeta1;  try now simpl in *.
      * eapply bisimulation_transpose_halting
          with (zeta1 := zeta1) (zeta2 := zeta2) in Hi; subst;
          try apply resolve_syntactic_empty_identity; eauto.
        eapply CFGKATStrongStepHalt
          with (zeta := cfgkat_floor zeta2); eauto.
        -- destruct zeta2; now simpl in *.
        -- simpl. rewrite resolve_syntactic_empty_identity.
           apply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
           apply CFGKATExpressionDynamicsLoopSeqHalt; eauto.
        -- simpl. rewrite resolve_syntactic_empty_identity.
           apply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
           apply CFGKATExpressionDynamicsLoopSeqHalt; eauto.
      * destruct zeta1; try now simpl in *.
        destruct s as (e', i'). clear H0 H1.
        eapply bisimulation_transpose_step
          with (zeta := zeta2) (p := p) (x1' := (e', i'))
          in Hi as [(f', i'') [? ?]]; subst;
          try apply resolve_syntactic_empty_identity; eauto.
        eapply CFGKATStrongStepNext.
        -- apply resolve_syntactic_empty_identity.
           apply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
           apply CFGKATExpressionDynamicsLoopSeqNext; eauto.
        -- apply resolve_syntactic_empty_identity.
           apply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
           apply CFGKATExpressionDynamicsLoopSeqNext; eauto.
        -- now constructor.
    + eapply CFGKATStrongStepHalt
        with (zeta := CFGKATAutomatonAccept i); eauto.
      * now simpl.
      * simpl. rewrite resolve_syntactic_empty_identity.
        now apply CFGKATExpressionDynamicsLoopGuardFalse.
      * simpl. rewrite resolve_syntactic_empty_identity.
        now apply CFGKATExpressionDynamicsLoopGuardFalse.
  - destruct (cfgkat_expression_dynamics_total (g, i) a) as [zeta1 Hzeta1].
    destruct (cfgkat_expression_dynamics_total (h, j) a) as [zeta2 Hzeta2].
    destruct (classic (cfgkat_continuing_output zeta1)); [|
    destruct (classic (cfgkat_halting_output zeta1)) ].
    + eapply bisimulation_transpose_halting
        with (zeta1 := zeta1) (zeta2 := zeta2) in H0; subst;
        try apply resolve_syntactic_empty_identity; eauto;
        try now (destruct zeta1; simpl in *).
      destruct zeta2; try (now simpl in *); clear H1.
      * destruct (eval_test_dec b a i0).
        -- dependent destruction Hzeta1.
           dependent destruction Hzeta2.
           eapply CFGKATStrongStepSilent; (try now constructor);
           apply CFGKATSilentLoopSeq; left; eauto.
        -- eapply CFGKATStrongStepHalt with
             (zeta := CFGKATAutomatonAccept i0); simpl; eauto;
           rewrite resolve_syntactic_empty_identity;
           eapply CFGKATExpressionDynamicsLoopSeqSkip; eauto;
           apply CFGKATExpressionDynamicsLoopGuardFalse; eauto.
      * destruct (eval_test_dec b a i0).
        -- dependent destruction Hzeta1.
           dependent destruction Hzeta2.
           eapply CFGKATStrongStepSilent; (try now constructor);
           apply CFGKATSilentLoopSeq; right; eauto.
        -- eapply CFGKATStrongStepHalt with
             (zeta := CFGKATAutomatonAccept i0); simpl; eauto;
           rewrite resolve_syntactic_empty_identity;
           eapply CFGKATExpressionDynamicsLoopSeqContinue; eauto;
           apply CFGKATExpressionDynamicsLoopGuardFalse; eauto.
    + eapply bisimulation_transpose_halting
        with (zeta1 := zeta1) (zeta2 := zeta2) in H0; subst;
        try apply resolve_syntactic_empty_identity; eauto;
        try now (destruct zeta1; simpl in *).
      eapply CFGKATStrongStepHalt
        with (zeta := cfgkat_floor zeta2); eauto.
      * destruct zeta2; simpl in *; intuition.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopSeqHalt; eauto.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopSeqHalt; eauto.
    + destruct zeta1; try now simpl in *.
      destruct s as (e', i'). clear H1 H2.
      eapply bisimulation_transpose_step
        with (zeta := zeta2) (p := p) (x1' := (e', i'))
        in H0 as [(f', i'') [? ?]]; subst;
        try apply resolve_syntactic_empty_identity; eauto.
      eapply CFGKATStrongStepNext.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopSeqNext; eauto.
      * simpl. rewrite resolve_syntactic_empty_identity.
        apply CFGKATExpressionDynamicsLoopSeqNext; eauto.
      * constructor; eauto.
Qed.

Theorem CFGKATCongruenceLoopBodyEmpty_sound :
  forall e f b i,
    (forall i, (e, i) ~~ (f, i)) ->
    (while b do e, i) ~~ (while b do f, i).
Proof.
  intros e f b i Hbody.
  unshelve eexists.
  - apply (strong_bisim_to_bisim [empty_syntactic_context]
                                 [empty_syntactic_context]).
    apply CFGKATCongruenceLoopBodyEmpty_bisim.
    apply CFGKATBisimilarity.
  - constructor. intros.
    destruct (Hbody j) as [R HR].
    now exists R.
Qed.

Inductive CFGKATCongruenceLoopBody_relation
  (E F : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  (b : CFGKATTest)
  : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop :=
| CFGKATCongruenceLoopBody_loop :
    forall i,
      CFGKATCongruenceLoopBody_relation E F e b
        (while b do e, i)
        (while b do e, i)
| CFGKATCongruenceLoopBody_loopseq :
    forall
      (Rprefix :
        CFGKATAutomatonBisimulation
          (resolve_list CFGKATExpressionAutomaton [lift E])
          (resolve_list CFGKATExpressionAutomaton [lift F]))
      h i,
      cfgkat_relation Rprefix (h, i) (h, i) ->
      CFGKATCongruenceLoopBody_relation E F e b
        (h |> while b do e, i)
        (h |> while b do e, i)
| CFGKATCongruenceLoopBody_univ :
    forall x y,
      x ~[lift E, lift F] y ->
      CFGKATCongruenceLoopBody_relation E F e b x y.

Local Lemma CFGKATCongruenceLoopBody_sym :
  forall E F e b x y,
    CFGKATCongruenceLoopBody_relation E F e b x y ->
    CFGKATCongruenceLoopBody_relation F E e b y x.
Proof.
  intros E F e b x y Hrel.
  inversion Hrel; subst.
  - constructor.
  - eapply CFGKATCongruenceLoopBody_loopseq with
      (Rprefix := bisim_sym Rprefix); eauto.
  - constructor.
    destruct H as [R HR].
    now exists (bisim_sym R).
Qed.

Local Lemma loop_guard_true_resolved_iff
  (E : label_environment CFGKATExpression)
  (b : CFGKATTest)
  (e : CFGKATExpression)
  (i : IndicatorAssignment)
  (a : Atom)
  :
  eval_test b a i ->
  forall r,
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      (while b do e, i) a r <->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      (e |> while b do e, i) a r.
Proof.
  intros Hb r. apply resolve_list_same_dynamics.
  intro r'. split; intro Hdyn.
  - eapply CFGKATExpressionDynamicsLoopGuardTrueInv; eauto.
  - eapply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
Qed.

Local Lemma loop_body_general_universal_to :
  forall E F e b x y a zeta,
    x ~[lift E, lift F] y ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      x a zeta ->
    exists zeta',
      cfgkat_transitions
        (resolve_list CFGKATExpressionAutomaton [lift F])
        y a zeta' /\
      lifted_relation
        (CFGKATCongruenceLoopBody_relation E F e b)
        zeta zeta'.
Proof.
  intros E F e b x y a zeta Huniv Hx.
  destruct (resolved_lift_total F y a) as [zeta' Hy].
  destruct Huniv as [Runiv HRuniv].
  exists zeta'. intuition.
  eapply lifted_relation_mono with (R := cfgkat_relation Runiv); eauto.
  - constructor. now exists Runiv.
  - eapply cfgkat_bisimulation_step; eauto.
Qed.

Local Lemma loop_body_general_finite_to :
  forall E F e b,
    (forall i, (e, i) ~[lift E, lift F] (e, i)) ->
    forall x y a zeta_raw zeta,
      CFGKATCongruenceLoopBody_relation E F e b x y ->
      CFGKATExpressionFiniteDynamics x a zeta_raw ->
      cfgkat_transitions
        (resolve_list CFGKATExpressionAutomaton [lift E])
        x a zeta ->
      exists zeta',
        cfgkat_transitions
          (resolve_list CFGKATExpressionAutomaton [lift F])
          y a zeta' /\
        lifted_relation
          (CFGKATCongruenceLoopBody_relation E F e b)
          zeta zeta'.
Proof.
  intros E F e b Hsound x y a zeta_raw zeta Hrel Hfin.
  revert y zeta Hrel.
  induction Hfin; intros y zeta Hrel Hx;
    repeat dependent destruction Hrel;
    try now eapply loop_body_general_universal_to; eauto.

  -
    eapply CFGKATExpressionDynamicsFinite in Hfin1.
    rewrite loopseq_resolved_accept_iff in Hx; eauto.
    destruct (IHHfin2 (while b do e, i') zeta)
      as [zeta' [Htail_y Hlift]]; eauto.
    + constructor.
    + exists zeta'. intuition.
      rewrite loopseq_resolved_accept_iff; eauto.

  -
    eapply CFGKATExpressionDynamicsFinite in Hfin.
    eapply CFGKATExpressionDynamicsLoopSeqReject in Hfin.
    erewrite resolved_lift_functional
      with (zeta1 := zeta) (zeta2 := CFGKATAutomatonReject); eauto.
    + exists CFGKATAutomatonReject.
      split; try now constructor.
      eapply Hlift_reject; eauto.
    + eapply Hlift_reject with (ys := [lift E]); eauto.

  -
    eapply CFGKATExpressionDynamicsFinite in Hfin.
    eapply CFGKATExpressionDynamicsLoopSeqReturn in Hfin.
    erewrite resolved_lift_functional
      with (zeta1 := zeta) (zeta2 := CFGKATAutomatonReturn); eauto.
    + exists CFGKATAutomatonReturn.
      split; try now constructor.
      eapply Hlift_return; eauto.
    + eapply Hlift_return with (ys := [lift E]); eauto.

  -
    eapply CFGKATExpressionDynamicsFinite in Hfin.
    eapply CFGKATExpressionDynamicsLoopSeqBreak in Hfin.
    erewrite resolved_lift_functional
      with (zeta1 := zeta) (zeta2 := CFGKATAutomatonAccept i'); eauto.
    + exists (CFGKATAutomatonAccept i').
      split; try now constructor.
      eapply Hlift_accept; eauto.
    + eapply Hlift_accept with (ys := [lift E]); eauto.

  -
    apply CFGKATExpressionDynamicsFinite in Hfin1.
    erewrite loopseq_resolved_continue_iff in Hx; eauto.
    destruct (IHHfin2 (while b do e, i') zeta)
      as [zeta' [Htail_y Hlift]]; eauto.
    + constructor.
    + exists zeta'. intuition.
      rewrite loopseq_resolved_continue_iff; eauto.

  -
    apply CFGKATExpressionDynamicsFinite in Hfin.
    erewrite loopseq_resolved_jump_iff in Hx; eauto.
    destruct (resolved_lift_total F (e1, i) a) as [zeta' Hy].
    eapply (cfgkat_bisimulation_step Rprefix) in Hy as ?; eauto.
    exists zeta'. split.
    * erewrite loopseq_resolved_jump_iff; eauto.
    * eapply lifted_relation_mono with (R := cfgkat_relation Rprefix); auto.
      intuition constructor. now exists Rprefix.

  -
    apply CFGKATExpressionDynamicsFinite in Hfin.
    edestruct @bisimulation_transpose_step with (B := Rprefix); eauto;
    try now (apply Hlift_next, Hfin).
    destruct H0; inversion H0; subst.
    exists (CFGKATAutomatonNext p (e1' |> while b do e, i')); intuition.
    + apply Hlift_next.
      now apply CFGKATExpressionDynamicsLoopSeqNext.
    + erewrite resolved_lift_functional
        with (zeta1 := zeta)
             (zeta2 := CFGKATAutomatonNext p _); eauto.
      * constructor.
        eapply CFGKATCongruenceLoopBody_loopseq; eauto.
      * eapply Hlift_next with (ys := [lift E]).
        now apply  CFGKATExpressionDynamicsLoopSeqNext.

  -
    rewrite loop_guard_true_resolved_iff in Hx; eauto.
    destruct (Hsound i) as [Rbody HRbody].
    destruct (IHHfin (e0 |> while b0 do e0, i) zeta)
      as [zeta' [Hbody_y Hlift]]; eauto.
    + eapply CFGKATCongruenceLoopBody_loopseq with (Rprefix := Rbody).
      exact HRbody.
    + exists zeta'. intuition.
      rewrite loop_guard_true_resolved_iff; eauto.

  -
    eapply CFGKATExpressionDynamicsLoopGuardFalse in H as H'.
    exists (CFGKATAutomatonAccept i).
    erewrite resolved_lift_functional
      with (zeta1 := zeta) (zeta2 := CFGKATAutomatonAccept i); eauto.
    + intuition.
      * apply Hlift_accept, H'.
      * constructor.
    + now apply Hlift_accept with (ys := [lift E]).
Qed.

Program Definition CFGKATCongruenceLoopBody_bisim
  (E F : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (Hsound : forall i, (e, i) ~[lift E, lift F] (e, i))
  : CFGKATAutomatonBisimulation
      (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
      (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift F))
:= {|
  cfgkat_relation := CFGKATCongruenceLoopBody_relation E F e b;
|}.
Next Obligation.
  intros E F e b Hsound x y a zeta1 zeta2 Hrel Hx Hy.
  destruct (CFGKATExpressionDynamics_total x a) as [raw_x Hxraw].
  destruct (CFGKATExpressionDynamics_total y a) as [raw_y Hyraw].
  dependent destruction Hxraw; [| dependent destruction Hyraw ].
  - edestruct loop_body_general_finite_to as [zeta2' [Hy' Hlift]]; eauto.
    erewrite resolved_lift_functional
      with (zeta1 := zeta2) (zeta2 := zeta2'); eauto.
  - eapply loop_body_general_finite_to
      in Hy as [zeta1' [Hx' Hlift_sym]]; eauto.
    + erewrite resolved_lift_functional
        with (zeta1 := zeta1) (zeta2 := zeta1'); eauto.
      inversion Hlift_sym; subst; constructor.
      apply CFGKATCongruenceLoopBody_sym; eauto.
    + intros. now apply CFGKATCongruenceSym_sound.
    + now apply CFGKATCongruenceLoopBody_sym.
  - apply CFGKATExpressionDynamicsDefaultReject in H, H0.
    erewrite resolved_lift_functional
      with (zeta1 := zeta1) (zeta2 := CFGKATAutomatonReject); eauto.
    erewrite resolved_lift_functional
      with (zeta1 := zeta2) (zeta2 := CFGKATAutomatonReject); eauto.
    + constructor.
    + now apply Hlift_reject with (ys := [lift F]).
    + now apply Hlift_reject with (ys := [lift E]).
Qed.

Theorem CFGKATCongruenceLoopBody_sound :
  forall E F e b,
    (forall i, (e, i) ~[lift E, lift F] (e, i)) ->
    forall i, (while b do e, i) ~[lift E, lift F] (while b do e, i).
Proof.
  intros E F e b Hsound i.
  exists (CFGKATCongruenceLoopBody_bisim E F e b Hsound).
  constructor.
Qed.
