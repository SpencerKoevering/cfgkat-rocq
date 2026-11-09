Require Import Stdlib.Program.Equality.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Logic.ClassicalEpsilon.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.

From CFGKAT.Semantics Require Export Bisimulation.
From CFGKAT.Completeness Require Export BooleanAlgebraCompleteness.

Local Open Scope cfgkat_scope.


Definition transition_output_inhabited
  : inhabited (CFGKATAutomatonOutputs CFGKATSyntConfiguration) :=
  inhabits CFGKATAutomatonReject.

Definition functional_relation_choice
  {X Y : Type}
  (Y_inhabited : inhabited Y)
  (R : X -> Y -> Prop)
  (x : X)
  : Y :=
  epsilon Y_inhabited (R x).

Lemma functional_relation_choice_spec_from_exists
  {X Y : Type}
  (Y_inhabited : inhabited Y)
  (R : X -> Y -> Prop)
  (x : X)
  :
  (exists y, R x y) ->
  R x (functional_relation_choice Y_inhabited R x).
Proof.
  unfold functional_relation_choice.
  apply epsilon_spec.
Qed.

Lemma functional_relation_choice_unique
  {X Y : Type}
  (Y_inhabited : inhabited Y)
  (R : X -> Y -> Prop)
  (R_functional : forall x y1 y2, R x y1 -> R x y2 -> y1 = y2)
  (x : X)
  (y : Y)
  :
  R x y ->
  functional_relation_choice Y_inhabited R x = y.
Proof.
  intro Hy.
  eapply R_functional; eauto.
  eapply functional_relation_choice_spec_from_exists; eauto.
Qed.

Definition expression_transition_input : Type :=
  (CFGKATExpression * (Atom * IndicatorAssignment))%type.

Definition expression_transition_relation
  (input : expression_transition_input)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : Prop :=
  match input with
  | (e, (a, i)) => CFGKATExpressionDynamics (e, i) a r
  end.

Lemma expression_transition_relation_total
  :
  forall input, exists r, expression_transition_relation input r.
Proof.
  intros [e [a i]].
  unfold expression_transition_relation.
  apply CFGKATExpressionDynamics_total.
Qed.

Lemma expression_transition_relation_functional
  :
  forall input r1 r2,
    expression_transition_relation input r1 ->
    expression_transition_relation input r2 ->
    r1 = r2.
Proof.
  intros [e [a i]] r1 r2 Hr1 Hr2.
  unfold expression_transition_relation in *.
  eapply cfgkat_dynamics_functional; eauto.
Qed.

Definition transition_output
  (e : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  : CFGKATAutomatonOutputs CFGKATSyntConfiguration :=
  functional_relation_choice
    transition_output_inhabited
    expression_transition_relation
    (e, (a, i)).

Lemma transition_output_spec
  (e : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  CFGKATExpressionDynamics
    (e, i)
    a
    (transition_output e a i).
Proof.
  eapply functional_relation_choice_spec_from_exists with
    (R := expression_transition_relation) (x := (e, (a, i))).
  apply expression_transition_relation_total.
Qed.

Lemma transition_output_unique
  (e : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  CFGKATExpressionDynamics (e, i) a r ->
  transition_output e a i = r.
Proof.
  intros. eapply functional_relation_choice_unique; auto.
  apply expression_transition_relation_functional.
Qed.

Theorem transition_output_exact
  (e : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  CFGKATExpressionDynamics (e, i) a r <->
  transition_output e a i = r.
Proof.
  split.
  - apply transition_output_unique.
  - intro Hr. subst r. apply transition_output_spec.
Qed.

Definition resolved_transition_input : Type :=
  ((label_environment CFGKATExpression) *
    (CFGKATExpression * (Atom * IndicatorAssignment)))%type.

Definition resolved_transition_relation
  (input : resolved_transition_input)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : Prop :=
  let '(E, (source, (a, i))) := input in
  cfgkat_transitions
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
    (source, i) a r.

Lemma resolved_transition_relation_total
  :
  forall input, exists r, resolved_transition_relation input r.
Proof.
  intros [E [source [a i]]].
  unfold resolved_transition_relation.
  apply resolved_lift_total.
Qed.

Lemma resolved_transition_relation_functional
  :
  forall input r1 r2,
    resolved_transition_relation input r1 ->
    resolved_transition_relation input r2 ->
    r1 = r2.
Proof.
  intros [E [source [a i]]] r1 r2 Hr1 Hr2.
  unfold resolved_transition_relation in *.
  eapply resolved_lift_functional; eauto.
Qed.

Definition resolved_transition_output
  (E : label_environment CFGKATExpression)
  (source : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  : CFGKATAutomatonOutputs CFGKATSyntConfiguration :=
  functional_relation_choice
    transition_output_inhabited
    resolved_transition_relation
    (E, (source, (a, i))).

Lemma resolved_transition_output_spec
  (E : label_environment CFGKATExpression)
  (source : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  cfgkat_transitions
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
    (source, i) a (resolved_transition_output E source a i).
Proof.
  eapply functional_relation_choice_spec_from_exists with
    (R := resolved_transition_relation) (x := (E, (source, (a, i)))).
  apply resolved_transition_relation_total.
Qed.

Lemma resolved_transition_output_unique
  (E : label_environment CFGKATExpression)
  (source : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  cfgkat_transitions
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
    (source, i) a r ->
  resolved_transition_output E source a i = r.
Proof.
  intros. eapply functional_relation_choice_unique; auto.
  apply resolved_transition_relation_functional.
Qed.

Lemma transition_output_eq_dynamics_iff
  (e f : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  transition_output e a i = transition_output f a i ->
  forall r,
    CFGKATExpressionDynamics (e, i) a r <->
    CFGKATExpressionDynamics (f, i) a r.
Proof.
  intros Hout r.
  rewrite !transition_output_exact.
  now rewrite Hout.
Qed.

Lemma transition_assert
  (b : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  transition_output (test b) a i =
    match eval_test_dec b a i with
    | left _ => CFGKATAutomatonAccept i
    | right _ => CFGKATAutomatonReject
    end.
Proof.
  apply transition_output_unique.
  destruct (eval_test_dec b a i) as [Hb | Hb].
  - now apply CFGKATExpressionDynamicsAssertTrue.
  - now apply CFGKATExpressionDynamicsAssertFalse.
Qed.

Lemma transition_assert_in_true
  (b : CFGKATTest)
  (m : (At x I^Y))
  :
  (m \in b) = true ->
  transition_output (test b) (AtIY_atom m) (AtIY_assignment m) =
    CFGKATAutomatonAccept (AtIY_assignment m).
Proof.
  intro Hsat. rewrite transition_assert.
  destruct (eval_test_dec b (AtIY_atom m) (AtIY_assignment m)); intuition.
  now pose proof (in_test_true b m Hsat).
Qed.

Lemma transition_assert_in_false
  (b : CFGKATTest)
  (m : (At x I^Y))
  :
  (m \in b) = false ->
  transition_output (test b) (AtIY_atom m) (AtIY_assignment m) =
    CFGKATAutomatonReject.
Proof.
  intro Hsat. rewrite transition_assert.
  destruct (eval_test_dec b (AtIY_atom m) (AtIY_assignment m)); intuition.
  now pose proof (in_test_false b m Hsat).
Qed.

Lemma transition_assign
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  transition_output (assign v to x) a i =
    CFGKATAutomatonAccept (update i x v).
Proof.
  apply transition_output_unique.
  apply CFGKATExpressionDynamicsAssign.
Qed.

Lemma transition_action
  (p : Action)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  transition_output (do p) a i =
    CFGKATAutomatonNext p (1, i).
Proof.
  apply transition_output_unique.
  apply CFGKATExpressionDynamicsAction.
Qed.

Lemma transition_break
  (a : Atom)
  (i : IndicatorAssignment)
  :
  transition_output break a i =
    CFGKATAutomatonBreak i.
Proof.
  apply transition_output_unique.
  apply CFGKATExpressionDynamicsBreak.
Qed.

Lemma transition_continue
  (a : Atom)
  (i : IndicatorAssignment)
  :
  transition_output continue a i =
    CFGKATAutomatonContinue i.
Proof.
  apply transition_output_unique.
  apply CFGKATExpressionDynamicsContinue.
Qed.

Lemma transition_return
  (a : Atom)
  (i : IndicatorAssignment)
  :
  transition_output return a i =
    CFGKATAutomatonReturn.
Proof.
  apply transition_output_unique.
  apply CFGKATExpressionDynamicsReturn.
Qed.

Lemma transition_goto
  (l : Label)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  transition_output (goto l) a i =
    CFGKATAutomatonJump l i.
Proof.
  apply transition_output_unique.
  apply CFGKATExpressionDynamicsGoto.
Qed.

Lemma transition_choice
  (b : CFGKATTest)
  (e f : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  transition_output (if b then e else f) a i =
    match eval_test_dec b a i with
    | left _ => transition_output e a i
    | right _ => transition_output f a i
    end.
Proof.
  apply transition_output_unique.
  destruct (eval_test_dec b a i) as [Hb | Hb].
  - apply CFGKATExpressionDynamicsChoiceLeft; auto.
    apply transition_output_spec.
  - apply CFGKATExpressionDynamicsChoiceRight; auto.
    apply transition_output_spec.
Qed.

Lemma transition_choice_in_true
  (b : CFGKATTest)
  (e f : CFGKATExpression)
  (m : (At x I^Y))
  :
  (m \in b) = true ->
  transition_output (if b then e else f) (AtIY_atom m) (AtIY_assignment m) =
    transition_output e (AtIY_atom m) (AtIY_assignment m).
Proof.
  intro Hsat. rewrite transition_choice.
  destruct (eval_test_dec b (AtIY_atom m) (AtIY_assignment m)); auto.
  now pose proof (in_test_true b m Hsat).
Qed.

Lemma transition_choice_in_false
  (b : CFGKATTest)
  (e f : CFGKATExpression)
  (m : (At x I^Y))
  :
  (m \in b) = false ->
  transition_output (if b then e else f) (AtIY_atom m) (AtIY_assignment m) =
    transition_output f (AtIY_atom m) (AtIY_assignment m).
Proof.
  intro Hsat. rewrite transition_choice.
  destruct (eval_test_dec b (AtIY_atom m) (AtIY_assignment m)); auto.
  now pose proof (in_test_false b m Hsat).
Qed.

Definition sequence_output
  (a : Atom)
  (e2 : CFGKATExpression)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : CFGKATAutomatonOutputs CFGKATSyntConfiguration :=
  match r with
  | CFGKATAutomatonReject => CFGKATAutomatonReject
  | CFGKATAutomatonAccept i' => transition_output e2 a i'
  | CFGKATAutomatonBreak i' => CFGKATAutomatonBreak i'
  | CFGKATAutomatonContinue i' => CFGKATAutomatonContinue i'
  | CFGKATAutomatonReturn => CFGKATAutomatonReturn
  | CFGKATAutomatonJump l i' => CFGKATAutomatonJump l i'
  | CFGKATAutomatonNext p (e1', i') =>
      CFGKATAutomatonNext p (e1' ;; e2, i')
  end.

Lemma transition_sequence
  (e1 e2 : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  transition_output (e1 ;; e2) a i =
    sequence_output a e2 (transition_output e1 a i).
Proof.
  apply transition_output_unique.
  pose proof (transition_output_spec e1 a i) as Hhead.
  destruct (transition_output e1 a i) as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p [e1' i']]; simpl.
  - apply CFGKATExpressionDynamicsSequenceReject; eauto.
  - apply CFGKATExpressionDynamicsSequenceSkip
      with (i' := i_accept); auto.
    apply transition_output_spec.
  - apply CFGKATExpressionDynamicsSequenceBreak; eauto.
  - apply CFGKATExpressionDynamicsSequenceContinue; eauto.
  - apply CFGKATExpressionDynamicsSequenceReturn; eauto.
  - apply CFGKATExpressionDynamicsSequenceJump; eauto.
  - apply CFGKATExpressionDynamicsSequenceNext; eauto.
Qed.

Definition loopseq_output
  (a : Atom)
  (e2 : CFGKATExpression)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : CFGKATAutomatonOutputs CFGKATSyntConfiguration :=
  match r with
  | CFGKATAutomatonReject => CFGKATAutomatonReject
  | CFGKATAutomatonAccept i' => transition_output e2 a i'
  | CFGKATAutomatonBreak i' => CFGKATAutomatonAccept i'
  | CFGKATAutomatonContinue i' => transition_output e2 a i'
  | CFGKATAutomatonReturn => CFGKATAutomatonReturn
  | CFGKATAutomatonJump l i' => CFGKATAutomatonJump l i'
  | CFGKATAutomatonNext p (e1', i') =>
      CFGKATAutomatonNext p (e1' |> e2, i')
  end.

Lemma transition_loopseq
  (e1 e2 : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  transition_output (e1 |> e2) a i =
    loopseq_output a e2 (transition_output e1 a i).
Proof.
  apply transition_output_unique.
  pose proof (transition_output_spec e1 a i) as Hhead.
  destruct (transition_output e1 a i) as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p [e1' i']]; simpl.
  - apply CFGKATExpressionDynamicsLoopSeqReject; eauto.
  - apply CFGKATExpressionDynamicsLoopSeqSkip
      with (i' := i_accept); eauto.
    apply transition_output_spec.
  - apply CFGKATExpressionDynamicsLoopSeqBreak; eauto.
  - apply CFGKATExpressionDynamicsLoopSeqContinue
      with (i' := i_continue); eauto.
    apply transition_output_spec.
  - apply CFGKATExpressionDynamicsLoopSeqReturn; eauto.
  - apply CFGKATExpressionDynamicsLoopSeqJump; eauto.
  - apply CFGKATExpressionDynamicsLoopSeqNext; eauto.
Qed.

Lemma transition_loop
  (b : CFGKATTest)
  (e : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  transition_output (while b do e) a i =
    match eval_test_dec b a i with
    | left _ => transition_output (e |> while b do e) a i
    | right _ => CFGKATAutomatonAccept i
    end.
Proof.
  apply transition_output_unique.
  destruct (eval_test_dec b a i) as [Hb | Hb].
  - apply CFGKATExpressionDynamicsLoopGuardTrue; auto.
    apply transition_output_spec.
  - apply CFGKATExpressionDynamicsLoopGuardFalse; auto.
Qed.

Lemma transition_loop_in_true
  (b : CFGKATTest)
  (e : CFGKATExpression)
  (m : (At x I^Y))
  :
  (m \in b) = true ->
  transition_output (while b do e) (AtIY_atom m) (AtIY_assignment m) =
    transition_output (e |> while b do e) (AtIY_atom m) (AtIY_assignment m).
Proof.
  intro Hsat. rewrite transition_loop.
  destruct (eval_test_dec b (AtIY_atom m) (AtIY_assignment m)); auto.
  now pose proof (in_test_true b m Hsat).
Qed.

Lemma transition_loop_in_false
  (b : CFGKATTest)
  (e : CFGKATExpression)
  (m : (At x I^Y))
  :
  (m \in b) = false ->
  transition_output (while b do e) (AtIY_atom m) (AtIY_assignment m) =
    CFGKATAutomatonAccept (AtIY_assignment m).
Proof.
  intro Hsat. rewrite transition_loop.
  destruct (eval_test_dec b (AtIY_atom m) (AtIY_assignment m)); auto.
  now pose proof (in_test_false b m Hsat).
Qed.

Definition acc_cont_loop_invariant
  (e : CFGKATExpression)
  (c : CFGKATTest)
  : Prop :=
  forall a i,
    eval_test c a i ->
    exists j,
      (transition_output e a i = CFGKATAutomatonAccept j \/
       transition_output e a i = CFGKATAutomatonContinue j) /\
      eval_test c a j.

Definition largest_loop_invariant_pred
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
  : Prop :=
  exists c,
    BA_leq c b /\
    acc_cont_loop_invariant e c /\
    eval_test c a i.

Definition largest_loop_invariant_test
  (e : CFGKATExpression)
  (b : CFGKATTest)
  : CFGKATTest :=
  predicate_to_test
    (largest_loop_invariant_pred e b)
    (fun a i =>
      excluded_middle_informative (largest_loop_invariant_pred e b a i)).

Notation "'C+[' e ',' b ']'" := (largest_loop_invariant_test e b)
  (at level 0, e at level 99, b at level 99).

Lemma largest_loop_invariant_test_complete
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  largest_loop_invariant_pred e b a i ->
  eval_test C+[e, b] a i.
Proof.
  unfold largest_loop_invariant_test.
  apply predicate_to_test_complete.
Qed.

Lemma largest_loop_invariant_test_sound
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  eval_test C+[e, b] a i ->
  largest_loop_invariant_pred e b a i.
Proof.
  unfold largest_loop_invariant_test.
  apply predicate_to_test_sound.
Qed.

Lemma largest_loop_invariant_test_leq_guard
  (e : CFGKATExpression)
  (b : CFGKATTest)
  :
  BA_leq C+[e, b] b.
Proof.
  apply Boolean_denotation_completeness.
  unfold CFGKATTestDenotationEquivalent; simpl; intuition.
  pose proof (largest_loop_invariant_test_sound e b a i H0)
    as [c [Hle [_ Hc_eval]]].
  eapply BA_leq_eval; eauto.
Qed.

Lemma largest_loop_invariant_test_largest
  (e : CFGKATExpression)
  (b c : CFGKATTest)
  :
  BA_leq c b ->
  acc_cont_loop_invariant e c ->
  BA_leq c C+[e, b].
Proof.
  intros Hle Hinv. apply Boolean_denotation_completeness.
  unfold CFGKATTestDenotationEquivalent; simpl; intuition.
  apply largest_loop_invariant_test_complete.
  exists c. intuition.
Qed.

Lemma largest_loop_invariant_test_acc_cont_invariant
  (e : CFGKATExpression)
  (b : CFGKATTest)
  :
  acc_cont_loop_invariant e C+[e, b].
Proof.
  intros a i Hcplus.
  pose proof (largest_loop_invariant_test_sound e b a i Hcplus)
    as [c [Hle [Hinv Hc]]].
  pose proof (Hinv a i Hc) as [j [Hout Hc_j]].
  exists j. split; auto.
  apply largest_loop_invariant_test_complete; firstorder.
Qed.

Lemma guarded_largest_loop_invariant_test_acc_cont_invariant
  (e : CFGKATExpression)
  (b : CFGKATTest)
  :
  acc_cont_loop_invariant e (b and C+[e, b]).
Proof.
  intros a i [_ Hcplus].
  pose proof (largest_loop_invariant_test_acc_cont_invariant e b a i Hcplus)
    as [j [Hout Hcplus_j]].
  exists j. split; auto.
  clear Hout. simpl. intuition.
  eapply BA_leq_eval; eauto.
  apply largest_loop_invariant_test_leq_guard.
Qed.

Lemma acc_cont_loop_invariant_stuck
  (e : CFGKATExpression)
  (c : CFGKATTest)
  :
  acc_cont_loop_invariant e c ->
  Stuck e c.
Proof.
  intros Hinv i a Hc.
  pose proof (Hinv a i Hc) as [j [Hacc_cont Hc_j]].
  right. exists j; intuition.
  - left. now apply transition_output_exact.
  - right. now apply transition_output_exact.
Qed.

Definition loop_cplus_progress
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (m n : At x I^Y)
  : Prop :=
  (m \in b) = true /\
  (m \in C+[e, b]) = false /\
  AtIY_atom n = AtIY_atom m /\
  (transition_output e (AtIY_atom m) (AtIY_assignment m) =
     CFGKATAutomatonAccept (AtIY_assignment n) \/
   transition_output e (AtIY_atom m) (AtIY_assignment m) =
     CFGKATAutomatonContinue (AtIY_assignment n)).

Inductive loop_cplus_relation_path
  {A : Type}
  (R : A -> A -> Prop)
  : nat -> A -> A -> Prop :=
| LoopCPlusRelationPathZero :
    forall x, loop_cplus_relation_path R 0 x x
| LoopCPlusRelationPathStep :
    forall n x y z,
      R x y ->
      loop_cplus_relation_path R n y z ->
      loop_cplus_relation_path R (S n) x z.

Arguments LoopCPlusRelationPathZero {A R} _.
Arguments LoopCPlusRelationPathStep {A R n x y z} _ _.

Inductive loop_cplus_relation_path_vertices
  {A : Type}
  (R : A -> A -> Prop)
  : A -> list A -> Prop :=
| LoopCPlusRelationPathVerticesSingle :
    forall x, loop_cplus_relation_path_vertices R x []
| LoopCPlusRelationPathVerticesCons :
    forall x y xs,
      R x y ->
      loop_cplus_relation_path_vertices R y xs ->
      loop_cplus_relation_path_vertices R x (y :: xs).

Arguments LoopCPlusRelationPathVerticesSingle {A R} _.
Arguments LoopCPlusRelationPathVerticesCons {A R x y xs} _ _.

Lemma loop_cplus_relation_path_vertices_incl
  {A : Type}
  (R : A -> A -> Prop)
  (universe : list A)
  (x : A)
  (xs : list A)
  :
  (forall x y, R x y -> In y universe) ->
  loop_cplus_relation_path_vertices R x xs ->
  In x universe ->
  incl (x :: xs) universe.
Proof.
  intros Hstep Hvertices.
  induction Hvertices as [x | x y xs Hxy Htail IH];
    simpl; intros Hx z Hz.
  - destruct Hz as [Hz | []].
    congruence.
  - destruct Hz as [Hz | Hz]; try congruence.
    eapply IH; eauto.
Qed.

Lemma loop_cplus_relation_path_vertices_in_path
  {A : Type}
  (R : A -> A -> Prop)
  (x y : A)
  (xs : list A)
  :
  loop_cplus_relation_path_vertices R x xs ->
  In y (x :: xs) ->
  exists n, loop_cplus_relation_path R n x y.
Proof.
  intro Hvertices. revert y.
  induction Hvertices as [x | x y xs Hxy Htail IH]; simpl; intros z Hin.
  - intuition; subst.
    exists O. apply LoopCPlusRelationPathZero.
  - destruct Hin as [Hz | Hin].
    + subst. exists O. apply LoopCPlusRelationPathZero.
    + pose proof (IH z Hin) as [n Hpath].
      exists (S n).
      eapply LoopCPlusRelationPathStep; eauto.
Qed.

Lemma last_nonempty_default_irrelevant
  {A : Type}
  (xs : list A)
  (d d' : A)
  :
  xs <> [] ->
  last xs d = last xs d'.
Proof.
  induction xs; intuition.
  destruct xs; auto.
  apply IHxs. discriminate.
Qed.

Lemma loop_cplus_relation_path_vertices_successor_or_last
  {A : Type}
  (R : A -> A -> Prop)
  (x y : A)
  (xs : list A)
  :
  loop_cplus_relation_path_vertices R x xs ->
  In y (x :: xs) ->
  (exists z, R y z /\ In z xs) \/ last xs x = y.
Proof.
  intro Hvertices.
  induction Hvertices as [x | x z xs Hxz Hzxs IH];
    intro Hin; try now firstorder.
  destruct Hin as [Hy | Hin].
  - subst y. left. firstorder.
  - pose proof (IH Hin) as [[w [Hyw Hwin]] | Hlast].
    + left. firstorder.
    + right. destruct xs as [|u us].
      * simpl in Hlast. exact Hlast.
      * erewrite last_nonempty_default_irrelevant; eauto.
        discriminate.
Qed.

Lemma loop_cplus_relation_path_vertices_cycle_successor
  {A : Type}
  (R : A -> A -> Prop)
  (x y : A)
  (xs : list A)
  :
  loop_cplus_relation_path_vertices R x xs ->
  xs <> [] ->
  last xs x = x ->
  In y (x :: xs) ->
  exists z, R y z /\ In z (x :: xs).
Proof.
  intros Hvertices Hnonempty Hlast Hin.
  pose proof
    (loop_cplus_relation_path_vertices_successor_or_last R x y xs Hvertices Hin)
    as [[z [Hyz Hz_in]] | Hy_last].
  - exists z. simpl in *; intuition.
  - subst. destruct Hvertices as [x | x z xs Hxz Hzxs].
    + intuition.
    + exists z. intuition; try congruence;
      now right; left.
Qed.

Lemma loop_cplus_relation_path_vertices_NoDup_no_cycle
  {A : Type}
  (R : A -> A -> Prop)
  (x : A)
  (xs : list A)
  :
  (forall y n, ~ loop_cplus_relation_path R (S n) y y) ->
  loop_cplus_relation_path_vertices R x xs ->
  NoDup (x :: xs).
Proof.
  intros Hno_cycle Hvertices.
  induction Hvertices as [x | x y xs Hxy Hyxs IH].
  - repeat constructor. intuition.
  - repeat constructor; try now inversion IH.
    intro Hin.
    pose proof
      (loop_cplus_relation_path_vertices_in_path R y x xs Hyxs Hin)
      as [n Hpath]; eauto.
    eapply Hno_cycle.
    eapply LoopCPlusRelationPathStep; eauto.
Qed.

Lemma loop_cplus_relation_path_vertices_length_bound_no_cycle
  {A : Type}
  (R : A -> A -> Prop)
  (universe : list A)
  (x : A)
  (xs : list A)
  :
  (forall x y, R x y -> In y universe) ->
  (forall y n, ~ loop_cplus_relation_path R (S n) y y) ->
  loop_cplus_relation_path_vertices R x xs ->
  In x universe ->
  S (length xs) <= length universe.
Proof.
  intros Hstep Hno_cycle Hvertices Hx.
  change (length (x :: xs) <= length universe).
  eapply NoDup_incl_length.
  - eapply loop_cplus_relation_path_vertices_NoDup_no_cycle; eauto.
  - eapply loop_cplus_relation_path_vertices_incl; eauto.
Qed.

Local Lemma loop_cplus_bounded_relation_path_vertices_acc
  {A : Type}
  (R : A -> A -> Prop)
  (n : nat)
  (x : A)
  :
  (forall xs, loop_cplus_relation_path_vertices R x xs -> length xs <= n) ->
  Acc (fun y x => R x y) x.
Proof.
  revert x.
  induction n as [|n IH]; intros x Hbound.
  - constructor. intros y Hxy.
    specialize (Hbound [y]).
    assert (Hvertices : loop_cplus_relation_path_vertices R x [y]).
    + apply LoopCPlusRelationPathVerticesCons; auto.
      apply LoopCPlusRelationPathVerticesSingle.
    + specialize (Hbound Hvertices).
      simpl in Hbound. lia.
  - constructor. intros y Hxy.
    apply IH. intros xs Hvertices.
    specialize (Hbound (y :: xs)).
    assert (Hfull : loop_cplus_relation_path_vertices R x (y :: xs)).
    + now apply LoopCPlusRelationPathVerticesCons.
    + specialize (Hbound Hfull).
      simpl in Hbound. lia.
Qed.

Local Definition loop_cplus_path_vertices_test
  (xs : list (At x I^Y))
  : CFGKATTest :=
  fold_TOr (map AtIY_test xs).

Local Lemma loop_cplus_eval_path_vertices_test_in
  (xs : list (At x I^Y))
  (a : Atom)
  (i : IndicatorAssignment)
  :
  eval_test (loop_cplus_path_vertices_test xs) a i ->
  exists m,
    In m xs /\
    a = AtIY_atom m /\
    i = AtIY_assignment m.
Proof.
  unfold loop_cplus_path_vertices_test.
  rewrite eval_fold_TOr.
  intros [t [Ht_in Ht_eval]].
  apply in_map_iff in Ht_in.
  destruct Ht_in as [m [Ht Hm_in]]; subst.
  pose proof (eval_AtIY_test_eq m a i Ht_eval) as [Ha Hi].
  exists m. intuition.
Qed.

Local Lemma loop_cplus_eval_path_vertices_test_of_in
  (xs : list (At x I^Y))
  (m : At x I^Y)
  :
  In m xs ->
  eval_test
    (loop_cplus_path_vertices_test xs)
    (AtIY_atom m)
    (AtIY_assignment m).
Proof.
  intro Hm.
  unfold loop_cplus_path_vertices_test.
  rewrite eval_fold_TOr.
  exists (AtIY_test m). repeat split.
  - now apply in_map.
  - now apply eval_atom_to_test.
  - now apply eval_complete_test.
Qed.

Lemma loop_cplus_relation_path_to_vertices
  {A : Type}
  (R : A -> A -> Prop)
  (n : nat)
  (x y : A)
  :
  loop_cplus_relation_path R n x y ->
  exists xs,
    loop_cplus_relation_path_vertices R x xs /\
    last xs x = y /\
    length xs = n.
Proof.
  intro Hpath.
  induction Hpath as [x | n x y z Hxy Hyz [xs [Hvertices [Hlast Hlen]]]].
  - exists []. repeat split.
    apply LoopCPlusRelationPathVerticesSingle.
  - exists (y :: xs). repeat split.
    + apply LoopCPlusRelationPathVerticesCons; assumption.
    + simpl. destruct xs as [|w ws].
      * simpl in Hlast. exact Hlast.
      * rewrite (last_nonempty_default_irrelevant (w :: ws) x y); auto.
        discriminate.
    + simpl. rewrite Hlen. reflexivity.
Qed.

Local Lemma loop_cplus_progress_cycle_succ
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (x y : At x I^Y)
  (xs : list At x I^Y)
  (H : loop_cplus_progress e b x y)
:
  loop_cplus_relation_path_vertices (loop_cplus_progress e b) y xs ->
  last (y :: xs) x = x ->
  forall q, In q (x :: y :: xs) ->
    exists z, loop_cplus_progress e b q z /\ In z (x :: y :: xs)
.
Proof.
  intros Hvertices Hlast q Hq.
  eapply loop_cplus_relation_path_vertices_cycle_successor;
    eauto; try discriminate.
  now constructor.
Qed.

Local Lemma loop_cplus_progress_cycle_no_cycle
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (m : At x I^Y)
  (n : nat)
  :
  ~ loop_cplus_relation_path (loop_cplus_progress e b) (S n) m m.
Proof.
  intro Hcycle.
  eapply loop_cplus_relation_path_to_vertices
    in Hcycle as [xs [Hvertices [Hlast Hlen]]].
  dependent destruction Hvertices; try discriminate.
  set (cycle := x :: y :: xs).
  set (C := loop_cplus_path_vertices_test cycle).
  apply Bool.diff_true_false. erewrite <- in_test_of_eval.
  - destruct H as [_ [Hm_not_cplus _]]; eauto.
  - eapply BA_leq_eval; eauto.
    apply largest_loop_invariant_test_largest.
    + apply Boolean_denotation_completeness.
      intros a i. simpl. split; try now intuition.
      intros [Hb | HC]; auto.
      eapply (loop_cplus_eval_path_vertices_test_in cycle)
        in HC as [q [Hq [Ha Hi]]]; subst.
      eapply loop_cplus_progress_cycle_succ
        in Hq as [r [[Hq_b _] _]]; eauto.
      now apply in_test_true.
    + intros a i HC.
      eapply (loop_cplus_eval_path_vertices_test_in cycle)
        in HC as [q [Hq [Ha Hi]]]; subst.
      eapply loop_cplus_progress_cycle_succ
        in Hq as [r [[_ [_ [Hr_atom Hr_out]]] Hr]]; eauto.
      exists (AtIY_assignment r).
      split; auto. rewrite <- Hr_atom.
      now apply loop_cplus_eval_path_vertices_test_of_in.
    + apply loop_cplus_eval_path_vertices_test_of_in.
      now left.
Qed.

Local Lemma loop_cplus_progress_accessible
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (m : At x I^Y)
  :
  In m all_AtIY ->
  Acc (fun y x => loop_cplus_progress e b x y) m.
Proof.
  intro Hm.
  apply loop_cplus_bounded_relation_path_vertices_acc
    with (n := length all_AtIY).
  intros xs Hvertices.
  eapply loop_cplus_relation_path_vertices_length_bound_no_cycle in Hm; eauto.
  - lia.
  - intros x [? ?] _. apply AtIY_in_all.
  - apply loop_cplus_progress_cycle_no_cycle.
Qed.

Theorem loop_cplus_AtIY_induction
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (P : (At x I^Y) -> Prop)
  :
  (forall m,
    In m all_AtIY ->
    (m \in b) = false ->
    P m) ->
  (forall m,
    In m all_AtIY ->
    (m \in b) = true ->
    (m \in C+[e, b]) = true ->
    P m) ->
  (forall m,
    In m all_AtIY ->
    (m \in b) = true ->
    (m \in C+[e, b]) = false ->
    (forall j,
      transition_output e (AtIY_atom m) (AtIY_assignment m) =
        CFGKATAutomatonAccept j ->
      P (fst m, j)) ->
    (forall j,
      transition_output e (AtIY_atom m) (AtIY_assignment m) =
        CFGKATAutomatonContinue j ->
      P (fst m, j)) ->
    P m) ->
  forall m,
    In m all_AtIY ->
    P m.
Proof.
  intros Hguard_false Hinvariant Hstep m Hm.
  pose proof (loop_cplus_progress_accessible e b m Hm) as Hacc.
  induction Hacc as [m _ IH].
  destruct (m \in b) eqn:Hb; intuition.
  destruct (m \in C+[e, b]) eqn:HC; intuition.
  apply Hstep; try assumption.
  - intros j Hout. apply IH.
    + unfold loop_cplus_progress. intuition.
    + apply AtIY_same_atom_assignment_in with (m := m).
  - intros j Hout. apply IH.
    + unfold loop_cplus_progress. intuition.
    + apply AtIY_same_atom_assignment_in with (m := m).
Qed.

Local Lemma always_reject_bisim
  (e : CFGKATExpression)
  :
  (forall i a,
    CFGKATExpressionDynamics (e, i) a CFGKATAutomatonReject) ->
  forall i,
    (e, i) ~~ (0, i).
Proof.
  intros Hreject i0.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar.
  unshelve eexists {|
    cfgkat_relation (x y: cfgkat_states ExprAutEmpty) :=
      exists i, x = (e, i) /\ y = (0, i)
  |}; [|simpl].
  - intros x1 x2 a zeta1 zeta2 HR Hzeta1 Hzeta2.
    destruct HR as [i [Hx1 Hx2]]; subst.
    erewrite cfgkat_dynamics_functional
      with (zeta1 := zeta1) (zeta2 := CFGKATAutomatonReject),
             cfgkat_dynamics_functional
      with (zeta1 := zeta2) (zeta2 := CFGKATAutomatonReject).
    + constructor.
    + apply resolve_syntactic_empty_identity in Hzeta2; eauto.
    + now apply CFGKATExpressionDynamicsAssertFalse.
    + apply resolve_syntactic_empty_identity in Hzeta1; eauto.
    + apply Hreject.
  - now exists i0.
Qed.

Lemma stuck_l11_premise
  (e : CFGKATExpression)
  (b : CFGKATTest)
  :
  Stuck e b ->
  CFGKATL11Premise e b.
Proof.
  intros Hstuck i.
  apply always_reject_bisim.
  intros j a. apply transition_output_exact.
  rewrite transition_loopseq, transition_sequence, transition_assert.
  destruct (eval_test_dec b a j) as [Hb | Hnb]; simpl; auto.
  destruct (Hstuck j a Hb) as [Hrej | [j' [[Hacc | Hcont] Hb_j]]];
  repeat (erewrite transition_output_unique; eauto; simpl); auto.
  - now apply CFGKATExpressionDynamicsAssertFalse.
  - now apply CFGKATExpressionDynamicsAssertFalse.
Qed.

Lemma acc_cont_loop_invariant_to_l11_premise
  (e : CFGKATExpression)
  (c : CFGKATTest)
  :
  acc_cont_loop_invariant e c ->
  CFGKATL11Premise e c.
Proof.
  intro Hinv.
  apply stuck_l11_premise.
  now apply acc_cont_loop_invariant_stuck.
Qed.

Lemma largest_loop_invariant_l11_premise
  (e : CFGKATExpression)
  (b : CFGKATTest)
  :
  CFGKATL11Premise e (b and C+[e, b]).
Proof.
  apply acc_cont_loop_invariant_to_l11_premise.
  apply guarded_largest_loop_invariant_test_acc_cont_invariant.
Qed.
