Require Import Stdlib.Program.Equality.
Require Import Stdlib.Logic.FunctionalExtensionality.
From Stdlib Require Import Lists.List.

From CFGKAT.Completeness Require Export Completeness.
From CFGKAT.Soundness Require Import AssignmentLaws.

Import ListNotations.

Local Open Scope cfgkat_scope.

Fixpoint ghost_erase
  (x : IndicatorVariable)
  (e : CFGKATExpression)
  : CFGKATExpression :=
  match e with
  | CFGKATAssert b => CFGKATAssert b
  | CFGKATAction p => CFGKATAction p
  | CFGKATAssign y v =>
      match Var_eq_dec y x with
      | left _ => 1
      | right _ => CFGKATAssign y v
      end
  | CFGKATBreak => CFGKATBreak
  | CFGKATContinue => CFGKATContinue
  | CFGKATReturn => CFGKATReturn
  | CFGKATGoto l => CFGKATGoto l
  | CFGKATChoice b e1 e2 =>
      CFGKATChoice b (ghost_erase x e1) (ghost_erase x e2)
  | CFGKATSequence e1 e2 =>
      CFGKATSequence (ghost_erase x e1) (ghost_erase x e2)
  | CFGKATLoopSeq e1 e2 =>
      CFGKATLoopSeq (ghost_erase x e1) (ghost_erase x e2)
  | CFGKATLoop b body =>
      CFGKATLoop b (ghost_erase x body)
  end.

Definition ghost_erase_env
  (x : IndicatorVariable)
  (E : label_environment CFGKATExpression)
  : label_environment CFGKATExpression.
Proof.
  refine (mk_environment
    (fun l =>
      match E l with
      | Some body => Some (ghost_erase x body)
      | None => None
      end)
    (env_support E)
    _).
  intros l body Hlookup.
  destruct (E l) eqn:HE.
  - eapply env_supported; exact HE.
  - discriminate Hlookup.
Defined.

Definition restore_ghost_value
  (x : IndicatorVariable)
  (ghost : IndicatorValue)
  (i : IndicatorAssignment)
  : IndicatorAssignment :=
  update i x ghost.

Definition restore_ghost_output
  (x : IndicatorVariable)
  (ghost : IndicatorValue)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : CFGKATAutomatonOutputs CFGKATSyntConfiguration :=
  match r with
  | CFGKATAutomatonReject => CFGKATAutomatonReject
  | CFGKATAutomatonAccept i => CFGKATAutomatonAccept (restore_ghost_value x ghost i)
  | CFGKATAutomatonBreak i => CFGKATAutomatonBreak (restore_ghost_value x ghost i)
  | CFGKATAutomatonContinue i => CFGKATAutomatonContinue (restore_ghost_value x ghost i)
  | CFGKATAutomatonReturn => CFGKATAutomatonReturn
  | CFGKATAutomatonJump l i => CFGKATAutomatonJump l (restore_ghost_value x ghost i)
  | CFGKATAutomatonNext p (e, i) =>
      CFGKATAutomatonNext p (ghost_erase x e, restore_ghost_value x ghost i)
  end.

Local Ltac invert_restored_ghost_output H :=
  match type of H with
  | restore_ghost_output _ _ ?r = _ =>
      destruct r as
        [|i_accept|i_break|i_continue| |l_jump i_jump|p_next [e_next i_next]];
      simpl in H; try discriminate; inversion H; subst; clear H
  end.

Local Ltac ghost_reverse_terminal IH Hno head pi ghost ctor :=
  destruct Hno as [Hno1 _];
  destruct (IH head pi ghost eq_refl Hno1)
    as [r_head [Hhead Herase_head]];
  invert_restored_ghost_output Herase_head;
  eexists; split;
  [ eapply ctor; exact Hhead
  | reflexivity ].

Local Ltac ghost_reverse_continuation
    IHhead IHtail Hno head tail pi ghost a tail_i ctor :=
  destruct Hno as [Hno1 Hno2];
  destruct (IHhead head pi ghost eq_refl Hno1)
    as [r_head [Hhead Herase_head]];
  invert_restored_ghost_output Herase_head;
  destruct (IHtail tail tail_i ghost eq_refl Hno2)
    as [r_tail [Htail Herase_tail]];
  exists r_tail;
  split;
  [ exact (ctor a pi tail_i head tail r_tail Hhead Htail)
  | exact Herase_tail ].

Fixpoint expression_does_not_test_indicator
  (x : IndicatorVariable)
  (e : CFGKATExpression)
  : Prop :=
  match e with
  | CFGKATAssert b => test_indicator_free x b
  | CFGKATAction _ => True
  | CFGKATAssign _ _ => True
  | CFGKATBreak => True
  | CFGKATContinue => True
  | CFGKATReturn => True
  | CFGKATGoto _ => True
  | CFGKATChoice b e1 e2 =>
      test_indicator_free x b /\
      expression_does_not_test_indicator x e1 /\
      expression_does_not_test_indicator x e2
  | CFGKATSequence e1 e2 =>
      expression_does_not_test_indicator x e1 /\
      expression_does_not_test_indicator x e2
  | CFGKATLoopSeq e1 e2 =>
      expression_does_not_test_indicator x e1 /\
      expression_does_not_test_indicator x e2
  | CFGKATLoop b body =>
      test_indicator_free x b /\
      expression_does_not_test_indicator x body
  end.

Definition env_all
  (P : CFGKATExpression -> Prop)
  (E : label_environment CFGKATExpression)
  : Prop :=
  forall l body, E l = Some body -> P body.

Definition env_does_not_test_indicator
  (x : IndicatorVariable)
  (E : label_environment CFGKATExpression)
  : Prop :=
  env_all (expression_does_not_test_indicator x) E.

Local Ltac ghost_forward_unary ctor IH Hno ghost :=
  destruct Hno as [He1 _]; apply ctor; exact (IH He1 ghost).

Local Ltac ghost_forward_binary ctor IH1 IH2 Hno ghost :=
  destruct Hno as [He1 He2]; eapply ctor;
  [exact (IH1 He1 ghost) | exact (IH2 He2 ghost)].

Local Lemma semanticlemmaindrem
  (x : IndicatorVariable)
  (s : CFGKATSyntConfiguration)
  (a : Atom)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  expression_does_not_test_indicator x (fst s) ->
  CFGKATExpressionFiniteDynamics s a r ->
  forall ghost,
    CFGKATExpressionFiniteDynamics
      (ghost_erase x (fst s), restore_ghost_value x ghost (snd s)) a
      (restore_ghost_output x ghost r).
Proof.
  intros Hno Hdyn.
  revert Hno.
  induction Hdyn; intros Hno ghost; simpl in Hno; simpl.
  - apply CFGKATExpressionFiniteDynamicsAssertTrue.
    apply (proj2 (test_indicator_free_update x b a _ ghost Hno)).
    exact H.
  - destruct (Var_eq_dec x0 x) as [Heq | Hneq].
    + subst x0.
      unfold restore_ghost_value.
      rewrite update_shadow.
      apply CFGKATExpressionFiniteDynamicsAssertTrue.
      exact I.
    + simpl.
      unfold restore_ghost_value.
      rewrite update_commute by congruence.
      apply CFGKATExpressionFiniteDynamicsAssign.
  - apply CFGKATExpressionFiniteDynamicsAction.
  - apply CFGKATExpressionFiniteDynamicsBreak.
  - apply CFGKATExpressionFiniteDynamicsContinue.
  - apply CFGKATExpressionFiniteDynamicsReturn.
  - apply CFGKATExpressionFiniteDynamicsGoto.
  - destruct Hno as [Hb [He1 He2]].
    apply CFGKATExpressionFiniteDynamicsChoiceLeft.
    + apply (proj2 (test_indicator_free_update x b a _ ghost Hb)).
      exact H.
    + exact (IHHdyn He1 ghost).
  - destruct Hno as [Hb [He1 He2]].
    apply CFGKATExpressionFiniteDynamicsChoiceRight.
    + intro Htest.
      apply H.
      apply (proj1 (test_indicator_free_update x b a _ ghost Hb)).
      exact Htest.
    + exact (IHHdyn He2 ghost).
  - ghost_forward_binary CFGKATExpressionFiniteDynamicsSequenceSkip
      IHHdyn1 IHHdyn2 Hno ghost.
  - ghost_forward_unary CFGKATExpressionFiniteDynamicsSequenceReject
      IHHdyn Hno ghost.
  - ghost_forward_unary CFGKATExpressionFiniteDynamicsSequenceReturn
      IHHdyn Hno ghost.
  - ghost_forward_unary CFGKATExpressionFiniteDynamicsSequenceBreak
      IHHdyn Hno ghost.
  - ghost_forward_unary CFGKATExpressionFiniteDynamicsSequenceContinue
      IHHdyn Hno ghost.
  - ghost_forward_unary CFGKATExpressionFiniteDynamicsSequenceJump
      IHHdyn Hno ghost.
  - ghost_forward_unary CFGKATExpressionFiniteDynamicsSequenceNext
      IHHdyn Hno ghost.
  - ghost_forward_binary CFGKATExpressionFiniteDynamicsLoopSeqSkip
      IHHdyn1 IHHdyn2 Hno ghost.
  - ghost_forward_unary CFGKATExpressionFiniteDynamicsLoopSeqReject
      IHHdyn Hno ghost.
  - ghost_forward_unary CFGKATExpressionFiniteDynamicsLoopSeqReturn
      IHHdyn Hno ghost.
  - ghost_forward_unary CFGKATExpressionFiniteDynamicsLoopSeqBreak
      IHHdyn Hno ghost.
  - ghost_forward_binary CFGKATExpressionFiniteDynamicsLoopSeqContinue
      IHHdyn1 IHHdyn2 Hno ghost.
  - ghost_forward_unary CFGKATExpressionFiniteDynamicsLoopSeqJump
      IHHdyn Hno ghost.
  - ghost_forward_unary CFGKATExpressionFiniteDynamicsLoopSeqNext
      IHHdyn Hno ghost.
  - destruct Hno as [Hb He].
    apply CFGKATExpressionFiniteDynamicsLoopGuardTrue.
    + apply (proj2 (test_indicator_free_update x b a _ ghost Hb)).
      exact H.
    + exact (IHHdyn (conj He (conj Hb He)) ghost).
  - destruct Hno as [Hb _].
    apply CFGKATExpressionFiniteDynamicsLoopGuardFalse.
    intro Htest.
    apply H.
    apply (proj1 (test_indicator_free_update x b a _ ghost Hb)).
    exact Htest.
Qed.

Local Lemma semanticlemmaindrem_reverse
  (x : IndicatorVariable)
  (e : CFGKATExpression)
  (pi : IndicatorAssignment)
  (ghost : IndicatorValue)
  (a : Atom)
  (r_erased : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  expression_does_not_test_indicator x e ->
  CFGKATExpressionFiniteDynamics
    (ghost_erase x e, restore_ghost_value x ghost pi) a r_erased ->
  exists r,
    CFGKATExpressionFiniteDynamics (e, pi) a r /\
    restore_ghost_output x ghost r = r_erased.
Proof.
  intros Hno Hdyn.
  remember (ghost_erase x e, restore_ghost_value x ghost pi) as s_erased.
  revert e pi ghost Heqs_erased Hno.
  induction Hdyn;
    intros e0 pi ghost Heq Hno;
    destruct e0 as
      [b0 | p0 | y val | | | | l0 | b0 d1 d2
       | d1 d2 | d1 d2 | b0 body];
    simpl in Heq;
    try (destruct (Var_eq_dec y x) as [Hyx | Hyx];
         simpl in Heq; try discriminate);
    try discriminate.
  - injection Heq as Hb Hi. subst b0 i.
    exists (CFGKATAutomatonAccept pi). split.
    + apply CFGKATExpressionFiniteDynamicsAssertTrue.
      apply (proj1 (test_indicator_free_update x b a pi ghost Hno)).
      exact H.
    + reflexivity.
  - injection Heq as Hb Hi. subst y b i.
    exists (CFGKATAutomatonAccept (update pi x val)).
    split; [apply CFGKATExpressionFiniteDynamicsAssign |].
    simpl. unfold restore_ghost_value. rewrite update_shadow. reflexivity.
  - injection Heq as Hy Hv Hi. subst y val i.
    exists (CFGKATAutomatonAccept (update pi x0 v)).
    split; [apply CFGKATExpressionFiniteDynamicsAssign |].
    simpl. unfold restore_ghost_value. rewrite update_commute by congruence.
    reflexivity.
  - injection Heq as Hp Hi. subst p0 i.
    exists (CFGKATAutomatonNext p (1, pi)).
    split; [apply CFGKATExpressionFiniteDynamicsAction | reflexivity].
  - injection Heq as Hi. subst i.
    exists (CFGKATAutomatonBreak pi).
    split; [apply CFGKATExpressionFiniteDynamicsBreak | reflexivity].
  - injection Heq as Hi. subst i.
    exists (CFGKATAutomatonContinue pi).
    split; [apply CFGKATExpressionFiniteDynamicsContinue | reflexivity].
  - injection Heq as Hi. subst i.
    exists CFGKATAutomatonReturn.
    split; [apply CFGKATExpressionFiniteDynamicsReturn | reflexivity].
  - injection Heq as Hl Hi. subst l0 i.
    exists (CFGKATAutomatonJump l pi).
    split; [apply CFGKATExpressionFiniteDynamicsGoto | reflexivity].
  - injection Heq as Hb He1 He2 Hi. subst b0 i e1 e2.
    destruct Hno as [Htest [Hno1 Hno2]].
    destruct (IHHdyn d1 pi ghost eq_refl Hno1) as [r0 [Hr0 Herase]].
    exists r0. split.
    + eapply CFGKATExpressionFiniteDynamicsChoiceLeft.
      * apply (proj1 (test_indicator_free_update x b a pi ghost Htest)).
        exact H.
      * exact Hr0.
    + exact Herase.
  - injection Heq as Hb He1 He2 Hi. subst b0 i e1 e2.
    destruct Hno as [Htest [Hno1 Hno2]].
    destruct (IHHdyn d2 pi ghost eq_refl Hno2) as [r0 [Hr0 Herase]].
    exists r0. split.
    + eapply CFGKATExpressionFiniteDynamicsChoiceRight.
      * intro Htest_pi.
        apply H.
        apply (proj2 (test_indicator_free_update x b a pi ghost Htest)).
        exact Htest_pi.
      * exact Hr0.
    + exact Herase.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_continuation
      IHHdyn1 IHHdyn2 Hno d1 d2 pi ghost a i_accept
      CFGKATExpressionFiniteDynamicsSequenceSkip.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_terminal
      IHHdyn Hno d1 pi ghost
      CFGKATExpressionFiniteDynamicsSequenceReject.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_terminal
      IHHdyn Hno d1 pi ghost
      CFGKATExpressionFiniteDynamicsSequenceReturn.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_terminal
      IHHdyn Hno d1 pi ghost
      CFGKATExpressionFiniteDynamicsSequenceBreak.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_terminal
      IHHdyn Hno d1 pi ghost
      CFGKATExpressionFiniteDynamicsSequenceContinue.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_terminal
      IHHdyn Hno d1 pi ghost
      CFGKATExpressionFiniteDynamicsSequenceJump.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_terminal
      IHHdyn Hno d1 pi ghost
      CFGKATExpressionFiniteDynamicsSequenceNext.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_continuation
      IHHdyn1 IHHdyn2 Hno d1 d2 pi ghost a i_accept
      CFGKATExpressionFiniteDynamicsLoopSeqSkip.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_terminal
      IHHdyn Hno d1 pi ghost
      CFGKATExpressionFiniteDynamicsLoopSeqReject.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_terminal
      IHHdyn Hno d1 pi ghost
      CFGKATExpressionFiniteDynamicsLoopSeqReturn.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_terminal
      IHHdyn Hno d1 pi ghost
      CFGKATExpressionFiniteDynamicsLoopSeqBreak.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_continuation
      IHHdyn1 IHHdyn2 Hno d1 d2 pi ghost a i_continue
      CFGKATExpressionFiniteDynamicsLoopSeqContinue.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_terminal
      IHHdyn Hno d1 pi ghost
      CFGKATExpressionFiniteDynamicsLoopSeqJump.
  - injection Heq as He1 He2 Hi. subst i e1 e2.
    ghost_reverse_terminal
      IHHdyn Hno d1 pi ghost
      CFGKATExpressionFiniteDynamicsLoopSeqNext.
  - injection Heq as Hb Hbody Hi. subst b0 i e.
    destruct Hno as [Htest Hbody_no].
    destruct (IHHdyn (body |> while b do body) pi ghost eq_refl)
      as [r0 [Hr0 Herase]].
    + simpl. split; [exact Hbody_no | split; assumption].
    + exists r0. split.
      * apply CFGKATExpressionFiniteDynamicsLoopGuardTrue.
        -- apply (proj1 (test_indicator_free_update x b a pi ghost Htest)).
           exact H.
        -- exact Hr0.
      * exact Herase.
  - injection Heq as Hb Hbody Hi. subst b0 i.
    destruct Hno as [Htest _].
    exists (CFGKATAutomatonAccept pi). split.
    + apply CFGKATExpressionFiniteDynamicsLoopGuardFalse.
      intro Htest_pi.
      apply H.
      apply (proj2 (test_indicator_free_update x b a pi ghost Htest)).
      exact Htest_pi.
    + reflexivity.
Qed.

Local Lemma semanticlemmaindrem_dynamics
  (x : IndicatorVariable)
  (e : CFGKATExpression)
  (pi : IndicatorAssignment)
  (a : Atom)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  expression_does_not_test_indicator x e ->
  CFGKATExpressionDynamics (e, pi) a r ->
  forall ghost,
    CFGKATExpressionDynamics
      (ghost_erase x e, restore_ghost_value x ghost pi) a
      (restore_ghost_output x ghost r).
Proof.
  intros Hno Hdyn ghost.
  inversion Hdyn; subst.
  - apply CFGKATExpressionDynamicsFinite.
    exact (semanticlemmaindrem x (e, pi) a r Hno H ghost).
  - apply CFGKATExpressionDynamicsDefaultReject.
    intros r_erased Hfin_erased.
    destruct (semanticlemmaindrem_reverse x e pi ghost a r_erased Hno Hfin_erased)
      as [r0 [Hfin0 _]].
    unfold CFGKATExpressionNoFiniteResult in H.
    exact (H r0 Hfin0).
Qed.

Fixpoint no_break_continue
  (e : CFGKATExpression)
  : Prop :=
  match e with
  | CFGKATBreak => False
  | CFGKATContinue => False
  | CFGKATChoice _ e1 e2 =>
      no_break_continue e1 /\ no_break_continue e2
  | CFGKATSequence e1 e2 =>
      no_break_continue e1 /\ no_break_continue e2
  | CFGKATLoopSeq e1 e2 =>
      no_break_continue e1 /\ no_break_continue e2
  | CFGKATLoop _ body =>
      no_break_continue body
  | _ => True
  end.

Inductive well_nested : CFGKATExpression -> Prop :=
| WN_base :
    forall e,
      no_break_continue e ->
      well_nested e
| WN_loopseq :
    forall f w,
      well_nested w ->
      well_nested (f |> w)
| WN_loop :
    forall b f,
      well_nested (while b do f)
| WN_seq :
    forall w v,
      well_nested w ->
      well_nested v ->
      well_nested (w ;; v)
| WN_choice :
    forall b w v,
      well_nested w ->
      well_nested v ->
      well_nested (if b then w else v).

Definition well_nested_env
  (E : label_environment CFGKATExpression)
  : Prop :=
  env_all well_nested E.

Definition ends_with_return
  (e : CFGKATExpression)
  : Prop :=
  exists prefix, e = prefix ;; return.

Definition no_free_goto_expr
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  : Prop :=
  forall l, contains_goto l e -> exists body, E l = Some body.

Definition no_free_goto_env
  (E : label_environment CFGKATExpression)
  : Prop :=
  forall l body, E l = Some body -> no_free_goto_expr E body.

Definition no_break_or_continue_output
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : Prop :=
  (forall i, r <> CFGKATAutomatonBreak i) /\
  (forall i, r <> CFGKATAutomatonContinue i).

Definition well_nested_output_safe
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : Prop :=
  no_break_or_continue_output r.

Local Lemma well_nested_sequence_inv
  (e f : CFGKATExpression)
  :
  well_nested (e ;; f) ->
  well_nested e /\ well_nested f.
Proof.
  intro Hwn.
  inversion Hwn; subst; try discriminate.
  - simpl in H. destruct H as [He Hf].
    split; apply WN_base; assumption.
  - split; assumption.
Qed.

Local Lemma well_nested_choice_inv
  (b : CFGKATTest)
  (e f : CFGKATExpression)
  :
  well_nested (if b then e else f) ->
  well_nested e /\ well_nested f.
Proof.
  intro Hwn.
  inversion Hwn; subst; try discriminate.
  - simpl in H. destruct H as [He Hf].
    split; apply WN_base; assumption.
  - split; assumption.
Qed.

Local Lemma well_nested_loopseq_second_inv
  (e f : CFGKATExpression)
  :
  well_nested (e |> f) ->
  well_nested f.
Proof.
  intro Hwn.
  inversion Hwn; subst; try discriminate.
  - simpl in H. destruct H as [_ Hf].
    apply WN_base. exact Hf.
  - exact H0.
Qed.

Ltac solve_well_nested_safe_base :=
  unfold well_nested_output_safe,
         no_break_or_continue_output;
  repeat split; intros j Hbad; discriminate Hbad.

Local Lemma well_nested_output_safe_step
  (s : CFGKATSyntConfiguration)
  (a : Atom)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  well_nested (fst s) ->
  CFGKATExpressionFiniteDynamics s a r ->
  well_nested_output_safe r.
Proof.
  intros Hwn Hdyn.
  revert Hwn.
  induction Hdyn; intro Hwn.
  - solve_well_nested_safe_base.
  - solve_well_nested_safe_base.
  - solve_well_nested_safe_base.
  - dependent destruction Hwn; simpl in *; contradiction.
  - dependent destruction Hwn; simpl in *; contradiction.
  - solve_well_nested_safe_base.
  - solve_well_nested_safe_base.
  - destruct (well_nested_choice_inv b e1 e2 Hwn) as [He1 _].
    exact (IHHdyn He1).
  - destruct (well_nested_choice_inv b e1 e2 Hwn) as [_ He2].
    exact (IHHdyn He2).
  - destruct (well_nested_sequence_inv e1 e2 Hwn) as [_ He2].
    exact (IHHdyn2 He2).
  - destruct (well_nested_sequence_inv e1 e2 Hwn) as [He1 _].
    exact (IHHdyn He1).
  - destruct (well_nested_sequence_inv e1 e2 Hwn) as [He1 _].
    exact (IHHdyn He1).
  - destruct (well_nested_sequence_inv e1 e2 Hwn) as [He1 _].
    destruct (IHHdyn He1) as [Hno_break _].
    exfalso. apply (Hno_break i'). reflexivity.
  - destruct (well_nested_sequence_inv e1 e2 Hwn) as [He1 _].
    destruct (IHHdyn He1) as [_ Hno_continue].
    exfalso. apply (Hno_continue i'). reflexivity.
  - destruct (well_nested_sequence_inv e1 e2 Hwn) as [He1 _].
    exact (IHHdyn He1).
  - destruct (well_nested_sequence_inv e1 e2 Hwn) as [He1 He2].
    solve_well_nested_safe_base.
  - exact (IHHdyn2 (well_nested_loopseq_second_inv e1 e2 Hwn)).
  - solve_well_nested_safe_base.
  - solve_well_nested_safe_base.
  - solve_well_nested_safe_base.
  - exact (IHHdyn2 (well_nested_loopseq_second_inv e1 e2 Hwn)).
  - solve_well_nested_safe_base.
  - solve_well_nested_safe_base.
  - apply IHHdyn.
    apply WN_loopseq.
    apply WN_loop.
  - solve_well_nested_safe_base.
Qed.

Local Lemma expression_does_not_test_indicator_next
  (x : IndicatorVariable)
  (e e' : CFGKATExpression)
  (pi i' : IndicatorAssignment)
  (a : Atom)
  (p : Action)
  :
  expression_does_not_test_indicator x e ->
  CFGKATExpressionFiniteDynamics (e, pi) a
    (CFGKATAutomatonNext p (e', i')) ->
  expression_does_not_test_indicator x e'.
Proof.
  intros Hno Hdyn.
  revert Hno.
  dependent induction Hdyn; intro Hno; simpl in Hno; try discriminate.
  - exact I.
  - destruct Hno as [_ [Hno1 _]].
    eapply IHHdyn; eauto.
  - destruct Hno as [_ [_ Hno2]].
    eapply IHHdyn; eauto.
  - destruct Hno as [_ Hno2].
    eapply IHHdyn2; eauto.
  - destruct Hno as [Hno1 Hno2].
    simpl. split.
    + eapply IHHdyn; eauto.
    + exact Hno2.
  - destruct Hno as [_ Hno2].
    eapply IHHdyn2; eauto.
  - destruct Hno as [_ Hno2].
    eapply IHHdyn2; eauto.
  - destruct Hno as [Hno1 Hno2].
    simpl. split.
    + eapply IHHdyn; eauto.
    + exact Hno2.
  - destruct Hno as [Hb Hbody].
    eapply IHHdyn; eauto.
    simpl. split; [exact Hbody | split; assumption].
Qed.

Local Lemma well_nested_next
  (e e' : CFGKATExpression)
  (pi i' : IndicatorAssignment)
  (a : Atom)
  (p : Action)
  :
  well_nested e ->
  CFGKATExpressionFiniteDynamics (e, pi) a
    (CFGKATAutomatonNext p (e', i')) ->
  well_nested e'.
Proof.
  intros Hwn Hdyn.
  revert Hwn.
  dependent induction Hdyn; intro Hwn; try discriminate.
  - apply WN_base. exact I.
  - destruct (well_nested_choice_inv b e1 e2 Hwn) as [He1 _].
    eapply IHHdyn; eauto.
  - destruct (well_nested_choice_inv b e1 e2 Hwn) as [_ He2].
    eapply IHHdyn; eauto.
  - destruct (well_nested_sequence_inv e1 e2 Hwn) as [_ He2].
    eapply IHHdyn2; eauto.
  - destruct (well_nested_sequence_inv e1 e2 Hwn) as [He1 He2].
    apply WN_seq.
    + eapply IHHdyn; eauto.
    + exact He2.
  - eapply IHHdyn2.
    + reflexivity.
    + reflexivity.
    + exact (well_nested_loopseq_second_inv e1 e2 Hwn).
  - eapply IHHdyn2.
    + reflexivity.
    + reflexivity.
    + exact (well_nested_loopseq_second_inv e1 e2 Hwn).
  - apply WN_loopseq.
    exact (well_nested_loopseq_second_inv e1 e2 Hwn).
  - eapply IHHdyn.
    + reflexivity.
    + reflexivity.
    + apply WN_loopseq. apply WN_loop.
Qed.

Lemma nestinglem
  (s : CFGKATSyntConfiguration)
  (a : Atom)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  well_nested (fst s) ->
  CFGKATExpressionFiniteDynamics s a r ->
  well_nested_output_safe r /\
    match r with
    | CFGKATAutomatonNext _ (e', _) => well_nested e'
    | _ => True
    end.
Proof.
  intros Hwn Hdyn.
  split.
  - eapply well_nested_output_safe_step; eauto.
  - destruct s as [e pi].
    destruct r as
      [|i_accept|i_break|i_continue| |l_jump i_jump|p [e' i']];
      simpl; try exact I.
    eapply well_nested_next; eauto.
Qed.

Local Lemma ends_with_return_no_accept
  (e : CFGKATExpression)
  (pi i' : IndicatorAssignment)
  (a : Atom)
  :
  ends_with_return e ->
  ~ CFGKATExpressionFiniteDynamics (e, pi) a
      (CFGKATAutomatonAccept i').
Proof.
  intros [prefix ->] Hdyn.
  dependent destruction Hdyn.
  - dependent destruction Hdyn2.
Qed.

Local Lemma ends_with_return_next
  (e e' : CFGKATExpression)
  (pi i' : IndicatorAssignment)
  (a : Atom)
  (p : Action)
  :
  ends_with_return e ->
  CFGKATExpressionFiniteDynamics (e, pi) a
    (CFGKATAutomatonNext p (e', i')) ->
  ends_with_return e'.
Proof.
  intros [prefix ->] Hdyn.
  dependent destruction Hdyn.
  - dependent destruction Hdyn2.
  - exists e1'. reflexivity.
Qed.

Local Lemma no_free_goto_expr_next
  (E : label_environment CFGKATExpression)
  (e e' : CFGKATExpression)
  (pi i' : IndicatorAssignment)
  (a : Atom)
  (p : Action)
  :
  no_free_goto_expr E e ->
  CFGKATExpressionFiniteDynamics (e, pi) a
    (CFGKATAutomatonNext p (e', i')) ->
  no_free_goto_expr E e'.
Proof.
  intros Hfree Hdyn l Hcontains.
  apply Hfree.
  eapply CFGKATExpressionDynamicsFinite in Hdyn.
  eapply contains_goto_next_back in Hdyn as Hback; eauto.
Qed.

Lemma jump_output_contains_goto
  (l : Label)
  (e : CFGKATExpression)
  (a : Atom)
  (i j : IndicatorAssignment)
  :
  transition_output e a i = CFGKATAutomatonJump l j ->
  contains_goto l e.
Proof.
  intro Hjump.
  pose proof
    (proj2 (transition_output_exact e a i (CFGKATAutomatonJump l j))
      Hjump) as Hdyn.
  eapply contains_goto_jump_back; eauto.
Qed.

Lemma no_contains_goto_no_jump_output
  (l : Label)
  (e : CFGKATExpression)
  (a : Atom)
  (i j : IndicatorAssignment)
  :
  ~ contains_goto l e ->
  transition_output e a i = CFGKATAutomatonJump l j ->
  False.
Proof.
  intros Hfresh Hjump.
  exact (Hfresh (jump_output_contains_goto l e a i j Hjump)).
Qed.

Definition ghost_variable_elimination_side_conditions
  (x : IndicatorVariable)
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  : Prop :=
  expression_does_not_test_indicator x e /\
  env_does_not_test_indicator x E /\
  well_nested e /\
  well_nested_env E /\
  ends_with_return e /\
  env_all ends_with_return E /\
  no_free_goto_expr E e /\
  no_free_goto_env E.

Definition ghost_state_side
  (x : IndicatorVariable)
  (E : label_environment CFGKATExpression)
  (s : CFGKATSyntConfiguration)
  : Prop :=
  expression_does_not_test_indicator x (fst s) /\
  well_nested (fst s) /\
  ends_with_return (fst s) /\
  no_free_goto_expr E (fst s).

Definition ghost_related_state
  (x : IndicatorVariable)
  (E : label_environment CFGKATExpression)
  (s t : CFGKATSyntConfiguration)
  : Prop :=
  exists ghost,
    t = (ghost_erase x (fst s), restore_ghost_value x ghost (snd s)) /\
    ghost_state_side x E s.

Local Lemma ghost_erasure_strong_bisimulation
  (x : IndicatorVariable)
  (E : label_environment CFGKATExpression)
  :
  env_does_not_test_indicator x E ->
  well_nested_env E ->
  env_all ends_with_return E ->
  no_free_goto_env E ->
  @CFGKATStrongBisimulation
    CFGKATExpressionAutomaton
    CFGKATExpressionAutomaton
    [lift E]
    [lift (ghost_erase_env x E)].
Proof.
  intros Henv_no Henv_wn Henv_ret Henv_free.
  refine {|
    cfgkat_strong_relation := ghost_related_state x E;
    cfgkat_strong_bisimulation_cond := _
  |}.
  intros [e1 pi1] s2 a HR.
  destruct HR as [ghost [Hs2 [Hno [Hwn [Hret Hfree]]]]].
  subst s2.
  destruct (cfgkat_synt_dynamics_total CFGKATExpressionAutomaton (e1, pi1) a)
    as [zeta1 Hleft].
  pose proof
    (semanticlemmaindrem_dynamics x e1 pi1 a zeta1 Hno Hleft ghost)
    as Hmatch.
  destruct zeta1 as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p next_state].
  cbn [restore_ghost_output] in Hmatch.
  - strong_halt_output
      (@CFGKATAutomatonReject CFGKATSyntConfiguration) Hleft Hmatch.
  - exfalso.
    apply (ends_with_return_no_accept e1 pi1 i_accept a Hret).
    eapply cfgkat_dynamics_nonreject_finite; [discriminate | exact Hleft].
  - exfalso.
    pose proof
      (nestinglem (e1, pi1) a (CFGKATAutomatonBreak i_break) Hwn
        (cfgkat_dynamics_nonreject_finite
          (e1, pi1) a (CFGKATAutomatonBreak i_break)
          ltac:(discriminate) Hleft)) as [Hsafe _].
    unfold well_nested_output_safe, no_break_or_continue_output in Hsafe.
    destruct Hsafe as [Hno_break _].
    apply (Hno_break i_break). reflexivity.
  - exfalso.
    pose proof
      (nestinglem (e1, pi1) a (CFGKATAutomatonContinue i_continue) Hwn
        (cfgkat_dynamics_nonreject_finite
          (e1, pi1) a (CFGKATAutomatonContinue i_continue)
          ltac:(discriminate) Hleft)) as [Hsafe _].
    unfold well_nested_output_safe, no_break_or_continue_output in Hsafe.
    destruct Hsafe as [_ Hno_continue].
    apply (Hno_continue i_continue). reflexivity.
  - change (CFGKATExpressionDynamics
      (ghost_erase x e1, restore_ghost_value x ghost pi1) a
      (@CFGKATAutomatonReturn CFGKATSyntConfiguration)) in Hmatch.
    strong_halt_output
      (@CFGKATAutomatonReturn CFGKATSyntConfiguration) Hleft Hmatch.
  - assert (Hfin :
      CFGKATExpressionFiniteDynamics (e1, pi1) a
        (CFGKATAutomatonJump l_jump i_jump)).
    {
      eapply cfgkat_dynamics_nonreject_finite; [discriminate | exact Hleft].
    }
    destruct (Hfree l_jump) as [body Hbody].
    {
      eapply jump_output_contains_goto.
      apply transition_output_exact.
      apply CFGKATExpressionDynamicsFinite.
      exact Hfin.
    }
    eapply CFGKATStrongStepSilent with
      (x1' := (body, i_jump))
      (x2' := (ghost_erase x body, restore_ghost_value x ghost i_jump)).
    + eapply CFGKATSilentBoundJump with (ys := []).
      * simpl. exact Hleft.
      * apply lift_label_some. exact Hbody.
    + eapply CFGKATSilentBoundJump with (ys := []).
      * simpl. exact Hmatch.
      * apply lift_label_some.
        unfold ghost_erase_env, mk_environment.
        simpl. rewrite Hbody. reflexivity.
    + exists ghost.
      split; [reflexivity |].
      repeat split.
      * unfold env_does_not_test_indicator, env_all in Henv_no.
        eapply Henv_no. exact Hbody.
      * unfold well_nested_env, env_all in Henv_wn.
        eapply Henv_wn. exact Hbody.
      * unfold env_all in Henv_ret.
        eapply Henv_ret. exact Hbody.
      * unfold no_free_goto_env in Henv_free.
        eapply Henv_free. exact Hbody.
  - destruct next_state as [e_next i_next].
    change (CFGKATExpressionDynamics
      (ghost_erase x e1, restore_ghost_value x ghost pi1) a
      (CFGKATAutomatonNext p
        (ghost_erase x e_next, restore_ghost_value x ghost i_next))) in Hmatch.
    assert (Hfin :
      CFGKATExpressionFiniteDynamics (e1, pi1) a
        (CFGKATAutomatonNext p (e_next, i_next))).
    {
      eapply cfgkat_dynamics_nonreject_finite; [discriminate | exact Hleft].
    }
    eapply CFGKATStrongStepNext.
    + lift_raw_transition Hleft.
    + lift_raw_transition Hmatch.
    + exists ghost.
      split; [reflexivity |].
      repeat split.
      * eapply expression_does_not_test_indicator_next; eauto.
      * eapply well_nested_next; eauto.
      * eapply ends_with_return_next; eauto.
      * eapply no_free_goto_expr_next; eauto.
Defined.

Local Lemma ghost_variable_elimination_updated_assignments_bridge
  (x : IndicatorVariable)
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  :
  ghost_variable_elimination_side_conditions x E e ->
  forall pi ghost,
    (e, pi) ~[lift E, lift (ghost_erase_env x E)]
      (ghost_erase x e, restore_ghost_value x ghost pi).
Proof.
  intros
    [Hno [Henv_no [Hwn [Henv_wn [Hret [Henv_ret [Hfree Henv_free]]]]]]]
    pi ghost.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar.
  exists
    (@strong_bisim_to_bisim
      CFGKATExpressionAutomaton
      CFGKATExpressionAutomaton
      [lift E]
      [lift (ghost_erase_env x E)]
      (ghost_erasure_strong_bisimulation
        x E Henv_no Henv_wn Henv_ret Henv_free)).
  exists ghost.
  split; [reflexivity |].
  repeat split; assumption.
Qed.

Theorem ghost_variable_elimination
  (x : IndicatorVariable)
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  :
  ghost_variable_elimination_side_conditions x E e ->
  E |- e == ghost_erase x e -| ghost_erase_env x E.
Proof.
  intro Hside.
  apply completeness.
  intro pi.
  pose proof
    (ghost_variable_elimination_updated_assignments_bridge
      x E e Hside pi (pi x)) as Hbridge.
  unfold restore_ghost_value in Hbridge.
  rewrite update_noop in Hbridge.
  exact Hbridge.
Qed.
