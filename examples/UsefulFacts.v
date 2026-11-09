From CFGKAT.Examples Require Export GhostVariableElimination.
From CFGKAT.Semantics Require Export LabelExtraction.
From CFGKAT.Soundness Require Export Soundness.
From CFGKAT.Completeness Require Import gtnflem1 gtnfthm.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Program.Equality.
Require Import Stdlib.micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.

Local Open Scope cfgkat_scope.
Local Open Scope cfgkat_setoid_scope.




Fixpoint expression_does_not_assign_indicator
  (x : IndicatorVariable)
  (e : CFGKATExpression)
  : Prop :=
  match e with
  | CFGKATAssert _ => True
  | CFGKATAction _ => True
  | CFGKATAssign y _ => y <> x
  | CFGKATBreak => True
  | CFGKATContinue => True
  | CFGKATReturn => True
  | CFGKATGoto _ => True
  | CFGKATChoice _ e1 e2 =>
      expression_does_not_assign_indicator x e1 /\
      expression_does_not_assign_indicator x e2
  | CFGKATSequence e1 e2 =>
      expression_does_not_assign_indicator x e1 /\
      expression_does_not_assign_indicator x e2
  | CFGKATLoopSeq e1 e2 =>
      expression_does_not_assign_indicator x e1 /\
      expression_does_not_assign_indicator x e2
  | CFGKATLoop _ body =>
      expression_does_not_assign_indicator x body
  end.

Notation "e 'dna' x" := (expression_does_not_assign_indicator x e)
  (at level 70).

Local Lemma empty_bisim_transition_lifted
  (s t : CFGKATSyntConfiguration)
  (a : Atom)
  :
  s ~~ t ->
  lifted_relation
    (fun s' t' => s' ~~ t')
    (transition_output (fst s) a (snd s))
    (transition_output (fst t) a (snd t)).
Proof.
  intro Hsim.
  destruct Hsim as [B HB].
  destruct s as [es i_s].
  destruct t as [et i_t].
  remember (transition_output es a i_s) as rs eqn:Hrs.
  remember (transition_output et a i_t) as rt eqn:Hrt.
  assert (Hstep :
    lifted_relation (cfgkat_relation B) rs rt).
  {
    pose proof
    (cfgkat_bisimulation_step B
      (es, i_s) (et, i_t) a
      rs rt HB) as Hstep.
    apply Hstep.
    - change
        (ResolveCFGKATAutomatonDynamics
          CFGKATExpressionAutomaton
          (CFGKATExpressionDynamics (es, i_s))
          empty_syntactic_context a rs).
      apply resolve_syntactic_empty_identity.
      rewrite Hrs. apply transition_output_spec.
    - change
        (ResolveCFGKATAutomatonDynamics
          CFGKATExpressionAutomaton
          (CFGKATExpressionDynamics (et, i_t))
          empty_syntactic_context a rt).
      apply resolve_syntactic_empty_identity.
      rewrite Hrt. apply transition_output_spec.
  }
  cbn.
  rewrite <- Hrs, <- Hrt.
  destruct Hstep; constructor.
  exists B. assumption.
Qed.


Lemma looptighten_largest
  (e : CFGKATExpression)
  (b : CFGKATTest)
  :
  (while b do e) ==
    (while b do (test (not C+[e, b]) ;; e)).
Proof.
  apply L11lemmaFTloop_unconditional.
Qed.

Local Lemma looptighten_invariant
  (e : CFGKATExpression)
  (b c : CFGKATTest)
  :
  BA_leq c b ->
  acc_cont_loop_invariant e c ->
  (while b do e) ==
    (while b do (test (not c) ;; e)).
Proof.
  intros Hle Hinv.
  eapply L11lemmaFTloop.
  - exact Hle.
  - exact Hinv.
  - intros m Hm.
    cfgkat_rewrite (fundamental_theorem e) at 1.
    unfold fundamental_normal_form.
    apply branchsel_plus.
Qed.


Local Definition singleton_label_context
  (l : Label)
  (body : CFGKATExpression)
  : label_environment CFGKATExpression :=
  @label_extend empty_label_context l body
    ltac:(change (empty_label_context l = None); reflexivity).

Local Lemma singleton_label_context_lookup
  (l : Label)
  (body : CFGKATExpression)
  :
  singleton_label_context l body l = Some body.
Proof.
  unfold singleton_label_context, label_extend, mk_environment.
  cbn.
  destruct (Label_eq_dec l l) as [_ | Hneq].
  - exact eq_refl.
  - contradiction Hneq. reflexivity.
Qed.

Local Lemma singleton_label_context_lookup_some
  (l k : Label)
  (body found : CFGKATExpression)
  :
  singleton_label_context l body k = Some found ->
  k = l /\ found = body.
Proof.
  unfold singleton_label_context, label_extend, empty_label_context,
    mk_environment.
  cbn.
  destruct (Label_eq_dec l k) as [Heq | Hneq].
  - intro Hfound.
    inversion Hfound; subst.
    split; [symmetry |]; reflexivity.
  - intro Hfound. discriminate.
Qed.

Local Lemma singleton_label_context_same_domain
  (l : Label)
  (body1 body2 : CFGKATExpression)
  :
  C7_same_domain
    (singleton_label_context l body1)
    (singleton_label_context l body2).
Proof.
  intro k.
  unfold label_in_dom.
  split; intros [body Hbody].
  - apply singleton_label_context_lookup_some in Hbody.
    destruct Hbody as [Hk _].
    subst k.
    exists body2.
    apply singleton_label_context_lookup.
  - apply singleton_label_context_lookup_some in Hbody.
    destruct Hbody as [Hk _].
    subst k.
    exists body1.
    apply singleton_label_context_lookup.
Qed.

Local Lemma singleton_label_context_guarded
  (l : Label)
  (body : CFGKATExpression)
  :
  guarded l body ->
  C7_guarded (singleton_label_context l body).
Proof.
  intros Hguard k k' found target Hfound Htarget.
  apply singleton_label_context_lookup_some in Hfound.
  apply singleton_label_context_lookup_some in Htarget.
  destruct Hfound as [_ Hfound].
  destruct Htarget as [Hk' _].
  subst k' found.
  exact Hguard.
Qed.

Local Lemma subst_goto_self
  (l : Label)
  (replacement : CFGKATExpression)
  :
  subst_goto l replacement (goto l) = replacement.
Proof.
  simpl.
  destruct (Label_eq_dec l l) as [_ | Hneq].
  - exact eq_refl.
  - contradiction Hneq. reflexivity.
Qed.
Local Fixpoint loop_unroll_exit_n
  (n : nat)
  (b : CFGKATTest)
  (e k r : CFGKATExpression)
  : CFGKATExpression :=
  match n with
  | O => k
  | S n' => if b then e |> loop_unroll_exit_n n' b e k r else r
  end.
Local Lemma loop_unroll_exit_n_rhs
  (l : Label)
  (n : nat)
  (b : CFGKATTest)
  (e r : CFGKATExpression)
  :
  ~ contains_goto l e ->
  ~ contains_goto l r ->
  RHS l (loop_unroll_exit_n n b e (goto l) r).
Proof.
  intros Hfresh Hr.
  induction n as [|n IH]; simpl.
  - apply RHS_goto.
  - apply RHS_choice.
    + apply RHS_loopseq.
      * exact Hfresh.
      * exact IH.
    + apply RHS_no_goto.
      exact Hr.
Qed.
Local Lemma subst_loop_unroll_exit_n
  (l : Label)
  (replacement : CFGKATExpression)
  (n : nat)
  (b : CFGKATTest)
  (e r : CFGKATExpression)
  :
  ~ contains_goto l e ->
  ~ contains_goto l r ->
  subst_goto l replacement (loop_unroll_exit_n n b e (goto l) r) =
    loop_unroll_exit_n n b e replacement r.
Proof.
  intros Hfresh Hr.
  induction n as [|n IH]; simpl.
  - apply subst_goto_self.
  - rewrite (subst_goto_no_goto l replacement e Hfresh).
    rewrite (subst_goto_no_goto l replacement r Hr).
    rewrite IH.
    reflexivity.
Qed.
Local Lemma loop_unroll_exit_n_fixed
  (n : nat)
  (b : CFGKATTest)
  (e g r : CFGKATExpression)
  :
  (if b then e |> g else r) == g ->
  loop_unroll_exit_n (S n) b e g r == g.
Proof.
  intro Hfixed.
  induction n as [|n IH]; simpl.
  - exact Hfixed.
  - cfgkat_rewrite IH.
    exact Hfixed.
Qed.

Local Lemma singleton_label_context_unfold_goto
  (l : Label)
  (body : CFGKATExpression)
  :
  singleton_label_context l body |- body == goto l -|
    singleton_label_context l body.
Proof.
  rewrite <- (subst_goto_self l body) at 2.
  unfold singleton_label_context.
  apply EqC5.
  apply RHS_goto.
Qed.
Local Lemma singleton_label_context_redundant_right
  (l : Label)
  (body e : CFGKATExpression)
  :
  ~ contains_goto l e ->
  empty_label_context |- e == e -|
    singleton_label_context l body.
Proof.
  intro Hfresh.
  assert (Hdisj_empty_singleton :
    label_disjoint empty_label_context (singleton_label_context l body)).
  {
    intros k [found Hfound].
    discriminate.
  }
  replace (singleton_label_context l body) with
      (empty_label_context + singleton_label_context l body).
  2: { apply label_env_cup_empty_l. }
  apply EqSym.
  apply EqC3.
  intros k [found Hfound].
  split.
  - intros k' found' Hfound'.
    discriminate.
  - intro Hcontains.
    apply singleton_label_context_lookup_some in Hfound.
    destruct Hfound as [Hk _].
    subst k.
    exact (Hfresh Hcontains).
Qed.

Local Lemma singleton_label_context_solution
  (l : Label)
  (body g : CFGKATExpression)
  :
  RHS l body ->
  subst_goto l g body == g ->
  singleton_label_context l g |- goto l == body -|
    singleton_label_context l g.
Proof.
  intros Hrhs Hfixed.
  cfgkat_rewrite <- (singleton_label_context_unfold_goto l g).
  cfgkat_rewrite <- (weaken_empty_to_env (singleton_label_context l g)
    (subst_goto l g body) g Hfixed) at 2.
  unfold singleton_label_context.
  apply EqC5.
  exact Hrhs.
Qed.

Local Lemma singleton_unique_contextual
  (l : Label)
  (body g h : CFGKATExpression)
  :
  RHS l body ->
  guarded l body ->
  subst_goto l g body == g ->
  subst_goto l h body == h ->
  singleton_label_context l g |- g == h -|
    singleton_label_context l h.
Proof.
  intros Hrhs Hguard Hg Hh.
  cfgkat_rewrite (singleton_label_context_unfold_goto l g).
  cfgkat_rewrite (@EqC7
    (singleton_label_context l body)
    (singleton_label_context l g)
    (goto l)
    ltac:(
      apply singleton_label_context_same_domain)
    ltac:(
      apply singleton_label_context_guarded; exact Hguard)
    ltac:(
      intros k found Hfound;
      apply singleton_label_context_lookup_some in Hfound;
      destruct Hfound as [Hk Hfound];
      subst k found;
      apply singleton_label_context_solution;
      [exact Hrhs | exact Hg])).
  cfgkat_rewrite <- (@EqC7
    (singleton_label_context l body)
    (singleton_label_context l h)
    (goto l)
    ltac:(
      apply singleton_label_context_same_domain)
    ltac:(
      apply singleton_label_context_guarded; exact Hguard)
    ltac:(
      intros k found Hfound;
      apply singleton_label_context_lookup_some in Hfound;
      destruct Hfound as [Hk Hfound];
      subst k found;
      apply singleton_label_context_solution;
      [exact Hrhs | exact Hh])).
  cfgkat_rewrite <- (singleton_label_context_unfold_goto l h).
  apply EqRefl.
Qed.

Local Lemma singleton_unique_closed
  (l : Label)
  (body g h : CFGKATExpression)
  :
  RHS l body ->
  guarded l body ->
  ~ contains_goto l g ->
  ~ contains_goto l h ->
  subst_goto l g body == g ->
  subst_goto l h body == h ->
  g == h.
Proof.
  intros Hrhs Hguard Hg_fresh Hh_fresh Hg Hh.
  change (cfgkat_equiv (empty_label_context, g) (empty_label_context, h)).
  cfgkat_rewrite (singleton_label_context_redundant_right l g g Hg_fresh).
  cfgkat_rewrite (singleton_unique_contextual l body g h
    Hrhs Hguard Hg Hh).
  cfgkat_rewrite <- (singleton_label_context_redundant_right l h h Hh_fresh).
  apply EqRefl.
Qed.

Local Lemma no_contains_goto_test_sequence
  (l : Label)
  (b : CFGKATTest)
  (e : CFGKATExpression)
  :
  ~ contains_goto l e ->
  ~ contains_goto l (test b ;; e).
Proof.
  intros Hfresh Hcontains.
  destruct Hcontains as [[] | Hcontains].
  exact (Hfresh Hcontains).
Qed.

Local Definition loop_progress
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (m n : At x I^Y)
  : Prop :=
  (m \in b) = true /\
  (m \in largest_loop_invariant_test e b) = false /\
  AtIY_atom n = AtIY_atom m /\
  (transition_output e (AtIY_atom m) (AtIY_assignment m) =
     CFGKATAutomatonAccept (AtIY_assignment n) \/
   transition_output e (AtIY_atom m) (AtIY_assignment m) =
     CFGKATAutomatonContinue (AtIY_assignment n)).


Local Definition path_vertices_test
  (xs : list (At x I^Y))
  : CFGKATTest :=
  fold_TOr (map AtIY_test xs).

Local Lemma eval_path_vertices_test_in
  (xs : list (At x I^Y))
  (a : Atom)
  (i : IndicatorAssignment)
  :
  eval_test (path_vertices_test xs) a i ->
  exists m,
    In m xs /\
    a = AtIY_atom m /\
    i = AtIY_assignment m.
Proof.
  unfold path_vertices_test.
  rewrite eval_fold_TOr.
  intros [t [Ht_in Ht_eval]].
  apply in_map_iff in Ht_in.
  destruct Ht_in as [m [Ht Hm_in]].
  subst t.
  pose proof (eval_AtIY_test_eq m a i Ht_eval) as [Ha Hi].
  exists m.
  repeat split; assumption.
Qed.

Local Lemma eval_path_vertices_test_of_in
  (xs : list (At x I^Y))
  (m : At x I^Y)
  :
  In m xs ->
  eval_test
    (path_vertices_test xs)
    (AtIY_atom m)
    (AtIY_assignment m).
Proof.
  intro Hm.
  unfold path_vertices_test.
  rewrite eval_fold_TOr.
  exists (AtIY_test m).
  split.
  - apply in_map. exact Hm.
  - unfold AtIY_test.
    split.
    + apply eval_atom_to_test.
      intro t. reflexivity.
    + apply eval_complete_test.
      intro y. reflexivity.
Qed.

Local Lemma loop_progress_cycle_no_cycle
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (m : At x I^Y)
  (n : nat)
  :
  ~ loop_cplus_relation_path (loop_progress e b) (S n) m m.
Proof.
  intro Hcycle.
  pose proof
    (loop_cplus_relation_path_to_vertices
      (loop_progress e b) (S n) m m Hcycle)
    as [xs [Hvertices [Hlast Hlen]]].
  assert (Hnonempty : xs <> []).
  {
    destruct xs as [|y ys].
    - simpl in Hlen. discriminate Hlen.
    - discriminate.
  }
  dependent destruction Hcycle.
  set (cycle := m :: xs).
  set (C := path_vertices_test cycle).
  assert (Hcycle_succ :
    forall q,
      In q cycle ->
      exists z, loop_progress e b q z /\ In z cycle).
  {
    intros q Hq.
    unfold cycle in Hq.
    eapply loop_cplus_relation_path_vertices_cycle_successor; eauto.
  }
  assert (HC_le : BA_leq C b).
  {
    unfold C, BA_leq.
    apply Boolean_denotation_completeness.
    unfold CFGKATTestDenotationEquivalent.
    intros a i.
    split.
    - intros [Hb | HC].
      + exact Hb.
      + pose proof (eval_path_vertices_test_in cycle a i HC)
          as [q [Hq [Ha Hi]]].
        pose proof (Hcycle_succ q Hq) as [r [Hqr _]].
        destruct Hqr as [Hq_b _].
        pose proof (in_test_true b q Hq_b) as Hq_b_eval.
        rewrite Ha, Hi.
        exact Hq_b_eval.
    - intro Hb.
      left. exact Hb.
  }
  assert (HC_inv : acc_cont_loop_invariant e C).
  {
    unfold acc_cont_loop_invariant.
    intros a i HC.
    pose proof (eval_path_vertices_test_in cycle a i HC)
      as [q [Hq [Ha Hi]]].
    pose proof (Hcycle_succ q Hq) as [r [Hqr Hr]].
    destruct Hqr as [_ [_ [Hr_atom Hr_out]]].
    subst a i.
    exists (AtIY_assignment r).
    split.
    - exact Hr_out.
    - rewrite <- Hr_atom.
      apply eval_path_vertices_test_of_in.
      exact Hr.
  }
  assert (HC_m : eval_test C (AtIY_atom m) (AtIY_assignment m)).
  {
    apply eval_path_vertices_test_of_in.
    unfold cycle. left. reflexivity.
  }
  pose proof
    (BA_leq_eval C (largest_loop_invariant_test e b)
      (AtIY_atom m) (AtIY_assignment m)
      (largest_loop_invariant_test_largest e b C HC_le HC_inv)
      HC_m)
    as HCplus_m.
  pose proof
    (in_test_of_eval
      (largest_loop_invariant_test e b) m HCplus_m)
    as HCplus_m_true.
  destruct H as [_ [Hm_not_Cplus _]].
  rewrite HCplus_m_true in Hm_not_Cplus.
  discriminate.
Qed.

Local Lemma trimmed_loop_body_accept_progress
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (a : Atom)
  (i j : IndicatorAssignment)
  :
  eval_test b a i ->
  transition_output (test (not largest_loop_invariant_test e b) ;; e) a i =
    CFGKATAutomatonAccept j ->
  loop_progress e b (a, i) (a, j).
Proof.
  intros Hb Hout.
  unfold loop_progress.
  split.
  - apply in_test_of_eval. exact Hb.
  - split.
    + rewrite transition_sequence in Hout.
      rewrite transition_assert in Hout.
      destruct
        (eval_test_dec (not largest_loop_invariant_test e b) a i)
        as [Hnot | Hnot]; simpl in Hout.
      * apply in_test_false_of_not_eval.
        exact Hnot.
      * discriminate.
    + split.
      * exact eq_refl.
      * rewrite transition_sequence in Hout.
      rewrite transition_assert in Hout.
      destruct
          (eval_test_dec (not largest_loop_invariant_test e b) a i)
          as [_ | Hnot]; simpl in Hout.
        -- left. exact Hout.
        -- discriminate.
Qed.

Local Lemma trimmed_loop_body_continue_progress
  (e : CFGKATExpression)
  (b : CFGKATTest)
  (a : Atom)
  (i j : IndicatorAssignment)
  :
  eval_test b a i ->
  transition_output (test (not largest_loop_invariant_test e b) ;; e) a i =
    CFGKATAutomatonContinue j ->
  loop_progress e b (a, i) (a, j).
Proof.
  intros Hb Hout.
  unfold loop_progress.
  split.
  - apply in_test_of_eval. exact Hb.
  - split.
    + rewrite transition_sequence in Hout.
      rewrite transition_assert in Hout.
      destruct
        (eval_test_dec (not largest_loop_invariant_test e b) a i)
        as [Hnot | Hnot]; simpl in Hout.
      * apply in_test_false_of_not_eval.
        exact Hnot.
      * discriminate.
    + split.
      * exact eq_refl.
      * rewrite transition_sequence in Hout.
      rewrite transition_assert in Hout.
      destruct
          (eval_test_dec (not largest_loop_invariant_test e b) a i)
          as [_ | Hnot]; simpl in Hout.
        -- right. exact Hout.
        -- discriminate.
Qed.
Local Lemma loop_unroll_largest_invariant_exit_jump_path
  (l : Label)
  (n : nat)
  (b : CFGKATTest)
  (e r : CFGKATExpression)
  (a : Atom)
  (i j : IndicatorAssignment)
  :
  ~ contains_goto l e ->
  ~ contains_goto l r ->
  transition_output
    (loop_unroll_exit_n n b
      (test (not largest_loop_invariant_test e b) ;; e) (goto l) r)
    a i =
    CFGKATAutomatonJump l j ->
  exists xs,
    length xs = n /\
    loop_cplus_relation_path_vertices (loop_progress e b) (a, i) xs.
Proof.
  intros Hfresh Hr.
  revert a i j.
  induction n as [|n IH]; intros a i j Hjump.
  - simpl in Hjump.
    rewrite transition_goto in Hjump.
    inversion Hjump; subst.
    exists [].
    split.
    + reflexivity.
    + apply LoopCPlusRelationPathVerticesSingle.
  - simpl in Hjump.
    rewrite transition_choice in Hjump.
    destruct (eval_test_dec b a i) as [Hb | Hnb].
    2:{
      exfalso.
      eapply no_contains_goto_no_jump_output.
      - exact Hr.
      - exact Hjump.
    }
    rewrite transition_loopseq in Hjump.
    remember
      (transition_output (test (not largest_loop_invariant_test e b) ;; e) a i)
      as out eqn:Hout.
    destruct out as
      [|i_accept|i_break|i_continue| |l_jump i_jump|p next_state];
      simpl in Hjump.
    + discriminate Hjump.
    + pose proof
        (IH a i_accept j Hjump)
        as [xs [Hlen Hvertices]].
      exists ((a, i_accept) :: xs).
      split.
      * simpl. lia.
      * apply LoopCPlusRelationPathVerticesCons.
        -- apply trimmed_loop_body_accept_progress.
           ++ exact Hb.
           ++ symmetry. exact Hout.
        -- exact Hvertices.
    + discriminate Hjump.
    + pose proof
        (IH a i_continue j Hjump)
        as [xs [Hlen Hvertices]].
      exists ((a, i_continue) :: xs).
      split.
      * simpl. lia.
      * apply LoopCPlusRelationPathVerticesCons.
        -- apply trimmed_loop_body_continue_progress.
           ++ exact Hb.
           ++ symmetry. exact Hout.
        -- exact Hvertices.
    + discriminate Hjump.
    + destruct (Label_eq_dec l_jump l) as [Heq | Hneq].
      * subst l_jump.
        exfalso.
        eapply no_contains_goto_no_jump_output.
        -- apply no_contains_goto_test_sequence. exact Hfresh.
        -- symmetry. exact Hout.
      * inversion Hjump; subst l_jump.
        contradiction.
    + destruct next_state as [e_next i_next].
      discriminate Hjump.
Qed.
Local Lemma loop_largest_invariant_exit_unroll_guarded
  (l : Label)
  (b : CFGKATTest)
  (e r : CFGKATExpression)
  :
  ~ contains_goto l e ->
  ~ contains_goto l r ->
  guarded l
    (loop_unroll_exit_n (S (length all_AtIY)) b
      (test (not largest_loop_invariant_test e b) ;; e)
      (goto l) r).
Proof.
  unfold guarded.
  intros Hfresh Hr a i j Hjump_dyn.
  pose proof
    (transition_output_unique
      (loop_unroll_exit_n (S (length all_AtIY)) b
        (test (not largest_loop_invariant_test e b) ;; e) (goto l) r)
      a i (CFGKATAutomatonJump l j) Hjump_dyn)
    as Hjump.
  pose proof
    (loop_unroll_largest_invariant_exit_jump_path l
      (S (length all_AtIY)) b e r a i j Hfresh Hr Hjump)
    as [xs [Hlen Hvertices]].
  pose proof
    (loop_cplus_relation_path_vertices_length_bound_no_cycle
      (loop_progress e b) all_AtIY (a, i) xs
      ltac:(intros _ [a' i'] _; apply AtIY_in_all)
      (loop_progress_cycle_no_cycle e b)
      Hvertices
      (AtIY_in_all a i))
    as Hbound.
  lia.
Qed.
Local Lemma loop_unique_closed_after_largest_invariant_exit_pair_with_fresh
  (l : Label)
  (b : CFGKATTest)
  (e r g h : CFGKATExpression)
  :
  ~ contains_goto l e ->
  ~ contains_goto l r ->
  ~ contains_goto l g ->
  ~ contains_goto l h ->
  (if b then (test (not largest_loop_invariant_test e b) ;; e) |> g else r) == g ->
  (if b then (test (not largest_loop_invariant_test e b) ;; e) |> h else r) == h ->
  g == h.
Proof.
  intros He_fresh Hr_fresh Hg_fresh Hh_fresh Hg Hh.
  eapply singleton_unique_closed
    with
      (l := l)
      (body :=
        loop_unroll_exit_n (S (length all_AtIY)) b
          (test (not largest_loop_invariant_test e b) ;; e)
          (goto l) r).
  - apply loop_unroll_exit_n_rhs.
    + apply no_contains_goto_test_sequence.
      exact He_fresh.
    + exact Hr_fresh.
  - apply loop_largest_invariant_exit_unroll_guarded;
      assumption.
  - exact Hg_fresh.
  - exact Hh_fresh.
  - rewrite (subst_loop_unroll_exit_n l g
      (S (length all_AtIY)) b
      (test (not largest_loop_invariant_test e b) ;; e) r).
    + apply loop_unroll_exit_n_fixed.
      exact Hg.
    + apply no_contains_goto_test_sequence.
      exact He_fresh.
    + exact Hr_fresh.
  - rewrite (subst_loop_unroll_exit_n l h
      (S (length all_AtIY)) b
      (test (not largest_loop_invariant_test e b) ;; e) r).
    + apply loop_unroll_exit_n_fixed.
      exact Hh.
    + apply no_contains_goto_test_sequence.
      exact He_fresh.
    + exact Hr_fresh.
Qed.

Lemma loop_unique_closed_after_largest_invariant_exit_pair
  (b : CFGKATTest)
  (e r g h : CFGKATExpression)
  :
  (if b then (test (not largest_loop_invariant_test e b) ;; e) |> g else r) == g ->
  (if b then (test (not largest_loop_invariant_test e b) ;; e) |> h else r) == h ->
  g == h.
Proof.
  intros Hg Hh.
  destruct (fresh_label_family [tt]
    (goto_labels e ++ goto_labels r ++ goto_labels g ++ goto_labels h))
    as [fresh_of [Hfresh _]].
  set (l := fresh_of tt).
  assert (Havoid : ~ In l
    (goto_labels e ++ goto_labels r ++ goto_labels g ++ goto_labels h)).
  {
    unfold l.
    apply Hfresh.
    left. reflexivity.
  }
  assert (He_fresh : ~ contains_goto l e).
  {
    intro Hcontains. apply Havoid.
    apply in_or_app. left.
    apply contains_goto_in_goto_labels.
    exact Hcontains.
  }
  assert (Hr_fresh : ~ contains_goto l r).
  {
    intro Hcontains. apply Havoid.
    apply in_or_app. right.
    apply in_or_app. left.
    apply contains_goto_in_goto_labels.
    exact Hcontains.
  }
  assert (Hg_fresh : ~ contains_goto l g).
  {
    intro Hcontains. apply Havoid.
    apply in_or_app. right.
    apply in_or_app. right.
    apply in_or_app. left.
    apply contains_goto_in_goto_labels.
    exact Hcontains.
  }
  assert (Hh_fresh : ~ contains_goto l h).
  {
    intro Hcontains. apply Havoid.
    apply in_or_app. right.
    apply in_or_app. right.
    apply in_or_app. right.
    apply contains_goto_in_goto_labels.
    exact Hcontains.
  }
  eapply (loop_unique_closed_after_largest_invariant_exit_pair_with_fresh
    l b e r g h).
  - exact He_fresh.
  - exact Hr_fresh.
  - exact Hg_fresh.
  - exact Hh_fresh.
  - exact Hg.
  - exact Hh.
Qed.


Local Definition output_keeps_indicator_assignment
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : Prop :=
  match r with
  | CFGKATAutomatonReject => True
  | CFGKATAutomatonAccept i => i x = v
  | CFGKATAutomatonBreak i => i x = v
  | CFGKATAutomatonContinue i => i x = v
  | CFGKATAutomatonReturn => True
  | CFGKATAutomatonJump _ i => i x = v
  | CFGKATAutomatonNext _ (e, i) =>
      i x = v /\ e dna x
  end.

Local Lemma expression_does_not_assign_indicator_finite_dynamics
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (s : CFGKATSyntConfiguration)
  (a : Atom)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  CFGKATExpressionFiniteDynamics s a r ->
  forall e i,
    s = (e, i) ->
    e dna x ->
    i x = v ->
    output_keeps_indicator_assignment x v r.
Proof.
  intro Hdyn.
  induction Hdyn; intros e0 i0 Hstate Hno Hx; inversion Hstate; subst;
    cbn in *; try exact I; try exact Hx; try reflexivity.
  - unfold update.
    destruct (Var_eq_dec _ _) as [Heq | _].
    + contradiction.
    + reflexivity.
  - split; [reflexivity | exact I].
  - destruct Hno as [Hno1 _].
    eapply IHHdyn; eauto.
  - destruct Hno as [_ Hno2].
    eapply IHHdyn; eauto.
  - destruct Hno as [Hno1 Hno2].
    pose proof (IHHdyn1 _ _ eq_refl Hno1 eq_refl) as Hhead.
    exact (IHHdyn2 _ _ eq_refl Hno2 Hhead).
  - destruct Hno as [Hno1 _].
    eapply IHHdyn; eauto.
  - destruct Hno as [Hno1 _].
    eapply IHHdyn; eauto.
  - destruct Hno as [Hno1 _].
    eapply IHHdyn; eauto.
  - destruct Hno as [Hno1 Hno2].
    pose proof (IHHdyn _ _ eq_refl Hno1 eq_refl) as [Hi' Hnext].
    split; [exact Hi' | split; assumption].
  - destruct Hno as [Hno1 Hno2].
    pose proof (IHHdyn1 _ _ eq_refl Hno1 eq_refl) as Hhead.
    exact (IHHdyn2 _ _ eq_refl Hno2 Hhead).
  - destruct Hno as [Hno1 _].
    eapply IHHdyn; eauto.
  - destruct Hno as [Hno1 Hno2].
    pose proof (IHHdyn1 _ _ eq_refl Hno1 eq_refl) as Hhead.
    exact (IHHdyn2 _ _ eq_refl Hno2 Hhead).
  - destruct Hno as [Hno1 _].
    eapply IHHdyn; eauto.
  - destruct Hno as [Hno1 Hno2].
    pose proof (IHHdyn _ _ eq_refl Hno1 eq_refl) as [Hi' Hnext].
    split; [exact Hi' | split; assumption].
  - eapply IHHdyn; eauto.
    simpl. split; assumption.
Qed.

Lemma expression_does_not_assign_indicator_transition_output
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  (i : IndicatorAssignment)
  (a : Atom)
  :
  e dna x ->
  i x = v ->
  output_keeps_indicator_assignment x v (transition_output e a i).
Proof.
  intros Hno Hx.
  pose proof (transition_output_spec e a i) as Hdyn.
  inversion Hdyn as [s a0 r0 Hfinite | s a0 Hnone]; subst.
  - eapply expression_does_not_assign_indicator_finite_dynamics; eauto.
  - exact I.
Qed.

Lemma assignment_prefix_transition_same
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  (i : IndicatorAssignment)
  (a : Atom)
  :
  i x = v ->
  transition_output (assign v to x ;; e) a i =
  transition_output e a i.
Proof.
  intro Hx.
  rewrite transition_sequence.
  rewrite transition_assign.
  rewrite (update_same_value i x v Hx).
  reflexivity.
Qed.

Ltac lifted_state_eq_refl :=
  apply lifted_relation_refl; intro s; left; reflexivity.

Local Definition empty_transition_output_bisim
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (Hstep : forall e i f j a,
    R (e, i) (f, j) ->
    lifted_relation R (transition_output e a i) (transition_output f a j))
  : CFGKATAutomatonBisimulation ExprAutEmpty ExprAutEmpty.
Proof.
  refine (@Build_CFGKATAutomatonBisimulation ExprAutEmpty ExprAutEmpty R _).
  intros [e i] [f j] a zeta1 zeta2 Hrel Hzeta1 Hzeta2.
  apply resolve_syntactic_empty_identity in Hzeta1.
  apply resolve_syntactic_empty_identity in Hzeta2.
  pose proof (transition_output_unique e a i zeta1 Hzeta1) as Hout1.
  pose proof (transition_output_unique f a j zeta2 Hzeta2) as Hout2.
  rewrite <- Hout1.
  rewrite <- Hout2.
  apply Hstep.
  exact Hrel.
Defined.

Local Definition loopseq_trailing_sequence_relation
  (q : CFGKATExpression)
  (s t : CFGKATSyntConfiguration)
  : Prop :=
  s = t \/
  (exists h k i,
      (h |> 1, i) ~~ ((h |> 1) ;; q, i) /\
      s = (h |> (k ;; q), i) /\
      t = ((h |> k) ;; q, i)).

Local Lemma loopseq_trailing_sequence_tail_lifted
  (q h k : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  (h |> 1, i) ~~ ((h |> 1) ;; q, i) ->
  lifted_relation
    (loopseq_trailing_sequence_relation q)
    (transition_output (h |> (k ;; q)) a i)
    (transition_output ((h |> k) ;; q) a i).
Proof.
  intro Htail.
  pose proof
    (empty_bisim_transition_lifted
      (h |> 1, i)
      ((h |> 1) ;; q, i)
      a Htail) as Hone.
  cbn in Hone.
  rewrite !transition_sequence in Hone.
  rewrite !transition_loopseq in Hone.
  rewrite !transition_sequence.
  rewrite !transition_loopseq.
  remember (transition_output h a i) as r eqn:Hr.
  destruct r as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p [h' i_next]];
    simpl in *.
  - constructor.
  - rewrite transition_sequence.
    lifted_state_eq_refl.
  - remember (transition_output q a i_break) as tq eqn:Htq.
    destruct tq as [|i_q|i_q|i_q| |l_q i_q|p_q s_q];
      inversion Hone; subst.
    constructor.
  - rewrite transition_sequence.
    lifted_state_eq_refl.
  - constructor.
  - constructor.
  - inversion Hone; subst.
    constructor.
    right.
    exists h', k, i_next.
    repeat split; try reflexivity.
    assumption.
Qed.

Local Lemma loopseq_trailing_sequence_bisim
  (h k q : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  (h |> 1, i) ~~ ((h |> 1) ;; q, i) ->
  (h |> (k ;; q), i) ~~ (((h |> k) ;; q), i).
Proof.
  intro Hprem.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar.
  unshelve eexists.
  - refine (empty_transition_output_bisim
      (loopseq_trailing_sequence_relation q) _).
    intros es idxs et it a Hrel.
    destruct Hrel as [Heq | Htail].
    + inversion Heq; subst.
      lifted_state_eq_refl.
    + destruct Htail as [h0 [k0 [i0 [Htail [Hs Ht]]]]].
      inversion Hs; inversion Ht; subst.
      eapply loopseq_trailing_sequence_tail_lifted.
      exact Htail.
  - right.
    exists h, k, i.
    repeat split; try reflexivity.
    exact Hprem.
Qed.

Lemma loopseq_trailing_sequence
  (h k q : CFGKATExpression)
  :
  h |> 1 == (h |> 1) ;; q ->
  h |> (k ;; q) == (h |> k) ;; q.
Proof.
  intro Hprem.
  apply completeness.
  intro i.
  apply loopseq_trailing_sequence_bisim.
  exact
    (CFGKATEquiv_sound empty_label_context
      (h |> 1)
      ((h |> 1) ;; q)
      empty_label_context Hprem i).
Qed.

Local Definition loopseq_leading_sequence_relation
  (q : CFGKATExpression)
  (s t : CFGKATSyntConfiguration)
  : Prop :=
  s = t \/
  (exists h k i,
      (h |> 1, i) ~~ ((h |> 1) ;; q, i) /\
      s = (h |> k, i) /\
      t = (h |> (q ;; k), i)).

Local Lemma loopseq_leading_sequence_tail_lifted
  (q h k : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  (h |> 1, i) ~~ ((h |> 1) ;; q, i) ->
  lifted_relation
    (loopseq_leading_sequence_relation q)
    (transition_output (h |> k) a i)
    (transition_output (h |> (q ;; k)) a i).
Proof.
  intro Htail.
  pose proof
    (empty_bisim_transition_lifted
      (h |> 1, i)
      ((h |> 1) ;; q, i)
      a Htail) as Hone.
  cbn in Hone.
  rewrite !transition_sequence in Hone.
  rewrite !transition_loopseq in Hone.
  rewrite !transition_loopseq.
  remember (transition_output h a i) as r eqn:Hr.
  destruct r as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p [h' i_next]];
    simpl in *.
  - constructor.
  - rewrite transition_sequence.
    rewrite transition_assert in Hone.
    destruct (eval_test_dec (1 : CFGKATTest) a i_accept) as [_ | Hfalse];
      simpl in Hone.
    2:{ exfalso. apply Hfalse. simpl. tauto. }
    remember (transition_output q a i_accept) as tq eqn:Htq.
    destruct tq as [|i_q|i_q|i_q| |l_q i_q|p_q s_q];
      inversion Hone; subst.
    lifted_state_eq_refl.
  - constructor.
  - rewrite transition_sequence.
    rewrite transition_assert in Hone.
    destruct (eval_test_dec (1 : CFGKATTest) a i_continue) as [_ | Hfalse];
      simpl in Hone.
    2:{ exfalso. apply Hfalse. simpl. tauto. }
    remember (transition_output q a i_continue) as tq eqn:Htq.
    destruct tq as [|i_q|i_q|i_q| |l_q i_q|p_q s_q];
      inversion Hone; subst.
    lifted_state_eq_refl.
  - constructor.
  - constructor.
  - inversion Hone; subst.
    constructor.
    right.
    exists h', k, i_next.
    repeat split; try reflexivity.
    assumption.
Qed.

Local Lemma loopseq_leading_sequence_bisim
  (h k q : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  (h |> 1, i) ~~ ((h |> 1) ;; q, i) ->
  (h |> k, i) ~~ (h |> (q ;; k), i).
Proof.
  intro Hprem.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar.
  unshelve eexists.
  - refine (empty_transition_output_bisim
      (loopseq_leading_sequence_relation q) _).
    intros es idxs et it a Hrel.
    destruct Hrel as [Heq | Htail].
    + inversion Heq; subst.
      lifted_state_eq_refl.
    + destruct Htail as [h0 [k0 [i0 [Htail [Hs Ht]]]]].
      inversion Hs; inversion Ht; subst.
      eapply loopseq_leading_sequence_tail_lifted.
      exact Htail.
  - right.
    exists h, k, i.
    repeat split; try reflexivity.
    exact Hprem.
Qed.

Lemma loopseq_leading_sequence
  (h k q : CFGKATExpression)
  :
  h |> 1 == (h |> 1) ;; q ->
  h |> k == h |> (q ;; k).
Proof.
  intro Hprem.
  apply completeness.
  intro i.
  apply loopseq_leading_sequence_bisim.
  exact
    (CFGKATEquiv_sound empty_label_context
      (h |> 1)
      ((h |> 1) ;; q)
      empty_label_context Hprem i).
Qed.

Local Definition assignment_loopseq_unit_assignment_relation
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (s t : CFGKATSyntConfiguration)
  : Prop :=
  s = t \/
  (exists i e,
      e dna x /\
      s = ((assign v to x ;; e) |> 1, i) /\
      t = (((assign v to x ;; e) |> 1) ;; assign v to x, i)) \/
  (exists i e,
      i x = v /\
      e dna x /\
      s = (e |> 1, i) /\
      t = ((e |> 1) ;; assign v to x, i)).

Local Lemma assignment_loopseq_unit_assignment_tail_lifted
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  (i : IndicatorAssignment)
  (a : Atom)
  :
  i x = v ->
  e dna x ->
  lifted_relation
    (assignment_loopseq_unit_assignment_relation x v)
    (transition_output (e |> 1) a i)
    (transition_output ((e |> 1) ;; assign v to x) a i).
Proof.
  intros Hx Hno.
  rewrite transition_sequence.
  rewrite !transition_loopseq.
  remember (transition_output e a i) as r eqn:Hr.
  pose proof
    (expression_does_not_assign_indicator_transition_output x v e i a
      Hno Hx) as Hkeep.
  rewrite <- Hr in Hkeep.
  destruct r as
    [|i_accept|i_break|i_continue| |l i_jump|p [e' i_next]];
    simpl in *.
  - constructor.
  - rewrite transition_assert.
    destruct (eval_test_dec (1 : CFGKATTest) a i_accept) as [_ | Hfalse];
      [|exfalso; apply Hfalse; simpl; tauto].
    simpl.
    rewrite transition_assign.
    rewrite (update_same_value i_accept x v Hkeep).
    constructor.
  - rewrite transition_assign.
    rewrite (update_same_value i_break x v Hkeep).
    constructor.
  - rewrite transition_assert.
    destruct (eval_test_dec (1 : CFGKATTest) a i_continue) as [_ | Hfalse];
      [|exfalso; apply Hfalse; simpl; tauto].
    simpl.
    rewrite transition_assign.
    rewrite (update_same_value i_continue x v Hkeep).
    constructor.
  - constructor.
  - constructor.
  - destruct Hkeep as [Hnext_value Hnext_noassign].
    constructor.
    right. right.
    exists i_next, e'.
    repeat split; try reflexivity; assumption.
Qed.

Local Lemma assignment_loopseq_unit_assignment_bisim
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  e dna x ->
  (((assign v to x ;; e) |> 1), i) ~~
  ((((assign v to x ;; e) |> 1) ;; assign v to x), i).
Proof.
  intro Hno.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar.
  unshelve eexists.
  - refine (empty_transition_output_bisim
      (assignment_loopseq_unit_assignment_relation x v) _).
    intros es idxs et it a Hrel.
    destruct Hrel as [Heq | [Hhead | Htail]].
    + inversion Heq; subst.
      lifted_state_eq_refl.
    + destruct Hhead as [i0 [e0 [Hno0 [Hs Ht]]]].
      inversion Hs; inversion Ht; subst.
      rewrite transition_sequence.
      rewrite !transition_loopseq.
      rewrite !transition_sequence.
      rewrite !transition_assign.
      simpl.
      rewrite <- !transition_loopseq.
      rewrite <- transition_sequence.
      apply assignment_loopseq_unit_assignment_tail_lifted.
      * apply update_same.
      * exact Hno0.
    + destruct Htail as [i0 [e0 [Hi0 [Hno0 [Hs Ht]]]]].
      assert (Hi_tail : i0 x = v) by exact Hi0.
      inversion Hs; inversion Ht; subst.
      apply assignment_loopseq_unit_assignment_tail_lifted.
      * exact Hi_tail.
      * exact Hno0.
  - right. left.
    exists i, e.
    repeat split; try reflexivity; exact Hno.
Qed.

Local Lemma assignment_loopseq_unit_trailing_assignment
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  :
  e dna x ->
  (assign v to x ;; e) |> 1 ==
    ((assign v to x ;; e) |> 1) ;; assign v to x.
Proof.
  intro Hno.
  apply completeness.
  intro i.
  apply assignment_loopseq_unit_assignment_bisim.
  exact Hno.
Qed.

Lemma indpushloopseq
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e f : CFGKATExpression)
  :
  e dna x ->
  (assign v to x ;; e) |> f ==
    (assign v to x ;; e) |> (assign v to x ;; f).
Proof.
  intro Hno.
  apply loopseq_leading_sequence.
  apply assignment_loopseq_unit_trailing_assignment.
  exact Hno.
Qed.


Local Lemma assignment_loopseq_trailing_assignment
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e f : CFGKATExpression)
  :
  e dna x ->
  assign v to x ;; (e |> (f ;; assign v to x)) ==
    assign v to x ;; ((e |> f) ;; assign v to x).
Proof.
  intro Hno.
  cfgkat_rewrite <- EqL8.
  cfgkat_rewrite
    (loopseq_trailing_sequence
      (assign v to x ;; e) f (assign v to x)
      (assignment_loopseq_unit_trailing_assignment x v e Hno)).
  cfgkat_rewrite EqL8.
  apply EqS1.
Qed.

Local Lemma test_loopseq_prefixed_unit_trailing_test
  (c d : CFGKATTest)
  (e : CFGKATExpression)
  :
  test d ;; (e |> 1) ==
    test d ;; ((e |> 1) ;; test c) ->
  (test d ;; e) |> 1 == ((test d ;; e) |> 1) ;; test c.
Proof.
  intro Hprem.
  cfgkat_rewrite <- (loopassoctest d e 1).
  cfgkat_rewrite EqS1.
  exact Hprem.
Qed.

Local Lemma test_loopseq_trailing_test
  (c d : CFGKATTest)
  (e f : CFGKATExpression)
  :
  test d ;; (e |> 1) ==
    test d ;; ((e |> 1) ;; test c) ->
  test d ;; (e |> (f ;; test c)) ==
    test d ;; ((e |> f) ;; test c).
Proof.
  intro Hprem.
  cfgkat_rewrite (loopassoctest d e (f ;; test c)).
  cfgkat_rewrite
    (loopseq_trailing_sequence
      (test d ;; e) f (test c)
      (test_loopseq_prefixed_unit_trailing_test c d e Hprem)).
  cfgkat_rewrite <- (loopassoctest d e f).
  apply EqS1.
Qed.

Local Lemma test_loopseq_leading_test
  (c d : CFGKATTest)
  (e f : CFGKATExpression)
  :
  test d ;; (e |> 1) ==
    test d ;; ((e |> 1) ;; test c) ->
  test d ;; (e |> f) ==
    test d ;; (e |> (test c ;; f)).
Proof.
  intro Hprem.
  cfgkat_rewrite (loopassoctest d e f).
  cfgkat_rewrite
    (loopseq_leading_sequence
      (test d ;; e) f (test c)
      (test_loopseq_prefixed_unit_trailing_test c d e Hprem)).
  cfgkat_rewrite <- (loopassoctest d e (test c ;; f)).
  apply EqRefl.
Qed.

Local Lemma loopinvariant_choice_test_prefix_pack
  (c b : CFGKATTest)
  (x : CFGKATExpression)
  :
  (if b then test c ;; x else test c) ==
    (if c and b then x else test c).
Proof.
  apply minterm_ext_ctx.
  intros m _.
  destruct (m \in b) eqn:Hb.
  - cfgkat_rewrite
      (minterm_choice_select_true b (test c ;; x) (test c) m Hb).
    destruct (m \in c) eqn:Hc.
    + assert (Hcb : (m \in (c and b)) = true).
      {
        apply in_test_of_eval.
        simpl. split.
        - apply in_test_true. exact Hc.
        - apply in_test_true. exact Hb.
      }
      cfgkat_rewrite
        (minterm_choice_select_true (c and b) x (test c) m Hcb).
      cfgkat_rewrite <- EqS1.
      cfgkat_rewrite (test_seq_ba (AtIY_test m) c (AtIY_test m)
        (minterm_test_true_right c m Hc)).
      apply EqRefl.
    + assert (Hcb : (m \in (c and b)) = false).
      {
        apply in_test_false_of_not_eval.
        intros [Hc_eval _].
        pose proof (in_test_false c m Hc) as Hnotc.
        contradiction.
      }
      cfgkat_rewrite
        (minterm_choice_select_false (c and b) x (test c) m Hcb).
      cfgkat_rewrite <- EqS1.
      cfgkat_rewrite (test_seq_ba (AtIY_test m) c 0
        (minterm_test_false_right c m Hc)).
      cfgkat_rewrite EqS2.
      apply EqRefl.
  - cfgkat_rewrite
      (minterm_choice_select_false b (test c ;; x) (test c) m Hb).
    assert (Hcb : (m \in (c and b)) = false).
    {
      apply in_test_false_of_not_eval.
      intros [_ Hb_eval].
      pose proof (in_test_false b m Hb) as Hnotb.
      contradiction.
    }
    cfgkat_rewrite
      (minterm_choice_select_false (c and b) x (test c) m Hcb).
    apply EqRefl.
Qed.

Local Lemma loopinvariant_left_raw_fixed
  (c b : CFGKATTest)
  (e : CFGKATExpression)
  :
  test (c and b) ;; (e |> 1) ==
    test (c and b) ;; ((e |> 1) ;; test c) ->
  (if c and b then e |> (test c ;; while b do e) else test c) ==
    test c ;; while b do e.
Proof.
  intro Hprem.
  cfgkat_rewrite EqL10 at 2.
  cfgkat_rewrite test_choice_split.
  cfgkat_rewrite EqS4.
  cfgkat_rewrite
    (EqG4 (e |> (test c ;; while b do e)) (test c) (c and b)).
  cfgkat_rewrite
    (EqG4 (e |> while b do e) (test c) (c and b)).
  cfgkat_rewrite <-
    (test_loopseq_leading_test c (c and b) e (while b do e) Hprem).
  apply EqRefl.
Qed.

Local Lemma loopinvariant_right_raw_fixed
  (c b : CFGKATTest)
  (e : CFGKATExpression)
  :
  test (c and b) ;; (e |> 1) ==
    test (c and b) ;; ((e |> 1) ;; test c) ->
  (if c and b then
      e |> ((while b do (test c ;; e)) ;; test c)
   else test c) ==
    (while b do (test c ;; e)) ;; test c.
Proof.
  intro Hprem.
  cfgkat_rewrite EqL10 at 2.
  cfgkat_rewrite EqG5.
  cfgkat_rewrite EqS3.
  cfgkat_rewrite <- loopassoctest.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite loopinvariant_choice_test_prefix_pack.
  cfgkat_rewrite
    (EqG4 (e |> ((while b do (test c ;; e)) ;; test c))
      (test c) (c and b)).
  cfgkat_rewrite
    (EqG4 ((e |> while b do (test c ;; e)) ;; test c)
      (test c) (c and b)).
  cfgkat_rewrite <-
    (test_loopseq_trailing_test c (c and b) e
      (while b do (test c ;; e)) Hprem).
  apply EqRefl.
Qed.

Local Lemma loopinvariant_trimmed_premise
  (c b : CFGKATTest)
  (e : CFGKATExpression)
  :
  test (c and b) ;; (e |> 1) ==
    test (c and b) ;; ((e |> 1) ;; test c) ->
  test (c and b) ;;
    ((test (not C+[e, c and b]) ;; e) |> 1) ==
  test (c and b) ;;
    (((test (not C+[e, c and b]) ;; e) |> 1) ;; test c).
Proof.
  intro Hprem.
  cfgkat_rewrite <- loopassoctest at 1.
  cfgkat_rewrite <- loopassoctest at 1.
  cfgkat_rewrite EqS1 at 1.
  cfgkat_rewrite <- EqS1 at 1.
  cfgkat_rewrite <- EqS1 at 1.
  cfgkat_rewrite
    (test_seq_ba
      (c and b) (not C+[e, c and b])
      ((c and b) and (not C+[e, c and b]))
      (BARefl _)).
  cfgkat_rewrite <-
    (test_seq_absorb_right
      ((c and b) and (not C+[e, c and b])) (c and b)
      ltac:(
        apply Boolean_denotation_completeness;
        unfold CFGKATTestDenotationEquivalent;
        intros a i; simpl; tauto)
      (e |> 1)) at 1.
  cfgkat_rewrite <-
    (test_seq_absorb_right
      ((c and b) and (not C+[e, c and b])) (c and b)
      ltac:(
        apply Boolean_denotation_completeness;
        unfold CFGKATTestDenotationEquivalent;
        intros a i; simpl; tauto)
      ((e |> 1) ;; test c)) at 1.
  cfgkat_rewrite Hprem.
  apply EqRefl.
Qed.

Local Lemma loopinvariant_largest_leq_guard
  (c b : CFGKATTest)
  (e : CFGKATExpression)
  :
  BA_leq C+[e, c and b] b.
Proof.
  unfold BA_leq.
  apply Boolean_denotation_completeness.
  unfold CFGKATTestDenotationEquivalent.
  intros a i.
  split.
  - intros [Hb | HC].
    + exact Hb.
    + pose proof
        (BA_leq_eval C+[e, c and b] (c and b) a i
          (largest_loop_invariant_test_leq_guard e (c and b)) HC)
        as [_ Hb].
      exact Hb.
  - intro Hb.
    left. exact Hb.
Qed.

Local Lemma loopinvariant_target_acc_cont_invariant
  (c b : CFGKATTest)
  (e : CFGKATExpression)
  :
  acc_cont_loop_invariant (test c ;; e) C+[e, c and b].
Proof.
  unfold acc_cont_loop_invariant.
  intros a i HC.
  pose proof
    (BA_leq_eval C+[e, c and b] (c and b) a i
      (largest_loop_invariant_test_leq_guard e (c and b)) HC)
    as [Hc _].
  pose proof
    (largest_loop_invariant_test_acc_cont_invariant e (c and b) a i HC)
    as [j [Hout HCj]].
  exists j.
  split.
  - rewrite transition_sequence.
    rewrite transition_assert.
    destruct (eval_test_dec c a i) as [_ | Hnotc].
    + simpl. exact Hout.
    + contradiction.
  - exact HCj.
Qed.

Local Lemma loopinvariant_source_largest_fixed
  (c b : CFGKATTest)
  (e : CFGKATExpression)
  :
  test (c and b) ;; (e |> 1) ==
    test (c and b) ;; ((e |> 1) ;; test c) ->
  (if c and b then
      (test (not C+[e, c and b]) ;; e) |>
        (test c ;; while b do e)
   else test c) ==
    test c ;; while b do e.
Proof.
  intro Hprem.
  cfgkat_rewrite (looptighten_invariant
    e b C+[e, c and b]
    (loopinvariant_largest_leq_guard c b e)
    (largest_loop_invariant_test_acc_cont_invariant e (c and b))).
  apply loopinvariant_left_raw_fixed.
  apply loopinvariant_trimmed_premise.
  exact Hprem.
Qed.

Local Lemma loopinvariant_target_largest_fixed
  (c b : CFGKATTest)
  (e : CFGKATExpression)
  :
  test (c and b) ;; (e |> 1) ==
    test (c and b) ;; ((e |> 1) ;; test c) ->
  (if c and b then
      (test (not C+[e, c and b]) ;; e) |>
        ((while b do (test c ;; e)) ;; test c)
   else test c) ==
    (while b do (test c ;; e)) ;; test c.
Proof.
  intro Hprem.
  cfgkat_rewrite (looptighten_invariant
    (test c ;; e) b C+[e, c and b]
    (loopinvariant_largest_leq_guard c b e)
    (loopinvariant_target_acc_cont_invariant c b e)).
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite (test_seq_ba
    (not C+[e, c and b]) c
    (c and not C+[e, c and b])
    (BAAndComm (not C+[e, c and b]) c)).
  cfgkat_rewrite <- EqS5.
  cfgkat_rewrite EqS1.
  apply loopinvariant_right_raw_fixed.
  apply loopinvariant_trimmed_premise.
  exact Hprem.
Qed.

Local Theorem loopinvariant
  (c b : CFGKATTest)
  (e : CFGKATExpression)
  :
  test (c and b) ;; (e |> 1) ==
    test (c and b) ;; ((e |> 1) ;; test c) ->
  (test c ;; while b do e) ==
    (while b do (test c ;; e)) ;; test c.
Proof.
  intro Hprem.
  eapply (loop_unique_closed_after_largest_invariant_exit_pair
    (c and b) e (test c)
    (test c ;; while b do e)
    ((while b do (test c ;; e)) ;; test c)).
  - apply loopinvariant_source_largest_fixed.
    exact Hprem.
  - apply loopinvariant_target_largest_fixed.
    exact Hprem.
Qed.

Local Definition indicator_variables_except
  (x : IndicatorVariable)
  : list IndicatorVariable :=
  filter
    (fun y =>
      match Var_eq_dec y x with
      | left _ => false
      | right _ => true
      end)
    (elements IndicatorVariable).

Local Lemma indicator_variables_except_spec
  (x y : IndicatorVariable)
  :
  In y (indicator_variables_except x) <-> y <> x.
Proof.
  unfold indicator_variables_except.
  split.
  - intro Hin.
    apply filter_In in Hin.
    destruct Hin as [_ Hin].
    destruct (Var_eq_dec y x) as [Hyx | Hyx].
    + discriminate.
    + exact Hyx.
  - intro Hyx.
    apply filter_In.
    split.
    + apply all_in.
    + destruct (Var_eq_dec y x) as [Heq | _].
      * contradiction.
      * reflexivity.
Qed.

Local Lemma eval_test_atom_ext
  (b : CFGKATTest)
  (a a' : Atom)
  (i : IndicatorAssignment)
  :
  (forall t, a t <-> a' t) ->
  (eval_test b a i <-> eval_test b a' i).
Proof.
  revert a a' i.
  induction b as [t | y vy | | | b1 IH1 b2 IH2 | b1 IH1 b2 IH2 | b IH];
    simpl; intros a a' i Ha.
  - exact (Ha t).
  - tauto.
  - tauto.
  - tauto.
  - specialize (IH1 a a' i Ha).
    specialize (IH2 a a' i Ha).
    tauto.
  - specialize (IH1 a a' i Ha).
    specialize (IH2 a a' i Ha).
    tauto.
  - specialize (IH a a' i Ha).
    tauto.
Qed.

Local Definition AtIY_test_without_indicator
  (x : IndicatorVariable)
  (m : At x I^Y)
  : CFGKATTest :=
  TAnd
    (atom_to_test (AtIY_atom m))
    (complete_test_on (indicator_variables_except x) (AtIY_assignment m)).

Local Definition boolean_dnf_without_indicator
  (x : IndicatorVariable)
  (b : CFGKATTest)
  : CFGKATTest :=
  fold_TOr
    (map (AtIY_test_without_indicator x)
       (filter (fun m => m \in b) all_AtIY)).

Local Lemma complete_test_on_indicator_free
  (x : IndicatorVariable)
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  :
  ~ In x xs ->
  test_indicator_free x (complete_test_on xs i).
Proof.
  unfold complete_test_on.
  induction xs as [|y ys IH]; simpl; intro Hnotin.
  - exact I.
  - split.
    + intro Hyx.
      apply Hnotin.
      left. exact Hyx.
    + apply IH.
      intro Hin.
      apply Hnotin.
      right. exact Hin.
Qed.

Local Lemma boolean_dnf_without_indicator_complete
  (x : IndicatorVariable)
  (b : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  eval_test b a i ->
  eval_test (boolean_dnf_without_indicator x b) a i.
Proof.
  intro Hb.
  unfold boolean_dnf_without_indicator.
  rewrite eval_fold_TOr.
  destruct (bool_to_atom_eq a) as [ba [Hba_in Hba_eq]].
  exists (AtIY_test_without_indicator x (bool_to_atom ba, i)).
  split.
  - apply in_map_iff.
    exists (bool_to_atom ba, i).
    split; [reflexivity |].
    apply filter_In.
    split.
    + unfold all_AtIY.
      apply in_flat_map.
      exists ba.
      split.
      * exact Hba_in.
      * apply in_map.
        apply all_assignments_complete.
    + unfold in_test, AtIY_atom, AtIY_assignment.
      simpl.
      destruct (eval_test_dec b (bool_to_atom ba) i) as [_ | Hnb].
      * reflexivity.
      * exfalso. apply Hnb.
        rewrite Hba_eq.
        exact Hb.
  - unfold AtIY_test_without_indicator.
    split.
    + apply eval_atom_to_test.
      intro t.
      rewrite Hba_eq.
      tauto.
    + apply eval_complete_test_on.
      intros y _.
      reflexivity.
Qed.

Local Lemma assignments_equal_after_forgetting_indicator
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (i j : IndicatorAssignment)
  :
  (forall y, y <> x -> j y = i y) ->
  update j x v = update i x v.
Proof.
  intro Hsame.
  apply functional_extensionality.
  intro y.
  unfold update.
  destruct (Var_eq_dec x y) as [_ | Hxy].
  - reflexivity.
  - apply Hsame.
    intro Hyx. apply Hxy. symmetry. exact Hyx.
Qed.

Local Lemma boolean_dnf_without_indicator_sound
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  (forall a0 i0,
    eval_test b a0 i0 <->
    eval_test b a0 (update i0 x v)) ->
  eval_test (boolean_dnf_without_indicator x b) a i ->
  eval_test b a i.
Proof.
  intros Hinv Hdnf.
  unfold boolean_dnf_without_indicator in Hdnf.
  rewrite eval_fold_TOr in Hdnf.
  destruct Hdnf as [t [Ht_in Ht_eval]].
  apply in_map_iff in Ht_in.
  destruct Ht_in as [[a' j] [Ht Hfilter]].
  subst t.
  apply filter_In in Hfilter.
  destruct Hfilter as [_ Hb_in].
  unfold AtIY_test_without_indicator in Ht_eval.
  destruct Ht_eval as [Ha Hj].
  pose proof (in_test_true b (a', j) Hb_in) as Hb_j_raw.
  rewrite eval_atom_to_test in Ha.
  pose proof (proj1 (eval_test_atom_ext b a' a j Ha) Hb_j_raw)
    as Hb_j.
  pose proof (proj1 (Hinv a j) Hb_j) as Hb_j_update.
  assert (Hupdate :
    update j x v = update i x v).
  {
    apply assignments_equal_after_forgetting_indicator.
    intros y Hyx.
    pose proof (proj1 (eval_complete_test_on
      (indicator_variables_except x) j i a) Hj) as Hj_same.
    apply Hj_same.
    apply indicator_variables_except_spec.
    exact Hyx.
  }
  rewrite Hupdate in Hb_j_update.
  apply (proj2 (Hinv a i)).
  exact Hb_j_update.
Qed.

Local Lemma indcommtest_update_invariant
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  :
  (forall a i,
    eval_test b a i <->
    eval_test b a (update i x v)) ->
  assign v to x ;; test b == test b ;; assign v to x.
Proof.
  intro Hinv.
  set (b_free := boolean_dnf_without_indicator x b).
  assert (Hb_free : b =BA b_free).
  {
    unfold b_free.
    apply Boolean_denotation_completeness.
    unfold CFGKATTestDenotationEquivalent.
    intros a i.
    split.
    - apply boolean_dnf_without_indicator_complete.
    - apply boolean_dnf_without_indicator_sound with (v := v).
      exact Hinv.
  }
  cfgkat_rewrite (EqBoolAssertCong b b_free Hb_free).
  apply indcommtest.
  unfold b_free.
  unfold boolean_dnf_without_indicator.
  remember
    (map (AtIY_test_without_indicator x)
      (filter (fun m : At x I^Y => m \in b) all_AtIY)) as tests.
  assert (Hfree : forall c, In c tests -> test_indicator_free x c).
  {
    subst tests.
    intros c Hc.
    apply in_map_iff in Hc.
    destruct Hc as [m [Hc _]].
    subst c.
    unfold AtIY_test_without_indicator.
    split.
    - apply atom_to_test_indicator_free.
    - apply complete_test_on_indicator_free.
      intro Hin.
      apply (proj1 (indicator_variables_except_spec x x) Hin).
      reflexivity.
  }
  clear Heqtests.
  induction tests as [|c tests IH]; simpl.
  - exact I.
  - split.
    + apply Hfree. left. reflexivity.
    + apply IH.
      intros d Hd.
      apply Hfree. right. exact Hd.
Qed.

Local Definition assignment_update_closure_pred
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (c : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
  : Prop :=
  exists j,
    eval_test c a j /\
    update i x v = update j x v.

Local Definition assignment_update_closure_test
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (c : CFGKATTest)
  : CFGKATTest :=
  predicate_to_test
    (assignment_update_closure_pred x v c)
    (fun a i =>
      excluded_middle_informative
        (assignment_update_closure_pred x v c a i)).

Local Lemma assignment_update_closure_test_complete
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (c : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  assignment_update_closure_pred x v c a i ->
  eval_test (assignment_update_closure_test x v c) a i.
Proof.
  unfold assignment_update_closure_test.
  apply predicate_to_test_complete.
Qed.

Local Lemma assignment_update_closure_test_sound
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (c : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  eval_test (assignment_update_closure_test x v c) a i ->
  assignment_update_closure_pred x v c a i.
Proof.
  unfold assignment_update_closure_test.
  apply predicate_to_test_sound.
Qed.

Local Lemma transition_prefixed_assign_same_update
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (h : CFGKATExpression)
  (a : Atom)
  (i j : IndicatorAssignment)
  :
  update i x v = update j x v ->
  transition_output (assign v to x ;; h) a i =
  transition_output (assign v to x ;; h) a j.
Proof.
  intro Hsame.
  rewrite !transition_sequence.
  rewrite !transition_assign.
  rewrite Hsame.
  reflexivity.
Qed.

Local Lemma assignment_update_closure_test_leq_guard
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b c : CFGKATTest)
  :
  test_indicator_free x b ->
  BA_leq c b ->
  BA_leq (assignment_update_closure_test x v c) b.
Proof.
  intros Hb_free Hle.
  unfold BA_leq.
  apply Boolean_denotation_completeness.
  unfold CFGKATTestDenotationEquivalent.
  intros a i.
  split.
  - intros [Hb | Hclosed].
    + exact Hb.
    + pose proof
        (assignment_update_closure_test_sound x v c a i Hclosed)
        as [j [Hc Hsame]].
      pose proof (BA_leq_eval c b a j Hle Hc) as Hb_j.
      pose proof
        (proj2
          (test_indicator_free_update
            x b a j v Hb_free) Hb_j)
        as Hb_update_j.
      assert (Hb_update_i : eval_test b a (update i x v)).
      {
        rewrite Hsame.
        exact Hb_update_j.
      }
      apply
        (proj1
          (test_indicator_free_update
            x b a i v Hb_free)).
      exact Hb_update_i.
  - intro Hb.
    left. exact Hb.
Qed.

Local Lemma assignment_update_closure_test_acc_cont_invariant
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (c : CFGKATTest)
  (h : CFGKATExpression)
  :
  acc_cont_loop_invariant (assign v to x ;; h) c ->
  acc_cont_loop_invariant
    (assign v to x ;; h)
    (assignment_update_closure_test x v c).
Proof.
  intros Hinv a i Hclosed.
  pose proof
    (assignment_update_closure_test_sound x v c a i Hclosed)
    as [j [Hc Hsame]].
  pose proof (Hinv a j Hc) as [k [[Hacc | Hcont] Hc_k]].
  - exists k.
    split.
    + left.
      rewrite (transition_prefixed_assign_same_update
        x v h a i j Hsame).
      exact Hacc.
    + apply assignment_update_closure_test_complete.
      exists k.
      split; [exact Hc_k | reflexivity].
  - exists k.
    split.
    + right.
      rewrite (transition_prefixed_assign_same_update
        x v h a i j Hsame).
      exact Hcont.
    + apply assignment_update_closure_test_complete.
      exists k.
      split; [exact Hc_k | reflexivity].
Qed.

Local Lemma largest_loop_invariant_test_prefixed_assign_update_invariant
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  (h : CFGKATExpression)
  :
  test_indicator_free x b ->
  forall a i,
    eval_test (largest_loop_invariant_test (assign v to x ;; h) b) a i <->
    eval_test
      (largest_loop_invariant_test (assign v to x ;; h) b)
      a (update i x v).
Proof.
  intros Hb_free a i.
  set (C := largest_loop_invariant_test (assign v to x ;; h) b).
  assert (Hclosed_leq :
    BA_leq (assignment_update_closure_test x v C) b).
  {
    apply assignment_update_closure_test_leq_guard.
    - exact Hb_free.
    - unfold C. apply largest_loop_invariant_test_leq_guard.
  }
  assert (Hclosed_inv :
    acc_cont_loop_invariant
      (assign v to x ;; h)
      (assignment_update_closure_test x v C)).
  {
    apply assignment_update_closure_test_acc_cont_invariant.
    unfold C. apply largest_loop_invariant_test_acc_cont_invariant.
  }
  split; intro HC.
  - apply largest_loop_invariant_test_complete.
    exists (assignment_update_closure_test x v C).
    split; [exact Hclosed_leq |].
    split; [exact Hclosed_inv |].
    apply assignment_update_closure_test_complete.
    exists i.
    split; [exact HC |].
    apply functional_extensionality.
    intro y.
    unfold update.
    destruct (Var_eq_dec x y); reflexivity.
  - apply largest_loop_invariant_test_complete.
    exists (assignment_update_closure_test x v C).
    split; [exact Hclosed_leq |].
    split; [exact Hclosed_inv |].
    apply assignment_update_closure_test_complete.
    exists (update i x v).
    split; [exact HC |].
    apply functional_extensionality.
    intro y.
    unfold update.
    destruct (Var_eq_dec x y); reflexivity.
Qed.

Lemma trim_largest_prefixed_assign_comm
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (b : CFGKATTest)
  (h : CFGKATExpression)
  :
  test_indicator_free x b ->
  test (not largest_loop_invariant_test (assign zero to x ;; h) b) ;;
    (assign zero to x ;; h) ==
  assign zero to x ;;
    (test (not largest_loop_invariant_test (assign zero to x ;; h) b) ;; h).
Proof.
  intro Hb_free.
  assert (Hinv :
    forall a i,
      eval_test (not largest_loop_invariant_test (assign zero to x ;; h) b)
        a i <->
      eval_test (not largest_loop_invariant_test (assign zero to x ;; h) b)
        a (update i x zero)).
  {
    intros a i.
    specialize
      (largest_loop_invariant_test_prefixed_assign_update_invariant
        x zero b h Hb_free a i) as Hinv.
    simpl. tauto.
  }
  apply EqSym.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite (indcommtest_update_invariant x zero _ Hinv).
  apply EqS1.
Qed.


Local Lemma assign_prefix_indicator_strengthen
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  :
  assign v to x ;; e ==
    assign v to x ;; (test x is v ;; e).
Proof.
  apply EqSym.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite EqA2.
  apply EqRefl.
Qed.

Local Lemma test_and_indicator_absorbs_same_assignment
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  :
  test ((x is v) and b) ;; assign v to x ==
    test ((x is v) and b).
Proof.
  cfgkat_rewrite
    (EqBoolAssertCong
      ((x is v) and b)
      (b and (x is v))
      (BAAndComm (x is v) b))
    at 1.
  cfgkat_rewrite <- EqS5 at 1.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite EqA3.
  cfgkat_rewrite EqS5.
  apply EqBoolAssertCong. apply BAAndComm.
Qed.

Local Lemma assignment_duplication_assert_any
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  :
  assign v to x ;; test b ==
    assign v to x ;; (test b ;; assign v to x).
Proof.
  apply EqSym.
  cfgkat_rewrite <- EqS1 at 1.
  cfgkat_rewrite (assign_prefix_indicator_strengthen x v (test b)).
  cfgkat_rewrite EqS1.
  cfgkat_rewrite EqS5 at 1.
  cfgkat_rewrite test_and_indicator_absorbs_same_assignment.
  cfgkat_rewrite <- EqS5.
  cfgkat_rewrite <- (assign_prefix_indicator_strengthen x v (test b)).
  apply EqRefl.
Qed.

Local Lemma assignment_duplication_right_annihilator
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  :
  e ;; assign v to x == e ->
  assign v to x ;; e ==
    assign v to x ;; (e ;; assign v to x).
Proof.
  intro Hann.
  apply EqSym.
  cfgkat_rewrite Hann.
  apply EqRefl.
Qed.

Local Lemma assignment_duplication_sequence
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e f : CFGKATExpression)
  :
  assign v to x ;; e ==
    assign v to x ;; (e ;; assign v to x) ->
  assign v to x ;; f ==
    assign v to x ;; (f ;; assign v to x) ->
  assign v to x ;; (e ;; f) ==
    assign v to x ;; ((e ;; f) ;; assign v to x).
Proof.
  intros He Hf.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite He.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite Hf.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite EqS1 at 2.
  cfgkat_rewrite <- He.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite <- EqS1 at 2.
  apply EqRefl.
Qed.


Local Lemma assignment_duplication_to_test_duplication
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  :
  assign v to x ;; e ==
    assign v to x ;; (e ;; assign v to x) ->
  test x is v ;; e ==
    test x is v ;; (e ;; test x is v).
Proof.
  intro Hdup.
  assert (Htest :
    test x is v ;; e ==
      test x is v ;; (e ;; assign v to x)).
  {
    cfgkat_rewrite <- (EqA3 x v) at 1.
    cfgkat_rewrite (EqS1 (test x is v) (assign v to x) e).
    cfgkat_rewrite Hdup.
    cfgkat_rewrite <- (EqS1
      (test x is v) (assign v to x) (e ;; assign v to x)).
    cfgkat_rewrite (EqA3 x v).
    apply EqRefl.
  }
  cfgkat_rewrite Htest.
  cfgkat_rewrite <- EqA2.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite EqS1 at 2.
  cfgkat_rewrite <- Htest.
  apply EqS1.
Qed.


Local Lemma assignment_duplication_loopseq
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e f : CFGKATExpression)
  :
  e dna x ->
  assign v to x ;; f ==
    assign v to x ;; (f ;; assign v to x) ->
  assign v to x ;; (e |> f) ==
    assign v to x ;; ((e |> f) ;; assign v to x).
Proof.
  intros He Hf.
  cfgkat_rewrite <- EqL8.
  cfgkat_rewrite (indpushloopseq x v e f He).
  cfgkat_rewrite Hf.
  cfgkat_rewrite <- (indpushloopseq
    x v e (f ;; assign v to x) He).
  cfgkat_rewrite EqL8.
  apply assignment_loopseq_trailing_assignment.
  exact He.
Qed.

Local Lemma assignment_duplication_loopinvariant_premise_dna_any_guard
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  (e : CFGKATExpression)
  :
  e dna x ->
  test ((x is v) and b) ;; (e |> 1) ==
    test ((x is v) and b) ;; ((e |> 1) ;; test x is v).
Proof.
  intro He.
  cfgkat_rewrite <- EqS5 at 1.
  cfgkat_rewrite EqS1 at 1.
  cfgkat_rewrite
    (assignment_duplication_to_test_duplication x v
      (test b ;; (e |> 1))
      (assignment_duplication_sequence x v (test b) (e |> 1)
        (assignment_duplication_assert_any x v b)
        (assignment_duplication_loopseq x v e 1 He
          ltac:(
            cfgkat_rewrite EqS4;
            cfgkat_rewrite EqS3;
            apply EqSym; apply EqA4)))).
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite <- EqS1 at 1.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite EqS5.
  apply EqRefl.
Qed.

Lemma loop_zero_invariant_dna
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  (e : CFGKATExpression)
  :
  e dna x ->
  test x is v ;; (while b do e) ==
  (while b do (test x is v ;; e)) ;;
    test x is v.
Proof.
  intro He.
  apply loopinvariant.
  apply assignment_duplication_loopinvariant_premise_dna_any_guard.
  exact He.
Qed.

Lemma assign_prefixed_from_tested
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (k1 k2 : CFGKATExpression)
  :
  test x is v ;; k1 == test x is v ;; k2 ->
  assign v to x ;; k1 == assign v to x ;; k2.
Proof.
  intro Htest.
  cfgkat_rewrite <- (EqA2 x v) at 1.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite Htest.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite (EqA2 x v).
  apply EqRefl.
Qed.

Local Lemma test_and_indicator_assign_sequence_absorb
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  (e : CFGKATExpression)
  :
  test ((x is v) and b) ;; (assign v to x ;; e) ==
    test ((x is v) and b) ;; e.
Proof.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite test_and_indicator_absorbs_same_assignment.
  apply EqRefl.
Qed.

Local Lemma assign_prefix_equiv_to_test_and_indicator_prefix
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  (e f : CFGKATExpression)
  :
  assign v to x ;; e == assign v to x ;; f ->
  test ((x is v) and b) ;; e ==
    test ((x is v) and b) ;; f.
Proof.
  intro Hassign.
  cfgkat_rewrite <- test_and_indicator_assign_sequence_absorb.
  cfgkat_rewrite Hassign.
  apply test_and_indicator_assign_sequence_absorb.
Qed.

Local Lemma assign_prefix_choice_cong_from_assign
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  (e1 e1' e2 e2' : CFGKATExpression)
  :
  assign v to x ;; e1 == assign v to x ;; e1' ->
  assign v to x ;; e2 == assign v to x ;; e2' ->
  assign v to x ;; (if b then e1 else e2) ==
    assign v to x ;; (if b then e1' else e2').
Proof.
  intros Hthen Helse.
  apply assign_prefixed_from_tested.
  cfgkat_rewrite test_choice_split.
  cfgkat_rewrite (EqG4 e1 (test x is v ;; e2) ((x is v) and b)).
  cfgkat_rewrite
    (EqChoiceCong empty_label_context empty_label_context
      (test ((x is v) and b) ;; e1)
      (test x is v ;; e2)
      (test ((x is v) and b) ;; e1')
      (test x is v ;; e2')
      ((x is v) and b)
      (assign_prefix_equiv_to_test_and_indicator_prefix
        x v b e1 e1' Hthen)
      ltac:(
        cfgkat_rewrite <- (EqA3 x v) at 1;
        cfgkat_rewrite (EqS1 (test x is v) (assign v to x) e2);
        cfgkat_rewrite Helse;
        cfgkat_rewrite <- (EqS1 (test x is v) (assign v to x) e2');
        cfgkat_rewrite (EqA3 x v);
        apply EqRefl)).
  cfgkat_rewrite <- (EqG4 e1' (test x is v ;; e2') ((x is v) and b)).
  cfgkat_rewrite <- (test_choice_split (x is v) b e1' e2').
  apply EqRefl.
Qed.


Theorem assignment_duplication
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  :
  e dna x ->
  assign v to x ;; e ==
    assign v to x ;; (e ;; assign v to x).
Proof.
  revert x v.
  induction e as
    [b | p | y w | | | | l | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b body IH];
    intros x v Hno; cbn [expression_does_not_assign_indicator] in Hno.
  - apply assignment_duplication_assert_any.
  - apply EqSym.
    cfgkat_rewrite <- EqS1 at 1.
    cfgkat_rewrite EqA1.
    cfgkat_rewrite EqS1.
    cfgkat_rewrite EqA4.
    apply EqRefl.
  - apply EqSym.
    cfgkat_rewrite <- EqS1 at 1.
    cfgkat_rewrite (EqA8 y x w v Hno).
    cfgkat_rewrite EqS1.
    cfgkat_rewrite EqA4.
    apply EqRefl.
  - apply assignment_duplication_right_annihilator. apply EqS8.
  - apply assignment_duplication_right_annihilator. apply EqS7.
  - apply assignment_duplication_right_annihilator. apply EqS6.
  - apply assignment_duplication_right_annihilator. apply EqS9.
  - destruct Hno as [H1 H2].
    cfgkat_rewrite (assign_prefix_choice_cong_from_assign
      x v b e1 (e1 ;; assign v to x) e2 (e2 ;; assign v to x)
      (IH1 x v H1) (IH2 x v H2)).
    cfgkat_rewrite <- EqG5.
    apply EqRefl.
  - destruct Hno as [H1 H2].
    apply assignment_duplication_sequence.
    + apply IH1. exact H1.
    + apply IH2. exact H2.
  - destruct Hno as [H1 H2].
    apply assignment_duplication_loopseq.
    + exact H1.
    + apply IH2. exact H2.
  - apply assign_prefixed_from_tested.
    apply EqSym.
    cfgkat_rewrite <- EqS1.
    cfgkat_rewrite (loop_zero_invariant_dna x v b body Hno).
    cfgkat_rewrite EqS1.
    cfgkat_rewrite EqA3.
    cfgkat_rewrite <- (loop_zero_invariant_dna x v b body Hno).
    apply EqRefl.
Qed.

Local Lemma test_prefixed_empty_equiv_lifted
  (c : CFGKATTest)
  (e f : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  test c ;; e == test c ;; f ->
  eval_test c a i ->
  lifted_relation
    (fun s t : CFGKATSyntConfiguration => s ~~ t)
    (transition_output e a i)
    (transition_output f a i).
Proof.
  intros Heq Hc.
  pose proof
    (empty_bisim_transition_lifted
      (test c ;; e, i) (test c ;; f, i) a
      (CFGKATEquiv_sound
        empty_label_context (test c ;; e) (test c ;; f)
        empty_label_context Heq i)) as Hlift.
  cbn in Hlift.
  rewrite !transition_sequence in Hlift.
  rewrite !transition_assert in Hlift.
  destruct (eval_test_dec c a i) as [_ | Hnc].
  - simpl in Hlift. exact Hlift.
  - contradiction.
Qed.

Lemma test_prefixed_empty_equiv_accept_iff
  (c : CFGKATTest)
  (e f : CFGKATExpression)
  (a : Atom)
  (i j : IndicatorAssignment)
  :
  test c ;; e == test c ;; f ->
  eval_test c a i ->
  (transition_output e a i = CFGKATAutomatonAccept j <->
   transition_output f a i = CFGKATAutomatonAccept j).
Proof.
  intros Heq Hc.
  pose proof (test_prefixed_empty_equiv_lifted c e f a i Heq Hc) as Hlift.
  split; intro Haccept.
  - rewrite Haccept in Hlift.
    inversion Hlift; subst.
    reflexivity.
  - rewrite Haccept in Hlift.
    inversion Hlift; subst.
    reflexivity.
Qed.

Lemma test_prefixed_empty_equiv_continue_iff
  (c : CFGKATTest)
  (e f : CFGKATExpression)
  (a : Atom)
  (i j : IndicatorAssignment)
  :
  test c ;; e == test c ;; f ->
  eval_test c a i ->
  (transition_output e a i = CFGKATAutomatonContinue j <->
   transition_output f a i = CFGKATAutomatonContinue j).
Proof.
  intros Heq Hc.
  pose proof (test_prefixed_empty_equiv_lifted c e f a i Heq Hc) as Hlift.
  split; intro Hcontinue.
  - rewrite Hcontinue in Hlift.
    inversion Hlift; subst.
    reflexivity.
  - rewrite Hcontinue in Hlift.
    inversion Hlift; subst.
    reflexivity.
Qed.


Lemma partialselection
  (d c c' : CFGKATTest)
  (e f : CFGKATExpression)
  :
  TAnd d c =BA TAnd d c' ->
  test d ;; (if c then e else f) ==
    test d ;; (if c' then e else f).
Proof.
  intro Hguards.
  cfgkat_rewrite test_choice_split.
  cfgkat_rewrite
    (EqBoolChoiceCong e (test d ;; f) (d and c) (d and c') Hguards).
  cfgkat_rewrite <- (test_choice_split d c' e f).
  apply EqRefl.
Qed.


Lemma assign_selects_indicator_branch
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e f : CFGKATExpression)
  :
  assign v to x ;; (if x is v then e else f) ==
    assign v to x ;; e.
Proof.
  cfgkat_rewrite <- (EqA2 x v) at 1.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite branchsel.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite (EqA2 x v).
  apply EqRefl.
Qed.

Lemma assign_selects_implied_branch
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  (e f : CFGKATExpression)
  :
  TAnd (x is v) b =BA (x is v) ->
  assign v to x ;; (if b then e else f) ==
    assign v to x ;; e.
Proof.
  intro Hle.
  apply assign_prefixed_from_tested.
  cfgkat_rewrite (partialselection (x is v) b (x is v) e f
    ltac:(eapply BATrans;
      [exact Hle | apply BASym; apply BAAndIdem])).
  apply branchsel.
Qed.

Lemma assign_skips_disjoint_branch
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  (e f : CFGKATExpression)
  :
  TAnd (x is v) b =BA 0 ->
  assign v to x ;; (if b then e else f) ==
    assign v to x ;; f.
Proof.
  intro Hdisjoint.
  apply assign_prefixed_from_tested.
  apply branchskip_disjoint.
  exact Hdisjoint.
Qed.

Lemma indicator_implies_or_right
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  :
  TAnd (x is v) (b or x is v) =BA (x is v).
Proof.
  apply BA_leq_to_and_right.
  apply BA_leq_or_right.
Qed.

Lemma indicator_distinct_and_false
  (x : IndicatorVariable)
  (v w : IndicatorValue)
  :
  v <> w ->
  TAnd (x is v) (x is w) =BA (0 : CFGKATTest).
Proof.
  apply BAIndicatorExclusivity.
Qed.


Lemma test_prefixed_same_assignment_in_sequence
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (f g : CFGKATExpression)
  :
  f dna x ->
  test x is v ;; (f ;; (assign v to x ;; g)) ==
    test x is v ;; (f ;; g).
Proof.
  intro Hf.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite
    (assignment_duplication_to_test_duplication
      x v f
      (assignment_duplication x v f Hf)).
  cfgkat_rewrite EqS1.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite <- (EqS1 (test x is v) (assign v to x) g).
  cfgkat_rewrite (EqA3 x v).
  apply EqSym.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite
    (assignment_duplication_to_test_duplication
      x v f
      (assignment_duplication x v f Hf)).
  cfgkat_rewrite EqS1.
  cfgkat_rewrite EqS1.
  apply EqRefl.
Qed.

Lemma assign_prefixed_dna_sequence_cong_from_assign
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e k1 k2 : CFGKATExpression)
  :
  e dna x ->
  assign v to x ;; k1 == assign v to x ;; k2 ->
  assign v to x ;; (e ;; k1) ==
    assign v to x ;; (e ;; k2).
Proof.
  intros He Hassign.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite (assignment_duplication x v e He).
  cfgkat_rewrite EqS1.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite Hassign.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite EqS1 at 2.
  cfgkat_rewrite <- (assignment_duplication x v e He).
  apply EqS1.
Qed.

Lemma assign_prefix_overwrite
  (x : IndicatorVariable)
  (old new : IndicatorValue)
  (e : CFGKATExpression)
  :
  assign old to x ;; (assign new to x ;; e) ==
    assign new to x ;; e.
Proof.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite EqA4.
  apply EqRefl.
Qed.

Lemma assign_prefix_sequence_right_cong_from_assign
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e f r : CFGKATExpression)
  :
  assign v to x ;; e == assign v to x ;; f ->
  assign v to x ;; (e ;; r) ==
    assign v to x ;; (f ;; r).
Proof.
  intro Hef.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite Hef.
  apply EqS1.
Qed.

Local Lemma assign_prefix_loopseq_left_cong_from_assign
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e f r : CFGKATExpression)
  :
  assign v to x ;; e == assign v to x ;; f ->
  assign v to x ;; (e |> r) ==
    assign v to x ;; (f |> r).
Proof.
  intro Hef.
  cfgkat_rewrite <- EqL8.
  cfgkat_rewrite Hef.
  apply EqL8.
Qed.

Lemma assign_prefixed_dna_loopseq_cong_from_assign
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e k1 k2 : CFGKATExpression)
  :
  e dna x ->
  assign v to x ;; k1 == assign v to x ;; k2 ->
  assign v to x ;; (e |> k1) ==
    assign v to x ;; (e |> k2).
Proof.
  intros He Hk.
  cfgkat_rewrite <- EqL8.
  cfgkat_rewrite (indpushloopseq x v e k1 He).
  cfgkat_rewrite Hk.
  cfgkat_rewrite <- (indpushloopseq x v e k2 He).
  apply EqL8.
Qed.


Fixpoint expression_gotos_copied_by_assignment
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  : Prop :=
  match e with
  | CFGKATAssert _ => True
  | CFGKATAction _ => True
  | CFGKATAssign _ _ => True
  | CFGKATBreak => True
  | CFGKATContinue => True
  | CFGKATReturn => True
  | CFGKATGoto _ => False
  | CFGKATChoice _ e1 e2 =>
      expression_gotos_copied_by_assignment x v e1 /\
      expression_gotos_copied_by_assignment x v e2
  | CFGKATSequence (CFGKATAssign y w) (CFGKATGoto _) =>
      y = x /\ w = v
  | CFGKATSequence e1 e2 =>
      expression_gotos_copied_by_assignment x v e1 /\
      expression_gotos_copied_by_assignment x v e2
  | CFGKATLoopSeq e1 e2 =>
      expression_gotos_copied_by_assignment x v e1 /\
      expression_gotos_copied_by_assignment x v e2
  | CFGKATLoop _ body =>
      expression_gotos_copied_by_assignment x v body
  end.

Fixpoint expression_assigns_indicator_only_value
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  : Prop :=
  match e with
  | CFGKATAssert _ => True
  | CFGKATAction _ => True
  | CFGKATAssign y w => y <> x \/ w = v
  | CFGKATBreak => True
  | CFGKATContinue => True
  | CFGKATReturn => True
  | CFGKATGoto _ => True
  | CFGKATChoice _ e1 e2 =>
      expression_assigns_indicator_only_value x v e1 /\
      expression_assigns_indicator_only_value x v e2
  | CFGKATSequence e1 e2 =>
      expression_assigns_indicator_only_value x v e1 /\
      expression_assigns_indicator_only_value x v e2
  | CFGKATLoopSeq e1 e2 =>
      expression_assigns_indicator_only_value x v e1 /\
      expression_assigns_indicator_only_value x v e2
  | CFGKATLoop _ body =>
      expression_assigns_indicator_only_value x v body
  end.

Definition label_environment_assigns_indicator_only_value
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (E : label_environment CFGKATExpression)
  : Prop :=
  forall l body,
    E l = Some body ->
    expression_assigns_indicator_only_value x v body.

Local Definition output_assigns_indicator_only_value
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : Prop :=
  match r with
  | CFGKATAutomatonReject => True
  | CFGKATAutomatonAccept i => i x = v
  | CFGKATAutomatonBreak i => i x = v
  | CFGKATAutomatonContinue i => i x = v
  | CFGKATAutomatonReturn => True
  | CFGKATAutomatonJump _ i => i x = v
  | CFGKATAutomatonNext _ (e, i) =>
      i x = v /\ expression_assigns_indicator_only_value x v e
  end.

Local Lemma expression_assigns_indicator_only_value_finite_dynamics
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (s : CFGKATSyntConfiguration)
  (a : Atom)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  CFGKATExpressionFiniteDynamics s a r ->
  forall e i,
    s = (e, i) ->
    expression_assigns_indicator_only_value x v e ->
    i x = v ->
    output_assigns_indicator_only_value x v r.
Proof.
  intro Hdyn.
  induction Hdyn; intros e0 i0 Hstate Honly Hx;
    inversion Hstate; subst e0 i0; cbn in Honly; cbn.
  - exact Hx.
  - destruct Honly as [Hneq | Hv].
    + unfold update.
      destruct (Var_eq_dec x0 x) as [Heq | _].
      * contradiction.
      * exact Hx.
    + subst v0.
      unfold update.
      destruct (Var_eq_dec x0 x) as [_ | _].
      * reflexivity.
      * exact Hx.
  - split; [exact Hx | exact I].
  - exact Hx.
  - exact Hx.
  - exact I.
  - exact Hx.
  - destruct Honly as [Honly1 _].
    eapply IHHdyn; eauto.
  - destruct Honly as [_ Honly2].
    eapply IHHdyn; eauto.
  - destruct Honly as [Honly1 Honly2].
    pose proof (IHHdyn1 _ _ eq_refl Honly1 Hx) as Hhead.
    exact (IHHdyn2 _ _ eq_refl Honly2 Hhead).
  - exact I.
  - exact I.
  - destruct Honly as [Honly1 _].
    eapply IHHdyn; eauto.
  - destruct Honly as [Honly1 _].
    eapply IHHdyn; eauto.
  - destruct Honly as [Honly1 _].
    eapply IHHdyn; eauto.
  - destruct Honly as [Honly1 Honly2].
    pose proof (IHHdyn _ _ eq_refl Honly1 Hx)
      as [Hnext_value Hnext_only].
    split; [exact Hnext_value | split; assumption].
  - destruct Honly as [Honly1 Honly2].
    pose proof (IHHdyn1 _ _ eq_refl Honly1 Hx) as Hhead.
    exact (IHHdyn2 _ _ eq_refl Honly2 Hhead).
  - exact I.
  - exact I.
  - destruct Honly as [Honly1 _].
    eapply IHHdyn; eauto.
  - destruct Honly as [Honly1 Honly2].
    pose proof (IHHdyn1 _ _ eq_refl Honly1 Hx) as Hhead.
    exact (IHHdyn2 _ _ eq_refl Honly2 Hhead).
  - destruct Honly as [Honly1 _].
    eapply IHHdyn; eauto.
  - destruct Honly as [Honly1 Honly2].
    pose proof (IHHdyn _ _ eq_refl Honly1 Hx)
      as [Hnext_value Hnext_only].
    split; [exact Hnext_value | split; assumption].
  - eapply IHHdyn; eauto.
    simpl. split; assumption.
  - exact Hx.
Qed.

Local Lemma expression_assigns_indicator_only_value_transition_output
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  (i : IndicatorAssignment)
  (a : Atom)
  :
  expression_assigns_indicator_only_value x v e ->
  i x = v ->
  output_assigns_indicator_only_value x v (transition_output e a i).
Proof.
  intros Honly Hx.
  pose proof (transition_output_spec e a i) as Hdyn.
  inversion Hdyn as [s a0 r0 Hfinite | s a0 Hnone]; subst.
  - eapply expression_assigns_indicator_only_value_finite_dynamics; eauto.
  - exact I.
Qed.

Definition assignment_prefixed_environment
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (E : label_environment CFGKATExpression)
  : label_environment CFGKATExpression.
Proof.
  refine (mk_environment
    (fun l =>
      match E l with
      | Some body => Some (assign v to x ;; body)
      | None => None
      end)
    (env_support E)
    _).
  intros l body Hlookup.
  destruct (E l) as [old_body |] eqn:HE.
  - eapply env_supported. exact HE.
  - discriminate Hlookup.
Defined.


Local Lemma assignment_copied_gotos_context_switch
  (E F : label_environment CFGKATExpression)
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (h : CFGKATExpression)
  :
  expression_gotos_copied_by_assignment x v h ->
  (forall l,
    contains_goto l h ->
    E |- assign v to x ;; goto l ==
      assign v to x ;; goto l -| F) ->
  E |- h == h -| F.
Proof.
  revert E F.
	  induction h as
	    [b | p | y w | | | | l | b h1 IH1 h2 IH2
	     | h1 IH1 h2 IH2 | h1 IH1 h2 IH2 | b body IH];
	    intros E F Hcopy Hgoto;
	    cbn [expression_gotos_copied_by_assignment] in Hcopy.
	  all: try (apply strong_equiv_no_goto; intro k; simpl; tauto).
	  - destruct Hcopy as [Hcopy1 Hcopy2].
    apply EqChoiceCong.
    + apply IH1.
      * exact Hcopy1.
      * intros k Hk. apply Hgoto. simpl. left. exact Hk.
    + apply IH2.
      * exact Hcopy2.
      * intros k Hk. apply Hgoto. simpl. right. exact Hk.
  - destruct h1 as
      [b1 | p1 | y1 w1 | | | | l1 | b1 a1 a2
       | a1 a2 | a1 a2 | b1 a1];
      destruct h2 as
      [b2 | p2 | y2 w2 | | | | l2 | b2 c1 c2
       | c1 c2 | c1 c2 | b2 c1];
      cbn [expression_gotos_copied_by_assignment] in Hcopy;
      try
        (destruct Hcopy as [Hcopy1 Hcopy2];
         apply EqSeqRightCong;
         [ apply IH2;
           [ exact Hcopy2
           | intros k Hk; apply Hgoto; simpl; right; exact Hk ]
         | apply IH1;
           [ exact Hcopy1
           | intros k Hk; apply Hgoto; simpl; left; exact Hk ]]).
    destruct Hcopy as [Hy Hv].
    subst y1 w1.
    apply Hgoto.
    simpl. right. reflexivity.
  - destruct Hcopy as [Hcopy1 Hcopy2].
    apply EqLoopSeqRightCong.
    + apply IH2.
      * exact Hcopy2.
      * intros k Hk. apply Hgoto. simpl. right. exact Hk.
    + apply IH1.
      * exact Hcopy1.
      * intros k Hk. apply Hgoto. simpl. left. exact Hk.
  - apply EqLoopBodyCong.
    apply IH.
    + exact Hcopy.
    + intros k Hk. apply Hgoto. simpl. exact Hk.
Qed.

Local Definition assignment_prefixed_bridge_relation
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (l : Label)
  (s t : CFGKATSyntConfiguration)
  : Prop :=
  (exists i,
      s = (assign v to x ;; goto l, i) /\
      t = (assign v to x ;; goto l, i)) \/
  (exists e i,
      i x = v /\
      expression_assigns_indicator_only_value x v e /\
      s = (e, i) /\
      t = (e, i)) \/
  (exists e i,
      i x = v /\
      expression_assigns_indicator_only_value x v e /\
      s = (e, i) /\
      t = (assign v to x ;; e, i)).

Local Lemma assignment_prefixed_bridge_strong_outputs
  (E : label_environment CFGKATExpression)
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (l : Label)
  (s t : CFGKATSyntConfiguration)
  (a : Atom)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  label_environment_assigns_indicator_only_value x v E ->
  output_assigns_indicator_only_value x v r ->
  CFGKATExpressionDynamics s a r ->
  CFGKATExpressionDynamics t a r ->
  CFGKATStrongStep
    CFGKATExpressionAutomaton
    CFGKATExpressionAutomaton
    [lift E]
    [lift (assignment_prefixed_environment x v E)]
    (assignment_prefixed_bridge_relation x v l)
    a s t.
Proof.
  intros Henv Hout Hleft Hright.
  destruct r as [|i|i|i| |k i|p [e i]]; cbn in Hout.
  - strong_halt_output
      (@CFGKATAutomatonReject CFGKATSyntConfiguration) Hleft Hright.
  - strong_halt_output
      (@CFGKATAutomatonAccept CFGKATSyntConfiguration i) Hleft Hright.
  - strong_halt_output
      (@CFGKATAutomatonBreak CFGKATSyntConfiguration i) Hleft Hright.
  - strong_halt_output
      (@CFGKATAutomatonContinue CFGKATSyntConfiguration i) Hleft Hright.
  - strong_halt_output
      (@CFGKATAutomatonReturn CFGKATSyntConfiguration) Hleft Hright.
  - destruct (E k) as [body |] eqn:HE.
    + eapply CFGKATStrongStepSilent with
        (x1' := (body, i))
        (x2' := (assign v to x ;; body, i)).
      * eapply CFGKATSilentBoundJump with (ys := []).
        -- simpl. exact Hleft.
        -- apply lift_label_some. exact HE.
      * eapply CFGKATSilentBoundJump with (ys := []).
        -- simpl. exact Hright.
        -- apply lift_label_some.
           unfold assignment_prefixed_environment, mk_environment.
           simpl. rewrite HE. reflexivity.
      * right. right.
        exists body, i.
        repeat split; try reflexivity.
        -- exact Hout.
        -- eapply Henv. exact HE.
    + eapply CFGKATStrongStepHalt with
        (zeta := CFGKATAutomatonJump k i).
      * simpl. constructor.
      * eapply Hlift_free_jump.
        -- exact Hleft.
        -- constructor.
           ++ apply lift_label_none. exact HE.
           ++ constructor.
      * eapply Hlift_free_jump with (ys := [lift (assignment_prefixed_environment x v E)]).
        -- exact Hright.
        -- constructor.
           ++ apply lift_label_none.
              unfold assignment_prefixed_environment, mk_environment.
              simpl. rewrite HE. reflexivity.
           ++ constructor.
  - destruct Hout as [Hi Honly].
    eapply CFGKATStrongStepNext.
    + lift_raw_transition Hleft.
    + lift_raw_transition Hright.
    + right. left.
      exists e, i.
      repeat split; try reflexivity; assumption.
Qed.

Local Lemma assignment_prefixed_environment_copied_goto_bridge
  (E : label_environment CFGKATExpression)
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (l : Label)
  :
  label_environment_assigns_indicator_only_value x v E ->
  E |- assign v to x ;; goto l ==
    assign v to x ;; goto l -|
    assignment_prefixed_environment x v E.
Proof.
  intro Henv.
  apply completeness.
  intro i.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar.
  change
    (exists R :
      CFGKATAutomatonBisimulation
        (resolve_list CFGKATExpressionAutomaton [lift E])
        (resolve_list CFGKATExpressionAutomaton
          [lift (assignment_prefixed_environment x v E)]),
      cfgkat_relation R (assign v to x ;; goto l, i)
        (assign v to x ;; goto l, i)).
  unshelve eexists.
  - refine
      (@strong_bisim_to_bisim
        CFGKATExpressionAutomaton
        CFGKATExpressionAutomaton
        [lift E]
        [lift (assignment_prefixed_environment x v E)]
        _).
    refine
      (@Build_CFGKATStrongBisimulation
        CFGKATExpressionAutomaton
        CFGKATExpressionAutomaton
        [lift E]
        [lift (assignment_prefixed_environment x v E)]
        (assignment_prefixed_bridge_relation x v l)
        _).
    intros s t a Hrel.
    destruct s as [es idxs].
    destruct t as [et it].
    unfold assignment_prefixed_bridge_relation in Hrel.
    destruct Hrel as
      [[i0 [Hs Ht]] |
       [[e0 [i0 [Hi [Honly [Hs Ht]]]]] |
        [e0 [i0 [Hi [Honly [Hs Ht]]]]]]];
      inversion Hs; subst es idxs; clear Hs;
      inversion Ht; subst et it; clear Ht.
    + eapply assignment_prefixed_bridge_strong_outputs
      with (r := transition_output (assign v to x ;; goto l) a i0).
      * exact Henv.
      * rewrite transition_sequence.
        rewrite transition_assign.
        simpl.
        rewrite transition_goto.
        apply update_same.
      * apply transition_output_spec.
      * apply transition_output_spec.
    + eapply assignment_prefixed_bridge_strong_outputs
      with (r := transition_output e0 a i0).
      * exact Henv.
      * apply expression_assigns_indicator_only_value_transition_output.
        -- exact Honly.
        -- try assumption; reflexivity.
      * apply transition_output_spec.
      * apply transition_output_spec.
    + pose proof
        (assignment_prefix_transition_same x v e0 i0 a Hi)
        as Hsame.
      pose proof
        (transition_output_spec (assign v to x ;; e0) a i0)
        as Hright.
      rewrite Hsame in Hright.
      eapply assignment_prefixed_bridge_strong_outputs
      with (r := transition_output e0 a i0).
      * exact Henv.
      * apply expression_assigns_indicator_only_value_transition_output.
        -- exact Honly.
        -- try assumption; reflexivity.
      * apply transition_output_spec.
      * exact Hright.
  - left.
    exists i.
    split; reflexivity.
Qed.

Lemma assignment_copied_gotos_prefix_environment
  (E : label_environment CFGKATExpression)
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (h : CFGKATExpression)
  :
  expression_gotos_copied_by_assignment x v h ->
  label_environment_assigns_indicator_only_value x v E ->
  E |- h == h -| assignment_prefixed_environment x v E.
Proof.
  intros Hcopy Henv.
  apply (assignment_copied_gotos_context_switch
    E (assignment_prefixed_environment x v E) x v h).
  - exact Hcopy.
  - intros l _.
    apply assignment_prefixed_environment_copied_goto_bridge.
    exact Henv.
Qed.


Fixpoint assignment_copied_goto_normal_form
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  : CFGKATExpression :=
  match e with
  | CFGKATAssert b => CFGKATAssert b
  | CFGKATAction p => CFGKATAction p
  | CFGKATAssign y w => CFGKATAssign y w
  | CFGKATBreak => CFGKATBreak
  | CFGKATContinue => CFGKATContinue
  | CFGKATReturn => CFGKATReturn
  | CFGKATGoto l => assign v to x ;; goto l
  | CFGKATChoice b e1 e2 =>
      if b then
        assignment_copied_goto_normal_form x v e1
      else
        assignment_copied_goto_normal_form x v e2
  | CFGKATSequence e1 e2 =>
      assignment_copied_goto_normal_form x v e1 ;;
      assignment_copied_goto_normal_form x v e2
  | CFGKATLoopSeq e1 e2 =>
      assignment_copied_goto_normal_form x v e1 |>
      assignment_copied_goto_normal_form x v e2
  | CFGKATLoop b body =>
      while b do assignment_copied_goto_normal_form x v body
  end.

Notation "e '^C[' x ',' v ']'" :=
  (assignment_copied_goto_normal_form x v e)
  (at level 40).

Lemma assignment_copied_goto_normal_form_copied
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  :
  expression_gotos_copied_by_assignment x v (e^C[x, v]).
Proof.
  induction e as
    [b | p | y w | | | | l | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b body IH];
    cbn [assignment_copied_goto_normal_form
      expression_gotos_copied_by_assignment];
    try exact I.
  - split; reflexivity.
  - split; assumption.
  - remember (e1^C[x, v]) as e1c.
    destruct e1c; try (split; assumption).
    destruct e2 as
      [b0 | p0 | y0 w0 | | | | l0 | b0 d1 d2
       | d1 d2 | d1 d2 | b0 d1];
      cbn [assignment_copied_goto_normal_form]; split; assumption.
  - split; assumption.
  - exact IH.
Qed.

Lemma assignment_prefix_preserves_copied_gotos
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  :
  expression_gotos_copied_by_assignment x v e ->
  expression_gotos_copied_by_assignment x v (assign v to x ;; e).
Proof.
  destruct e as
    [b | p | y w | | | | l | b e1 e2
     | e1 e2 | e1 e2 | b body];
    cbn [expression_gotos_copied_by_assignment];
    intro Hcopy; try (split; [exact I | exact Hcopy]).
  split; reflexivity.
Qed.

Lemma expression_gotos_copied_sequence_intro
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e f : CFGKATExpression)
  :
  expression_gotos_copied_by_assignment x v e ->
  expression_gotos_copied_by_assignment x v f ->
  expression_gotos_copied_by_assignment x v (e ;; f).
Proof.
  destruct e as
    [b1 | p1 | y1 w1 | | | | l1 | b1 e1 e2
     | e1 e2 | e1 e2 | b1 body1];
    destruct f as
    [b2 | p2 | y2 w2 | | | | l2 | b2 f1 f2
     | f1 f2 | f1 f2 | b2 body2];
    cbn [expression_gotos_copied_by_assignment];
    tauto.
Qed.

Lemma expression_gotos_copied_loopseq_intro
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e f : CFGKATExpression)
  :
  expression_gotos_copied_by_assignment x v e ->
  expression_gotos_copied_by_assignment x v f ->
  expression_gotos_copied_by_assignment x v (e |> f).
Proof.
  simpl. tauto.
Qed.

Lemma expression_gotos_copied_loop_intro
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  (e : CFGKATExpression)
  :
  expression_gotos_copied_by_assignment x v e ->
  expression_gotos_copied_by_assignment x v (while b do e).
Proof.
  simpl. exact (fun H => H).
Qed.

Local Lemma assignment_copied_goto_loopinvariant_premise_dna
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  (e e' : CFGKATExpression)
  :
  e dna x ->
  assign v to x ;; e == assign v to x ;; e' ->
  test ((x is v) and b) ;; (e' |> 1) ==
    test ((x is v) and b) ;; ((e' |> 1) ;; test x is v).
Proof.
  intros He Hnormal.
  cfgkat_rewrite <-
    (assign_prefix_equiv_to_test_and_indicator_prefix x v b
      (e |> 1) (e' |> 1)
      (assign_prefix_loopseq_left_cong_from_assign
        x v e e' 1 Hnormal)).
  cfgkat_rewrite
    (assignment_duplication_loopinvariant_premise_dna_any_guard
      x v b e He).
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite
    (assign_prefix_equiv_to_test_and_indicator_prefix x v b
      (e |> 1) (e' |> 1)
      (assign_prefix_loopseq_left_cong_from_assign
        x v e e' 1 Hnormal)).
  apply EqS1.
Qed.

Theorem assignment_copied_goto_normal_form_equiv
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  :
  e dna x ->
  assign v to x ;; e == assign v to x ;; e^C[x, v].
Proof.
  revert x v.
  induction e as
    [b | p | y vy | | | | l | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b e IH];
    intros x v Hno;
    cbn [assignment_copied_goto_normal_form] in *.
  - apply EqRefl.
  - apply EqRefl.
  - apply EqRefl.
  - apply EqRefl.
  - apply EqRefl.
  - apply EqRefl.
  - apply EqSym.
    cfgkat_rewrite <- EqS1.
    cfgkat_rewrite EqA4.
    apply EqRefl.
  - destruct Hno as [H1 H2].
    apply assign_prefix_choice_cong_from_assign.
    + apply IH1. exact H1.
    + apply IH2. exact H2.
  - destruct Hno as [H1 H2].
    cfgkat_rewrite (assign_prefixed_dna_sequence_cong_from_assign
      x v e1 e2 (e2^C[x, v]) H1 (IH2 x v H2)).
    apply assign_prefix_sequence_right_cong_from_assign.
    apply IH1. exact H1.
  - destruct Hno as [H1 H2].
    cfgkat_rewrite (assign_prefixed_dna_loopseq_cong_from_assign
      x v e1 e2 (e2^C[x, v]) H1 (IH2 x v H2)).
    apply assign_prefix_loopseq_left_cong_from_assign.
    apply IH1. exact H1.
  - pose proof (IH x v Hno) as Hnormal_body.
    apply assign_prefixed_from_tested.
    cfgkat_rewrite (loop_zero_invariant_dna x v b e Hno).
    assert (Htest_normal :
      test x is v ;; e == test x is v ;; e^C[x, v]).
    {
      cfgkat_rewrite <- (EqA3 x v) at 1;
      cfgkat_rewrite (EqS1 (test x is v) (assign v to x) e);
      cfgkat_rewrite Hnormal_body;
      cfgkat_rewrite <- (EqS1 (test x is v) (assign v to x) (e^C[x, v]));
      cfgkat_rewrite (EqA3 x v);
      apply EqRefl.
    }
    cfgkat_rewrite Htest_normal.
    cfgkat_rewrite <- (loopinvariant (x is v) b (e^C[x, v])
      (assignment_copied_goto_loopinvariant_premise_dna
        x v b e (e^C[x, v]) Hno Hnormal_body)).
    apply EqRefl.
Qed.


Lemma assignment_prefix_environment
  (E : label_environment CFGKATExpression)
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (h : CFGKATExpression)
  :
  h dna x ->
  label_environment_assigns_indicator_only_value x v E ->
  E |- assign v to x ;; h ==
    assign v to x ;; h -| assignment_prefixed_environment x v E.
Proof.
  intros Hno Henv.
  cfgkat_rewrite (weaken_empty_to_env E _ _
    (assignment_copied_goto_normal_form_equiv x v h Hno)).
  cfgkat_rewrite (assignment_copied_gotos_prefix_environment
    E x v (assign v to x ;; h^C[x, v])
    (assignment_prefix_preserves_copied_gotos x v (h^C[x, v])
      (assignment_copied_goto_normal_form_copied x v h))
    Henv).
  now cfgkat_rewrite <- (weaken_empty_to_env
    (assignment_prefixed_environment x v E) _ _
	    (assignment_copied_goto_normal_form_equiv x v h Hno)).
Qed.


Definition label_binding_equiv
  (old new : option CFGKATExpression)
  : Prop :=
  match old, new with
  | Some old_body, Some new_body => old_body == new_body
  | None, None => True
  | _, _ => False
  end.

Local Fixpoint environment_replace_labels
  (labels : list Label)
  (Eold Enew : label_environment CFGKATExpression)
  : label_environment CFGKATExpression :=
  match labels with
  | [] => Eold
  | k :: labels' =>
      match Enew k with
      | Some body =>
          label_set
            (environment_replace_labels labels' Eold Enew)
            k body
      | None => environment_replace_labels labels' Eold Enew
      end
  end.

Local Lemma label_set_shadow
  (E : label_environment CFGKATExpression)
  (k : Label)
  (old_body new_body : CFGKATExpression)
  :
  label_set (label_set E k old_body) k new_body =
    label_set E k new_body.
Proof.
  apply environment_eq.
  intro l.
  unfold label_set, mk_environment.
  cbn.
  destruct (Label_eq_dec k l) as [_ | _]; reflexivity.
Qed.

Local Lemma environment_replace_labels_not_in
  (labels : list Label)
  (Eold Enew : label_environment CFGKATExpression)
  (k : Label)
  :
  ~ In k labels ->
  environment_replace_labels labels Eold Enew k = Eold k.
Proof.
  induction labels as [|l labels IH]; intro Hnotin.
  - reflexivity.
  - simpl.
    destruct (Enew l) as [body |] eqn:HEnew.
    + unfold label_set, mk_environment.
      cbn.
      destruct (Label_eq_dec l k) as [Heq | Hneq].
      * subst l. exfalso. apply Hnotin. left. reflexivity.
      * apply IH. intro Hin. apply Hnotin. right. exact Hin.
    + apply IH. intro Hin. apply Hnotin. right. exact Hin.
Qed.

Local Lemma label_replacement_step
  (E : label_environment CFGKATExpression)
  (k : Label)
  (old_body new_body h : CFGKATExpression)
  :
  E k = Some old_body ->
  old_body == new_body ->
  E |- h == h -| label_set E k new_body.
Proof.
  intros HE Hbody.
  set (Base := label_remove E k).
  assert (HCur_eq : E = label_set Base k old_body).
  {
    symmetry.
    unfold Base.
    apply label_remove_set_same.
    exact HE.
  }
  rewrite HCur_eq.
  rewrite label_set_shadow.
  assert (Hfresh : label_fresh Base k).
  { unfold Base. apply label_remove_fresh. }
  rewrite (@label_set_as_extend Base k old_body Hfresh).
  rewrite (@label_set_as_extend Base k new_body Hfresh).
  apply EqC2.
  apply weaken_empty_to_env.
  exact Hbody.
Qed.

Local Lemma environment_replace_labels_induction_on
  (labels : list Label)
  (Eold Enew : label_environment CFGKATExpression)
  (h : CFGKATExpression)
  :
  NoDup labels ->
  (forall k, label_binding_equiv (Eold k) (Enew k)) ->
  Eold |- h == h -| environment_replace_labels labels Eold Enew.
Proof.
  induction labels as [|k labels IH]; intros Hnodup Hagree.
  - apply EqRefl.
  - inversion Hnodup as [|? ? Hnotin Hnodup_tail]; subst.
    simpl.
    destruct (Enew k) as [new_body |] eqn:Hnew.
    + cfgkat_rewrite (IH Hnodup_tail Hagree).
      specialize (Hagree k).
      rewrite Hnew in Hagree.
      destruct (Eold k) as [old_body |] eqn:Hold.
      * apply label_replacement_step with (old_body := old_body).
        -- rewrite environment_replace_labels_not_in.
           ++ exact Hold.
           ++ exact Hnotin.
        -- exact Hagree.
      * contradiction.
    + apply IH.
      * exact Hnodup_tail.
      * exact Hagree.
Qed.

Local Lemma environment_replace_labels_complete
  (labels : list Label)
  (Eold Enew : label_environment CFGKATExpression)
  :
  (forall k, In k labels -> label_in_dom Enew k) ->
  (forall k, ~ In k labels -> Eold k = Enew k) ->
  environment_replace_labels labels Eold Enew = Enew.
Proof.
  intros Hdom Houtside.
  apply environment_eq.
  intro k.
  specialize (Houtside k) as Houtside.
  revert Hdom Houtside.
  induction labels as [|l labels IH]; intros Hdom Houtside.
  - apply Houtside. intro Hin. contradiction.
  - simpl.
    destruct (Hdom l (or_introl eq_refl)) as [body Hbody].
    rewrite Hbody.
    unfold label_set, mk_environment.
    cbn.
    destruct (Label_eq_dec l k) as [Heq | Hneq].
    + subst k. symmetry. exact Hbody.
    + apply IH.
      * intros m Hin.
        apply Hdom. right. exact Hin.
      * intro Hnotin_tail.
        apply Houtside.
        intro Hin.
        destruct Hin as [Hin | Hin].
        -- subst k. contradiction.
        -- contradiction.
Qed.

Lemma iterated_environment_replacement
  (Eold Enew : label_environment CFGKATExpression)
  (h : CFGKATExpression)
  :
  (forall k, label_binding_equiv (Eold k) (Enew k)) ->
  Eold |- h == h -| Enew.
Proof.
  intro Hagree.
  set (labels :=
    List.filter
      (fun k =>
        match Enew k with
        | Some _ => true
        | None => false
        end)
      (List.nodup Label_eq_dec (env_support Enew))).
  replace Enew with
    (environment_replace_labels labels Eold Enew).
  - apply environment_replace_labels_induction_on.
    + unfold labels.
      apply NoDup_filter.
      apply List.NoDup_nodup.
    + exact Hagree.
  - apply environment_replace_labels_complete.
    + intros k Hin.
      unfold labels in Hin.
      rewrite List.filter_In in Hin.
      destruct Hin as [_ Hdefined].
      destruct (Enew k) as [body |] eqn:HE.
      * exists body. exact HE.
      * discriminate Hdefined.
    + intros k Hnotin.
      destruct (Enew k) as [new_body |] eqn:Hnew.
      * exfalso. apply Hnotin.
        unfold labels.
        apply List.filter_In.
        split.
        -- apply List.nodup_In.
           eapply env_supported. exact Hnew.
        -- rewrite Hnew. reflexivity.
      * specialize (Hagree k).
        rewrite Hnew in Hagree.
        destruct (Eold k) as [old_body |] eqn:Hold.
        -- contradiction.
        -- reflexivity.
Qed.

Lemma assignment_copied_goto_normal_form_does_not_test_indicator
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  :
  expression_does_not_test_indicator x e ->
  expression_does_not_test_indicator x (e^C[x, v]).
Proof.
  induction e as
    [b | p | y w | | | | l | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b body IH];
    cbn [assignment_copied_goto_normal_form
      expression_does_not_test_indicator];
    intro Hno; try exact Hno; try exact I.
  - split; exact I.
  - destruct Hno as [Hb [H1 H2]].
    repeat split; [exact Hb | apply IH1 | apply IH2]; assumption.
  - destruct Hno as [H1 H2].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [H1 H2].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [Hb Hbody].
    split; [exact Hb | apply IH; exact Hbody].
Qed.

Local Lemma assignment_copied_goto_normal_form_no_break_continue
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  :
  no_break_continue e ->
  no_break_continue (e^C[x, v]).
Proof.
  induction e as
    [b | p | y w | | | | l | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b body IH];
    cbn [assignment_copied_goto_normal_form no_break_continue];
    intro Hno; try exact Hno; try exact I; try contradiction.
  - split; exact I.
  - destruct Hno as [H1 H2].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [H1 H2].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [H1 H2].
    split; [apply IH1 | apply IH2]; assumption.
  - apply IH. exact Hno.
Qed.

Lemma assignment_copied_goto_normal_form_well_nested
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  :
  well_nested e ->
  well_nested (e^C[x, v]).
Proof.
  intro Hwn.
  induction Hwn.
  - apply WN_base.
    apply assignment_copied_goto_normal_form_no_break_continue.
    exact H.
  - cbn [assignment_copied_goto_normal_form].
    apply WN_loopseq. exact IHHwn.
  - cbn [assignment_copied_goto_normal_form].
    apply WN_loop.
  - cbn [assignment_copied_goto_normal_form].
    apply WN_seq; assumption.
  - cbn [assignment_copied_goto_normal_form].
    apply WN_choice; assumption.
Qed.

Lemma contains_goto_assignment_copied_goto_normal_form
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (l : Label)
  (e : CFGKATExpression)
  :
  contains_goto l (e^C[x, v]) ->
  contains_goto l e.
Proof.
  induction e as
    [b | p | y w | | | | k | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b body IH];
    cbn [assignment_copied_goto_normal_form contains_goto];
    intro Hcontains; try contradiction.
  - destruct Hcontains as [Hcontains | Hcontains].
    + contradiction.
    + exact Hcontains.
  - destruct Hcontains as [Hcontains | Hcontains].
    + left. apply IH1. exact Hcontains.
    + right. apply IH2. exact Hcontains.
  - destruct Hcontains as [Hcontains | Hcontains].
    + left. apply IH1. exact Hcontains.
    + right. apply IH2. exact Hcontains.
  - destruct Hcontains as [Hcontains | Hcontains].
    + left. apply IH1. exact Hcontains.
    + right. apply IH2. exact Hcontains.
  - apply IH. exact Hcontains.
Qed.


Lemma ghost_erase_assignment_copied_goto_normal_form
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  :
  e dna x ->
  ghost_erase x (e^C[x, v]) == e.
Proof.
  induction e as
    [b | p | y w | | | | l | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b body IH];
    cbn [assignment_copied_goto_normal_form ghost_erase];
    intro Hno; try apply EqRefl.
  - destruct (Var_eq_dec y x) as [Heq | Hneq].
    + contradiction.
    + apply EqRefl.
  - destruct (Var_eq_dec x x) as [_ | Hneq].
    + apply EqS3.
    + contradiction Hneq. reflexivity.
  - destruct Hno as [H1 H2].
    apply EqChoiceCong; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [H1 H2].
    cfgkat_rewrite (IH1 H1).
    cfgkat_rewrite (IH2 H2).
    apply EqRefl.
  - destruct Hno as [H1 H2].
    cfgkat_rewrite (IH1 H1).
    cfgkat_rewrite (IH2 H2).
    apply EqRefl.
  - apply EqLoopBodyEmptyCong.
    apply IH. exact Hno.
Qed.


Local Fixpoint program_no_break_continue
  (e : CFGKATProgramSyntax)
  : Prop :=
  match e with
  | CFGKATProgramBreak => False
  | CFGKATProgramContinue => False
  | CFGKATProgramChoice _ e1 e2 =>
      program_no_break_continue e1 /\ program_no_break_continue e2
  | CFGKATProgramSequence e1 e2 =>
      program_no_break_continue e1 /\ program_no_break_continue e2
  | CFGKATProgramLoopSeq e1 e2 =>
      program_no_break_continue e1 /\ program_no_break_continue e2
  | CFGKATProgramLoop _ body =>
      program_no_break_continue body
  | _ => True
  end.

Inductive program_well_nested : CFGKATProgramSyntax -> Prop :=
| PWN_base :
    forall e,
      program_no_break_continue e ->
      program_well_nested e
| PWN_loopseq :
    forall f w,
      program_well_nested w ->
      program_well_nested (f |> w)%cfgkat_program
| PWN_loop :
    forall b f,
      program_well_nested (while b do f)%cfgkat_program
| PWN_seq :
    forall w v,
      program_well_nested w ->
      program_well_nested v ->
      program_well_nested (w ;; v)%cfgkat_program
| PWN_choice :
    forall b w v,
      program_well_nested w ->
      program_well_nested v ->
      program_well_nested (if b then w else v)%cfgkat_program.

Lemma program_well_nested_sequence_left
  (e f : CFGKATProgramSyntax)
  :
  program_well_nested (e ;; f)%cfgkat_program ->
  program_well_nested e.
Proof.
  intro Hwn.
  inversion Hwn; subst.
  - apply PWN_base. simpl in H. tauto.
  - exact H1.
Qed.

Lemma program_well_nested_sequence_right
  (e f : CFGKATProgramSyntax)
  :
  program_well_nested (e ;; f)%cfgkat_program ->
  program_well_nested f.
Proof.
  intro Hwn.
  inversion Hwn; subst.
  - apply PWN_base. simpl in H. tauto.
  - exact H2.
Qed.

Definition program_ends_with_return
  (e : CFGKATProgramSyntax)
  : Prop :=
  exists prefix, e = (prefix ;; return)%cfgkat_program.

Fixpoint program_contains_goto
  (target : Label)
  (e : CFGKATProgramSyntax)
  : Prop :=
  match e with
  | CFGKATProgramAssert _
  | CFGKATProgramAction _
  | CFGKATProgramAssign _ _
  | CFGKATProgramBreak
  | CFGKATProgramContinue
  | CFGKATProgramReturn
  | CFGKATProgramLabel _ => False
  | CFGKATProgramGoto l => l = target
  | CFGKATProgramChoice _ e1 e2 =>
      program_contains_goto target e1 \/ program_contains_goto target e2
  | CFGKATProgramSequence e1 e2 =>
      program_contains_goto target e1 \/ program_contains_goto target e2
  | CFGKATProgramLoopSeq e1 e2 =>
      program_contains_goto target e1 \/ program_contains_goto target e2
  | CFGKATProgramLoop _ body =>
      program_contains_goto target body
  end.

Definition program_no_free_goto
  (e : CFGKATProgramSyntax)
  : Prop :=
  forall l, program_contains_goto l e -> program_label_occurs l e.

Local Lemma program_no_break_continue_erase
  (e : CFGKATProgramSyntax)
  :
  program_no_break_continue e ->
  no_break_continue (label_erase e).
Proof.
  induction e as
    [b | p | x v | | | | l | l | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b e IH];
    simpl; intuition.
Qed.

Local Lemma program_no_break_continue_extraction
  (e : CFGKATProgramSyntax)
  (l : Label)
  (body : CFGKATExpression)
  :
  program_no_break_continue e ->
  label_extraction_syntax e l = Some body ->
  no_break_continue body.
Proof.
  revert l body.
  induction e as
    [b | p | x v | | | | l0 | l0 | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b e IH];
    intros l body Hnbc Hbody; simpl in Hbody; try discriminate.
  - destruct (Label_eq_dec l0 l); inversion Hbody; subst.
    exact I.
  - destruct Hnbc as [H1 H2].
    destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody1.
    + inversion Hbody; subst.
      eapply IH1; eauto.
    + eapply IH2; eauto.
  - destruct Hnbc as [H1 H2].
    destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody1.
    + inversion Hbody; subst.
      split.
      * eapply IH1; eauto.
      * apply program_no_break_continue_erase. exact H2.
    + eapply IH2; eauto.
  - destruct Hnbc as [H1 H2].
    destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody1.
    + inversion Hbody; subst.
      split.
      * eapply IH1; eauto.
      * apply program_no_break_continue_erase. exact H2.
    + eapply IH2; eauto.
  - destruct (label_extraction_syntax e l) as [body1 |] eqn:Hinner;
      inversion Hbody; subst.
    split.
    + eapply IH; eauto.
    + simpl. apply program_no_break_continue_erase. exact Hnbc.
Qed.

Lemma program_well_nested_erase
  (e : CFGKATProgramSyntax)
  :
  program_well_nested e ->
  well_nested (label_erase e).
Proof.
  intro Hwn.
  induction Hwn.
  - apply WN_base.
    apply program_no_break_continue_erase. exact H.
  - simpl. apply WN_loopseq. exact IHHwn.
  - simpl. apply WN_loop.
  - simpl. apply WN_seq; assumption.
  - simpl. apply WN_choice; assumption.
Qed.

Local Lemma program_well_nested_extraction
  (e : CFGKATProgramSyntax)
  (l : Label)
  (body : CFGKATExpression)
  :
  program_well_nested e ->
  label_extraction_syntax e l = Some body ->
  well_nested body.
Proof.
  intro Hwn.
  revert l body.
  induction Hwn as
    [e Hnbc | f w Hwnw IHw | b f | w v Hwnw IHw Hwnv IHv
     | b w v Hwnw IHw Hwnv IHv];
    intros l body Hbody; simpl in Hbody.
  - apply WN_base.
    eapply program_no_break_continue_extraction; eauto.
  - destruct (label_extraction_syntax f l) as [body1 |] eqn:Hbody1.
    + inversion Hbody; subst.
      apply WN_loopseq.
      apply program_well_nested_erase. exact Hwnw.
    + eapply IHw. exact Hbody.
  - destruct (label_extraction_syntax f l) as [body1 |] eqn:Hinner;
      inversion Hbody; subst.
    apply WN_loopseq.
    apply WN_loop.
  - destruct (label_extraction_syntax w l) as [body1 |] eqn:Hbody1.
    + inversion Hbody; subst.
      apply WN_seq.
      * eapply IHw. exact Hbody1.
      * apply program_well_nested_erase. exact Hwnv.
    + eapply IHv. exact Hbody.
  - destruct (label_extraction_syntax w l) as [body1 |] eqn:Hbody1.
    + inversion Hbody; subst.
      eapply IHw. exact Hbody1.
    + eapply IHv. exact Hbody.
Qed.

Lemma program_well_nested_reduced
  (e : CFGKATProgramSyntax)
  :
  program_well_nested e ->
  well_nested (label_erase e) /\
  well_nested_env (label_extraction_syntax_environment e).
Proof.
  intro Hwn.
  split.
  - apply program_well_nested_erase. exact Hwn.
  - unfold well_nested_env, env_all, label_extraction_syntax_environment.
    intros l body Hbody.
    eapply program_well_nested_extraction; eauto.
Qed.

Lemma program_ends_with_return_reduced
  (e : CFGKATProgramSyntax)
  :
  program_ends_with_return e ->
  ends_with_return (label_erase e) /\
  env_all ends_with_return (label_extraction_syntax_environment e).
Proof.
  intros [prefix Heq].
  subst e.
  split.
  - exists (label_erase prefix). reflexivity.
  - unfold env_all, label_extraction_syntax_environment.
    intros l body Hbody.
    simpl in Hbody.
    destruct (label_extraction_syntax prefix l) as [body_prefix |] eqn:Hprefix;
      inversion Hbody; subst.
    exists body_prefix. reflexivity.
Qed.

Lemma program_contains_goto_erase
  (e : CFGKATProgramSyntax)
  (l : Label)
  :
  contains_goto l (label_erase e) ->
  program_contains_goto l e.
Proof.
  induction e as
    [b | p | x v | | | | k | k | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b e IH];
    simpl; intuition.
Qed.

Lemma label_extraction_contains_goto
  (e : CFGKATProgramSyntax)
  (k l : Label)
  (body : CFGKATExpression)
  :
  label_extraction_syntax e k = Some body ->
  contains_goto l body ->
  program_contains_goto l e.
Proof.
  revert k l body.
  induction e as
    [b | p | x v | | | | k0 | k0 | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b e IH];
    intros k l body Hbody Hcontains; simpl in Hbody; try discriminate.
  - destruct (Label_eq_dec k0 k); inversion Hbody; subst.
    simpl in Hcontains. contradiction.
  - destruct (label_extraction_syntax e1 k) as [body1 |] eqn:Hbody1.
    + inversion Hbody; subst.
      left. eapply IH1; eauto.
    + right. eapply IH2; eauto.
  - destruct (label_extraction_syntax e1 k) as [body1 |] eqn:Hbody1.
    + inversion Hbody; subst.
      destruct Hcontains as [Hcontains | Hcontains].
      * left. eapply IH1; eauto.
      * right. apply program_contains_goto_erase. exact Hcontains.
    + right. eapply IH2; eauto.
  - destruct (label_extraction_syntax e1 k) as [body1 |] eqn:Hbody1.
    + inversion Hbody; subst.
      destruct Hcontains as [Hcontains | Hcontains].
      * left. eapply IH1; eauto.
      * right. apply program_contains_goto_erase. exact Hcontains.
    + right. eapply IH2; eauto.
  - destruct (label_extraction_syntax e k) as [body1 |] eqn:Hinner;
      inversion Hbody; subst.
    destruct Hcontains as [Hcontains | Hcontains].
    + eapply IH; eauto.
    + apply program_contains_goto_erase. exact Hcontains.
Qed.

Lemma program_no_free_goto_reduced
  (e : CFGKATProgramSyntax)
  :
  program_no_free_goto e ->
  no_free_goto_expr (label_extraction_syntax_environment e) (label_erase e) /\
  no_free_goto_env (label_extraction_syntax_environment e).
Proof.
  intro Hfree.
  split.
  - intros l Hcontains.
    apply label_extraction_occurs_some.
    apply Hfree.
    apply program_contains_goto_erase.
    exact Hcontains.
  - intros k body Hbody l Hcontains.
    apply label_extraction_occurs_some.
    apply Hfree.
    eapply label_extraction_contains_goto; eauto.
Qed.
