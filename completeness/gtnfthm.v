Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.ClassicalDescription.
From Stdlib Require Import Lists.List.
Import ListNotations.

From CFGKAT.Completeness Require Export gtnflem2.

Local Open Scope cfgkat_scope.
Local Open Scope cfgkat_setoid_scope.


Local Lemma gtnflem2_env_lookup_expr
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (f : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  gtnflem2_reachable_state (E := E) (e := e) (f, i) ->
  gtnflem2_env supply (gtnf_supply_expr_label E e supply f) =
    Some (gtnflem2_state_body supply f).
Proof.
  intro Hreach.
  unfold gtnflem2_env, mk_environment.
  simpl.
  destruct (E (gtnf_supply_expr_label E e supply f)) as [body |] eqn:HE.
  - exfalso.
    pose proof
      (gtnf_supply_expr_label_fresh_original E e supply f
        (gtnf_supply_expr_label E e supply f) body
        (ex_intro _ i
          (gtnflem2_reachable_state_in_supply supply (f, i) Hreach))
        HE) as Hfresh.
    apply Hfresh. reflexivity.
  - rewrite gtnflem2_reachable_ell_source_in_some with (i := i).
    + reflexivity.
    + apply gtnflem2_reachable_states_contains. exact Hreach.
Qed.

Definition sysc_Y
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : CFGKATExpression :=
  match r with
  | CFGKATAutomatonNext p (f, i) =>
      do p ;;
      goto (gtnf_supply_label supply (f, i))
  | _ => sys r
  end.

Local Lemma sysc_Y_jump_label_inv
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  (i j : IndicatorAssignment)
  (a : Atom)
  (l : Label)
  :
  CFGKATExpressionDynamics (sysc_Y supply r, i) a
    (CFGKATAutomatonJump l j) ->
  exists j0, r = CFGKATAutomatonJump l j0.
Proof.
  intro Hdyn.
  pose proof
    (transition_output_unique
      (sysc_Y supply r) a i
      (CFGKATAutomatonJump l j) Hdyn) as Hout.
  destruct r as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p [f i_next]];
    simplify_sysc_transition_in Hout;
    try discriminate.
  injection Hout as Hlabel _.
  exists i_jump.
  rewrite Hlabel.
  reflexivity.
Qed.


Definition gtnf_body_Y
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (source : CFGKATSyntConfiguration)
  : CFGKATExpression :=
  let '(f, i) := source in
  guarded_atom_sum_all
    (fun a =>
      sysc_Y supply
        (resolved_transition_output E f a i)).

Definition gtnf_full_Y_body
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (source : CFGKATExpression)
  : CFGKATExpression :=
  guarded_sum_all
    (fun m =>
      sysc_Y supply
        (resolved_transition_output
          E source (AtIY_atom m) (AtIY_assignment m))).

Definition gtnf_assignment_prefixed_initial_sum
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  : CFGKATExpression :=
  guarded_assignment_sum_all
    (fun i =>
      complete_assignment i ;;
      goto (gtnf_supply_label supply (e, i))).

Definition gtnf_initial_sum
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  : CFGKATExpression :=
  guarded_assignment_sum_all
    (fun i =>
      goto (gtnf_supply_label supply (e, i))).


Inductive gtnfthm_reachable_state
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  : CFGKATSyntConfiguration -> Prop :=
| gtnfthm_reachable_initial :
    forall i, gtnfthm_reachable_state (e, i)
| gtnfthm_reachable_next :
    forall f i a p next,
      gtnfthm_reachable_state (f, i) ->
      resolved_transition_output E f a i =
        CFGKATAutomatonNext p next ->
      gtnfthm_reachable_state next.

Local Lemma gtnfthm_reachable_state_to_gtnflem2
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  :
  gtnfthm_reachable_state (E := E) (e := e) s ->
  gtnflem2_reachable_state (E := E) (e := e) s.
Proof.
  intro Hreach.
  induction Hreach.
  - apply gtnflem2_reachable_initial.
  - eapply gtnflem2_reachable_next; eauto.
Qed.

Definition gtnfthm_reachable_states
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  : list CFGKATSyntConfiguration :=
  filter
    (fun s =>
      match excluded_middle_informative
        (gtnfthm_reachable_state (E := E) (e := e) s) with
      | left _ => true
      | right _ => false
      end)
    (gtnf_supply_states E e supply).

Lemma gtnfthm_reachable_states_in_supply
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  :
  In s (gtnfthm_reachable_states supply) ->
  In s (gtnf_supply_states E e supply).
Proof.
  unfold gtnfthm_reachable_states.
  intro Hin.
  apply filter_In in Hin.
  exact (proj1 Hin).
Qed.

Lemma gtnfthm_reachable_states_in_reachable
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  :
  In s (gtnfthm_reachable_states supply) ->
  gtnfthm_reachable_state (E := E) (e := e) s.
Proof.
  unfold gtnfthm_reachable_states.
  intro Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Hselected].
  destruct (excluded_middle_informative
    (gtnfthm_reachable_state (E := E) (e := e) s))
    as [Hreach | Hnot]; [exact Hreach | discriminate Hselected].
Qed.

Lemma gtnfthm_reachable_states_contains
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  :
  gtnfthm_reachable_state (E := E) (e := e) s ->
  In s (gtnfthm_reachable_states supply).
Proof.
  intro Hreach.
  unfold gtnfthm_reachable_states.
  apply filter_In.
  split.
  - eapply gtnflem2_reachable_state_in_supply.
    apply (gtnfthm_reachable_state_to_gtnflem2 supply).
    exact Hreach.
  - destruct (excluded_middle_informative
      (gtnfthm_reachable_state (E := E) (e := e) s))
      as [_ | Hnot]; [reflexivity | contradiction].
Qed.

Lemma gtnfthm_reachable_states_label_injective
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  forall s t,
    In s (gtnfthm_reachable_states supply) ->
    In t (gtnfthm_reachable_states supply) ->
    gtnf_supply_label supply s = gtnf_supply_label supply t ->
    s = t.
Proof.
  intros s t Hs Ht Hlabel.
  eapply gtnf_supply_label_injective.
  - eapply gtnfthm_reachable_states_in_supply. exact Hs.
  - eapply gtnfthm_reachable_states_in_supply. exact Ht.
  - exact Hlabel.
Qed.

Local Definition gtnf_prefix_body
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (source : CFGKATSyntConfiguration)
  : CFGKATExpression :=
  let '(f, i) := source in
  complete_assignment i ;; gtnflem2_state_body supply f.


Definition gtnfthm_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  : label_environment CFGKATExpression.
Proof.
  refine
    (mk_environment
      (fun k =>
        match lookup_gtnf_state
          (gtnf_supply_label supply)
          (gtnfthm_reachable_states supply)
          k with
        | Some source => Some (gtnf_body_Y supply source)
        | None => None
        end)
      (map (fun source => gtnf_supply_label supply source)
        (gtnfthm_reachable_states supply))
      _).
  intros k value Hlookup.
  destruct (lookup_gtnf_state
    (gtnf_supply_label supply)
    (gtnfthm_reachable_states supply)
    k) as [source |] eqn:Hstate;
    [| discriminate Hlookup].
  destruct (lookup_gtnf_state_some_in _ _ _ _ Hstate)
    as [Hin Hlabel].
  subst k.
  apply in_map. exact Hin.
Defined.

Local Definition gtnf_prefix_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  : label_environment CFGKATExpression.
Proof.
  refine
    (mk_environment
      (fun k =>
        match lookup_gtnf_state
          (gtnf_supply_label supply)
          (gtnfthm_reachable_states supply)
          k with
        | Some source => Some (gtnf_prefix_body supply source)
        | None => None
        end)
      (map (fun source => gtnf_supply_label supply source)
        (gtnfthm_reachable_states supply))
      _).
  intros k value Hlookup.
  destruct (lookup_gtnf_state
    (gtnf_supply_label supply)
    (gtnfthm_reachable_states supply)
    k) as [source |] eqn:Hstate;
    [| discriminate Hlookup].
  destruct (lookup_gtnf_state_some_in _ _ _ _ Hstate)
    as [Hin Hlabel].
  subst k.
  apply in_map. exact Hin.
Defined.

Local Definition gtnf_prefix_lem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  : label_environment CFGKATExpression.
Proof.
  refine
    (mk_environment
      (fun k =>
        match gtnflem2_env supply k with
        | Some body => Some body
        | None => gtnf_prefix_env supply k
        end)
      (env_support (gtnflem2_env supply) ++
       env_support (gtnf_prefix_env supply))
      _).
  intros k value Hlookup.
  destruct (gtnflem2_env supply k) as [body |] eqn:Hbody.
  - apply in_or_app. left.
    eapply env_supported. exact Hbody.
  - apply in_or_app. right.
    eapply env_supported. exact Hlookup.
Defined.

Local Definition gtnfthm_lem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  : label_environment CFGKATExpression.
Proof.
  refine
    (mk_environment
      (fun k =>
        match gtnflem2_env supply k with
        | Some body => Some body
        | None => gtnfthm_env supply k
        end)
      (env_support (gtnflem2_env supply) ++
       env_support (gtnfthm_env supply))
      _).
  intros k value Hlookup.
  destruct (gtnflem2_env supply k) as [body |] eqn:Hbody.
  - apply in_or_app. left.
    eapply env_supported. exact Hbody.
  - apply in_or_app. right.
    eapply env_supported. exact Hlookup.
Defined.

Definition canonical_gtnf_initial_sum
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  : CFGKATExpression :=
  gtnf_initial_sum (canonical_gtnf_supply (E := E) (e := e)).

Definition canonical_gtnfthm_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  : label_environment CFGKATExpression :=
  gtnfthm_env (canonical_gtnf_supply (E := E) (e := e)).


Local Lemma guarded_atom_sum_on_jump_inv
  (atoms : list (Test -> bool))
  (body : Atom -> CFGKATExpression)
  (i j : IndicatorAssignment)
  (a : Atom)
  (l : Label)
  :
  CFGKATExpressionDynamics (guarded_atom_sum_on atoms body, i) a
    (CFGKATAutomatonJump l j) ->
  exists ba,
    In ba atoms /\
    CFGKATExpressionDynamics (body (bool_to_atom ba), i) a
      (CFGKATAutomatonJump l j).
Proof.
  intro Hdyn.
  pose proof
    (transition_output_unique
      (guarded_atom_sum_on atoms body) a i
      (CFGKATAutomatonJump l j) Hdyn) as Hout.
  revert Hout.
  induction atoms as [|ba atoms IH]; simpl; intro Hout.
  - exfalso.
    rewrite transition_zero in Hout.
    discriminate.
  - rewrite transition_choice in Hout.
    destruct (eval_test_dec (atom_to_test (bool_to_atom ba)) a i)
      as [Htrue | Hfalse].
    + exists ba.
      split; [left; reflexivity |].
      apply (proj2 (transition_output_exact (body (bool_to_atom ba)) a i _)).
      exact Hout.
    + pose proof (IH
        (proj2 (transition_output_exact
          (guarded_atom_sum_on atoms body) a i _) Hout)
        Hout) as Hex.
      destruct Hex as [tail_ba [Hin Htail]].
      exists tail_ba.
      split; [right; exact Hin | exact Htail].
Qed.

Lemma guarded_atom_sum_all_jump_inv
  (body : Atom -> CFGKATExpression)
  (i j : IndicatorAssignment)
  (a : Atom)
  (l : Label)
  :
  CFGKATExpressionDynamics (guarded_atom_sum_all body, i) a
    (CFGKATAutomatonJump l j) ->
  exists ba,
    In ba all_bool_atoms /\
    CFGKATExpressionDynamics (body (bool_to_atom ba), i) a
      (CFGKATAutomatonJump l j).
Proof.
  unfold guarded_atom_sum_all.
  apply guarded_atom_sum_on_jump_inv.
Qed.

Local Lemma gtnf_body_Y_jump_inv
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  (runtime_i j : IndicatorAssignment)
  (a : Atom)
  (l : Label)
  :
  CFGKATExpressionDynamics
    (gtnf_body_Y supply s, runtime_i) a
    (CFGKATAutomatonJump l j) ->
  exists branch_atom j0,
    resolved_transition_output E (fst s) branch_atom (snd s) =
      CFGKATAutomatonJump l j0.
Proof.
  destruct s as [f source_i].
  intro Hdyn.
  unfold gtnf_body_Y in Hdyn.
  destruct (guarded_atom_sum_all_jump_inv _ _ _ _ _ Hdyn)
    as [ba [_ Hbranch]].
  destruct (sysc_Y_jump_label_inv supply _ _ _ _ _ Hbranch)
    as [j0 Hj].
  exists (bool_to_atom ba), j0.
  exact Hj.
Qed.

Local Lemma gtnf_body_Y_no_supply_state_label_jump
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (target_state source_state : CFGKATSyntConfiguration)
  (i j : IndicatorAssignment)
  (a : Atom)
  :
  In target_state (gtnf_supply_states E e supply) ->
  In source_state (gtnf_supply_states E e supply) ->
  ~ CFGKATExpressionDynamics
      (gtnf_body_Y supply source_state, i) a
      (CFGKATAutomatonJump (gtnf_supply_label supply target_state) j).
Proof.
  intros Htarget Hsource Hdyn.
  destruct (gtnf_body_Y_jump_inv
    supply source_state i j a
    (gtnf_supply_label supply target_state) Hdyn)
    as [branch_atom [j0 Hout]].
  destruct source_state as [source source_i].
  eapply resolved_transition_output_no_supply_state_label_jump.
  - exact Htarget.
  - exact Hsource.
  - exact Hout.
Qed.

Local Lemma gtnf_body_Y_no_original_jump
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (source_state : CFGKATSyntConfiguration)
  (i j : IndicatorAssignment)
  (a : Atom)
  (l : Label)
  (body : CFGKATExpression)
  :
  E l = Some body ->
  ~ CFGKATExpressionDynamics
      (gtnf_body_Y supply source_state, i) a
      (CFGKATAutomatonJump l j).
Proof.
  intros HE Hdyn.
  destruct (gtnf_body_Y_jump_inv supply source_state i j a l Hdyn)
    as [branch_atom [j0 Hout]].
  destruct source_state as [source source_i].
  eapply resolved_transition_output_no_original_bound_jump.
  - exact HE.
  - exact Hout.
Qed.

Local Lemma gtnf_body_Y_no_supply_expr_label_jump
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (target : CFGKATExpression)
  (source_state : CFGKATSyntConfiguration)
  (i j : IndicatorAssignment)
  (a : Atom)
  :
  (exists u, In (target, u) (gtnf_supply_states E e supply)) ->
  In source_state (gtnf_supply_states E e supply) ->
  ~ CFGKATExpressionDynamics
      (gtnf_body_Y supply source_state, i) a
      (CFGKATAutomatonJump (gtnf_supply_expr_label E e supply target) j).
Proof.
  intros Htarget Hsource Hdyn.
  destruct (gtnf_body_Y_jump_inv
    supply source_state i j a
    (gtnf_supply_expr_label E e supply target) Hdyn)
    as [branch_atom [j0 Hout]].
  destruct source_state as [source source_i].
  eapply resolved_transition_output_no_supply_expr_label_jump.
  - exact Htarget.
  - exact Hsource.
  - exact Hout.
Qed.

Local Lemma guarded_assignment_sum_on_contains
  (target : Label)
  (assignments : list IndicatorAssignment)
  (body : IndicatorAssignment -> CFGKATExpression)
  :
  contains_goto target (guarded_assignment_sum_on assignments body) ->
  exists i, In i assignments /\ contains_goto target (body i).
Proof.
  induction assignments as [|i assignments IH]; simpl.
  - intro Hcontains. contradiction.
  - intros [Hhead | Htail].
    + exists i. split; [left; reflexivity | exact Hhead].
    + destruct (IH Htail) as [j [Hj Hcontains]].
      exists j. split; [right; exact Hj | exact Hcontains].
Qed.

Local Lemma choice_then_guarded_cong_ctx
  (E F : label_environment CFGKATExpression)
  (g : CFGKATTest)
  (e e' h h' : CFGKATExpression)
  :
  E |- (test g ;; e) == (test g ;; e') -| F ->
  E |- h == h' -| F ->
  E |- (if g then e else h) == (if g then e' else h') -| F.
Proof.
  intros Hguard Htail.
  cfgkat_rewrite (weaken_empty_to_env E
    (if g then e else h)
    (if g then test g ;; e else h)
    (EqG4 e h g)).
  cfgkat_rewrite (EqChoiceCong E F (test g ;; e) h
    (test g ;; e') h' g Hguard Htail).
  cfgkat_rewrite <- (weaken_empty_to_env F
    (if g then e' else h')
    (if g then test g ;; e' else h')
    (EqG4 e' h' g)).
  apply EqRefl.
Qed.

Local Lemma guarded_assignment_sum_on_guarded_cong_ctx
  (E F : label_environment CFGKATExpression)
  (assignments : list IndicatorAssignment)
  (body body' : IndicatorAssignment -> CFGKATExpression)
  :
  (forall i,
    In i assignments ->
    E |- test (complete_test i) ;; body i ==
      test (complete_test i) ;; body' i -| F) ->
  E |- guarded_assignment_sum_on assignments body ==
    guarded_assignment_sum_on assignments body' -| F.
Proof.
  intros Hbranches.
  induction assignments as [|i assignments IH]; simpl.
  - apply strong_equiv_no_goto.
    intro k. simpl. tauto.
  - apply choice_then_guarded_cong_ctx.
    + apply Hbranches. left. reflexivity.
    + apply IH.
      intros j Hj.
      apply Hbranches. right. exact Hj.
Qed.

Lemma guarded_assignment_sum_all_guarded_cong_ctx
  (E F : label_environment CFGKATExpression)
  (body body' : IndicatorAssignment -> CFGKATExpression)
  :
  (forall i,
    In i all_assignments ->
    E |- test (complete_test i) ;; body i ==
      test (complete_test i) ;; body' i -| F) ->
  E |- guarded_assignment_sum_all body ==
    guarded_assignment_sum_all body' -| F.
Proof.
  unfold guarded_assignment_sum_all.
  apply guarded_assignment_sum_on_guarded_cong_ctx.
Qed.

Local Lemma guarded_assignment_sum_on_const_as_test
  (assignments : list IndicatorAssignment)
  (e0 : CFGKATExpression)
  :
  guarded_assignment_sum_on assignments (fun _ => e0) ==
  test (fold_TOr (map complete_test assignments)) ;; e0.
Proof.
  induction assignments as [|i assignments IH]; simpl.
  - apply EqSym. apply EqS2.
  - cfgkat_rewrite IH.
    apply choice_or_test_seq.
Qed.

Lemma guarded_assignment_sum_all_const
  (e0 : CFGKATExpression)
  :
  guarded_assignment_sum_all (fun _ => e0) == e0.
Proof.
  unfold guarded_assignment_sum_all.
  cfgkat_rewrite (guarded_assignment_sum_on_const_as_test all_assignments e0).
  cfgkat_rewrite (EqSeqLeftEmptyCong
    (test (fold_TOr (map complete_test all_assignments)))
    (test (1 : CFGKATTest)) e0
    (EqBoolAssertCong _ _ complete_test_partition)).
  apply EqS3.
Qed.

Lemma guarded_assignment_sum_all_complete_assignment
  (e : CFGKATExpression)
  :
  e == guarded_assignment_sum_all (fun i => complete_assignment i ;; e).
Proof.
  cfgkat_rewrite <- (guarded_assignment_sum_all_const e) at 1.
  apply guarded_assignment_sum_all_guarded_cong_ctx.
  intros i _.
  cfgkat_rewrite indred_plus at 1.
  apply EqS1.
Qed.

Local Lemma branchsel_atom_all_under_minterm
  (body : Atom -> CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  test (AtIY_test (a, i)) ;;
    guarded_atom_sum_all body == test (AtIY_test (a, i)) ;; body a.
Proof.
  cfgkat_rewrite <- (test_seq_absorb_right
    (AtIY_test (a, i)) (atom_to_test a)
    (BA_leq_to_and_right _ _ (AtIY_test_leq_atom_to_test a i))
    (guarded_atom_sum_all body)).
  destruct (bool_to_atom_eq a) as [ba [Hin Hba]].
  rewrite <- Hba.
  unfold guarded_atom_sum_all.
  cfgkat_rewrite (branchsel_atom_on all_bool_atoms body ba Hin).
  cfgkat_rewrite (test_seq_absorb_right
    (AtIY_test (bool_to_atom ba, i)) (atom_to_test (bool_to_atom ba))
    (BA_leq_to_and_right _
      _ (AtIY_test_leq_atom_to_test (bool_to_atom ba) i))
    (body (bool_to_atom ba))).
  apply EqRefl.
Qed.

Local Lemma complete_test_filters_full_Y_body
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (f : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  test (complete_test i) ;;
    guarded_sum_all
      (fun m =>
        sysc_Y supply
          (resolved_transition_output
            E f (AtIY_atom m) (AtIY_assignment m))) ==
  test (complete_test i) ;;
    guarded_atom_sum_all
      (fun a =>
        sysc_Y supply
          (resolved_transition_output E f a i)).
Proof.
  change (guarded_sum_all
    (fun m =>
      sysc_Y supply
        (resolved_transition_output
          E f (AtIY_atom m) (AtIY_assignment m)))) with
    (gtnf_full_Y_body supply f).
  change (guarded_atom_sum_all
    (fun a =>
      sysc_Y supply
        (resolved_transition_output E f a i))) with
    (gtnf_body_Y supply (f, i)).
  apply minterm_ext_ctx.
  intros [a j] Hm.
  destruct (classic (j = i)) as [Hji | Hji].
  - subst j.
    cfgkat_rewrite
      (test_seq_absorb_right (AtIY_test (a, i)) (complete_test i)
        (AtIY_test_complete_test_same a i) (gtnf_full_Y_body supply f)).
    cfgkat_rewrite
      (ltac:(unfold gtnf_full_Y_body;
        apply (branchsel_plus
          (fun m =>
            sysc_Y supply
              (resolved_transition_output
                E f (AtIY_atom m) (AtIY_assignment m)))
          (a, i)))).
    cfgkat_rewrite
      (test_seq_absorb_right (AtIY_test (a, i)) (complete_test i)
        (AtIY_test_complete_test_same a i) (gtnf_body_Y supply (f, i))).
    cfgkat_rewrite
      (ltac:(unfold gtnf_body_Y;
        apply (branchsel_atom_all_under_minterm
          (fun a =>
            sysc_Y supply (resolved_transition_output E f a i))
          a i))).
    apply EqRefl.
  - cfgkat_rewrite (test_seq_annihilate_right
      (AtIY_test (a, j)) (complete_test i)
      ltac:(apply AtIY_test_complete_test_disagree; exact Hji)
      (gtnf_full_Y_body supply f)).
    cfgkat_rewrite <- (test_seq_annihilate_right
      (AtIY_test (a, j)) (complete_test i)
      ltac:(apply AtIY_test_complete_test_disagree; exact Hji)
      (gtnf_body_Y supply (f, i))).
    apply EqRefl.
Qed.

Local Lemma syscannih
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (i : IndicatorAssignment)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  complete_assignment i ;; sysc supply r == sysc supply r.
Proof.
  destruct r as
    [|j_accept|j_break|j_continue| |l_jump j_jump|p [f j_next]];
    simpl.
  - apply complete_assignment_abort.
  - apply indannih_plus.
  - cfgkat_rewrite <- EqS1.
    cfgkat_rewrite indannih_plus.
    apply EqRefl.
  - cfgkat_rewrite <- EqS1.
    cfgkat_rewrite indannih_plus.
    apply EqRefl.
  - apply complete_assignment_return.
  - cfgkat_rewrite <- EqS1.
    cfgkat_rewrite indannih_plus.
    apply EqRefl.
  - cfgkat_rewrite <- EqS1 at 1.
    cfgkat_rewrite indannih_plus_prefix.
    apply EqRefl.
Qed.

Local Lemma sysc_resolved_no_supply_state_label_contains
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (target_state : CFGKATSyntConfiguration)
  (source : CFGKATExpression)
  (source_i : IndicatorAssignment)
  (a : Atom)
  :
  In target_state (gtnf_supply_states E e supply) ->
  In (source, source_i) (gtnf_supply_states E e supply) ->
  ~ contains_goto (gtnf_supply_label supply target_state)
      (sysc supply
        (resolved_transition_output E source a source_i)).
Proof.
  intros Htarget Hsource Hcontains.
  remember (resolved_transition_output E source a source_i) as r.
  destruct r as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p [f i_next]];
    simpl in Hcontains.
  - exact Hcontains.
  - exact (complete_assignment_no_contains_goto i_accept
      (gtnf_supply_label supply target_state) Hcontains).
  - destruct Hcontains as [Hbad | Hbad].
    + exact (complete_assignment_no_contains_goto i_break
        (gtnf_supply_label supply target_state) Hbad).
    + exact Hbad.
  - destruct Hcontains as [Hbad | Hbad].
    + exact (complete_assignment_no_contains_goto i_continue
        (gtnf_supply_label supply target_state) Hbad).
    + exact Hbad.
  - exact Hcontains.
  - destruct Hcontains as [Hbad | Hlabel].
    + exact (complete_assignment_no_contains_goto i_jump
        (gtnf_supply_label supply target_state) Hbad).
    + subst l_jump.
      eapply resolved_transition_output_no_supply_state_label_jump.
      * exact Htarget.
      * exact Hsource.
      * symmetry in Heqr. exact Heqr.
  - destruct Hcontains as [[Hbad | Hbad] | Hlabel].
    + exact (complete_assignment_no_contains_goto i_next
        (gtnf_supply_label supply target_state) Hbad).
    + exact Hbad.
    + pose proof
        (gtnf_supply_label_expr_disjoint E e supply target_state f
          Htarget
          (ex_intro _ i_next
            (gtnf_supply_next_closed E e supply source source_i a p
              (f, i_next) Hsource (eq_sym Heqr)))) as Hdisjoint.
      apply Hdisjoint.
      symmetry.
      exact Hlabel.
Qed.

Local Lemma gtnflem2_state_body_no_supply_state_label_contains
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (target_state : CFGKATSyntConfiguration)
  (source : CFGKATExpression)
  :
  In target_state (gtnf_supply_states E e supply) ->
  (exists source_i, In (source, source_i) (gtnf_supply_states E e supply)) ->
  ~ contains_goto (gtnf_supply_label supply target_state)
      (gtnflem2_state_body supply source).
Proof.
  intros Htarget [source_i Hsource].
  unfold gtnflem2_state_body.
  apply guarded_sum_all_no_contains.
  intro m.
  eapply sysc_resolved_no_supply_state_label_contains.
  - exact Htarget.
  - eapply gtnf_supply_assignment_closed.
    exact Hsource.
Qed.

Local Lemma gtnflem2_env_no_supply_state_label_contains
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (target_state : CFGKATSyntConfiguration)
  (l : Label)
  (body : CFGKATExpression)
  :
  In target_state (gtnf_supply_states E e supply) ->
  gtnflem2_env supply l = Some body ->
  ~ contains_goto (gtnf_supply_label supply target_state) body.
Proof.
  intros Htarget Hbody.
  unfold gtnflem2_env, mk_environment in Hbody.
  simpl in Hbody.
  destruct (E l) as [original |] eqn:HEl.
  - injection Hbody as <-.
    eapply gtnflem2_state_body_no_supply_state_label_contains.
    + exact Htarget.
    + exists indicator_assignment_witness.
      eapply gtnf_supply_original.
      exact HEl.
  - destruct (gtnflem2_reachable_ell_source supply l)
      as [source |] eqn:Hlookup;
      [| discriminate Hbody].
    injection Hbody as <-.
    eapply gtnflem2_state_body_no_supply_state_label_contains.
    + exact Htarget.
    + destruct (gtnflem2_reachable_ell_source_some_in supply l source Hlookup)
        as [source_i [Hsource _]].
      exists source_i.
      eapply gtnflem2_reachable_states_in_supply.
      exact Hsource.
Qed.

Local Lemma gtnf_prefix_env_disjoint
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  label_disjoint (gtnflem2_env supply)
    (gtnf_prefix_env supply).
Proof.
  unfold label_disjoint, label_in_dom,
    gtnf_prefix_env,
    mk_environment.
  simpl.
  intros l [body Hbody] [state_body Hstate].
  destruct (lookup_gtnf_state
    (gtnf_supply_label supply)
    (gtnfthm_reachable_states supply) l) as [s |] eqn:Hlookup;
    [| discriminate Hstate].
  destruct (lookup_gtnf_state_some_in _ _ _ _ Hlookup)
    as [Hs_reach Hlabel].
  assert (Hs : In s (gtnf_supply_states E e supply)).
  { eapply gtnfthm_reachable_states_in_supply. exact Hs_reach. }
  subst l.
  unfold gtnflem2_env, mk_environment in Hbody.
  destruct (E (gtnf_supply_label supply s)) as [original |] eqn:HE.
  - pose proof
      (gtnf_supply_label_fresh_original E e supply s
        (gtnf_supply_label supply s) original Hs HE) as Hfresh.
    apply Hfresh. reflexivity.
  - destruct (gtnflem2_reachable_ell_source supply (gtnf_supply_label supply s))
      as [f |] eqn:Hexpr.
    + destruct (gtnflem2_reachable_ell_source_some_in supply
        (gtnf_supply_label supply s) f Hexpr)
        as [i [Hf Hexpr_label]].
      pose proof
        (gtnf_supply_label_expr_disjoint E e supply s f Hs
          (ex_intro _ i
            (gtnflem2_reachable_states_in_supply supply (f, i) Hf)))
        as Hdisjoint.
      apply Hdisjoint. exact Hexpr_label.
    + discriminate Hbody.
Qed.
#[local] Existing Instance
  gtnf_prefix_env_disjoint.

Local Lemma gtnflem2_env_no_goto_gtnf_prefix_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  no_goto_env (gtnflem2_env supply)
    (gtnf_prefix_env supply).
Proof.
  unfold no_goto_env, no_goto_expr, label_in_dom,
    gtnf_prefix_env, mk_environment.
  simpl.
  intros l body Hbody target [target_body Htarget_body].
  destruct (lookup_gtnf_state
    (gtnf_supply_label supply)
    (gtnfthm_reachable_states supply) target) as [target_state |]
      eqn:Hlookup;
    [| discriminate Htarget_body].
  destruct (lookup_gtnf_state_some_in _ _ _ _ Hlookup)
    as [Htarget_reach Hlabel].
  rewrite Hlabel.
  eapply gtnflem2_env_no_supply_state_label_contains.
  - eapply gtnfthm_reachable_states_in_supply.
    exact Htarget_reach.
  - exact Hbody.
Qed.

Local Lemma gtnflem2_state_body_no_goto_gtnf_prefix_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (f : CFGKATExpression)
  :
  (exists i, In (f, i) (gtnf_supply_states E e supply)) ->
  no_goto_expr (gtnflem2_state_body supply f)
    (gtnf_prefix_env supply).
Proof.
  intros Hf target [target_body Htarget_body].
  unfold gtnf_prefix_env,
    mk_environment in Htarget_body.
  simpl in Htarget_body.
  destruct (lookup_gtnf_state
    (gtnf_supply_label supply)
    (gtnfthm_reachable_states supply) target) as [target_state |]
      eqn:Hlookup;
    [| discriminate Htarget_body].
  destruct (lookup_gtnf_state_some_in _ _ _ _ Hlookup)
    as [Htarget_reach Hlabel].
  rewrite Hlabel.
  eapply gtnflem2_state_body_no_supply_state_label_contains.
  - eapply gtnfthm_reachable_states_in_supply.
    exact Htarget_reach.
  - exact Hf.
Qed.

Local Lemma gtnflem2_env_add_gtnf_prefix_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (x : CFGKATExpression)
  :
  no_goto_expr x (gtnf_prefix_env supply) ->
  gtnflem2_env supply |- x == x -|
    gtnf_prefix_lem2_env supply.
Proof.
  intro Hx.
  apply EqSym.
  assert (Hcup :
    gtnflem2_env supply + gtnf_prefix_env supply =
    gtnf_prefix_lem2_env supply).
  {
    apply environment_eq.
    intro k.
    unfold label_env_cup, gtnf_prefix_lem2_env, mk_environment.
    destruct (gtnflem2_env supply k); reflexivity.
  }
  rewrite <- Hcup.
  apply EqC3.
  intros l Hl.
  split.
  - intros k body Hbody.
    eapply
      gtnflem2_env_no_goto_gtnf_prefix_env;
      eauto.
  - apply Hx. exact Hl.
Qed.

Local Lemma gtnf_prefix_lem2_env_lookup_state
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  :
  In s (gtnfthm_reachable_states supply) ->
  gtnf_prefix_lem2_env supply (gtnf_supply_label supply s) =
    Some (gtnf_prefix_body supply s).
Proof.
  intro Hs.
  unfold gtnf_prefix_lem2_env,
    gtnf_prefix_env, mk_environment.
  simpl.
  assert (Hs_supply : In s (gtnf_supply_states E e supply)).
  { eapply gtnfthm_reachable_states_in_supply. exact Hs. }
  destruct (E (gtnf_supply_label supply s)) as [body |] eqn:HE.
  - exfalso.
    pose proof
      (gtnf_supply_label_fresh_original E e supply s
        (gtnf_supply_label supply s) body Hs_supply HE) as Hfresh.
    apply Hfresh.
    reflexivity.
  - destruct (gtnflem2_reachable_ell_source supply
        (gtnf_supply_label supply s))
      as [f |] eqn:Hlookup.
    + exfalso.
      destruct (gtnflem2_reachable_ell_source_some_in supply
        (gtnf_supply_label supply s) f Hlookup)
        as [i [Hf Hlabel]].
      pose proof
        (gtnf_supply_label_expr_disjoint E e supply s f Hs_supply
          (ex_intro _ i
            (gtnflem2_reachable_states_in_supply supply (f, i) Hf)))
        as Hdisjoint.
      apply Hdisjoint.
      exact Hlabel.
    + rewrite lookup_gtnf_state_in_some.
      * reflexivity.
      * exact (gtnfthm_reachable_states_label_injective supply).
      * exact Hs.
Qed.

Local Lemma gtnf_prefix_lem2_env_lookup_expr
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (f : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  gtnflem2_reachable_state (E := E) (e := e) (f, i) ->
  gtnf_prefix_lem2_env supply
    (gtnf_supply_expr_label E e supply f) =
    Some (gtnflem2_state_body supply f).
Proof.
  intro Hreach.
  unfold gtnf_prefix_lem2_env, mk_environment.
  change
    (match gtnflem2_env supply
      (gtnf_supply_expr_label E e supply f) with
    | Some body => Some body
    | None =>
        gtnf_prefix_env supply
          (gtnf_supply_expr_label E e supply f)
    end = Some (gtnflem2_state_body supply f)).
  rewrite (gtnflem2_env_lookup_expr supply f i Hreach).
  reflexivity.
Qed.

Local Lemma sysc_to_sysc_Y_in_gtnf_prefix_lem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  (forall p s,
    r = CFGKATAutomatonNext p s ->
    In s (gtnfthm_reachable_states supply)) ->
  gtnf_prefix_lem2_env supply |-
    sysc supply r == sysc_Y supply r -|
    gtnf_prefix_lem2_env supply.
Proof.
  intro Hnext.
  destruct r as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p [f i_next]];
    simpl; try apply EqRefl.
  set (W := gtnf_prefix_lem2_env supply).
  assert (Hstate_reach : In (f, i_next) (gtnfthm_reachable_states supply)).
  { apply Hnext with (p := p). reflexivity. }
  assert (Hstate_lemma2 :
    gtnflem2_reachable_state (E := E) (e := e) (f, i_next)).
  {
    apply (gtnfthm_reachable_state_to_gtnflem2 supply).
    eapply gtnfthm_reachable_states_in_reachable.
    exact Hstate_reach.
  }
  change (W |~
    (complete_assignment i_next ;; do p) ;;
      goto (gtnf_supply_expr_label E e supply f) =~=
    do p ;; goto (gtnf_supply_label supply (f, i_next)))%cfgkat_setoid.
  cfgkat_rewrite (unfold_bound_goto W
    (gtnf_supply_expr_label E e supply f)
    (gtnflem2_state_body supply f)
    (gtnf_prefix_lem2_env_lookup_expr
      supply f i_next Hstate_lemma2)).
  cfgkat_rewrite (weaken_empty_to_env W
    ((complete_assignment i_next ;; do p) ;;
      gtnflem2_state_body supply f)
    (do p ;; (complete_assignment i_next ;;
      gtnflem2_state_body supply f))
    ltac:(cfgkat_rewrite complete_assignment_comm_action;
      apply EqS1)).
  change (W |~
    do p ;; gtnf_prefix_body supply (f, i_next) =~=
    do p ;; goto (gtnf_supply_label supply (f, i_next)))%cfgkat_setoid.
  apply EqSeqRightCong.
  - apply EqSym.
    apply (unfold_bound_goto W
      (gtnf_supply_label supply (f, i_next))
      (gtnf_prefix_body supply (f, i_next))
      (gtnf_prefix_lem2_env_lookup_state
        supply (f, i_next) Hstate_reach)).
  - apply EqRefl.
Qed.

Local Lemma gtnflem2_body_to_full_Y_body_reachable
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (f : CFGKATExpression)
  :
  (forall i, In (f, i) (gtnfthm_reachable_states supply)) ->
  gtnf_prefix_lem2_env supply |-
    gtnflem2_state_body supply f ==
    guarded_sum_all
      (fun m =>
        sysc_Y supply
          (resolved_transition_output
            E f (AtIY_atom m) (AtIY_assignment m))) -|
    gtnf_prefix_lem2_env supply.
Proof.
  intro Hall_reach.
  change (guarded_sum_all
    (fun m =>
      sysc_Y supply
        (resolved_transition_output
          E f (AtIY_atom m) (AtIY_assignment m)))) with
    (gtnf_full_Y_body supply f).
  unfold gtnflem2_state_body, gtnf_full_Y_body.
  apply guarded_sum_all_cong_ctx.
  intros m _.
  apply sysc_to_sysc_Y_in_gtnf_prefix_lem2_env.
  intros p s Hnext.
  apply gtnfthm_reachable_states_contains.
  eapply gtnfthm_reachable_next.
  - eapply gtnfthm_reachable_states_in_reachable.
    apply Hall_reach.
  - exact Hnext.
Qed.

Local Lemma sysc_Yannih_in_gtnf_prefix_lem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (i : IndicatorAssignment)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  (forall p s,
    r = CFGKATAutomatonNext p s ->
    In s (gtnfthm_reachable_states supply)) ->
  gtnf_prefix_lem2_env supply |-
    complete_assignment i ;; sysc_Y supply r ==
    sysc_Y supply r -| gtnf_prefix_lem2_env supply.
Proof.
  intro Hnext.
  set (W := gtnf_prefix_lem2_env supply).
  change (W |~
    complete_assignment i ;; sysc_Y supply r =~=
    sysc_Y supply r)%cfgkat_setoid.
  cfgkat_rewrite <-
    (sysc_to_sysc_Y_in_gtnf_prefix_lem2_env supply r Hnext).
  cfgkat_rewrite (weaken_empty_to_env W
    (complete_assignment i ;; sysc supply r)
    (sysc supply r)
    (syscannih supply i r)).
  apply EqRefl.
Qed.

Local Lemma gtnf_prefix_body_to_gtnf_body_Y
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (f : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  In (f, i) (gtnfthm_reachable_states supply) ->
  gtnf_prefix_lem2_env supply |-
    complete_assignment i ;; gtnflem2_state_body supply f ==
    guarded_atom_sum_all
      (fun a =>
        sysc_Y supply
          (resolved_transition_output E f a i)) -|
    gtnf_prefix_lem2_env supply.
Proof.
  intro Hin.
  change (complete_assignment i ;; gtnflem2_state_body supply f) with
    (gtnf_prefix_body supply (f, i)).
  change (guarded_atom_sum_all
    (fun a =>
      sysc_Y supply
        (resolved_transition_output E f a i))) with
    (gtnf_body_Y supply (f, i)).
  unfold gtnf_prefix_body.
  apply minterm_ext_ctx.
  intros [a j] Hm.
  set (W := gtnf_prefix_lem2_env supply).
  set (r := resolved_transition_output E f a i).
  assert (Hnext :
    forall p s,
      r = CFGKATAutomatonNext p s ->
      In s (gtnfthm_reachable_states supply)).
  {
    intros p s Hr.
    apply gtnfthm_reachable_states_contains.
    eapply gtnfthm_reachable_next.
    - eapply gtnfthm_reachable_states_in_reachable.
      exact Hin.
    - exact Hr.
  }
  cfgkat_rewrite (AtIY_complete_assignment_branch_expr_ctx
    W a j i (gtnflem2_state_body supply f) (sysc_Y supply r)
    ltac:(cfgkat_rewrite (weaken_empty_to_env W
        (test (AtIY_test (a, i)) ;; gtnflem2_state_body supply f)
        (test (AtIY_test (a, i)) ;; sysc supply r)
        ltac:(unfold gtnflem2_state_body; apply branchsel_plus));
      apply EqSeqRightCong;
      [apply sysc_to_sysc_Y_in_gtnf_prefix_lem2_env; exact Hnext
      | apply EqRefl])
    ltac:(apply sysc_Yannih_in_gtnf_prefix_lem2_env;
      exact Hnext)).
  cfgkat_rewrite <- (weaken_empty_to_env W
    (test (AtIY_test (a, j)) ;; gtnf_body_Y supply (f, i))
    (test (AtIY_test (a, j)) ;; sysc_Y supply r)
    ltac:(unfold gtnf_body_Y;
      apply branchsel_atom_all_under_minterm)).
  apply EqRefl.
Qed.

Local Lemma gtnf_full_Y_body_to_assignment_prefixed_initial_sum_reachable
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  gtnf_prefix_lem2_env supply |-
    guarded_sum_all
      (fun m =>
        sysc_Y supply
          (resolved_transition_output
            E e (AtIY_atom m) (AtIY_assignment m))) ==
    guarded_assignment_sum_all
      (fun i =>
        complete_assignment i ;;
        goto (gtnf_supply_label supply (e, i))) -|
    gtnf_prefix_lem2_env supply.
Proof.
  change (guarded_sum_all
    (fun m =>
      sysc_Y supply
        (resolved_transition_output
          E e (AtIY_atom m) (AtIY_assignment m)))) with
    (gtnf_full_Y_body supply e).
  change (guarded_assignment_sum_all
    (fun i =>
      complete_assignment i ;;
      goto (gtnf_supply_label supply (e, i)))) with
    (gtnf_assignment_prefixed_initial_sum supply).
  cfgkat_rewrite <- (weaken_empty_to_env
    (gtnf_prefix_lem2_env supply)
    (guarded_assignment_sum_all (fun _ => gtnf_full_Y_body supply e))
    (gtnf_full_Y_body supply e)
    (guarded_assignment_sum_all_const (gtnf_full_Y_body supply e))).
  unfold gtnf_assignment_prefixed_initial_sum.
  apply guarded_assignment_sum_all_guarded_cong_ctx.
  intros i _.
  assert (Hinitial_reach : In (e, i) (gtnfthm_reachable_states supply)).
  {
    apply gtnfthm_reachable_states_contains.
    apply gtnfthm_reachable_initial.
  }
  cfgkat_rewrite (weaken_empty_to_env
    (gtnf_prefix_lem2_env supply)
    (test (complete_test i) ;; gtnf_full_Y_body supply e)
    (test (complete_test i) ;; gtnf_body_Y supply (e, i))
    (complete_test_filters_full_Y_body supply e i)).
  assert (Hbody_to_goto :
    gtnf_prefix_lem2_env supply |-
      gtnf_body_Y supply (e, i) ==
      goto (gtnf_supply_label supply (e, i)) -|
    gtnf_prefix_lem2_env supply).
  {
    apply EqSym.
    cfgkat_rewrite (unfold_bound_goto _ _ _
      (gtnf_prefix_lem2_env_lookup_state
        supply (e, i) Hinitial_reach)).
    apply gtnf_prefix_body_to_gtnf_body_Y.
    exact Hinitial_reach.
  }
  change (gtnf_prefix_lem2_env supply |~
    gtnf_body_Y supply (e, i) =~=
    goto (gtnf_supply_label supply (e, i)))%cfgkat_setoid
    in Hbody_to_goto.
  change (gtnf_prefix_lem2_env supply |~
    test (complete_test i) ;; gtnf_body_Y supply (e, i) =~=
    test (complete_test i) ;;
      (complete_assignment i ;;
        goto (gtnf_supply_label supply (e, i))))%cfgkat_setoid.
  setoid_rewrite Hbody_to_goto.
  apply weaken_empty_to_env.
  cfgkat_rewrite (indred_plus i) at 1.
  apply EqS1.
Qed.

Local Lemma guarded_atom_sum_on_no_contains
  (target : Label)
  (atoms : list (Test -> bool))
  (body : Atom -> CFGKATExpression)
  :
  (forall ba, In ba atoms ->
    ~ contains_goto target (body (bool_to_atom ba))) ->
  ~ contains_goto target (guarded_atom_sum_on atoms body).
Proof.
  intros Hbody.
  induction atoms as [|ba atoms IH]; simpl.
  - tauto.
  - intros [Hhead | Htail].
    + exact (Hbody ba (or_introl eq_refl) Hhead).
    + apply IH.
      * intros ba' Hba'.
        apply Hbody. right. exact Hba'.
      * exact Htail.
Qed.

Lemma guarded_atom_sum_all_no_contains
  (target : Label)
  (body : Atom -> CFGKATExpression)
  :
  (forall ba, In ba all_bool_atoms ->
    ~ contains_goto target (body (bool_to_atom ba))) ->
  ~ contains_goto target (guarded_atom_sum_all body).
Proof.
  unfold guarded_atom_sum_all.
  apply guarded_atom_sum_on_no_contains.
Qed.

Local Lemma sysc_Y_resolved_no_original_label_contains
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (k : Label)
  (target_body source : CFGKATExpression)
  (source_i : IndicatorAssignment)
  (a : Atom)
  :
  E k = Some target_body ->
  In (source, source_i) (gtnf_supply_states E e supply) ->
  ~ contains_goto k
      (sysc_Y supply
        (resolved_transition_output E source a source_i)).
Proof.
  intros HE Hsource Hcontains.
  remember (resolved_transition_output E source a source_i) as r.
  destruct r as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p [f i_next]];
    simpl in Hcontains.
  - exact Hcontains.
  - exact (complete_assignment_no_contains_goto i_accept k Hcontains).
  - destruct Hcontains as [Hbad | Hbad].
    + exact (complete_assignment_no_contains_goto i_break k Hbad).
    + exact Hbad.
  - destruct Hcontains as [Hbad | Hbad].
    + exact (complete_assignment_no_contains_goto i_continue k Hbad).
    + exact Hbad.
  - exact Hcontains.
  - destruct Hcontains as [Hbad | Hlabel].
    + exact (complete_assignment_no_contains_goto i_jump k Hbad).
    + subst l_jump.
      eapply resolved_transition_output_no_original_bound_jump.
      * exact HE.
      * symmetry in Heqr. exact Heqr.
  - destruct Hcontains as [Hbad | Hlabel].
    + exact Hbad.
    + pose proof
        (gtnf_supply_label_fresh_original E e supply (f, i_next)
          k target_body
          (gtnf_supply_next_closed E e supply source source_i a p
            (f, i_next) Hsource (eq_sym Heqr))
          HE) as Hfresh.
      apply Hfresh.
      exact Hlabel.
Qed.

Local Lemma sysc_Y_resolved_no_expr_label_contains
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (target source : CFGKATExpression)
  (source_i : IndicatorAssignment)
  (a : Atom)
  :
  (exists target_i, In (target, target_i)
    (gtnf_supply_states E e supply)) ->
  In (source, source_i) (gtnf_supply_states E e supply) ->
  ~ contains_goto (gtnf_supply_expr_label E e supply target)
      (sysc_Y supply
        (resolved_transition_output E source a source_i)).
Proof.
  intros Htarget Hsource Hcontains.
  remember (resolved_transition_output E source a source_i) as r.
  destruct r as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p [f i_next]];
    simpl in Hcontains.
  - exact Hcontains.
  - exact (complete_assignment_no_contains_goto i_accept
      (gtnf_supply_expr_label E e supply target) Hcontains).
  - destruct Hcontains as [Hbad | Hbad].
    + exact (complete_assignment_no_contains_goto i_break
        (gtnf_supply_expr_label E e supply target) Hbad).
    + exact Hbad.
  - destruct Hcontains as [Hbad | Hbad].
    + exact (complete_assignment_no_contains_goto i_continue
        (gtnf_supply_expr_label E e supply target) Hbad).
    + exact Hbad.
  - exact Hcontains.
  - destruct Hcontains as [Hbad | Hlabel].
    + exact (complete_assignment_no_contains_goto i_jump
        (gtnf_supply_expr_label E e supply target) Hbad).
    + subst l_jump.
      eapply resolved_transition_output_no_supply_expr_label_jump.
      * exact Htarget.
      * exact Hsource.
      * symmetry in Heqr. exact Heqr.
  - destruct Hcontains as [Hbad | Hlabel].
    + exact Hbad.
    + pose proof
        (gtnf_supply_label_expr_disjoint E e supply (f, i_next) target
          (gtnf_supply_next_closed E e supply source source_i a p
            (f, i_next) Hsource (eq_sym Heqr))
          Htarget) as Hdisjoint.
      apply Hdisjoint.
      exact Hlabel.
Qed.

Local Lemma gtnf_body_Y_no_original_label_contains
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  (k : Label)
  (body : CFGKATExpression)
  :
  In s (gtnf_supply_states E e supply) ->
  E k = Some body ->
  ~ contains_goto k (gtnf_body_Y supply s).
Proof.
  destruct s as [source source_i].
  intros Hsource HE.
  unfold gtnf_body_Y.
  apply guarded_atom_sum_all_no_contains.
  intros ba _.
  eapply sysc_Y_resolved_no_original_label_contains.
  - exact HE.
  - exact Hsource.
Qed.

Local Lemma gtnf_body_Y_no_expr_label_contains
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  (target : CFGKATExpression)
  :
  In s (gtnf_supply_states E e supply) ->
  (exists target_i, In (target, target_i)
    (gtnf_supply_states E e supply)) ->
  ~ contains_goto (gtnf_supply_expr_label E e supply target)
      (gtnf_body_Y supply s).
Proof.
  destruct s as [source source_i].
  intros Hsource Htarget.
  unfold gtnf_body_Y.
  apply guarded_atom_sum_all_no_contains.
  intros ba _.
  eapply sysc_Y_resolved_no_expr_label_contains.
  - exact Htarget.
  - exact Hsource.
Qed.
Local Lemma gtnf_indicator_push_gtnf_prefix_lem2_env
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  (supply : gtnf_label_supply E e)
  :
  gtnflem2_env supply |-
    goto (gtnf_supply_expr_label E e supply e) ==
    guarded_assignment_sum_all
      (fun i =>
        complete_assignment i ;;
        goto (gtnf_supply_label supply (e, i))) -|
    gtnf_prefix_lem2_env supply.
Proof.
  change (guarded_assignment_sum_all
    (fun i =>
      complete_assignment i ;;
      goto (gtnf_supply_label supply (e, i)))) with
    (gtnf_assignment_prefixed_initial_sum supply).
  set (i0 := indicator_assignment_witness).
  cfgkat_rewrite (unfold_bound_goto _ _ _
    (gtnflem2_env_lookup_expr supply e i0
      (gtnflem2_reachable_initial i0))).
  cfgkat_rewrite (gtnflem2_env_add_gtnf_prefix_env supply
    (gtnflem2_state_body supply e)
    (gtnflem2_state_body_no_goto_gtnf_prefix_env
      supply e
      (ex_intro _ i0 (gtnf_supply_initial E e supply i0)))).
  cfgkat_rewrite (gtnflem2_body_to_full_Y_body_reachable supply e
    (fun i =>
      gtnfthm_reachable_states_contains supply (e, i)
        (gtnfthm_reachable_initial i))).
  apply gtnf_full_Y_body_to_assignment_prefixed_initial_sum_reachable.
Qed.

Local Lemma gtnfthm_canonical_prefix_lem2_env
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  :
  E |- e ==
    guarded_assignment_sum_all
      (fun i =>
        complete_assignment i ;;
        goto (gtnf_supply_label
          (canonical_gtnf_supply (E := E) (e := e)) (e, i))) -|
    gtnf_prefix_lem2_env
      (canonical_gtnf_supply (E := E) (e := e)).
Proof.
  set (supply := canonical_gtnf_supply (E := E) (e := e)).
  change (guarded_assignment_sum_all
    (fun i =>
      complete_assignment i ;;
      goto (gtnf_supply_label supply (e, i)))) with
    (gtnf_assignment_prefixed_initial_sum supply).
  change (gtnflem2_env supply) with
    (canonical_gtnflem2_env E e).
  cfgkat_rewrite (proj1 (gtnflem2 E e)).
  change (gtnf_supply_expr_label E e supply e) with
    (gtnflem2_ell E e e).
  cfgkat_rewrite (proj2 (gtnflem2 E e)).
  exact (gtnf_indicator_push_gtnf_prefix_lem2_env E e supply).
Qed.

Local Lemma gtnflem2_state_body_no_supply_state_label_jump
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (target_state : CFGKATSyntConfiguration)
  (source : CFGKATExpression)
  (i j : IndicatorAssignment)
  (a : Atom)
  :
  In target_state (gtnf_supply_states E e supply) ->
  (exists u, In (source, u) (gtnf_supply_states E e supply)) ->
  ~ CFGKATExpressionDynamics
      (gtnflem2_state_body supply source, i) a
      (CFGKATAutomatonJump (gtnf_supply_label supply target_state) j).
Proof.
  intros Htarget [source_i Hsource] Hdyn.
  destruct (gtnflem2_state_body_jump_inv
    supply source i j a
    (gtnf_supply_label supply target_state) Hdyn)
    as [m [j0 [_ Hout]]].
  eapply resolved_transition_output_no_supply_state_label_jump.
  - exact Htarget.
  - eapply gtnf_supply_assignment_closed.
    exact Hsource.
  - exact Hout.
Qed.

Local Lemma gtnfthm_lem2_env_guarded
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  C7_guarded (gtnfthm_lem2_env supply).
Proof.
  unfold C7_guarded.
  intros l target body target_body Hbody Htarget_body.
  unfold guarded.
  intros a i j.
  change
    ((match gtnflem2_env supply l with
      | Some lem2_body => Some lem2_body
      | None => gtnfthm_env supply l
      end) = Some body) in Hbody.
  change
    ((match gtnflem2_env supply target with
      | Some lem2_target_body => Some lem2_target_body
      | None => gtnfthm_env supply target
      end) = Some target_body) in Htarget_body.
  destruct (gtnflem2_env supply l) as [lem2_body |] eqn:Hlem2_body.
  - injection Hbody as <-.
    destruct (gtnflem2_env supply target)
      as [lem2_target_body |] eqn:Hlem2_target.
    + eapply gtnflem2_env_guarded_direct.
      * exact Hlem2_body.
      * exact Hlem2_target.
    + unfold gtnfthm_env, mk_environment in Htarget_body.
      simpl in Htarget_body.
      destruct (lookup_gtnf_state
        (gtnf_supply_label supply)
        (gtnfthm_reachable_states supply) target)
        as [target_state |] eqn:Htarget_state;
        [| discriminate Htarget_body].
      injection Htarget_body as <-.
      destruct (lookup_gtnf_state_some_in _ _ _ _ Htarget_state)
        as [Htarget_reach Htarget_label].
      rewrite Htarget_label.
      unfold gtnflem2_env, mk_environment in Hlem2_body.
      simpl in Hlem2_body.
      destruct (E l) as [original |] eqn:HEl.
      * injection Hlem2_body as <-.
        eapply gtnflem2_state_body_no_supply_state_label_jump.
        -- eapply gtnfthm_reachable_states_in_supply.
           exact Htarget_reach.
        -- exists i.
           eapply gtnf_supply_original.
           exact HEl.
      * destruct (gtnflem2_reachable_ell_source supply l)
          as [source |] eqn:Hsource;
          [| discriminate Hlem2_body].
        injection Hlem2_body as <-.
        eapply gtnflem2_state_body_no_supply_state_label_jump.
        -- eapply gtnfthm_reachable_states_in_supply.
           exact Htarget_reach.
        -- destruct (gtnflem2_reachable_ell_source_some_in
             supply l source Hsource) as [source_i [Hsource_in _]].
           exists source_i.
           eapply gtnflem2_reachable_states_in_supply.
           exact Hsource_in.
  - unfold gtnfthm_env, mk_environment in Hbody.
    simpl in Hbody.
    destruct (lookup_gtnf_state
      (gtnf_supply_label supply)
      (gtnfthm_reachable_states supply) l)
      as [source_state |] eqn:Hsource_state;
      [| discriminate Hbody].
    injection Hbody as <-.
    destruct (lookup_gtnf_state_some_in _ _ _ _ Hsource_state)
      as [Hsource_reach _].
    destruct (gtnflem2_env supply target)
      as [lem2_target_body |] eqn:Hlem2_target.
    + unfold gtnflem2_env, mk_environment in Hlem2_target.
      simpl in Hlem2_target.
      destruct (E target) as [original_target |] eqn:HEtarget.
      * eapply gtnf_body_Y_no_original_jump.
        exact HEtarget.
      * destruct (gtnflem2_reachable_ell_source supply target)
          as [target_expr |] eqn:Htarget_expr;
          [| discriminate Hlem2_target].
        destruct (gtnflem2_reachable_ell_source_some_in
          supply target target_expr Htarget_expr)
          as [target_i [Htarget_in Htarget_label]].
        rewrite Htarget_label.
        eapply gtnf_body_Y_no_supply_expr_label_jump.
        -- exists target_i.
           eapply gtnflem2_reachable_states_in_supply.
           exact Htarget_in.
        -- eapply gtnfthm_reachable_states_in_supply.
           exact Hsource_reach.
    + unfold gtnfthm_env, mk_environment in Htarget_body.
      simpl in Htarget_body.
      destruct (lookup_gtnf_state
        (gtnf_supply_label supply)
        (gtnfthm_reachable_states supply) target)
        as [target_state |] eqn:Htarget_state;
        [| discriminate Htarget_body].
      injection Htarget_body as <-.
      destruct (lookup_gtnf_state_some_in _ _ _ _ Htarget_state)
        as [Htarget_reach Htarget_label].
      rewrite Htarget_label.
      eapply gtnf_body_Y_no_supply_state_label_jump.
      * eapply gtnfthm_reachable_states_in_supply.
        exact Htarget_reach.
      * eapply gtnfthm_reachable_states_in_supply.
        exact Hsource_reach.
Qed.

Local Lemma gtnfthm_lem2_env_same_domain_as_prefix_lem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  C7_same_domain (gtnfthm_lem2_env supply)
    (gtnf_prefix_lem2_env supply).
Proof.
  unfold C7_same_domain, label_in_dom.
  intro l.
  unfold gtnfthm_lem2_env, gtnf_prefix_lem2_env,
    gtnfthm_env, gtnf_prefix_env,
    mk_environment.
  simpl.
  destruct (E l) as [original |] eqn:HE.
  - split; intros _.
    + exists (gtnflem2_state_body supply original). reflexivity.
    + exists (gtnflem2_state_body supply original). reflexivity.
  - destruct (gtnflem2_reachable_ell_source supply l) as [source |] eqn:Hexpr.
    + split; intros _.
      * exists (gtnflem2_state_body supply source). reflexivity.
      * exists (gtnflem2_state_body supply source). reflexivity.
    + destruct (lookup_gtnf_state
        (gtnf_supply_label supply)
        (gtnfthm_reachable_states supply) l) as [s |] eqn:Hstate.
      * split; intros _.
        -- exists (gtnf_prefix_body supply s). reflexivity.
        -- exists (gtnf_body_Y supply s). reflexivity.
      * split; intros [body Hbody]; discriminate Hbody.
Qed.

Local Lemma gtnfthm_lem2_env_solution_in_prefix_lem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  C7_solution (gtnfthm_lem2_env supply)
    (gtnf_prefix_lem2_env supply).
Proof.
  unfold C7_solution.
  intros l body Hbody.
  unfold gtnfthm_lem2_env,
    gtnfthm_env, mk_environment in Hbody.
  simpl in Hbody.
  destruct (E l) as [original |] eqn:HE.
  - injection Hbody as <-.
    apply unfold_bound_goto.
    unfold gtnf_prefix_lem2_env, mk_environment.
    simpl.
    rewrite HE.
    reflexivity.
  - destruct (gtnflem2_reachable_ell_source supply l) as [source |] eqn:Hexpr.
    + injection Hbody as <-.
      destruct (gtnflem2_reachable_ell_source_some_in supply l source Hexpr)
        as [i [Hin Hlabel]].
      rewrite Hlabel.
      apply unfold_bound_goto.
      apply gtnf_prefix_lem2_env_lookup_expr with (i := i).
      eapply gtnflem2_reachable_states_in_reachable.
      exact Hin.
    + destruct (lookup_gtnf_state
        (gtnf_supply_label supply)
        (gtnfthm_reachable_states supply) l) as [s |] eqn:Hstate;
        [| discriminate Hbody].
      injection Hbody as <-.
      destruct (lookup_gtnf_state_some_in _ _ _ _ Hstate)
        as [Hin Hlabel].
      rewrite Hlabel.
      destruct s as [f i].
      cfgkat_rewrite (unfold_bound_goto _ _ _
        (gtnf_prefix_lem2_env_lookup_state supply (f, i) Hin)).
      apply gtnf_prefix_body_to_gtnf_body_Y.
      exact Hin.
Qed.

Local Lemma gtnf_prefix_lem2_env_to_gtnfthm_lem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (x : CFGKATExpression)
  :
  gtnf_prefix_lem2_env supply |- x == x -|
    gtnfthm_lem2_env supply.
Proof.
  apply EqC7_from_side_condition.
  split.
  - apply gtnfthm_lem2_env_same_domain_as_prefix_lem2_env.
  - split.
    + apply gtnfthm_lem2_env_solution_in_prefix_lem2_env.
    + apply gtnfthm_lem2_env_guarded.
Qed.

Local Lemma gtnf_assignment_prefixed_initial_sum_to_initial_sum_reachable_with_Y
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  gtnfthm_lem2_env supply |-
    guarded_assignment_sum_all
      (fun i =>
        complete_assignment i ;;
        goto (gtnf_supply_label supply (e, i))) ==
    guarded_assignment_sum_all
      (fun i =>
        goto (gtnf_supply_label supply (e, i))) -|
    gtnfthm_lem2_env supply.
Proof.
  change (guarded_assignment_sum_all
    (fun i =>
      complete_assignment i ;;
      goto (gtnf_supply_label supply (e, i)))) with
    (gtnf_assignment_prefixed_initial_sum supply).
  change (guarded_assignment_sum_all
    (fun i =>
      goto (gtnf_supply_label supply (e, i)))) with
    (gtnf_initial_sum supply).
  unfold gtnf_assignment_prefixed_initial_sum, gtnf_initial_sum.
  apply guarded_assignment_sum_all_guarded_cong_ctx.
  intros i _.
  apply weaken_empty_to_env.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite <- (indred_plus i).
  apply EqRefl.
Qed.

Local Lemma gtnfthm_env_gtnflem2_env_disjoint
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  label_disjoint (gtnfthm_env supply) (gtnflem2_env supply).
Proof.
  unfold label_disjoint, label_in_dom, gtnfthm_env,
    mk_environment.
  simpl.
  intros l [body Hbody] [extra Hextra].
  destruct (lookup_gtnf_state
    (gtnf_supply_label supply)
    (gtnfthm_reachable_states supply) l) as [s |] eqn:Hstate;
    [| discriminate Hbody].
  destruct (lookup_gtnf_state_some_in _ _ _ _ Hstate)
    as [Hs_reach Hstate_label].
  assert (Hs : In s (gtnf_supply_states E e supply)).
  { eapply gtnfthm_reachable_states_in_supply. exact Hs_reach. }
  destruct (E l) as [original |] eqn:HE.
  - pose proof
      (gtnf_supply_label_fresh_original E e supply s l original Hs HE)
      as Hfresh.
    apply Hfresh. symmetry. exact Hstate_label.
  - destruct (gtnflem2_reachable_ell_source supply l) as [f |] eqn:Hexpr;
      [| discriminate Hextra].
    destruct (gtnflem2_reachable_ell_source_some_in supply l f Hexpr)
      as [i [Hf Hexpr_label]].
    pose proof
      (gtnf_supply_label_expr_disjoint E e supply s f Hs
        (ex_intro _ i
          (gtnflem2_reachable_states_in_supply supply (f, i) Hf)))
      as Hdisjoint.
    apply Hdisjoint.
    transitivity l.
    + symmetry. exact Hstate_label.
    + exact Hexpr_label.
Qed.
#[local] Existing Instance gtnfthm_env_gtnflem2_env_disjoint.

Local Lemma gtnfthm_lem2_env_as_cup
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  gtnfthm_env supply + gtnflem2_env supply =
  gtnfthm_lem2_env supply.
Proof.
  apply environment_eq.
  intro k.
  unfold label_env_cup, gtnfthm_env,
    gtnfthm_lem2_env, mk_environment.
  simpl.
  destruct (lookup_gtnf_state
    (gtnf_supply_label supply)
    (gtnfthm_reachable_states supply) k) as [s |] eqn:Hstate.
  - destruct (E k) as [body |] eqn:HE.
    + exfalso.
      destruct (lookup_gtnf_state_some_in _ _ _ _ Hstate)
        as [Hs_reach Hlabel].
      assert (Hs : In s (gtnf_supply_states E e supply)).
      { eapply gtnfthm_reachable_states_in_supply. exact Hs_reach. }
      pose proof
        (gtnf_supply_label_fresh_original E e supply s k body Hs HE)
        as Hfresh.
      apply Hfresh. symmetry. exact Hlabel.
    + destruct (gtnflem2_reachable_ell_source supply k) as [f |] eqn:Hexpr.
      * exfalso.
        destruct (lookup_gtnf_state_some_in _ _ _ _ Hstate)
          as [Hs_reach Hstate_label].
        assert (Hs : In s (gtnf_supply_states E e supply)).
        { eapply gtnfthm_reachable_states_in_supply. exact Hs_reach. }
        destruct (gtnflem2_reachable_ell_source_some_in supply k f Hexpr)
          as [i [Hf Hexpr_label]].
        pose proof
          (gtnf_supply_label_expr_disjoint E e supply s f Hs
            (ex_intro _ i
              (gtnflem2_reachable_states_in_supply supply (f, i) Hf)))
          as Hdisjoint.
        apply Hdisjoint.
        transitivity k.
        -- symmetry. exact Hstate_label.
        -- exact Hexpr_label.
      * reflexivity.
  - destruct (E k) as [body |] eqn:HE.
    + reflexivity.
    + destruct (gtnflem2_reachable_ell_source supply k) as [f |] eqn:Hexpr.
      * reflexivity.
      * reflexivity.
Qed.

Local Lemma gtnfthm_env_no_goto_gtnflem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  no_goto_env (gtnfthm_env supply) (gtnflem2_env supply).
Proof.
  unfold no_goto_env, no_goto_expr, label_in_dom.
  intros l body Hbody target [target_body Htarget_body].
  unfold gtnfthm_env, mk_environment in Hbody.
  simpl in Hbody.
  destruct (lookup_gtnf_state
    (gtnf_supply_label supply)
    (gtnfthm_reachable_states supply) l) as [source_state |]
      eqn:Hsource;
    [| discriminate Hbody].
  injection Hbody as <-.
  destruct (lookup_gtnf_state_some_in _ _ _ _ Hsource)
    as [Hsource_reach _].
  assert (Hsource_supply : In source_state (gtnf_supply_states E e supply)).
  { eapply gtnfthm_reachable_states_in_supply. exact Hsource_reach. }
  unfold mk_environment in Htarget_body.
  simpl in Htarget_body.
  destruct (E target) as [original |] eqn:HEtarget.
  - eapply gtnf_body_Y_no_original_label_contains.
    + exact Hsource_supply.
    + exact HEtarget.
  - destruct (gtnflem2_reachable_ell_source supply target)
      as [target_expr |] eqn:Hexpr;
      [| discriminate Htarget_body].
    destruct (gtnflem2_reachable_ell_source_some_in supply target target_expr Hexpr)
      as [target_i [Htarget Hlabel]].
    rewrite Hlabel.
    eapply gtnf_body_Y_no_expr_label_contains.
    + exact Hsource_supply.
    + exists target_i.
      eapply gtnflem2_reachable_states_in_supply.
      exact Htarget.
Qed.

Local Lemma gtnf_initial_sum_no_goto_gtnflem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  no_goto_expr
    (guarded_assignment_sum_all
      (fun i =>
        goto (gtnf_supply_label supply (e, i))))
    (gtnflem2_env supply).
Proof.
  change (guarded_assignment_sum_all
    (fun i =>
      goto (gtnf_supply_label supply (e, i)))) with
    (gtnf_initial_sum supply).
  intros target [target_body Htarget_body] Hcontains.
  unfold gtnf_initial_sum in Hcontains.
  unfold guarded_assignment_sum_all in Hcontains.
  destruct (guarded_assignment_sum_on_contains
    target
    all_assignments
    (fun i => goto (gtnf_supply_label supply (e, i)))
    Hcontains) as [i [_ Hgoto]].
  simpl in Hgoto.
  subst target.
  unfold mk_environment in Htarget_body.
  simpl in Htarget_body.
  destruct (E (gtnf_supply_label supply (e, i))) as [original |] eqn:HE.
  - pose proof
      (gtnf_supply_label_fresh_original E e supply (e, i)
        (gtnf_supply_label supply (e, i)) original
        (gtnf_supply_initial E e supply i) HE) as Hfresh.
    apply Hfresh. reflexivity.
  - destruct (gtnflem2_reachable_ell_source supply (gtnf_supply_label supply (e, i)))
      as [f |] eqn:Hexpr;
      [| discriminate Htarget_body].
    destruct (gtnflem2_reachable_ell_source_some_in supply
      (gtnf_supply_label supply (e, i)) f Hexpr)
      as [j [Hf Hlabel]].
    pose proof
      (gtnf_supply_label_expr_disjoint E e supply (e, i) f
        (gtnf_supply_initial E e supply i)
        (ex_intro _ j
          (gtnflem2_reachable_states_in_supply supply (f, j) Hf)))
      as Hdisjoint.
    apply Hdisjoint. exact Hlabel.
Qed.

Local Lemma gtnf_initial_sum_remove_gtnflem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  gtnfthm_lem2_env supply |-
    guarded_assignment_sum_all
      (fun i =>
        goto (gtnf_supply_label supply (e, i))) ==
    guarded_assignment_sum_all
      (fun i =>
        goto (gtnf_supply_label supply (e, i))) -|
    gtnfthm_env supply.
Proof.
  change (guarded_assignment_sum_all
    (fun i =>
      goto (gtnf_supply_label supply (e, i)))) with
    (gtnf_initial_sum supply).
  rewrite <- gtnfthm_lem2_env_as_cup.
  apply EqC3.
  intros l Hl.
  split.
  - intros k body Hbody.
    eapply gtnfthm_env_no_goto_gtnflem2_env; eauto.
  - eapply gtnf_initial_sum_no_goto_gtnflem2_env; eauto.
Qed.

Theorem gtnfthm
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  :
  E |- e ==
    guarded_assignment_sum_all
      (fun i =>
        goto (gtnf_supply_label
          (canonical_gtnf_supply (E := E) (e := e)) (e, i))) -|
    canonical_gtnfthm_env (E := E) (e := e).
Proof.
  change (guarded_assignment_sum_all
    (fun i =>
      goto (gtnf_supply_label
        (canonical_gtnf_supply (E := E) (e := e)) (e, i)))) with
    (canonical_gtnf_initial_sum (E := E) (e := e)).
  unfold canonical_gtnf_initial_sum, canonical_gtnfthm_env, canonical_gtnf_supply.
  cfgkat_rewrite (gtnfthm_canonical_prefix_lem2_env E e).
  cfgkat_rewrite (gtnf_prefix_lem2_env_to_gtnfthm_lem2_env
    (gtnf_label_supply_exists E e)
    (gtnf_assignment_prefixed_initial_sum (gtnf_label_supply_exists E e))).
  cfgkat_rewrite
    (gtnf_assignment_prefixed_initial_sum_to_initial_sum_reachable_with_Y
    (gtnf_label_supply_exists E e)).
  apply gtnf_initial_sum_remove_gtnflem2_env.
Qed.

Local Lemma gtnf_assignment_prefixed_initial_sum_select
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (i : IndicatorAssignment)
  :
  complete_assignment i ;;
    guarded_assignment_sum_all
      (fun j =>
        complete_assignment j ;;
        goto (gtnf_supply_label supply (e, j))) ==
    complete_assignment i ;; goto (gtnf_supply_label supply (e, i)).
Proof.
  change (guarded_assignment_sum_all
    (fun j =>
      complete_assignment j ;;
      goto (gtnf_supply_label supply (e, j)))) with
    (gtnf_assignment_prefixed_initial_sum supply).
  apply minterm_ext_ctx.
  intros [a j] Hm.
  set (body := fun sigma : IndicatorAssignment =>
    complete_assignment sigma ;;
    goto (gtnf_supply_label supply (e, sigma))).
  assert (Hbranch :
    test (AtIY_test (a, i)) ;; gtnf_assignment_prefixed_initial_sum supply ==
    test (AtIY_test (a, i)) ;; body i).
  {
    unfold gtnf_assignment_prefixed_initial_sum.
    fold body.
    cfgkat_rewrite <- (test_seq_absorb_right
      (AtIY_test (a, i)) (complete_test i)
      (AtIY_test_complete_test_same a i)
      (guarded_assignment_sum_all body)).
    unfold guarded_assignment_sum_all.
    cfgkat_rewrite (branchsel_assignment_on all_assignments body i
      (all_assignments_complete i)).
    cfgkat_rewrite (test_seq_absorb_right
      (AtIY_test (a, i)) (complete_test i)
      (AtIY_test_complete_test_same a i)
      (body i)).
    apply EqRefl.
  }
  apply AtIY_complete_assignment_branch_expr.
  - exact Hbranch.
  - unfold body.
    apply indannih_plus_prefix.
Qed.

Local Lemma gtnfcor_assignment_goto_state_label_prefix_lem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (i : IndicatorAssignment)
  :
  gtnf_prefix_lem2_env supply |-
    complete_assignment i ;; goto (gtnf_supply_label supply (e, i)) ==
    goto (gtnf_supply_label supply (e, i)) -|
    gtnf_prefix_lem2_env supply.
Proof.
  set (W := gtnf_prefix_lem2_env supply).
  set (l := gtnf_supply_label supply (e, i)).
  set (body := gtnf_prefix_body supply (e, i)).
  change (W |~
    complete_assignment i ;; goto l =~=
    goto l)%cfgkat_setoid.
  cfgkat_rewrite (unfold_bound_goto W l body
    ltac:(unfold W, l, body;
      apply gtnf_prefix_lem2_env_lookup_state;
      apply gtnfthm_reachable_states_contains;
      apply gtnfthm_reachable_initial)).
  unfold body, gtnf_prefix_body.
  cfgkat_rewrite (weaken_empty_to_env W
    (complete_assignment i ;;
      (complete_assignment i ;; gtnflem2_state_body supply e))
    (complete_assignment i ;; gtnflem2_state_body supply e)
    (indannih_plus_prefix i i (gtnflem2_state_body supply e))).
  apply EqRefl.
Qed.

Local Lemma gtnf_state_goto_no_goto_gtnflem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  :
  In s (gtnf_supply_states E e supply) ->
  no_goto_expr
    (goto (gtnf_supply_label supply s))
    (gtnflem2_env supply).
Proof.
  intros Hs target [target_body Htarget_body] Hcontains.
  simpl in Hcontains. subst target.
  unfold mk_environment in Htarget_body.
  simpl in Htarget_body.
  destruct (E (gtnf_supply_label supply s)) as [original |] eqn:HE.
  - pose proof
      (gtnf_supply_label_fresh_original E e supply s
        (gtnf_supply_label supply s) original Hs HE) as Hfresh.
    apply Hfresh. reflexivity.
  - destruct (gtnflem2_reachable_ell_source supply (gtnf_supply_label supply s))
      as [f |] eqn:Hexpr;
      [| discriminate Htarget_body].
    destruct (gtnflem2_reachable_ell_source_some_in supply
      (gtnf_supply_label supply s) f Hexpr)
      as [i [Hf Hlabel]].
    pose proof
      (gtnf_supply_label_expr_disjoint E e supply s f Hs
        (ex_intro _ i
          (gtnflem2_reachable_states_in_supply supply (f, i) Hf)))
      as Hdisjoint.
    apply Hdisjoint. exact Hlabel.
Qed.

Local Lemma gtnfthm_reachable_goto_remove_gtnflem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  :
  gtnfthm_reachable_state (E := E) (e := e) s ->
  gtnfthm_lem2_env supply |-
    goto (gtnf_supply_label supply s) ==
    goto (gtnf_supply_label supply s) -|
    gtnfthm_env supply.
Proof.
  intro Hreach.
  rewrite <- gtnfthm_lem2_env_as_cup.
  apply EqC3.
  intros l Hl.
  split.
  - intros k body Hbody.
    eapply gtnfthm_env_no_goto_gtnflem2_env; eauto.
  - eapply gtnf_state_goto_no_goto_gtnflem2_env.
    + eapply gtnflem2_reachable_state_in_supply.
      apply (gtnfthm_reachable_state_to_gtnflem2 supply).
      exact Hreach.
    + exact Hl.
Qed.

Corollary gtnfcor
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  E |- complete_assignment i ;; e ==
    goto (gtnf_supply_label (canonical_gtnf_supply (E := E) (e := e)) (e, i))
    -| canonical_gtnfthm_env (E := E) (e := e).
Proof.
  set (supply := canonical_gtnf_supply (E := E) (e := e)).
  change (E |- complete_assignment i ;; e ==
    goto (gtnf_supply_label supply (e, i)) -| gtnfthm_env supply).
  cfgkat_rewrite (@EqSeqRightCong
    E (gtnf_prefix_lem2_env supply)
    e (gtnf_assignment_prefixed_initial_sum supply)
    (complete_assignment i)
    (gtnfthm_canonical_prefix_lem2_env E e)
    ltac:(apply strong_equiv_no_goto;
      intro k; apply complete_assignment_no_contains_goto)).
  cfgkat_rewrite (weaken_empty_to_env
    (gtnf_prefix_lem2_env supply)
    (complete_assignment i ;; gtnf_assignment_prefixed_initial_sum supply)
    (complete_assignment i ;; goto (gtnf_supply_label supply (e, i)))
    (gtnf_assignment_prefixed_initial_sum_select supply i)).
  cfgkat_rewrite (gtnfcor_assignment_goto_state_label_prefix_lem2_env
    supply i).
  cfgkat_rewrite (gtnf_prefix_lem2_env_to_gtnfthm_lem2_env supply
    (goto (gtnf_supply_label supply (e, i)))).
  apply gtnfthm_reachable_goto_remove_gtnflem2_env.
  apply gtnfthm_reachable_initial.
Qed.
