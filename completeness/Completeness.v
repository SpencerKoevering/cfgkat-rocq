Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.Logic.ProofIrrelevance.
Require Import Stdlib.Program.Equality.
From Stdlib Require Import Lists.List.
Import ListNotations.

From CFGKAT.Completeness Require Export CFGKATCoalgebra.

Local Open Scope cfgkat_scope.
Local Open Scope cfgkat_setoid_scope.

Local Lemma resolved_transition_output_bisim
  (E F : label_environment CFGKATExpression)
  (R : CFGKATAutomatonBisimulation
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift F)))
  (s t : CFGKATSyntConfiguration)
  :
  cfgkat_relation R s t ->
  forall a,
    lifted_relation (cfgkat_relation R)
      (resolved_transition_output E (fst s) a (snd s))
      (resolved_transition_output F (fst t) a (snd t)).
Proof.
  intros Hrel a.
  destruct s as [e i].
  destruct t as [f j].
  eapply cfgkat_bisimulation_step.
  - exact Hrel.
  - apply resolved_transition_output_spec.
  - apply resolved_transition_output_spec.
Qed.

Local Lemma completeness_semantic_initial_outputs
  (E F : label_environment CFGKATExpression)
  (e f : CFGKATExpression)
  :
  (forall i, (e, i) ~[lift E, lift F] (f, i)) ->
  forall i,
    exists R : CFGKATAutomatonBisimulation
      (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
      (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift F)),
      cfgkat_relation R (e, i) (f, i) /\
      forall a,
        lifted_relation (cfgkat_relation R)
          (resolved_transition_output E e a i)
          (resolved_transition_output F f a i).
Proof.
  intros Hsem i.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar in Hsem.
  destruct (Hsem i) as [R HR].
  exists R.
  split.
  - exact HR.
  - intro a.
    exact (resolved_transition_output_bisim E F R (e, i) (f, i) HR a).
Qed.


Definition gtnf_resolved_step
  (E : label_environment CFGKATExpression)
  (s : CFGKATSyntConfiguration)
  (a : Atom)
  : CFGKATAutomatonOutputs CFGKATSyntConfiguration :=
  resolved_transition_output E (fst s) a (snd s).

Corollary ebotsemenv
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  :
  canonical_env_Y
    (gtnfthm_reachable_states
      (canonical_gtnf_supply (E := E) (e := e)))
    (gtnf_supply_label
      (canonical_gtnf_supply (E := E) (e := e)))
    (gtnf_resolved_step E)
  =
  canonical_gtnfthm_env (E := E) (e := e).
Proof.
  unfold canonical_gtnfthm_env.
  set (supply := canonical_gtnf_supply (E := E) (e := e)).
  apply environment_eq.
  intro k.
  unfold canonical_env_Y, gtnfthm_env, mk_environment.
  simpl.
  destruct (lookup_gtnf_state
    (gtnf_supply_label supply)
    (gtnfthm_reachable_states supply) k) as [[f i] |].
  - apply f_equal.
    unfold canonical_body_Y, gtnf_body_Y, gtnf_resolved_step.
    apply f_equal.
    apply functional_extensionality.
    intro a.
    unfold canonical_sysc_Y, sysc_Y, canonical_control_sys,
      canonical_control_output.
    simpl.
    destruct (resolved_transition_output E f a i) as
      [|j_accept|j_break|j_continue| |l_jump j_jump|p [g j_next]];
      reflexivity.
  - reflexivity.
Qed.

Definition relation_pair_state : Type :=
  (CFGKATSyntConfiguration * CFGKATSyntConfiguration)%type.

Definition relation_pair_related_state
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  : Type :=
  { p : relation_pair_state | R (fst p) (snd p) }.

Definition relation_pair_related_state_pair
  {R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop}
  (p : relation_pair_related_state R)
  : relation_pair_state :=
  proj1_sig p.

Coercion relation_pair_related_state_pair
  : relation_pair_related_state >-> relation_pair_state.

Definition relation_pair_left
  {R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop}
  (p : relation_pair_related_state R)
  : CFGKATSyntConfiguration :=
  fst (relation_pair_related_state_pair p).

Definition relation_pair_right
  {R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop}
  (p : relation_pair_related_state R)
  : CFGKATSyntConfiguration :=
  snd (relation_pair_related_state_pair p).

Definition relation_pair_related_label
  {R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop}
  (pair_label : relation_pair_state -> Label)
  (p : relation_pair_related_state R)
  : Label :=
  pair_label (relation_pair_related_state_pair p).

Definition relation_pair_states
  (left right : list CFGKATSyntConfiguration)
  : list relation_pair_state :=
  flat_map (fun s => map (fun t => (s, t)) right) left.

Local Lemma relation_pair_states_in
  (left right : list CFGKATSyntConfiguration)
  (s t : CFGKATSyntConfiguration)
  :
  In s left ->
  In t right ->
  In (s, t) (relation_pair_states left right).
Proof.
  intros Hs Ht.
  unfold relation_pair_states.
  apply in_flat_map.
  exists s.
  split.
  - exact Hs.
  - apply in_map.
    exact Ht.
Qed.

Local Lemma relation_pair_states_fst_in
  (left right : list CFGKATSyntConfiguration)
  (p : relation_pair_state)
  :
  In p (relation_pair_states left right) ->
  In (fst p) left.
Proof.
  unfold relation_pair_states.
  intro Hp.
  apply in_flat_map in Hp.
  destruct Hp as [s [Hs Hmap]].
  apply in_map_iff in Hmap.
  destruct Hmap as [t [Hp Ht]].
  subst p.
  exact Hs.
Qed.

Local Lemma relation_pair_states_snd_in
  (left right : list CFGKATSyntConfiguration)
  (p : relation_pair_state)
  :
  In p (relation_pair_states left right) ->
  In (snd p) right.
Proof.
  unfold relation_pair_states.
  intro Hp.
  apply in_flat_map in Hp.
  destruct Hp as [s [Hs Hmap]].
  apply in_map_iff in Hmap.
  destruct Hmap as [t [Hp Ht]].
  subst p.
  exact Ht.
Qed.

Definition relation_pair_label_avoid
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (left_label right_label : CFGKATSyntConfiguration -> Label)
  (l : Label)
  : Prop :=
  (exists s, In s left /\ l = left_label s) \/
  (exists t, In t right /\ l = right_label t) \/
  (exists s, In s left /\ contains_goto l (fst s)) \/
  (exists t, In t right /\ contains_goto l (fst t)) \/
  (exists s a j,
    In s left /\
    resolved_transition_output E (fst s) a (snd s) =
      CFGKATAutomatonJump l j) \/
	  (exists t a j,
	    In t right /\
	    resolved_transition_output F (fst t) a (snd t) =
	      CFGKATAutomatonJump l j).

Definition output_jump_labels
  {X : Type}
  (r : CFGKATAutomatonOutputs X)
  : list Label :=
  match r with
  | CFGKATAutomatonJump l _ => [l]
  | _ => []
  end.

Definition relation_resolved_jump_labels
  (E : label_environment CFGKATExpression)
  (states : list CFGKATSyntConfiguration)
  : list Label :=
  flat_map
    (fun s =>
      flat_map
        (fun ba =>
          output_jump_labels
            (resolved_transition_output E (fst s) (bool_to_atom ba) (snd s)))
        all_bool_atoms)
    states.

Definition relation_pair_label_avoid_list
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (left_label right_label : CFGKATSyntConfiguration -> Label)
  : list Label :=
  map left_label left ++
  map right_label right ++
  flat_map (fun s => goto_labels (fst s)) left ++
  flat_map (fun t => goto_labels (fst t)) right ++
  relation_resolved_jump_labels E left ++
  relation_resolved_jump_labels F right.

Local Lemma relation_resolved_jump_labels_complete
  (E : label_environment CFGKATExpression)
  (states : list CFGKATSyntConfiguration)
  (s : CFGKATSyntConfiguration)
  (a : Atom)
  (j : IndicatorAssignment)
  (l : Label)
  :
  In s states ->
  resolved_transition_output E (fst s) a (snd s) =
    CFGKATAutomatonJump l j ->
  In l (relation_resolved_jump_labels E states).
Proof.
  intros Hs Hjump.
  destruct (bool_to_atom_eq a) as [ba [Hba Hatom]].
  subst a.
  unfold relation_resolved_jump_labels.
  apply in_flat_map.
  exists s. split; [exact Hs |].
  apply in_flat_map.
    exists ba. split; [exact Hba |].
  rewrite Hjump.
  simpl. left. reflexivity.
Qed.

Local Lemma relation_pair_label_avoid_list_complete
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (left_label right_label : CFGKATSyntConfiguration -> Label)
  (l : Label)
  :
  relation_pair_label_avoid left right E F left_label right_label l ->
  In l (relation_pair_label_avoid_list left right E F left_label right_label).
Proof.
  unfold relation_pair_label_avoid,
    relation_pair_label_avoid_list.
  intros [H | [H | [H | [H | [H | H]]]]].
  - destruct H as [s [Hs ->]].
    repeat apply in_or_app; left.
    apply in_map. exact Hs.
  - destruct H as [t [Ht ->]].
    apply in_or_app. right.
    repeat apply in_or_app; left.
    apply in_map. exact Ht.
  - destruct H as [s [Hs Hcontains]].
    apply in_or_app. right.
    apply in_or_app. right.
    repeat apply in_or_app; left.
    apply in_flat_map.
    exists s. split; [exact Hs |].
    apply contains_goto_in_goto_labels.
    exact Hcontains.
  - destruct H as [t [Ht Hcontains]].
    apply in_or_app. right.
    apply in_or_app. right.
    apply in_or_app. right.
    repeat apply in_or_app; left.
    apply in_flat_map.
    exists t. split; [exact Ht |].
    apply contains_goto_in_goto_labels.
    exact Hcontains.
  - destruct H as [s [a [j [Hs Hjump]]]].
    apply in_or_app. right.
    apply in_or_app. right.
    apply in_or_app. right.
    apply in_or_app. right.
    apply in_or_app. left.
    eapply relation_resolved_jump_labels_complete; eauto.
  - destruct H as [t [a [j [Ht Hjump]]]].
    apply in_or_app. right.
    apply in_or_app. right.
    apply in_or_app. right.
    apply in_or_app. right.
    apply in_or_app. right.
    eapply relation_resolved_jump_labels_complete; eauto.
Qed.

Definition relation_pair_labels_fresh
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (left_label right_label : CFGKATSyntConfiguration -> Label)
  (pair_label : relation_pair_state -> Label)
  : Prop :=
  (forall p,
    In p (relation_pair_states left right) ->
    ~ relation_pair_label_avoid left right E F left_label right_label
        (pair_label p)) /\
  (forall p q,
    In p (relation_pair_states left right) ->
    In q (relation_pair_states left right) ->
    pair_label p = pair_label q ->
    p = q).

Lemma relation_pair_labels_exist
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (left_label right_label : CFGKATSyntConfiguration -> Label)
  :
  exists pair_label,
    relation_pair_labels_fresh left right E F left_label right_label pair_label.
Proof.
  destruct (fresh_label_family
    (relation_pair_states left right)
    (relation_pair_label_avoid_list left right E F left_label right_label))
    as [pair_label [Hfresh Hinj]].
  exists pair_label.
  split.
  - intros p Hp Havoid.
    apply (Hfresh p Hp).
    eapply relation_pair_label_avoid_list_complete.
    exact Havoid.
  - exact Hinj.
Qed.

Local Lemma relation_pair_label_fresh_left_state
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (left_label right_label : CFGKATSyntConfiguration -> Label)
  (pair_label : relation_pair_state -> Label)
  (p : relation_pair_state)
  (s : CFGKATSyntConfiguration)
  :
  relation_pair_labels_fresh left right E F left_label right_label pair_label ->
  In p (relation_pair_states left right) ->
  In s left ->
  pair_label p <> left_label s.
Proof.
  intros [Hfresh _] Hp Hs Heq.
  apply (Hfresh p Hp).
  left.
  exists s.
  split; [exact Hs | exact Heq].
Qed.

Local Lemma relation_pair_label_fresh_right_state
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (left_label right_label : CFGKATSyntConfiguration -> Label)
  (pair_label : relation_pair_state -> Label)
  (p : relation_pair_state)
  (t : CFGKATSyntConfiguration)
  :
  relation_pair_labels_fresh left right E F left_label right_label pair_label ->
  In p (relation_pair_states left right) ->
  In t right ->
  pair_label p <> right_label t.
Proof.
  intros [Hfresh _] Hp Ht Heq.
  apply (Hfresh p Hp).
  right; left.
  exists t.
  split; [exact Ht | exact Heq].
Qed.

Local Lemma relation_pair_label_no_left_resolved_jump
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (left_label right_label : CFGKATSyntConfiguration -> Label)
  (pair_label : relation_pair_state -> Label)
  (p : relation_pair_state)
  (s : CFGKATSyntConfiguration)
  (a : Atom)
  (j : IndicatorAssignment)
  :
  relation_pair_labels_fresh left right E F left_label right_label pair_label ->
  In p (relation_pair_states left right) ->
  In s left ->
  resolved_transition_output E (fst s) a (snd s) <>
    CFGKATAutomatonJump (pair_label p) j.
Proof.
  intros [Hfresh _] Hp Hs Hjump.
  apply (Hfresh p Hp).
  right; right; right; right; left.
  exists s, a, j.
  split; [exact Hs | exact Hjump].
Qed.

Local Lemma relation_pair_label_no_right_resolved_jump
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (left_label right_label : CFGKATSyntConfiguration -> Label)
  (pair_label : relation_pair_state -> Label)
  (p : relation_pair_state)
  (t : CFGKATSyntConfiguration)
  (a : Atom)
  (j : IndicatorAssignment)
  :
  relation_pair_labels_fresh left right E F left_label right_label pair_label ->
  In p (relation_pair_states left right) ->
  In t right ->
  resolved_transition_output F (fst t) a (snd t) <>
    CFGKATAutomatonJump (pair_label p) j.
Proof.
  intros [Hfresh _] Hp Ht Hjump.
  apply (Hfresh p Hp).
  right; right; right; right; right.
  exists t, a, j.
  split; [exact Ht | exact Hjump].
Qed.

Definition relation_pair_output_agreement
  (E F : label_environment CFGKATExpression)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  : Prop :=
  forall s t,
    R s t ->
    forall a,
      lifted_relation R
        (resolved_transition_output E (fst s) a (snd s))
        (resolved_transition_output F (fst t) a (snd t)).

Local Lemma guarded_atom_sum_all_cong_ctx
  (E F : label_environment CFGKATExpression)
  (body body' : Atom -> CFGKATExpression)
  :
  (forall ba,
    In ba all_bool_atoms ->
    E |- body (bool_to_atom ba) == body' (bool_to_atom ba) -| F) ->
  E |- guarded_atom_sum_all body ==
    guarded_atom_sum_all body' -| F.
Proof.
  unfold guarded_atom_sum_all.
  generalize all_bool_atoms as atoms.
  intros atoms Hbranches.
  induction atoms as [|ba atoms IH]; simpl.
  - apply strong_equiv_no_goto.
    intro k. simpl. tauto.
  - apply EqChoiceCong.
    + apply Hbranches. left. reflexivity.
    + apply IH.
      intros ba' Hba'.
      apply Hbranches. right. exact Hba'.
Qed.


Local Lemma canonical_sysc_Y_jump_label_inv
  {state : Type}
  (state_label : state -> Label)
  (r : CFGKATAutomatonOutputs state)
  (runtime_i j : IndicatorAssignment)
  (a : Atom)
  (l : Label)
  :
  CFGKATExpressionDynamics
    (canonical_sysc_Y state_label r, runtime_i) a
    (CFGKATAutomatonJump l j) ->
  exists j0, r = CFGKATAutomatonJump l j0.
Proof.
  intro Hdyn.
  pose proof
    (transition_output_unique
      (canonical_sysc_Y state_label r) a runtime_i
      (CFGKATAutomatonJump l j) Hdyn) as Hout.
  unfold canonical_sysc_Y, canonical_control_sys,
    canonical_control_output in Hout.
  destruct r as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p next];
    simpl in Hout.
  - simplify_sysc_transition_in Hout; inversion Hout.
  - simplify_sysc_transition_in Hout; inversion Hout.
  - simplify_sysc_transition_in Hout; inversion Hout.
  - simplify_sysc_transition_in Hout; inversion Hout.
  - simplify_sysc_transition_in Hout; inversion Hout.
  - simplify_sysc_transition_in Hout.
    inversion Hout; subst.
    eexists. reflexivity.
  - simplify_sysc_transition_in Hout; discriminate.
Qed.

Local Lemma canonical_body_Y_jump_inv
  {state : Type}
  (state_label : state -> Label)
  (step : state -> Atom -> CFGKATAutomatonOutputs state)
  (s : state)
  (runtime_i j : IndicatorAssignment)
  (a : Atom)
  (l : Label)
  :
  CFGKATExpressionDynamics
    (canonical_body_Y state_label step s, runtime_i) a
    (CFGKATAutomatonJump l j) ->
  exists branch_atom j0,
    step s branch_atom = CFGKATAutomatonJump l j0.
Proof.
  intro Hdyn.
  unfold canonical_body_Y in Hdyn.
  destruct (guarded_atom_sum_all_jump_inv _ _ _ _ _ Hdyn)
    as [ba [_ Hbranch]].
  destruct (canonical_sysc_Y_jump_label_inv
    state_label _ _ _ _ _ Hbranch) as [j0 Hout].
  exists (bool_to_atom ba), j0.
  exact Hout.
Qed.

Definition supply_restricted_relation
  (left right : list CFGKATSyntConfiguration)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (s t : CFGKATSyntConfiguration)
  : Prop :=
  R s t /\ In s left /\ In t right.

Local Lemma relation_pair_output_agreement_reachable_of_bisim
  (E F : label_environment CFGKATExpression)
  (e f : CFGKATExpression)
  (supplyE : gtnf_label_supply E e)
  (supplyF : gtnf_label_supply F f)
  (R : CFGKATAutomatonBisimulation
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift F)))
  :
  relation_pair_output_agreement E F
    (supply_restricted_relation
      (gtnfthm_reachable_states supplyE)
      (gtnfthm_reachable_states supplyF)
      (cfgkat_relation R)).
Proof.
  intros s t [HR [Hs Ht]] a.
  pose proof (resolved_transition_output_bisim E F R s t HR a) as Hlift.
  remember (resolved_transition_output E (fst s) a (snd s))
    as lout eqn:Hlout.
  remember (resolved_transition_output F (fst t) a (snd t))
    as rout eqn:Hrout.
  assert (Hlift' :
    lifted_relation (cfgkat_relation R) lout rout).
  {
    exact Hlift.
  }
  induction Hlift'.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
    split.
    + exact H.
    + split.
      * destruct s as [source source_i].
        apply gtnfthm_reachable_states_contains.
        eapply gtnfthm_reachable_next.
        -- eapply gtnfthm_reachable_states_in_reachable.
           exact Hs.
        -- symmetry. exact Hlout.
      * destruct t as [target target_i].
        apply gtnfthm_reachable_states_contains.
        eapply gtnfthm_reachable_next.
        -- eapply gtnfthm_reachable_states_in_reachable.
           exact Ht.
        -- symmetry. exact Hrout.
Qed.

Local Lemma canonical_sysc_Y_no_contains
  {state : Type}
  (state_label : state -> Label)
  (target : Label)
  (r : CFGKATAutomatonOutputs state)
  :
  (forall j, r <> CFGKATAutomatonJump target j) ->
  (forall p s, r = CFGKATAutomatonNext p s ->
    state_label s <> target) ->
  ~ contains_goto target (canonical_sysc_Y state_label r).
Proof.
  intros Hjump Hnext.
  destruct r as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p next];
    simpl.
  - tauto.
  - apply complete_assignment_no_contains_goto.
  - intros [Hbad | Hbad].
    + exact (complete_assignment_no_contains_goto i_break target Hbad).
    + exact Hbad.
  - intros [Hbad | Hbad].
    + exact (complete_assignment_no_contains_goto i_continue target Hbad).
    + exact Hbad.
  - tauto.
  - intros [Hbad | Hlabel].
    + exact (complete_assignment_no_contains_goto i_jump target Hbad).
    + apply (Hjump i_jump).
      subst l_jump. reflexivity.
  - intros [Hact | Hlabel].
    + exact Hact.
    + apply (Hnext p next eq_refl).
      exact Hlabel.
Qed.

Local Lemma canonical_body_Y_no_contains
  {state : Type}
  (state_label : state -> Label)
  (step : state -> Atom -> CFGKATAutomatonOutputs state)
  (target : Label)
  (s : state)
  :
  (forall a j, step s a <> CFGKATAutomatonJump target j) ->
  (forall a p next, step s a = CFGKATAutomatonNext p next ->
    state_label next <> target) ->
  ~ contains_goto target (canonical_body_Y state_label step s).
Proof.
  intros Hjump Hnext.
  unfold canonical_body_Y.
  apply guarded_atom_sum_all_no_contains.
  intros ba _.
  apply canonical_sysc_Y_no_contains.
  - intro j. apply Hjump.
  - intros p next Hout.
    eapply Hnext.
    exact Hout.
Qed.

Definition relation_pair_related_states
  (left right : list CFGKATSyntConfiguration)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  : list (relation_pair_related_state R) :=
  flat_map
    (fun p =>
      match excluded_middle_informative (R (fst p) (snd p)) with
      | left HR => [exist _ p HR]
      | right _ => []
      end)
    (relation_pair_states left right).

Local Lemma relation_pair_related_states_in
  (left right : list CFGKATSyntConfiguration)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (s t : CFGKATSyntConfiguration)
  (HR : R s t)
  :
  In s left ->
  In t right ->
  In (exist _ (s, t) HR) (relation_pair_related_states left right R).
Proof.
  intros Hs Ht.
  unfold relation_pair_related_states.
  apply in_flat_map.
  exists (s, t).
  split.
  - apply relation_pair_states_in; assumption.
  - destruct (excluded_middle_informative (R (fst (s, t)) (snd (s, t))))
      as [HR' | Hnot].
    + cbn. left. apply subset_eq_compat. reflexivity.
    + change (~ R s t) in Hnot.
      apply Hnot. exact HR.
Qed.

Local Lemma relation_pair_related_states_pair_in
  (left right : list CFGKATSyntConfiguration)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (p : relation_pair_related_state R)
  :
  In p (relation_pair_related_states left right R) ->
  In (relation_pair_related_state_pair p) (relation_pair_states left right).
Proof.
  unfold relation_pair_related_states.
  intro Hp.
  apply in_flat_map in Hp.
  destruct Hp as [q [Hq Hmember]].
  destruct (excluded_middle_informative (R (fst q) (snd q))) as [HR | Hnot].
  - simpl in Hmember.
    destruct Hmember as [Hp | []].
    subst p.
    exact Hq.
  - contradiction.
Qed.

Local Lemma relation_pair_related_state_ext
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (p q : relation_pair_related_state R)
  :
  relation_pair_related_state_pair p =
    relation_pair_related_state_pair q ->
  p = q.
Proof.
  destruct p as [p Hp].
  destruct q as [q Hq].
  simpl.
  intro Heq.
  subst q.
  apply subset_eq_compat.
  reflexivity.
Qed.

Definition relation_pair_lifted_output
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (left_out right_out : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  (Hlift :
    lifted_relation R left_out right_out)
  : CFGKATAutomatonOutputs (relation_pair_related_state R).
Proof.
  destruct left_out as [| i | i | i | | l i | act s'].
  - exact CFGKATAutomatonReject.
  - exact (CFGKATAutomatonAccept i).
  - exact (CFGKATAutomatonBreak i).
  - exact (CFGKATAutomatonContinue i).
  - exact CFGKATAutomatonReturn.
  - exact (CFGKATAutomatonJump l i).
  - destruct right_out as [| i | i | i | | l i | act_right t'].
    all: try solve [exfalso; inversion Hlift].
    + exact (CFGKATAutomatonNext act
        (exist (fun p : relation_pair_state => R (fst p) (snd p)) (s', t')
          ltac:(inversion Hlift; subst; eauto))).
Defined.

Definition relation_pair_step
  (E F : label_environment CFGKATExpression)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (Hagree : relation_pair_output_agreement E F R)
  (p : relation_pair_related_state R)
  (a : Atom)
  : CFGKATAutomatonOutputs (relation_pair_related_state R) :=
  let s := relation_pair_left p in
  let t := relation_pair_right p in
  relation_pair_lifted_output R _ _
    (Hagree s t (proj2_sig p) a).

Local Lemma relation_pair_lifted_output_left_hom
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (left_out right_out : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  (Hlift : lifted_relation R left_out right_out)
  :
  lifted_relation
    (fun x' z' => relation_pair_left x' = z')
    (relation_pair_lifted_output R left_out right_out Hlift)
    left_out.
Proof.
  dependent destruction Hlift;
    cbn [relation_pair_lifted_output relation_pair_left];
    constructor; reflexivity.
Qed.

Local Lemma relation_pair_lifted_output_right_hom
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (left_out right_out : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  (Hlift : lifted_relation R left_out right_out)
  :
  lifted_relation
    (fun x' z' => relation_pair_right x' = z')
    (relation_pair_lifted_output R left_out right_out Hlift)
    right_out.
Proof.
  dependent destruction Hlift;
    cbn [relation_pair_lifted_output relation_pair_right];
    constructor; reflexivity.
Qed.

Local Lemma relation_pair_lifted_output_next_inv
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (left_out right_out : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  (Hlift : lifted_relation R left_out right_out)
  (act : Action)
  (next : relation_pair_related_state R)
  :
  relation_pair_lifted_output R left_out right_out Hlift =
    CFGKATAutomatonNext act next ->
  exists s' t' HRnext,
    left_out = CFGKATAutomatonNext act s' /\
    right_out = CFGKATAutomatonNext act t' /\
    next = exist _ (s', t') HRnext.
Proof.
  intro Hnext.
  dependent destruction Hlift;
    cbn [relation_pair_lifted_output] in Hnext;
  inversion Hnext; subst.
  repeat eexists; repeat split; reflexivity.
Qed.

Local Lemma relation_pair_lifted_output_left_jump_inv
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (left_out right_out : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  (Hlift : lifted_relation R left_out right_out)
  (l : Label)
  (j : IndicatorAssignment)
  :
  relation_pair_lifted_output R left_out right_out Hlift =
    CFGKATAutomatonJump l j ->
  exists j0, left_out = CFGKATAutomatonJump l j0.
Proof.
  intro Hjump.
  dependent destruction Hlift;
    cbn [relation_pair_lifted_output] in Hjump;
  inversion Hjump; subst.
  exists j. reflexivity.
Qed.

Local Lemma relation_pair_lifted_output_right_jump_inv
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (left_out right_out : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  (Hlift : lifted_relation R left_out right_out)
  (l : Label)
  (j : IndicatorAssignment)
  :
  relation_pair_lifted_output R left_out right_out Hlift =
    CFGKATAutomatonJump l j ->
  exists j0, right_out = CFGKATAutomatonJump l j0.
Proof.
  intro Hjump.
  dependent destruction Hlift;
    cbn [relation_pair_lifted_output] in Hjump;
  inversion Hjump; subst.
  exists j. reflexivity.
Qed.

Definition hompressol_E_x_as_z
  {X Z : Type}
  (xs : list X)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  : label_environment CFGKATExpression.
Proof.
  refine (mk_environment
    (fun k =>
      match lookup_canonical_state labelX xs k with
      | Some x => Some (canonical_body labelZ zeta (h x))
      | None => None
      end)
    (map labelX xs)
    _).
  intros k body Hlookup.
  destruct (lookup_canonical_state labelX xs k) as [x |] eqn:Hx.
  - destruct (lookup_canonical_state_some_in _ _ _ _ Hx)
      as [Hin Hlabel].
    subst k.
    apply in_map.
    exact Hin.
  - discriminate Hlookup.
Defined.

Local Lemma relation_pair_step_next_in_related
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (Hagree : relation_pair_output_agreement E F R)
  (source next : relation_pair_related_state R)
  (a : Atom)
  (act : Action)
  :
  In source (relation_pair_related_states left right R) ->
  (forall s a0 act0 next0,
    In s left ->
    resolved_transition_output E (fst s) a0 (snd s) =
      CFGKATAutomatonNext act0 next0 ->
    In next0 left) ->
  (forall t a0 act0 next0,
    In t right ->
    resolved_transition_output F (fst t) a0 (snd t) =
      CFGKATAutomatonNext act0 next0 ->
    In next0 right) ->
  relation_pair_step E F R Hagree source a =
    CFGKATAutomatonNext act next ->
  In next (relation_pair_related_states left right R).
Proof.
  intros Hsource Hleft_closed Hright_closed Hnext.
  pose proof (relation_pair_related_states_pair_in left right R source Hsource)
    as Hsource_pair.
  unfold relation_pair_step in Hnext.
  destruct (relation_pair_lifted_output_next_inv
    R _ _ _ act next Hnext)
    as [s' [t' [HRnext [Hleft [Hright Hnext_eq]]]]].
  subst next.
  apply (relation_pair_related_states_in left right R s' t' HRnext).
  - eapply Hleft_closed.
    + eapply relation_pair_states_fst_in. exact Hsource_pair.
    + exact Hleft.
  - eapply Hright_closed.
    + eapply relation_pair_states_snd_in. exact Hsource_pair.
    + exact Hright.
Qed.

Local Lemma relation_pair_step_left_jump_inv
  (E F : label_environment CFGKATExpression)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (Hagree : relation_pair_output_agreement E F R)
  (source : relation_pair_related_state R)
  (a : Atom)
  (l : Label)
  (j : IndicatorAssignment)
  :
  relation_pair_step E F R Hagree source a = CFGKATAutomatonJump l j ->
  exists j0,
    resolved_transition_output E
      (fst (relation_pair_left source)) a
      (snd (relation_pair_left source)) =
      CFGKATAutomatonJump l j0.
Proof.
  intro Hjump.
  unfold relation_pair_step in Hjump.
  apply (relation_pair_lifted_output_left_jump_inv
    R _ _ _ l j Hjump).
Qed.

Local Lemma canonical_body_Y_no_jump_to_label
  {state : Type}
  (state_label : state -> Label)
  (step : state -> Atom -> CFGKATAutomatonOutputs state)
  (source : state)
  (target : Label)
  (runtime_i j : IndicatorAssignment)
  (a : Atom)
  :
  (forall branch_atom j0,
    step source branch_atom <> CFGKATAutomatonJump target j0) ->
  ~ CFGKATExpressionDynamics
      (canonical_body_Y state_label step source, runtime_i) a
      (CFGKATAutomatonJump target j).
Proof.
  intros Hno Hdyn.
  destruct (canonical_body_Y_jump_inv
    state_label step source runtime_i j a target Hdyn)
    as [branch_atom [j0 Hout]].
  exact (Hno branch_atom j0 Hout).
Qed.

Local Lemma relation_pair_step_no_pair_label_jump
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (Hagree : relation_pair_output_agreement E F R)
  (left_label right_label : CFGKATSyntConfiguration -> Label)
  (pair_label : relation_pair_state -> Label)
  (source target : relation_pair_related_state R)
  (a : Atom)
  (j : IndicatorAssignment)
  :
  relation_pair_labels_fresh left right E F left_label right_label pair_label ->
  In source (relation_pair_related_states left right R) ->
  In target (relation_pair_related_states left right R) ->
  relation_pair_step E F R Hagree source a <>
    CFGKATAutomatonJump (pair_label target) j.
Proof.
  intros Hfresh Hsource Htarget Hjump.
  destruct (relation_pair_step_left_jump_inv
    E F R Hagree source a (pair_label target) j Hjump)
    as [j0 Hleft_jump].
  eapply relation_pair_label_no_left_resolved_jump.
  - exact Hfresh.
  - eapply relation_pair_related_states_pair_in. exact Htarget.
  - eapply relation_pair_states_fst_in.
    eapply relation_pair_related_states_pair_in. exact Hsource.
  - exact Hleft_jump.
Qed.

Local Lemma relation_pair_step_no_left_label_jump
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (Hagree : relation_pair_output_agreement E F R)
  (left_label : CFGKATSyntConfiguration -> Label)
  (source : relation_pair_related_state R)
  (target : CFGKATSyntConfiguration)
  (a : Atom)
  (j : IndicatorAssignment)
  :
  In source (relation_pair_related_states left right R) ->
  In target left ->
  (forall source_state target_state branch_atom j0,
    In source_state left ->
    In target_state left ->
    resolved_transition_output E (fst source_state) branch_atom
      (snd source_state) <>
      CFGKATAutomatonJump (left_label target_state) j0) ->
  relation_pair_step E F R Hagree source a <>
    CFGKATAutomatonJump (left_label target) j.
Proof.
  intros Hsource Htarget Hno Hjump.
  destruct (relation_pair_step_left_jump_inv
    E F R Hagree source a (left_label target) j Hjump)
    as [j0 Hleft_jump].
  eapply Hno.
  - eapply relation_pair_states_fst_in.
    eapply relation_pair_related_states_pair_in. exact Hsource.
  - exact Htarget.
  - exact Hleft_jump.
Qed.

Local Lemma relation_pair_step_no_right_label_jump
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (Hagree : relation_pair_output_agreement E F R)
  (right_label : CFGKATSyntConfiguration -> Label)
  (source : relation_pair_related_state R)
  (target : CFGKATSyntConfiguration)
  (a : Atom)
  (j : IndicatorAssignment)
  :
  In source (relation_pair_related_states left right R) ->
  In target right ->
  (forall source_state target_state branch_atom j0,
    In source_state right ->
    In target_state right ->
    resolved_transition_output F (fst source_state) branch_atom
      (snd source_state) <>
      CFGKATAutomatonJump (right_label target_state) j0) ->
  relation_pair_step E F R Hagree source a <>
    CFGKATAutomatonJump (right_label target) j.
Proof.
  intros Hsource Htarget Hno Hjump.
  unfold relation_pair_step in Hjump.
  destruct (relation_pair_lifted_output_right_jump_inv
    R _ _ _ (right_label target) j Hjump)
    as [j0 Hright_jump].
  eapply Hno.
  - eapply relation_pair_states_snd_in.
    eapply relation_pair_related_states_pair_in. exact Hsource.
  - exact Htarget.
  - exact Hright_jump.
Qed.

Definition hompressol_E_x
  {X : Type}
  (xs : list X)
  (labelX : X -> Label)
  (chi : CFGKATCoalgebra X)
  : label_environment CFGKATExpression :=
  canonical_env xs labelX chi.

Definition hompressol_E_z
  {Z : Type}
  (zs : list Z)
  (labelZ : Z -> Label)
  (zeta : CFGKATCoalgebra Z)
  : label_environment CFGKATExpression :=
  canonical_env zs labelZ zeta.

Definition hompressol_E_x'
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (chi : CFGKATCoalgebra X)
  (zeta : CFGKATCoalgebra Z)
  : label_environment CFGKATExpression.
Proof.
  refine (mk_environment
    (fun k =>
      match lookup_canonical_state labelX xs k with
      | Some x => Some (canonical_body labelX chi x)
      | None =>
          match lookup_canonical_state labelZ zs k with
          | Some z => Some (canonical_body labelZ zeta z)
          | None => None
          end
      end)
    (map labelX xs ++ map labelZ zs)
    _).
  intros k body Hlookup.
  destruct (lookup_canonical_state labelX xs k) as [x |] eqn:Hx.
  - destruct (lookup_canonical_state_some_in _ _ _ _ Hx)
      as [Hin Hlabel].
    subst k.
    apply in_or_app.
    left.
    apply in_map.
    exact Hin.
  - destruct (lookup_canonical_state labelZ zs k) as [z |] eqn:Hz.
    + destruct (lookup_canonical_state_some_in _ _ _ _ Hz)
        as [Hin Hlabel].
      subst k.
      apply in_or_app.
      right.
      apply in_map.
      exact Hin.
    + discriminate Hlookup.
Defined.

Definition hompressol_E_z'
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  : label_environment CFGKATExpression.
Proof.
  refine (mk_environment
    (fun k =>
      match lookup_canonical_state labelX xs k with
      | Some x => Some (canonical_body labelZ zeta (h x))
      | None =>
          match lookup_canonical_state labelZ zs k with
          | Some z => Some (canonical_body labelZ zeta z)
          | None => None
          end
      end)
    (map labelX xs ++ map labelZ zs)
    _).
  intros k body Hlookup.
  destruct (lookup_canonical_state labelX xs k) as [x |] eqn:Hx.
  - destruct (lookup_canonical_state_some_in _ _ _ _ Hx)
      as [Hin Hlabel].
    subst k.
    apply in_or_app.
    left.
    apply in_map.
    exact Hin.
  - destruct (lookup_canonical_state labelZ zs k) as [z |] eqn:Hz.
    + destruct (lookup_canonical_state_some_in _ _ _ _ Hz)
        as [Hin Hlabel].
      subst k.
      apply in_or_app.
      right.
      apply in_map.
      exact Hin.
    + discriminate Hlookup.
Defined.

Local Lemma hompressol_E_x_prime_eq
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (chi : CFGKATCoalgebra X)
  (zeta : CFGKATCoalgebra Z)
  (Hdisj :
    label_disjoint
      (hompressol_E_x xs labelX chi)
      (hompressol_E_z zs labelZ zeta))
  :
  hompressol_E_x' xs zs labelX labelZ chi zeta =
    hompressol_E_x xs labelX chi + hompressol_E_z zs labelZ zeta.
Proof.
  apply environment_eq.
  intro k.
  unfold hompressol_E_x', hompressol_E_x, hompressol_E_z,
    canonical_env, label_env_cup, mk_environment.
  cbn.
  destruct (lookup_canonical_state labelX xs k); reflexivity.
Qed.

Local Lemma hompressol_E_z_prime_eq_comm
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  :
  forall
    (Hdisj :
      label_disjoint
        (hompressol_E_z zs labelZ zeta)
        (hompressol_E_x_as_z xs labelX labelZ zeta h)),
  hompressol_E_z' xs zs labelX labelZ zeta h =
    hompressol_E_z zs labelZ zeta +
      hompressol_E_x_as_z xs labelX labelZ zeta h.
Proof.
  intro Hdisj.
  apply environment_eq.
  intro k.
  unfold hompressol_E_z', hompressol_E_z, canonical_env,
    hompressol_E_x_as_z, label_env_cup, mk_environment.
  cbn.
  destruct (lookup_canonical_state labelX xs k) as [x |] eqn:Hx;
  destruct (lookup_canonical_state labelZ zs k) as [z |] eqn:Hz;
    try reflexivity.
  exfalso.
  eapply (Hdisj k).
  - unfold label_in_dom, hompressol_E_z, canonical_env.
    cbn.
    rewrite Hz. eexists. reflexivity.
  - unfold label_in_dom, hompressol_E_x_as_z.
    cbn.
    rewrite Hx. eexists. reflexivity.
Qed.

Local Lemma hompressol_E_z_prime_lookup_x
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  (x : X)
  :
  (forall u v,
    In u xs ->
    In v xs ->
    labelX u = labelX v ->
    u = v) ->
  In x xs ->
  hompressol_E_z' xs zs labelX labelZ zeta h (labelX x) =
    Some (canonical_body labelZ zeta (h x)).
Proof.
  intros Hinj Hin.
  unfold hompressol_E_z'.
  cbn.
  rewrite (lookup_canonical_state_in_some labelX xs x Hinj Hin).
  reflexivity.
Qed.

Local Lemma hompressol_E_z_prime_lookup_z
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  (z : Z)
  :
  label_disjoint
    (hompressol_E_z zs labelZ zeta)
    (hompressol_E_x_as_z xs labelX labelZ zeta h) ->
  (forall u v,
    In u zs ->
    In v zs ->
    labelZ u = labelZ v ->
    u = v) ->
  In z zs ->
  hompressol_E_z' xs zs labelX labelZ zeta h (labelZ z) =
    Some (canonical_body labelZ zeta z).
Proof.
  intros Hdisj Hinj Hin.
  unfold hompressol_E_z'.
  cbn.
  destruct (lookup_canonical_state labelX xs (labelZ z)) as [x |]
    eqn:Hx.
  - exfalso.
    eapply (Hdisj (labelZ z)).
    + exists (canonical_body labelZ zeta z).
      unfold hompressol_E_z, canonical_env.
      cbn.
      rewrite (lookup_canonical_state_in_some labelZ zs z Hinj Hin).
      reflexivity.
    + exists (canonical_body labelZ zeta (h x)).
      unfold hompressol_E_x_as_z. cbn. rewrite Hx. reflexivity.
  - rewrite (lookup_canonical_state_in_some labelZ zs z Hinj Hin).
    reflexivity.
Qed.

Local Lemma hompressol_E_z_prime_project_goto
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  (x : X)
  :
  label_disjoint
    (hompressol_E_z zs labelZ zeta)
    (hompressol_E_x_as_z xs labelX labelZ zeta h) ->
  (forall u v,
    In u xs ->
    In v xs ->
    labelX u = labelX v ->
    u = v) ->
  (forall u v,
    In u zs ->
    In v zs ->
    labelZ u = labelZ v ->
    u = v) ->
  (forall y, In y xs -> In (h y) zs) ->
  In x xs ->
  hompressol_E_z' xs zs labelX labelZ zeta h |-
    goto (labelX x) == goto (labelZ (h x)) -|
  hompressol_E_z' xs zs labelX labelZ zeta h.
Proof.
  intros Hdisj HinjX HinjZ Hh_in Hx.
  cfgkat_rewrite (unfold_bound_goto _ _ _
    ltac:(apply (@hompressol_E_z_prime_lookup_x
      X Z xs zs labelX labelZ zeta h x); assumption)).
  cfgkat_rewrite <- (unfold_bound_goto _ _ _
    ltac:(apply (@hompressol_E_z_prime_lookup_z
      X Z xs zs labelX labelZ zeta h (h x)); try assumption;
      apply Hh_in; exact Hx)).
  apply EqRefl.
Qed.

Local Lemma hom_canonical_sysc_equiv
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (chi : CFGKATCoalgebra X)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  (source : X)
  (a : Atom)
  :
  label_disjoint
    (hompressol_E_z zs labelZ zeta)
    (hompressol_E_x_as_z xs labelX labelZ zeta h) ->
  CFGKATCoalgebraHomomorphism chi zeta h ->
  (forall y a0 p y',
    In y xs ->
    chi y a0 = CFGKATAutomatonNext p y' ->
    In y' xs) ->
  (forall y, In y xs -> In (h y) zs) ->
  (forall u v,
    In u xs ->
    In v xs ->
    labelX u = labelX v ->
    u = v) ->
  (forall u v,
    In u zs ->
    In v zs ->
    labelZ u = labelZ v ->
    u = v) ->
  In source xs ->
  hompressol_E_z' xs zs labelX labelZ zeta h |-
    canonical_sysc labelX (chi source a) ==
    canonical_sysc labelZ (zeta (h source) a) -|
  hompressol_E_z' xs zs labelX labelZ zeta h.
Proof.
  intros Hdisj Hhom Hclosed Hh_in HinjX HinjZ Hsource.
  pose proof (Hhom source a) as Hstep.
  remember (chi source a) as left_out eqn:Hleft.
  remember (zeta (h source) a) as right_out eqn:Hright.
  revert Hleft Hright.
  induction Hstep; intros Hleft Hright; subst; simpl; try apply EqRefl.
  apply EqSeqRightCong.
  - eapply hompressol_E_z_prime_project_goto; eauto.
  - apply strong_equiv_no_goto.
    intro k. simpl. tauto.
Qed.

Local Lemma hom_canonical_body_equiv
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (chi : CFGKATCoalgebra X)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  (source : X)
  :
  label_disjoint
    (hompressol_E_z zs labelZ zeta)
    (hompressol_E_x_as_z xs labelX labelZ zeta h) ->
  CFGKATCoalgebraHomomorphism chi zeta h ->
  (forall y a0 p y',
    In y xs ->
    chi y a0 = CFGKATAutomatonNext p y' ->
    In y' xs) ->
  (forall y, In y xs -> In (h y) zs) ->
  (forall u v,
    In u xs ->
    In v xs ->
    labelX u = labelX v ->
    u = v) ->
  (forall u v,
    In u zs ->
    In v zs ->
    labelZ u = labelZ v ->
    u = v) ->
  In source xs ->
  hompressol_E_z' xs zs labelX labelZ zeta h |-
    canonical_body labelX chi source ==
    canonical_body labelZ zeta (h source) -|
  hompressol_E_z' xs zs labelX labelZ zeta h.
Proof.
  intros Hdisj Hhom Hclosed Hh_in HinjX HinjZ Hsource.
  unfold canonical_body.
  apply guarded_atom_sum_all_cong_ctx.
  intros ba _.
  apply hom_canonical_sysc_equiv; assumption.
Qed.

Local Lemma hompressol_E_x_prime_E_z_prime_solution
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (chi : CFGKATCoalgebra X)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  :
  label_disjoint
    (hompressol_E_z zs labelZ zeta)
    (hompressol_E_x_as_z xs labelX labelZ zeta h) ->
  CFGKATCoalgebraHomomorphism chi zeta h ->
  (forall y a0 p y',
    In y xs ->
    chi y a0 = CFGKATAutomatonNext p y' ->
    In y' xs) ->
  (forall y, In y xs -> In (h y) zs) ->
  (forall u v,
    In u xs ->
    In v xs ->
    labelX u = labelX v ->
    u = v) ->
  (forall u v,
    In u zs ->
    In v zs ->
    labelZ u = labelZ v ->
    u = v) ->
  C7_solution
    (hompressol_E_x' xs zs labelX labelZ chi zeta)
    (hompressol_E_z' xs zs labelX labelZ zeta h).
Proof.
  intros Hdisj Hhom Hclosed Hh_in HinjX HinjZ.
  unfold C7_solution.
  intros l body Hbody.
  unfold hompressol_E_x' in Hbody.
  cbn in Hbody.
  destruct (lookup_canonical_state labelX xs l) as [x |] eqn:Hx.
  - injection Hbody as <-.
    destruct (lookup_canonical_state_some_in _ _ _ _ Hx)
      as [Hin Hlabel].
    rewrite Hlabel.
    cfgkat_rewrite (unfold_bound_goto _ _ _
      ltac:(apply (@hompressol_E_z_prime_lookup_x
        X Z xs zs labelX labelZ zeta h x); assumption)).
    cfgkat_rewrite <- (hom_canonical_body_equiv xs zs labelX labelZ
      chi zeta h x Hdisj Hhom Hclosed Hh_in HinjX HinjZ Hin).
    apply EqRefl.
  - destruct (lookup_canonical_state labelZ zs l) as [z |] eqn:Hz;
      [| discriminate Hbody].
    injection Hbody as <-.
    destruct (lookup_canonical_state_some_in _ _ _ _ Hz)
      as [Hin Hlabel].
    rewrite Hlabel.
    apply unfold_bound_goto.
    unfold hompressol_E_z'.
    cbn.
    assert (Hxnone :
      lookup_canonical_state labelX xs (labelZ z) = None).
    { rewrite <- Hlabel. exact Hx. }
    rewrite Hxnone.
    rewrite (lookup_canonical_state_in_some labelZ zs z HinjZ Hin).
    reflexivity.
Qed.

Local Lemma hompressol_E_x_prime_E_z_prime_same_domain
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (chi : CFGKATCoalgebra X)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  :
  C7_same_domain
    (hompressol_E_x' xs zs labelX labelZ chi zeta)
    (hompressol_E_z' xs zs labelX labelZ zeta h).
Proof.
  intro l.
  unfold label_in_dom, hompressol_E_x', hompressol_E_z'.
  cbn.
  destruct (lookup_canonical_state labelX xs l);
  destruct (lookup_canonical_state labelZ zs l);
    split; intros [body H]; try discriminate; eexists; reflexivity.
Qed.

Local Definition hompressol_chosen_labels_disjoint
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  : Prop :=
  forall x z,
    In x xs ->
    In z zs ->
    labelX x <> labelZ z.

Local Definition hompressol_chosen_no_jump_to
  {X Target : Type}
  (xs : list X)
  (targets : list Target)
  (chi : CFGKATCoalgebra X)
  (target_label : Target -> Label)
  : Prop :=
  forall source target a j,
    In source xs ->
    In target targets ->
    chi source a <> CFGKATAutomatonJump (target_label target) j.

Record hompressol_label_hypotheses
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (ellX : X -> Label)
  (ellZ : Z -> Label)
  (chi : CFGKATCoalgebra X)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  : Prop :=
{
  hompressol_image_closed :
    forall y, In y xs -> In (h y) zs;
  hompressol_source_next_closed :
    forall y a p y',
      In y xs ->
      chi y a = CFGKATAutomatonNext p y' ->
      In y' xs;
  hompressol_target_next_closed :
    forall y a p y',
      In y zs ->
      zeta y a = CFGKATAutomatonNext p y' ->
      In y' zs;
  hompressol_source_label_injective :
    forall u v,
      In u xs ->
      In v xs ->
      ellX u = ellX v ->
      u = v;
  hompressol_target_label_injective :
    forall u v,
      In u zs ->
      In v zs ->
      ellZ u = ellZ v ->
      u = v;
  hompressol_labels_disjoint :
    hompressol_chosen_labels_disjoint xs zs ellX ellZ;
  hompressol_source_no_jump_to_source_labels :
    hompressol_chosen_no_jump_to xs xs chi ellX;
  hompressol_source_no_jump_to_target_labels :
    hompressol_chosen_no_jump_to xs zs chi ellZ;
  hompressol_target_no_jump_to_source_labels :
    hompressol_chosen_no_jump_to zs xs zeta ellX;
  hompressol_target_no_jump_to_target_labels :
    hompressol_chosen_no_jump_to zs zs zeta ellZ
}.

Local Lemma hompressol_chosen_env_disjoint
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (chi : CFGKATCoalgebra X)
  (zeta : CFGKATCoalgebra Z)
  :
  hompressol_chosen_labels_disjoint xs zs labelX labelZ ->
  label_disjoint
    (hompressol_E_x xs labelX chi)
    (hompressol_E_z zs labelZ zeta).
Proof.
  intros Hdistinct l [bodyX HX] [bodyZ HZ].
  unfold hompressol_E_x, hompressol_E_z, canonical_env in *.
  cbn in *.
  destruct (lookup_canonical_state labelX xs l) as [x |] eqn:Hx;
    [| discriminate].
  destruct (lookup_canonical_state labelZ zs l) as [z |] eqn:Hz;
    [| discriminate].
  destruct (lookup_canonical_state_some_in _ _ _ _ Hx)
    as [Hx_in Hx_label].
  destruct (lookup_canonical_state_some_in _ _ _ _ Hz)
    as [Hz_in Hz_label].
  apply (Hdistinct x z Hx_in Hz_in).
  rewrite <- Hx_label.
  exact Hz_label.
Qed.

Local Lemma hompressol_chosen_project_disjoint
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  :
  hompressol_chosen_labels_disjoint xs zs labelX labelZ ->
  label_disjoint
    (hompressol_E_z zs labelZ zeta)
    (hompressol_E_x_as_z xs labelX labelZ zeta h).
Proof.
  intros Hdistinct l [bodyZ HZ] [bodyX HX].
  unfold hompressol_E_z, hompressol_E_x_as_z,
    canonical_env in *.
  cbn in *.
  destruct (lookup_canonical_state labelZ zs l) as [z |] eqn:Hz;
    [| discriminate].
  destruct (lookup_canonical_state labelX xs l) as [x |] eqn:Hx;
    [| discriminate].
  destruct (lookup_canonical_state_some_in _ _ _ _ Hz)
    as [Hz_in Hz_label].
  destruct (lookup_canonical_state_some_in _ _ _ _ Hx)
    as [Hx_in Hx_label].
  apply (Hdistinct x z Hx_in Hz_in).
  rewrite <- Hx_label.
  exact Hz_label.
Qed.

Local Lemma hompressol_chosen_add_c3
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (chi : CFGKATCoalgebra X)
  (zeta : CFGKATCoalgebra Z)
  :
  hompressol_chosen_labels_disjoint xs zs labelX labelZ ->
  hompressol_chosen_no_jump_to xs zs chi labelZ ->
  forall x,
  (forall y a p y',
    In y xs ->
    chi y a = CFGKATAutomatonNext p y' ->
    In y' xs) ->
  In x xs ->
  forall l,
    label_in_dom (hompressol_E_z zs labelZ zeta) l ->
    (forall k body,
      hompressol_E_x xs labelX chi k = Some body ->
      ~ contains_goto l body) /\
    ~ contains_goto l (goto (labelX x)).
Proof.
  intros Hdistinct Hno_XZ x Hclosed Hx l [target_body Htarget].
  unfold hompressol_E_z, canonical_env in Htarget.
  cbn in Htarget.
  destruct (lookup_canonical_state labelZ zs l) as [z |] eqn:Hz;
    [| discriminate].
  destruct (lookup_canonical_state_some_in _ _ _ _ Hz)
    as [Hz_in Hz_label].
  subst l.
  split.
  - intros k body Hsource.
    unfold hompressol_E_x, canonical_env in Hsource.
    cbn in Hsource.
    destruct (lookup_canonical_state labelX xs k) as [y |] eqn:Hy;
      [| discriminate].
    injection Hsource as <-.
    destruct (lookup_canonical_state_some_in _ _ _ _ Hy)
      as [Hy_in _].
    eapply canonical_body_Y_no_contains.
    + intros a j Hjump.
      eapply Hno_XZ; eauto.
    + intros a p next Hnext Hlabel.
      eapply Hdistinct.
      * eapply Hclosed; eauto.
      * exact Hz_in.
      * exact Hlabel.
  - intro Hcontains.
    eapply Hdistinct; eauto.
Qed.

Local Lemma hompressol_chosen_drop_c3
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  :
  hompressol_chosen_labels_disjoint xs zs labelX labelZ ->
  hompressol_chosen_no_jump_to zs xs zeta labelX ->
  forall x,
  (forall y, In y xs -> In (h y) zs) ->
  (forall y a p y',
    In y zs ->
    zeta y a = CFGKATAutomatonNext p y' ->
    In y' zs) ->
  In x xs ->
  forall l,
    label_in_dom (hompressol_E_x_as_z xs labelX labelZ zeta h) l ->
    (forall k body,
      hompressol_E_z zs labelZ zeta k = Some body ->
      ~ contains_goto l body) /\
    ~ contains_goto l (goto (labelZ (h x))).
Proof.
  intros Hdistinct Hno_ZX x Himage Hclosed Hx l [source_body Hsource].
  unfold hompressol_E_x_as_z in Hsource.
  cbn in Hsource.
  destruct (lookup_canonical_state labelX xs l) as [y |] eqn:Hy;
    [| discriminate].
  destruct (lookup_canonical_state_some_in _ _ _ _ Hy)
    as [Hy_in Hy_label].
  subst l.
  split.
  - intros k body Htarget.
    unfold hompressol_E_z, canonical_env in Htarget.
    cbn in Htarget.
    destruct (lookup_canonical_state labelZ zs k) as [z |] eqn:Hz;
      [| discriminate].
    injection Htarget as <-.
    destruct (lookup_canonical_state_some_in _ _ _ _ Hz)
      as [Hz_in _].
    eapply canonical_body_Y_no_contains.
    + intros a j Hjump.
      eapply Hno_ZX; eauto.
    + intros a p next Hnext Hlabel.
      eapply Hdistinct.
      * exact Hy_in.
      * eapply Hclosed; eauto.
      * symmetry. exact Hlabel.
  - intro Hcontains.
    eapply Hdistinct.
    + exact Hy_in.
    + apply Himage. exact Hx.
    + symmetry. exact Hcontains.
Qed.

Local Lemma hompressol_chosen_guarded
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (labelX : X -> Label)
  (labelZ : Z -> Label)
  (chi : CFGKATCoalgebra X)
  (zeta : CFGKATCoalgebra Z)
  :
  hompressol_chosen_no_jump_to xs xs chi labelX ->
  hompressol_chosen_no_jump_to xs zs chi labelZ ->
  hompressol_chosen_no_jump_to zs xs zeta labelX ->
  hompressol_chosen_no_jump_to zs zs zeta labelZ ->
  C7_guarded (hompressol_E_x' xs zs labelX labelZ chi zeta).
Proof.
  intros Hno_XX Hno_XZ Hno_ZX Hno_ZZ.
  unfold C7_guarded, guarded.
  intros l l' body target Hbody Htarget a runtime_i j Hdyn.
  unfold hompressol_E_x' in Hbody, Htarget.
  cbn in Hbody, Htarget.
  destruct (lookup_canonical_state labelX xs l) as [x |] eqn:Hx.
  - injection Hbody as <-.
    destruct (lookup_canonical_state_some_in _ _ _ _ Hx)
      as [Hx_in _].
    destruct (lookup_canonical_state labelX xs l') as [x' |] eqn:Hx'.
    + destruct (lookup_canonical_state_some_in _ _ _ _ Hx')
        as [Hx'_in Hx'_label].
      subst l'.
      eapply (canonical_body_Y_no_jump_to_label
        labelX chi x (labelX x') runtime_i j a).
      * intros branch_atom j0 Hjump.
        exact (Hno_XX x x' branch_atom j0 Hx_in Hx'_in Hjump).
      * exact Hdyn.
    + destruct (lookup_canonical_state labelZ zs l') as [z' |] eqn:Hz';
        [| discriminate].
      destruct (lookup_canonical_state_some_in _ _ _ _ Hz')
        as [Hz'_in Hz'_label].
      subst l'.
      eapply (canonical_body_Y_no_jump_to_label
        labelX chi x (labelZ z') runtime_i j a).
      * intros branch_atom j0 Hjump.
        exact (Hno_XZ x z' branch_atom j0 Hx_in Hz'_in Hjump).
      * exact Hdyn.
  - destruct (lookup_canonical_state labelZ zs l) as [z |] eqn:Hz;
      [| discriminate].
    injection Hbody as <-.
    destruct (lookup_canonical_state_some_in _ _ _ _ Hz)
      as [Hz_in _].
    destruct (lookup_canonical_state labelX xs l') as [x' |] eqn:Hx'.
    + destruct (lookup_canonical_state_some_in _ _ _ _ Hx')
        as [Hx'_in Hx'_label].
      subst l'.
      eapply (canonical_body_Y_no_jump_to_label
        labelZ zeta z (labelX x') runtime_i j a).
      * intros branch_atom j0 Hjump.
        exact (Hno_ZX z x' branch_atom j0 Hz_in Hx'_in Hjump).
      * exact Hdyn.
    + destruct (lookup_canonical_state labelZ zs l') as [z' |] eqn:Hz';
        [| discriminate].
      destruct (lookup_canonical_state_some_in _ _ _ _ Hz')
        as [Hz'_in Hz'_label].
      subst l'.
      eapply (canonical_body_Y_no_jump_to_label
        labelZ zeta z (labelZ z') runtime_i j a).
      * intros branch_atom j0 Hjump.
        exact (Hno_ZZ z z' branch_atom j0 Hz_in Hz'_in Hjump).
      * exact Hdyn.
Qed.


(* The paper writes the canonical labels as indexed labels [ell_x] and
   [ell_z].  Rocq represents that literal indexed family by the functions
   [ellX] and [ellZ], where [ellX x] is the paper's [ell_x].  The paper's
   "canonical environment" construction chooses these labels fresh and closed
   for finite coalgebras.  Here those facts are explicit premises because the
   theorem is also used with labels that have already been chosen elsewhere
   in the formalization, such as the GTNF labels. *)
Theorem hompressol
  {X Z : Type}
  (xs : list X)
  (zs : list Z)
  (ellX : X -> Label)
  (ellZ : Z -> Label)
  (chi : CFGKATCoalgebra X)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  :
  CFGKATCoalgebraHomomorphism chi zeta h ->
  hompressol_label_hypotheses xs zs ellX ellZ chi zeta h ->
  forall x,
  In x xs ->
  hompressol_E_x xs ellX chi |-
    goto (ellX x) == goto (ellZ (h x)) -|
  hompressol_E_z zs ellZ zeta.
Proof.
  intros Hhom Hlabels x Hx.
  destruct Hlabels as
    [Himage HclosedX HclosedZ HinjX HinjZ
      Hlabels_disjoint Hno_XX Hno_XZ Hno_ZX Hno_ZZ].
  pose proof (hompressol_chosen_env_disjoint
    xs zs ellX ellZ chi zeta Hlabels_disjoint) as Hadd_disjoint.
  pose proof (hompressol_chosen_add_c3
    xs zs ellX ellZ chi zeta Hlabels_disjoint Hno_XZ)
    as Hadd_c3.
  pose proof (hompressol_chosen_project_disjoint
    xs zs ellX ellZ zeta h Hlabels_disjoint)
    as Hproject_disjoint.
  pose proof (hompressol_chosen_drop_c3
    xs zs ellX ellZ zeta h Hlabels_disjoint Hno_ZX)
    as Hdrop_c3.
  pose proof (hompressol_chosen_guarded
    xs zs ellX ellZ chi zeta Hno_XX Hno_XZ Hno_ZX Hno_ZZ)
    as Hguarded.
  assert (Hadd :
    hompressol_E_x xs ellX chi |-
      goto (ellX x) == goto (ellX x) -|
    hompressol_E_x' xs zs ellX ellZ chi zeta).
  {
    rewrite (hompressol_E_x_prime_eq
      xs zs ellX ellZ chi zeta Hadd_disjoint).
    apply EqSym.
    apply EqC3.
    apply Hadd_c3; assumption.
  }
  assert (Huniq :
    hompressol_E_x' xs zs ellX ellZ chi zeta |-
      goto (ellX x) == goto (ellX x) -|
    hompressol_E_z' xs zs ellX ellZ zeta h).
  {
    apply EqSym.
    apply EqC7_from_side_condition.
    split.
    - apply hompressol_E_x_prime_E_z_prime_same_domain.
    - split.
      + apply hompressol_E_x_prime_E_z_prime_solution.
        * exact Hproject_disjoint.
        * exact Hhom.
        * exact HclosedX.
        * exact Himage.
        * exact HinjX.
        * exact HinjZ.
      + exact Hguarded.
  }
  assert (Hproject :
    hompressol_E_z' xs zs ellX ellZ zeta h |-
      goto (ellX x) == goto (ellZ (h x)) -|
    hompressol_E_z' xs zs ellX ellZ zeta h).
  {
    apply hompressol_E_z_prime_project_goto.
    - exact Hproject_disjoint.
    - exact HinjX.
    - exact HinjZ.
    - exact Himage.
    - exact Hx.
  }
  assert (Hdrop :
    hompressol_E_z' xs zs ellX ellZ zeta h |-
      goto (ellZ (h x)) == goto (ellZ (h x)) -|
    hompressol_E_z zs ellZ zeta).
  {
    rewrite (hompressol_E_z_prime_eq_comm
      xs zs ellX ellZ zeta h Hproject_disjoint).
    apply EqC3.
    apply Hdrop_c3; assumption.
  }
  cfgkat_rewrite Hadd.
  cfgkat_rewrite Huniq.
  cfgkat_rewrite Hproject.
  exact Hdrop.
Qed.

Local Lemma relation_pair_left_hompressol_hypotheses
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (left_label right_label : CFGKATSyntConfiguration -> Label)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (Hagree : relation_pair_output_agreement E F R)
  (pair_label : relation_pair_state -> Label)
  :
  relation_pair_labels_fresh left right E F left_label right_label pair_label ->
  (forall source a act0 next,
    In source left ->
    resolved_transition_output E (fst source) a (snd source) =
      CFGKATAutomatonNext act0 next ->
    In next left) ->
  (forall source a act0 next,
    In source right ->
    resolved_transition_output F (fst source) a (snd source) =
      CFGKATAutomatonNext act0 next ->
    In next right) ->
  (forall u v,
    In u left ->
    In v left ->
    left_label u = left_label v ->
    u = v) ->
  (forall source_state target_state branch_atom j0,
    In source_state left ->
    In target_state left ->
    resolved_transition_output E (fst source_state) branch_atom
      (snd source_state) <>
      CFGKATAutomatonJump (left_label target_state) j0) ->
  hompressol_label_hypotheses
    (relation_pair_related_states left right R)
    left
    (relation_pair_related_label pair_label)
    left_label
    (relation_pair_step E F R Hagree)
    (gtnf_resolved_step E)
    relation_pair_left.
Proof.
  intros Hfresh Hleft_closed Hright_closed Hleft_inj Hleft_no_jump.
  refine {|
    hompressol_image_closed := _;
    hompressol_source_next_closed := _;
    hompressol_target_next_closed := _;
    hompressol_source_label_injective := _;
    hompressol_target_label_injective := _;
    hompressol_labels_disjoint := _;
    hompressol_source_no_jump_to_source_labels := _;
    hompressol_source_no_jump_to_target_labels := _;
    hompressol_target_no_jump_to_source_labels := _;
    hompressol_target_no_jump_to_target_labels := _
  |}.
  - intros y Hy.
    eapply relation_pair_states_fst_in.
    eapply relation_pair_related_states_pair_in.
    exact Hy.
  - intros y a act next Hy Hnext.
    eapply relation_pair_step_next_in_related; eauto.
  - intros y a act next Hy Hnext.
    eapply Hleft_closed.
    + exact Hy.
    + exact Hnext.
  - intros u v Hu Hv Hlabel.
    apply relation_pair_related_state_ext.
    apply (proj2 Hfresh).
    + eapply relation_pair_related_states_pair_in. exact Hu.
    + eapply relation_pair_related_states_pair_in. exact Hv.
    + unfold relation_pair_related_label in Hlabel.
      exact Hlabel.
  - exact Hleft_inj.
  - intros source target Hsource Htarget Hlabel.
    unfold relation_pair_related_label in Hlabel.
    eapply relation_pair_label_fresh_left_state.
    + exact Hfresh.
    + eapply relation_pair_related_states_pair_in. exact Hsource.
    + exact Htarget.
    + exact Hlabel.
  - intros source target a j Hsource Htarget Hjump.
    unfold relation_pair_related_label in Hjump.
    exact (relation_pair_step_no_pair_label_jump
      left right E F R Hagree left_label right_label pair_label
      source target a j Hfresh Hsource Htarget Hjump).
  - intros source target a j Hsource Htarget Hjump.
    exact (relation_pair_step_no_left_label_jump
      left right E F R Hagree left_label source target a j
      Hsource Htarget Hleft_no_jump Hjump).
  - intros source target a j Hsource Htarget Hjump.
    unfold relation_pair_related_label in Hjump.
    unfold gtnf_resolved_step in Hjump.
    eapply relation_pair_label_no_left_resolved_jump.
    + exact Hfresh.
    + eapply relation_pair_related_states_pair_in. exact Htarget.
    + exact Hsource.
    + exact Hjump.
  - intros source target a j Hsource Htarget Hjump.
    unfold gtnf_resolved_step in Hjump.
    exact (Hleft_no_jump source target a j Hsource Htarget Hjump).
Qed.

Local Lemma relation_pair_right_hompressol_hypotheses
  (left right : list CFGKATSyntConfiguration)
  (E F : label_environment CFGKATExpression)
  (left_label right_label : CFGKATSyntConfiguration -> Label)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (Hagree : relation_pair_output_agreement E F R)
  (pair_label : relation_pair_state -> Label)
  :
  relation_pair_labels_fresh left right E F left_label right_label pair_label ->
  (forall source a act0 next,
    In source left ->
    resolved_transition_output E (fst source) a (snd source) =
      CFGKATAutomatonNext act0 next ->
    In next left) ->
  (forall source a act0 next,
    In source right ->
    resolved_transition_output F (fst source) a (snd source) =
      CFGKATAutomatonNext act0 next ->
    In next right) ->
  (forall u v,
    In u right ->
    In v right ->
    right_label u = right_label v ->
    u = v) ->
  (forall source_state target_state branch_atom j0,
    In source_state right ->
    In target_state right ->
    resolved_transition_output F (fst source_state) branch_atom
      (snd source_state) <>
      CFGKATAutomatonJump (right_label target_state) j0) ->
  hompressol_label_hypotheses
    (relation_pair_related_states left right R)
    right
    (relation_pair_related_label pair_label)
    right_label
    (relation_pair_step E F R Hagree)
    (gtnf_resolved_step F)
    relation_pair_right.
Proof.
  intros Hfresh Hleft_closed Hright_closed Hright_inj Hright_no_jump.
  refine {|
    hompressol_image_closed := _;
    hompressol_source_next_closed := _;
    hompressol_target_next_closed := _;
    hompressol_source_label_injective := _;
    hompressol_target_label_injective := _;
    hompressol_labels_disjoint := _;
    hompressol_source_no_jump_to_source_labels := _;
    hompressol_source_no_jump_to_target_labels := _;
    hompressol_target_no_jump_to_source_labels := _;
    hompressol_target_no_jump_to_target_labels := _
  |}.
  - intros y Hy.
    eapply relation_pair_states_snd_in.
    eapply relation_pair_related_states_pair_in.
    exact Hy.
  - intros y a act next Hy Hnext.
    eapply relation_pair_step_next_in_related; eauto.
  - intros y a act next Hy Hnext.
    eapply Hright_closed.
    + exact Hy.
    + exact Hnext.
  - intros u v Hu Hv Hlabel.
    apply relation_pair_related_state_ext.
    apply (proj2 Hfresh).
    + eapply relation_pair_related_states_pair_in. exact Hu.
    + eapply relation_pair_related_states_pair_in. exact Hv.
    + unfold relation_pair_related_label in Hlabel.
      exact Hlabel.
  - exact Hright_inj.
  - intros source target Hsource Htarget Hlabel.
    unfold relation_pair_related_label in Hlabel.
    eapply relation_pair_label_fresh_right_state.
    + exact Hfresh.
    + eapply relation_pair_related_states_pair_in. exact Hsource.
    + exact Htarget.
    + exact Hlabel.
  - intros source target a j Hsource Htarget Hjump.
    unfold relation_pair_related_label in Hjump.
    exact (relation_pair_step_no_pair_label_jump
      left right E F R Hagree left_label right_label pair_label
      source target a j Hfresh Hsource Htarget Hjump).
  - intros source target a j Hsource Htarget Hjump.
    exact (relation_pair_step_no_right_label_jump
      left right E F R Hagree right_label source target a j
      Hsource Htarget Hright_no_jump Hjump).
  - intros source target a j Hsource Htarget Hjump.
    unfold relation_pair_related_label in Hjump.
    unfold gtnf_resolved_step in Hjump.
    eapply relation_pair_label_no_right_resolved_jump.
    + exact Hfresh.
    + eapply relation_pair_related_states_pair_in. exact Htarget.
    + exact Hsource.
    + exact Hjump.
  - intros source target a j Hsource Htarget Hjump.
    unfold gtnf_resolved_step in Hjump.
    exact (Hright_no_jump source target a j Hsource Htarget Hjump).
Qed.

Local Lemma relation_pair_projection_bridge
  (E F : label_environment CFGKATExpression)
  (e f : CFGKATExpression)
  (supplyE : gtnf_label_supply E e)
  (supplyF : gtnf_label_supply F f)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (s t : CFGKATSyntConfiguration)
  :
  relation_pair_output_agreement E F
    (supply_restricted_relation
      (gtnfthm_reachable_states supplyE)
      (gtnfthm_reachable_states supplyF)
      R) ->
  supply_restricted_relation
    (gtnfthm_reachable_states supplyE)
    (gtnfthm_reachable_states supplyF)
    R s t ->
  canonical_env_Y
    (gtnfthm_reachable_states supplyE)
    (gtnf_supply_label supplyE)
    (gtnf_resolved_step E) |-
    goto (gtnf_supply_label supplyE s) ==
    goto (gtnf_supply_label supplyF t) -|
  canonical_env_Y
    (gtnfthm_reachable_states supplyF)
    (gtnf_supply_label supplyF)
    (gtnf_resolved_step F).
Proof.
  intros Hagree Hrel.
  set (left := gtnfthm_reachable_states supplyE).
  set (right := gtnfthm_reachable_states supplyF).
  set (left_label := gtnf_supply_label supplyE).
  set (right_label := gtnf_supply_label supplyF).
  set (Rel := supply_restricted_relation left right R).
  destruct (relation_pair_labels_exist left right E F left_label right_label)
    as [pair_label Hfresh].
  destruct Hrel as [HR [Hs Ht]].
  assert (Hleft_closed : forall source a act0 next,
    In source left ->
    resolved_transition_output E (fst source) a (snd source) =
      CFGKATAutomatonNext act0 next ->
    In next left).
  {
    subst left.
    intros source a act0 next Hsource Hnext.
    destruct source as [source source_i].
    apply gtnfthm_reachable_states_contains.
    eapply gtnfthm_reachable_next.
    + eapply gtnfthm_reachable_states_in_reachable.
      exact Hsource.
    + exact Hnext.
  }
  assert (Hright_closed : forall source a act0 next,
    In source right ->
    resolved_transition_output F (fst source) a (snd source) =
      CFGKATAutomatonNext act0 next ->
    In next right).
  {
    subst right.
    intros source a act0 next Hsource Hnext.
    destruct source as [source source_i].
    apply gtnfthm_reachable_states_contains.
    eapply gtnfthm_reachable_next.
    + eapply gtnfthm_reachable_states_in_reachable.
      exact Hsource.
    + exact Hnext.
  }
  assert (Hleft_no_jump : forall source_state target_state branch_atom j0,
    In source_state left ->
    In target_state left ->
    resolved_transition_output E (fst source_state) branch_atom
      (snd source_state) <>
      CFGKATAutomatonJump (left_label target_state) j0).
  {
    subst left left_label.
    intros source_state target_state branch_atom j0 Hsource Htarget.
    destruct source_state as [source source_i].
    eapply resolved_transition_output_no_supply_state_label_jump.
    + eapply gtnfthm_reachable_states_in_supply. exact Htarget.
    + eapply gtnfthm_reachable_states_in_supply. exact Hsource.
  }
  assert (Hright_no_jump : forall source_state target_state branch_atom j0,
    In source_state right ->
    In target_state right ->
    resolved_transition_output F (fst source_state) branch_atom
      (snd source_state) <>
      CFGKATAutomatonJump (right_label target_state) j0).
  {
    subst right right_label.
    intros source_state target_state branch_atom j0 Hsource Htarget.
    destruct source_state as [source source_i].
    eapply resolved_transition_output_no_supply_state_label_jump.
    + eapply gtnfthm_reachable_states_in_supply. exact Htarget.
    + eapply gtnfthm_reachable_states_in_supply. exact Hsource.
  }
  set (pairs := relation_pair_related_states left right Rel).
  set (pair_step := relation_pair_step E F Rel Hagree).
  set (p := exist
    (fun p : relation_pair_state => Rel (fst p) (snd p))
    (s, t)
    ltac:(unfold Rel, supply_restricted_relation; repeat split; assumption)
    : relation_pair_related_state Rel).
  assert (Hp : In p pairs).
  {
    subst p pairs Rel.
    apply relation_pair_related_states_in; assumption.
  }
  assert (Hleft :
    hompressol_E_x pairs (relation_pair_related_label pair_label)
      pair_step |-
      goto (relation_pair_related_label pair_label p) ==
      goto (left_label (relation_pair_left p)) -|
    hompressol_E_z left left_label (gtnf_resolved_step E)).
  {
    eapply hompressol.
    - subst pair_step.
      intros q a.
      unfold relation_pair_step, gtnf_resolved_step.
      apply relation_pair_lifted_output_left_hom.
    - subst pair_step pairs.
      eapply relation_pair_left_hompressol_hypotheses; eauto.
      + subst left left_label.
        exact (gtnfthm_reachable_states_label_injective supplyE).
    - exact Hp.
  }
  assert (Hright :
    hompressol_E_x pairs (relation_pair_related_label pair_label)
      pair_step |-
      goto (relation_pair_related_label pair_label p) ==
      goto (right_label (relation_pair_right p)) -|
    hompressol_E_z right right_label (gtnf_resolved_step F)).
  {
    eapply hompressol.
    - subst pair_step.
      intros q a.
      unfold relation_pair_step, gtnf_resolved_step.
      apply relation_pair_lifted_output_right_hom.
    - subst pair_step pairs.
      eapply relation_pair_right_hompressol_hypotheses; eauto.
      + subst right right_label.
        exact (gtnfthm_reachable_states_label_injective supplyF).
    - exact Hp.
  }
  change
    (hompressol_E_z left left_label (gtnf_resolved_step E) |-
      goto (left_label s) == goto (right_label t) -|
    hompressol_E_z right right_label (gtnf_resolved_step F)).
  subst p.
  cbn [relation_pair_left relation_pair_right
    relation_pair_related_label relation_pair_related_state_pair] in Hleft, Hright.
  cfgkat_rewrite <- Hleft at 1.
  exact Hright.
Qed.


Theorem completeness
  (E F : label_environment CFGKATExpression)
  (e f : CFGKATExpression)
  :
  (forall i, (e, i) ~[lift E, lift F] (f, i)) ->
  E |- e == f -| F.
Proof.
  intro Hsem.
  cfgkat_rewrite (weaken_empty_to_env E e _
    (guarded_assignment_sum_all_complete_assignment e)).
  assert (Hsum :
    E |-
      guarded_assignment_sum_all (fun i => complete_assignment i ;; e) ==
      guarded_assignment_sum_all (fun i => complete_assignment i ;; f) -| F).
  {
    apply guarded_assignment_sum_all_guarded_cong_ctx.
    intros i _.
    eapply EqSeqRightCong.
    - cfgkat_rewrite (gtnfcor E e i) at 1.
      destruct (completeness_semantic_initial_outputs E F e f Hsem i)
        as [R [HR _]].
      assert (Hlabels :
        canonical_gtnfthm_env (E := E) (e := e) |-
          goto (gtnf_supply_label
            (canonical_gtnf_supply (E := E) (e := e)) (e, i)) ==
          goto (gtnf_supply_label
            (canonical_gtnf_supply (E := F) (e := f)) (f, i)) -|
          canonical_gtnfthm_env (E := F) (e := f)).
      {
        set (supplyE := canonical_gtnf_supply (E := E) (e := e)).
        set (supplyF := canonical_gtnf_supply (E := F) (e := f)).
        assert (Hcanon :
          canonical_env_Y
            (gtnfthm_reachable_states supplyE)
            (gtnf_supply_label supplyE)
            (gtnf_resolved_step E) |-
            goto (gtnf_supply_label supplyE (e, i)) ==
            goto (gtnf_supply_label supplyF (f, i)) -|
          canonical_env_Y
            (gtnfthm_reachable_states supplyF)
            (gtnf_supply_label supplyF)
            (gtnf_resolved_step F)).
        {
          eapply (relation_pair_projection_bridge
            E F e f supplyE supplyF (cfgkat_relation R) (e, i) (f, i)).
          - apply relation_pair_output_agreement_reachable_of_bisim.
          - unfold supply_restricted_relation.
            repeat split.
            + exact HR.
            + subst supplyE.
              apply gtnfthm_reachable_states_contains.
              apply gtnfthm_reachable_initial.
            + subst supplyF.
              apply gtnfthm_reachable_states_contains.
              apply gtnfthm_reachable_initial.
        }
        change (gtnfthm_env supplyE |-
          goto (gtnf_supply_label supplyE (e, i)) ==
          goto (gtnf_supply_label supplyF (f, i)) -|
          gtnfthm_env supplyF).
        subst supplyE supplyF.
        change (canonical_gtnfthm_env (E := E) (e := e) |-
          goto (gtnf_supply_label
            (canonical_gtnf_supply (E := E) (e := e)) (e, i)) ==
          goto (gtnf_supply_label
            (canonical_gtnf_supply (E := F) (e := f)) (f, i)) -|
          canonical_gtnfthm_env (E := F) (e := f)).
        rewrite <- (ebotsemenv E e).
        rewrite <- (ebotsemenv F f).
        exact Hcanon.
      }
      cfgkat_rewrite Hlabels at 1.
      cfgkat_rewrite <- (gtnfcor F f i) at 1.
      apply EqRefl.
    - apply strong_equiv_no_goto.
      intro k. simpl. tauto.
  }
  cfgkat_rewrite Hsum.
  cfgkat_rewrite <- (weaken_empty_to_env F f _
    (guarded_assignment_sum_all_complete_assignment f)).
  apply EqRefl.
Qed.
