
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Logic.ClassicalEpsilon.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.Program.Equality.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Classes.Morphisms.
From Stdlib Require Import Lists.List.
Import ListNotations.

From CFGKAT.Completeness Require Export GuardedSumContext.

Local Open Scope cfgkat_scope.
Local Open Scope cfgkat_setoid_scope.


Definition resolved_branch
  (E : label_environment CFGKATExpression)
  (source : CFGKATExpression)
  (m : At x I^Y)
  : CFGKATExpression :=
  sys
    (resolved_transition_output
      E source (AtIY_atom m) (AtIY_assignment m)).

Definition resolved_body
  (E : label_environment CFGKATExpression)
  (source : CFGKATExpression)
  : CFGKATExpression :=
  guarded_sum_all (resolved_branch E source).

Definition resolved_env
  (E : label_environment CFGKATExpression)
  : label_environment CFGKATExpression :=
  environment_map_values E (fun _ body => resolved_body E body).

Local Definition gtnflem1_statement
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  : Prop :=
  E |- e == e -| resolved_env E.

Lemma transition_zero
  (a : Atom)
  (i : IndicatorAssignment)
  :
  transition_output 0 a i = CFGKATAutomatonReject.
Proof.
  rewrite transition_assert.
  destruct (eval_test_dec 0 a i) as [Hfalse | _].
  - contradiction.
  - reflexivity.
Qed.

Ltac simplify_sysc_transition :=
  simpl;
  repeat
    (rewrite transition_sequence ||
     rewrite transition_complete_assignment ||
     rewrite transition_break ||
     rewrite transition_continue ||
     rewrite transition_return ||
     rewrite transition_goto ||
     rewrite transition_action ||
     rewrite transition_zero);
  simpl;
  repeat
    (rewrite transition_sequence ||
     rewrite transition_complete_assignment ||
     rewrite transition_break ||
     rewrite transition_continue ||
     rewrite transition_return ||
     rewrite transition_goto ||
     rewrite transition_action ||
     rewrite transition_zero);
  simpl.

Ltac simplify_sysc_transition_in H :=
  simpl in H;
  repeat
    (rewrite transition_sequence in H ||
     rewrite transition_complete_assignment in H ||
     rewrite transition_break in H ||
     rewrite transition_continue in H ||
     rewrite transition_return in H ||
     rewrite transition_goto in H ||
     rewrite transition_action in H ||
     rewrite transition_zero in H);
  simpl in H;
  repeat
    (rewrite transition_sequence in H ||
     rewrite transition_complete_assignment in H ||
     rewrite transition_break in H ||
     rewrite transition_continue in H ||
     rewrite transition_return in H ||
     rewrite transition_goto in H ||
     rewrite transition_action in H ||
     rewrite transition_zero in H);
  simpl in H.

Lemma RHS_assign_then_goto
  (target : Label)
  (i : IndicatorAssignment)
  :
  RHS target (complete_assignment i ;; goto target).
Proof.
  apply RHS_sequence.
  - unfold Expm_r.
    apply complete_assignment_no_contains_goto.
  - apply RHS_goto.
Qed.

Lemma guarded_sum_on_no_contains
  (target : Label)
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  :
  (forall m, In m ms -> ~ contains_goto target (body m)) ->
  ~ contains_goto target (guarded_sum_on ms body).
Proof.
  intros Hbody.
  induction ms as [|m ms IH]; simpl.
  - tauto.
  - intros [Hhead | Htail].
    + exact (Hbody m (or_introl eq_refl) Hhead).
    + apply IH.
      * intros n Hn. apply Hbody. right. exact Hn.
      * exact Htail.
Qed.

Lemma guarded_sum_all_no_contains
  (target : Label)
  (body : (At x I^Y) -> CFGKATExpression)
  :
  (forall m, ~ contains_goto target (body m)) ->
  ~ contains_goto target (guarded_sum_all body).
Proof.
  intro H.
  unfold guarded_sum_all.
  apply guarded_sum_on_no_contains.
  intros m _.
  apply H.
Qed.




Definition raw_label_step
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (source target : Label * IndicatorAssignment)
  : Prop :=
  exists body target_body,
    E (fst source) = Some body /\
    E (fst target) = Some target_body /\
    transition_output body a (snd source) =
      CFGKATAutomatonJump (fst target) (snd target).

Inductive raw_label_path
  (E : label_environment CFGKATExpression)
  (a : Atom)
  : Label * IndicatorAssignment ->
    list (Label * IndicatorAssignment) ->
    Label * IndicatorAssignment ->
    Prop :=
| raw_label_path_nil :
    forall source,
      raw_label_path E a source [] source
| raw_label_path_cons :
    forall source mid rest target,
      raw_label_step E a source mid ->
      raw_label_path E a mid rest target ->
      raw_label_path E a source (mid :: rest) target.

Definition path_avoids_label
  (k : Label)
  (xs : list (Label * IndicatorAssignment))
  : Prop :=
  forall s, In s xs -> fst s <> k.

Definition first_return_to_label
  (E : label_environment CFGKATExpression)
  (k : Label)
  (a : Atom)
  (pi sigma : IndicatorAssignment)
  : Prop :=
  exists prefix,
    raw_label_path E a (k, pi) (prefix ++ [(k, sigma)]) (k, sigma) /\
    path_avoids_label k prefix.

Definition label_return_domain
  (E : label_environment CFGKATExpression)
  (k : Label)
  (a : Atom)
  (pi : IndicatorAssignment)
  : Prop :=
  exists sigma, first_return_to_label E k a pi sigma.

Definition goto_return_invariant
  (E : label_environment CFGKATExpression)
  (k : Label)
  (C : CFGKATTest)
  : Prop :=
  forall a pi,
    eval_test C a pi ->
    label_return_domain E k a pi /\
    forall sigma,
      first_return_to_label E k a pi sigma ->
      eval_test C a sigma.

Definition goto_Cplus_pred
  (E : label_environment CFGKATExpression)
  (k : Label)
  (a : Atom)
  (pi : IndicatorAssignment)
  : Prop :=
  exists C,
    goto_return_invariant E k C /\
    eval_test C a pi.

Definition goto_Cplus_dec
  (E : label_environment CFGKATExpression)
  (k : Label)
  (a : Atom)
  (pi : IndicatorAssignment)
  : {goto_Cplus_pred E k a pi} + {~ goto_Cplus_pred E k a pi}.
Proof.
  destruct (excluded_middle_informative (goto_Cplus_pred E k a pi)) as [H | H].
  - left. exact H.
  - right. exact H.
Defined.

Definition goto_Cplus
  (E : label_environment CFGKATExpression)
  (k : Label)
  : CFGKATTest :=
  predicate_to_test
    (goto_Cplus_pred E k)
    (goto_Cplus_dec E k).

Notation "'C+[' E ';' k ']'" := (goto_Cplus E k)
  (at level 0, E at level 99, k at level 99) : cfgkat_scope.

Local Lemma goto_Cplus_complete
  (E : label_environment CFGKATExpression)
  (k : Label)
  (a : Atom)
  (pi : IndicatorAssignment)
  :
  goto_Cplus_pred E k a pi ->
  eval_test (C+[E; k]) a pi.
Proof.
  apply predicate_to_test_complete.
Qed.

Local Lemma goto_Cplus_sound
  (E : label_environment CFGKATExpression)
  (k : Label)
  (a : Atom)
  (pi : IndicatorAssignment)
  :
  eval_test (C+[E; k]) a pi ->
  goto_Cplus_pred E k a pi.
Proof.
  apply predicate_to_test_sound.
Qed.

Local Lemma goto_Cplus_invariant
  (E : label_environment CFGKATExpression)
  (k : Label)
  :
  goto_return_invariant E k (C+[E; k]).
Proof.
  unfold goto_return_invariant.
  intros a pi HC.
  apply goto_Cplus_sound in HC.
  destruct HC as [C [Hinv HC]].
  destruct (Hinv a pi HC) as [Hdom Hclosed].
  split.
  - exact Hdom.
  - intros sigma Hret.
    apply goto_Cplus_complete.
    exists C. split.
    + exact Hinv.
    + apply Hclosed. exact Hret.
Qed.

Definition raw_fundamental_branch
  (body : CFGKATExpression)
  (m : At x I^Y)
  : CFGKATExpression :=
  sys (transition_output body (AtIY_atom m) (AtIY_assignment m)).

Lemma raw_label_step_functional
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (source target1 target2 : Label * IndicatorAssignment)
  :
  raw_label_step E a source target1 ->
  raw_label_step E a source target2 ->
  target1 = target2.
Proof.
  intros H1 H2.
  unfold raw_label_step in H1, H2.
  destruct H1 as [body1 [target_body1 [Hsource1 [_ Hout1]]]].
  destruct H2 as [body2 [target_body2 [Hsource2 [_ Hout2]]]].
  rewrite Hsource1 in Hsource2.
  injection Hsource2 as <-.
  destruct target1 as [l1 i1].
  destruct target2 as [l2 i2].
  rewrite Hout1 in Hout2.
  injection Hout2 as -> ->.
  reflexivity.
Qed.

Local Lemma raw_label_path_cons_inv
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (source mid target : Label * IndicatorAssignment)
  (rest : list (Label * IndicatorAssignment))
  :
  raw_label_path E a source (mid :: rest) target ->
  raw_label_step E a source mid /\
  raw_label_path E a mid rest target.
Proof.
  intro Hpath.
  inversion Hpath; subst.
  split; assumption.
Qed.

Definition raw_first_hit_label
  (E : label_environment CFGKATExpression)
  (stop : Label)
  (a : Atom)
  (source : Label * IndicatorAssignment)
  (sigma : IndicatorAssignment)
  : Prop :=
  exists prefix,
    raw_label_path E a source (prefix ++ [(stop, sigma)]) (stop, sigma) /\
    path_avoids_label stop prefix.

Local Lemma raw_first_hit_label_functional_aux
  (E : label_environment CFGKATExpression)
  (stop : Label)
  (a : Atom)
  :
  forall
    (prefix1 : list (Label * IndicatorAssignment))
    (source : Label * IndicatorAssignment)
    (sigma1 : IndicatorAssignment),
    raw_label_path E a source
      (prefix1 ++ [(stop, sigma1)])
      (stop, sigma1) ->
    path_avoids_label stop prefix1 ->
    forall
      (prefix2 : list (Label * IndicatorAssignment))
      (sigma2 : IndicatorAssignment),
      raw_label_path E a source
        (prefix2 ++ [(stop, sigma2)])
        (stop, sigma2) ->
      path_avoids_label stop prefix2 ->
      sigma1 = sigma2.
Proof.
  induction prefix1 as [|h1 t1 IH];
    intros source sigma1 Hpath1 Havoid1 prefix2 sigma2 Hpath2 Havoid2.
  - simpl in Hpath1.
    destruct (raw_label_path_cons_inv E a source (stop, sigma1)
      (stop, sigma1) [] Hpath1) as [Hstep1 _].
    destruct prefix2 as [|h2 t2].
    + simpl in Hpath2.
      destruct (raw_label_path_cons_inv E a source (stop, sigma2)
        (stop, sigma2) [] Hpath2) as [Hstep2 _].
      pose proof (raw_label_step_functional E a source
        (stop, sigma1) (stop, sigma2) Hstep1 Hstep2) as Heq.
      inversion Heq.
      reflexivity.
    + simpl in Hpath2.
      destruct (raw_label_path_cons_inv E a source h2
        (stop, sigma2) (t2 ++ [(stop, sigma2)]) Hpath2)
        as [Hstep2 _].
      pose proof (raw_label_step_functional E a source
        (stop, sigma1) h2 Hstep1 Hstep2) as Heq.
      subst h2.
      specialize (Havoid2 (stop, sigma1) (or_introl eq_refl)).
      contradiction Havoid2. reflexivity.
  - simpl in Hpath1.
    destruct (raw_label_path_cons_inv E a source h1
      (stop, sigma1) (t1 ++ [(stop, sigma1)]) Hpath1)
      as [Hstep1 Htail1].
    assert (Hh1_not_stop : fst h1 <> stop).
    { apply Havoid1. left. reflexivity. }
    destruct prefix2 as [|h2 t2].
    + simpl in Hpath2.
      destruct (raw_label_path_cons_inv E a source (stop, sigma2)
        (stop, sigma2) [] Hpath2) as [Hstep2 _].
      pose proof (raw_label_step_functional E a source
        h1 (stop, sigma2) Hstep1 Hstep2) as Heq.
      subst h1.
      contradiction Hh1_not_stop. reflexivity.
    + simpl in Hpath2.
      destruct (raw_label_path_cons_inv E a source h2
        (stop, sigma2) (t2 ++ [(stop, sigma2)]) Hpath2)
        as [Hstep2 Htail2].
      pose proof (raw_label_step_functional E a source
        h1 h2 Hstep1 Hstep2) as Heq.
      subst h2.
      eapply IH.
      * exact Htail1.
      * intros s Hs. apply Havoid1. right. exact Hs.
      * exact Htail2.
      * intros s Hs. apply Havoid2. right. exact Hs.
Qed.

Local Lemma raw_first_hit_label_functional
  (E : label_environment CFGKATExpression)
  (stop : Label)
  (a : Atom)
  (source : Label * IndicatorAssignment)
  (sigma1 sigma2 : IndicatorAssignment)
  :
  raw_first_hit_label E stop a source sigma1 ->
  raw_first_hit_label E stop a source sigma2 ->
  sigma1 = sigma2.
Proof.
  intros [prefix1 [Hpath1 Havoid1]] [prefix2 [Hpath2 Havoid2]].
  eapply raw_first_hit_label_functional_aux.
  - exact Hpath1.
  - exact Havoid1.
  - exact Hpath2.
  - exact Havoid2.
Qed.

Local Lemma transition_guarded_sum_on_miss
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  (forall n,
    In n ms ->
    ~ eval_test (AtIY_test n) a i) ->
  transition_output (guarded_sum_on ms body) a i =
    CFGKATAutomatonReject.
Proof.
  induction ms as [|m ms IH]; intro Hmiss; simpl.
  - rewrite transition_assert.
    destruct (eval_test_dec 0 a i) as [Hfalse | _].
    + contradiction.
    + reflexivity.
  - rewrite transition_choice.
    destruct (eval_test_dec (AtIY_test m) a i) as [Hm | _].
    + exfalso. apply (Hmiss m); [left; reflexivity | exact Hm].
    + apply IH.
      intros n Hn.
      apply Hmiss. right. exact Hn.
Qed.

Local Lemma transition_guarded_sum_on_select
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  (m : At x I^Y)
  :
  In m ms ->
  transition_output (guarded_sum_on ms body)
    (AtIY_atom m) (AtIY_assignment m) =
  transition_output (body m)
    (AtIY_atom m) (AtIY_assignment m).
Proof.
  induction ms as [|n ms IH]; intro Hin; simpl in *.
  - contradiction.
  - rewrite transition_choice.
    destruct (eval_test_dec (AtIY_test n)
      (AtIY_atom m) (AtIY_assignment m)) as [Hn | Hn].
    + destruct n as [b j].
      destruct m as [a i].
      destruct (eval_AtIY_test_inv b a j i Hn) as [-> ->].
      reflexivity.
    + destruct Hin as [Heq | Hin_tail].
      * subst n. exfalso. apply Hn. apply eval_AtIY_test_refl.
      * apply IH. exact Hin_tail.
Qed.
Definition cycle_label_pred
  (k : Label)
  (a : Atom)
  (cycle : list (Label * IndicatorAssignment))
  (b : Atom)
  (pi : IndicatorAssignment)
  : Prop :=
  b = a /\ In (k, pi) cycle.

Definition cycle_label_dec
  (k : Label)
  (a : Atom)
  (cycle : list (Label * IndicatorAssignment))
  (b : Atom)
  (pi : IndicatorAssignment)
  :
  {cycle_label_pred k a cycle b pi} +
  {~ cycle_label_pred k a cycle b pi}.
Proof.
  destruct (excluded_middle_informative
    (cycle_label_pred k a cycle b pi)) as [H | H].
  - left. exact H.
  - right. exact H.
Defined.

Definition cycle_label_test
  (k : Label)
  (a : Atom)
  (cycle : list (Label * IndicatorAssignment))
  : CFGKATTest :=
  predicate_to_test
    (cycle_label_pred k a cycle)
    (cycle_label_dec k a cycle).

Local Lemma cycle_label_test_complete
  (k : Label)
  (a b : Atom)
  (cycle : list (Label * IndicatorAssignment))
  (pi : IndicatorAssignment)
  :
  cycle_label_pred k a cycle b pi ->
  eval_test (cycle_label_test k a cycle) b pi.
Proof.
  apply predicate_to_test_complete.
Qed.

Local Lemma cycle_label_goto_invariant
  (E : label_environment CFGKATExpression)
  (k : Label)
  (a : Atom)
  (cycle : list (Label * IndicatorAssignment))
  :
  (forall pi,
    In (k, pi) cycle ->
    exists sigma,
      first_return_to_label E k a pi sigma /\
      In (k, sigma) cycle) ->
  goto_return_invariant E k (cycle_label_test k a cycle).
Proof.
  intros Hclosed b pi Hpi.
  apply predicate_to_test_sound in Hpi.
  destruct Hpi as [-> Hin].
  destruct (Hclosed pi Hin) as [sigma [Hret Hnext]].
  split.
  - exists sigma. exact Hret.
  - intros sigma' Hret'.
    assert (Hsame : sigma' = sigma).
    { unfold first_return_to_label in Hret', Hret.
      eapply raw_first_hit_label_functional.
      - exact Hret'.
      - exact Hret. }
    subst sigma'.
    apply cycle_label_test_complete.
    split; [reflexivity | exact Hnext].
Qed.

Local Lemma cycle_label_in_goto_Cplus
  (E : label_environment CFGKATExpression)
  (k : Label)
  (a : Atom)
  (cycle : list (Label * IndicatorAssignment))
  (pi : IndicatorAssignment)
  :
  (forall pi0,
    In (k, pi0) cycle ->
    exists sigma,
      first_return_to_label E k a pi0 sigma /\
      In (k, sigma) cycle) ->
  In (k, pi) cycle ->
  eval_test (C+[E; k]) a pi.
Proof.
  intros Hclosed Hin.
  apply goto_Cplus_complete.
  exists (cycle_label_test k a cycle).
  split.
  - apply cycle_label_goto_invariant.
    exact Hclosed.
  - apply cycle_label_test_complete.
    split; [reflexivity | exact Hin].
Qed.




Definition label_set
  (E : label_environment CFGKATExpression)
  (l : Label)
  (body : CFGKATExpression)
  : label_environment CFGKATExpression.
Proof.
  refine
    (mk_environment
      (fun k =>
        match Label_eq_dec l k with
        | left _ => Some body
        | right _ => E k
        end)
      (l :: env_support E)
      _).
  intros k value Hlookup.
  destruct (Label_eq_dec l k) as [Heq | Hneq].
  - subst. left. reflexivity.
  - right. eapply env_supported. exact Hlookup.
Defined.

Definition label_remove
  (E : label_environment CFGKATExpression)
  (l : Label)
  : label_environment CFGKATExpression.
Proof.
  refine
    (mk_environment
      (fun k =>
        match Label_eq_dec l k with
        | left _ => None
        | right _ => E k
        end)
      (env_support E)
      _).
  intros k value Hlookup.
  destruct (Label_eq_dec l k) as [_ | _].
  - discriminate.
  - eapply env_supported. exact Hlookup.
Defined.

Lemma label_remove_fresh
  (E : label_environment CFGKATExpression)
  (l : Label)
  :
  label_fresh (label_remove E l) l.
Proof.
  change (label_remove E l l = None).
  unfold label_remove, mk_environment.
  simpl.
  destruct (Label_eq_dec l l) as [_ | Hneq].
  - reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.
#[global] Existing Instance label_remove_fresh.

Lemma label_set_same
  (E : label_environment CFGKATExpression)
  (l : Label)
  (body : CFGKATExpression)
  :
  label_set E l body l = Some body.
Proof.
  unfold label_set, mk_environment.
  simpl.
  destruct (Label_eq_dec l l) as [_ | Hneq].
  - reflexivity.
  - contradiction Hneq. reflexivity.
Qed.

Lemma label_set_other
  (E : label_environment CFGKATExpression)
  (l k : Label)
  (body : CFGKATExpression)
  :
  l <> k ->
  label_set E l body k = E k.
Proof.
  intro Hneq.
  unfold label_set, mk_environment.
  simpl.
  destruct (Label_eq_dec l k) as [Heq | _].
  - contradiction.
  - reflexivity.
Qed.

Lemma label_remove_set_same
  (E : label_environment CFGKATExpression)
  (l : Label)
  (body : CFGKATExpression)
  :
  E l = Some body ->
  label_set (label_remove E l) l body = E.
Proof.
  intro HE.
  apply environment_eq.
  intro k.
  unfold label_set, label_remove, mk_environment.
  simpl.
  destruct (Label_eq_dec l k) as [-> | Hneq].
  - symmetry. exact HE.
  - reflexivity.
Qed.

Lemma label_set_as_extend
  (E : label_environment CFGKATExpression)
  (l : Label)
  (body : CFGKATExpression)
  `{label_fresh E l}
  :
  label_set E l body = (E ## l # body).
Proof.
  apply environment_eq.
  intro k.
  unfold label_set, label_extend, mk_environment.
  simpl.
  destruct (Label_eq_dec l k); reflexivity.
Qed.

Lemma unfold_bound_goto
  (E : label_environment CFGKATExpression)
  (l : Label)
  (body : CFGKATExpression)
  :
  E l = Some body ->
  E |- goto l == body -| E.
Proof.
  intro HE.
	  set (Base := label_remove E l).
	  assert (Hfresh : label_fresh Base l).
	  { unfold Base. apply label_remove_fresh. }
			  assert (Hsame : E = label_set Base l body).
			  { unfold Base. symmetry. apply label_remove_set_same. exact HE. }
			  rewrite Hsame.
			  rewrite (@label_set_as_extend Base l body Hfresh).
		  apply EqSym.
	  pose proof
	    (EqC5 Base (goto l) body l (RHS_goto l))
	    as Hunfold.
  simpl in Hunfold.
  destruct (Label_eq_dec l l) as [_ | Hneq] in Hunfold.
  - exact Hunfold.
  - contradiction Hneq. reflexivity.
Qed.

Fixpoint env_on_list
  (E : label_environment CFGKATExpression)
  (ls : list Label)
  : label_environment CFGKATExpression :=
  match ls with
  | [] => empty_label_context
  | l :: ls' =>
      match E l with
      | Some body => label_set (env_on_list E ls') l body
      | None => env_on_list E ls'
      end
  end.

Local Lemma env_on_list_not_in
  (E : label_environment CFGKATExpression)
  (ls : list Label)
  (k : Label)
  :
  ~ In k ls ->
  env_on_list E ls k = None.
Proof.
  induction ls as [|l ls IH]; simpl.
  - reflexivity.
	  - intro Hnot.
	    destruct (E l) as [body |] eqn:HE.
	    + destruct (Label_eq_dec l k) as [Heq | Hneq].
	      * subst k. exfalso. apply Hnot. left. reflexivity.
	      * rewrite label_set_other by exact Hneq.
	        apply IH. intro Hin. apply Hnot. right. exact Hin.
	    + apply IH. intro Hin. apply Hnot. right. exact Hin.
Qed.

Local Lemma env_on_list_some
  (E : label_environment CFGKATExpression)
  (ls : list Label)
  (k : Label)
  (body : CFGKATExpression)
  :
  E k = Some body ->
  In k ls ->
  env_on_list E ls k = Some body.
Proof.
  induction ls as [|l ls IH]; simpl.
  - intros _ Hin. contradiction.
  - intros HE Hin.
    destruct Hin as [Hlk | Hin].
    + subst l.
      rewrite HE.
      apply label_set_same.
    + destruct (E l) as [head |] eqn:Hl.
      * destruct (Label_eq_dec l k) as [Heq | Hneq].
        -- subst l. rewrite HE in Hl. inversion Hl; subst.
           apply label_set_same.
        -- rewrite label_set_other by exact Hneq.
           apply IH; assumption.
      * apply IH; assumption.
Qed.

Local Lemma env_on_list_none
  (E : label_environment CFGKATExpression)
  (ls : list Label)
  (k : Label)
  :
  E k = None ->
  env_on_list E ls k = None.
Proof.
  induction ls as [|l ls IH]; simpl.
  - reflexivity.
  - intro HE.
    destruct (E l) as [head |] eqn:Hl.
    + destruct (Label_eq_dec l k) as [Heq | Hneq].
      * subst l. rewrite HE in Hl. discriminate.
      * rewrite label_set_other by exact Hneq.
        apply IH. exact HE.
    + apply IH. exact HE.
Qed.

Local Lemma env_on_nodup_support
  (E : label_environment CFGKATExpression)
  :
  env_on_list E (List.nodup Label_eq_dec (env_support E)) = E.
Proof.
  apply environment_eq.
  intro k.
  destruct (E k) as [body |] eqn:HE.
  - apply env_on_list_some.
    + exact HE.
    + apply List.nodup_In.
      eapply env_supported. exact HE.
  - apply env_on_list_none. exact HE.
Qed.

Local Lemma weaken_empty_to_env_on
  (ls : list Label)
  (E : label_environment CFGKATExpression)
  (e f : CFGKATExpression)
  :
  NoDup ls ->
  e == f ->
  env_on_list E ls |- e == f -| env_on_list E ls.
Proof.
  induction ls as [|l ls IH]; simpl.
  - intros _ H. exact H.
  - intros Hnodup H.
    inversion Hnodup as [|? ? Hnotin Hnodup_tail]; subst.
    destruct (E l) as [body |] eqn:HE.
    + set (Etail := env_on_list E ls).
	      assert (Hfresh : label_fresh Etail l).
		      { change (Etail l = None).
		        unfold Etail.
		        apply env_on_list_not_in.
		        exact Hnotin. }
		      change (label_set Etail l body |- e == f -| label_set Etail l body).
		      rewrite (@label_set_as_extend Etail l body Hfresh).
		      apply EqC1.
	      apply IH.
      * exact Hnodup_tail.
      * exact H.
    + apply IH; assumption.
Qed.

Lemma weaken_empty_to_env
  (E : label_environment CFGKATExpression)
  (e f : CFGKATExpression)
  :
  e == f ->
  E |- e == f -| E.
Proof.
  intro H.
  rewrite <- (env_on_nodup_support E).
  apply weaken_empty_to_env_on.
  - apply List.NoDup_nodup.
  - exact H.
Qed.

#[export] Instance label_context_pair_proper
  (E : label_environment CFGKATExpression)
  :
  Proper (cfgkat_non_ctx_equiv ==> cfgkat_equiv) (pair E).
Proof.
  intros e f H.
  apply weaken_empty_to_env.
  exact H.
Qed.

Definition fundamental_phase_env
  (E : label_environment CFGKATExpression)
  (P : list Label)
  : label_environment CFGKATExpression :=
  environment_map_values E
    (fun k body =>
      match in_dec Label_eq_dec k P with
      | left _ => fundamental_normal_form body
      | right _ => body
      end).

Definition fundamental_branch_env
  (E : label_environment CFGKATExpression)
  : label_environment CFGKATExpression :=
  environment_map_values E (fun _ body => fundamental_normal_form body).

Local Lemma fundamental_phase_env_empty
  (E : label_environment CFGKATExpression)
  :
  fundamental_phase_env E [] = E.
Proof.
  apply environment_eq.
  intro k.
  unfold fundamental_phase_env, environment_map_values, mk_environment.
  simpl.
  destruct (E k); reflexivity.
Qed.

Local Lemma fundamental_phase_env_nodup_support
  (E : label_environment CFGKATExpression)
  :
  fundamental_phase_env E (List.nodup Label_eq_dec (env_support E)) =
  fundamental_branch_env E.
Proof.
  apply environment_eq.
  intro k.
  unfold fundamental_phase_env, fundamental_branch_env,
    environment_map_values, mk_environment.
  simpl.
  destruct (E k) as [body |] eqn:HE; [| reflexivity].
  destruct (in_dec Label_eq_dec k (List.nodup Label_eq_dec (env_support E)))
    as [_ | Hnotin].
  - reflexivity.
  - exfalso. apply Hnotin. apply List.nodup_In.
    eapply env_supported. exact HE.
Qed.

Local Lemma fundamental_phase_env_step
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  (body e : CFGKATExpression)
  :
  ~ In k P ->
  E k = Some body ->
  fundamental_phase_env E P |- e == e -|
    fundamental_phase_env E (k :: P).
Proof.
  intros Hnotin HE.
	  set (Cur := fundamental_phase_env E P).
	  set (Next := fundamental_phase_env E (k :: P)).
	  assert (HCur_k : Cur k = Some body).
	  { unfold Cur, fundamental_phase_env, environment_map_values, mk_environment.
	    simpl.
	    rewrite HE.
	    destruct (in_dec Label_eq_dec k P) as [Hin | _].
	    - contradiction.
	    - reflexivity. }
	  assert (HNext_eq :
	    Next = label_set (label_remove Cur k) k (fundamental_normal_form body)).
	  {
	    apply environment_eq.
	    intro l.
	    unfold Next, Cur, fundamental_phase_env, label_set, label_remove,
	      environment_map_values, mk_environment.
	    simpl.
	    destruct (Label_eq_dec k l) as [Hkl | Hneq].
    - subst l. rewrite HE.
      destruct (in_dec Label_eq_dec k (k :: P)) as [_ | Hbad].
      + reflexivity.
      + exfalso. apply Hbad. left. reflexivity.
    - destruct (E l) as [lbody |] eqn:HEl; [| reflexivity].
      destruct (in_dec Label_eq_dec l (k :: P)) as [Hin_kP | Hnot_kP].
      + destruct Hin_kP as [Hlk | HinP].
        * exfalso. apply Hneq. exact Hlk.
        * destruct (in_dec Label_eq_dec l P) as [_ | Hbad].
          -- reflexivity.
          -- contradiction.
      + destruct (in_dec Label_eq_dec l P) as [HinP | _].
        * exfalso. apply Hnot_kP. right. exact HinP.
        * reflexivity.
	  }
	  assert (HCur_eq :
	    Cur = label_set (label_remove Cur k) k body).
  { symmetry.
    apply label_remove_set_same.
    exact HCur_k. }
	  rewrite HCur_eq.
	  rewrite HNext_eq.
	  set (Base := label_remove Cur k).
	  assert (Hfresh : label_fresh Base k).
	  { unfold Base. apply label_remove_fresh. }
		  rewrite (@label_set_as_extend Base k body Hfresh).
		  rewrite (@label_set_as_extend Base k (fundamental_normal_form body) Hfresh).
				  apply EqC2.
          apply weaken_empty_to_env.
          apply fundamental_theorem.
Qed.

Local Lemma fundamental_phase_env_chain_on
  (E : label_environment CFGKATExpression)
  (ls : list Label)
  (e : CFGKATExpression)
  :
  NoDup ls ->
  fundamental_phase_env E [] |- e == e -|
    fundamental_phase_env E ls.
Proof.
  induction ls as [|k ls IH]; intro Hnodup.
  - apply EqRefl.
  - inversion Hnodup as [|? ? Hnotin Hnodup_tail]; subst.
    cfgkat_rewrite (IH Hnodup_tail).
    destruct (E k) as [body |] eqn:HE.
    + apply fundamental_phase_env_step with (body := body); assumption.
    + assert (Hsame :
        fundamental_phase_env E (k :: ls) =
        fundamental_phase_env E ls).
	      {
	        apply environment_eq.
	        intro l.
	        unfold fundamental_phase_env, environment_map_values, mk_environment.
	        simpl.
	        destruct (E l) as [lbody |] eqn:HEl; [| reflexivity].
        destruct (Label_eq_dec k l) as [Hkl | Hkl].
        - subst l. rewrite HE in HEl. discriminate.
        - destruct (in_dec Label_eq_dec l (k :: ls)) as [Hin_kls | Hnot_kls].
          + destruct Hin_kls as [Hlk | Hinls].
            * exfalso. apply Hkl. exact Hlk.
            * destruct (in_dec Label_eq_dec l ls) as [_ | Hbad].
              -- reflexivity.
              -- contradiction.
          + destruct (in_dec Label_eq_dec l ls) as [Hinls | _].
            * exfalso. apply Hnot_kls. right. exact Hinls.
            * reflexivity.
      }
      rewrite Hsame.
      apply EqRefl.
Qed.



Definition chosen_first_return_assignment
  (E : label_environment CFGKATExpression)
  (k : Label)
  (a : Atom)
  (pi : IndicatorAssignment)
  : IndicatorAssignment :=
  functional_relation_choice
    indicator_assignment_inhabited
    (fun _ sigma => first_return_to_label E k a pi sigma)
    tt.

Local Lemma chosen_first_return_assignment_spec
  (E : label_environment CFGKATExpression)
  (k : Label)
  (a : Atom)
  (pi : IndicatorAssignment)
  :
  label_return_domain E k a pi ->
  first_return_to_label E k a pi
    (chosen_first_return_assignment E k a pi).
Proof.
  intro Hdomain.
  unfold chosen_first_return_assignment.
  unfold label_return_domain in Hdomain.
  exact (@functional_relation_choice_spec_from_exists
    unit
    IndicatorAssignment
    indicator_assignment_inhabited
    (fun _ sigma => first_return_to_label E k a pi sigma)
    tt
    Hdomain).
Qed.

Local Lemma goto_Cplus_chosen_first_return
  (E : label_environment CFGKATExpression)
  (k : Label)
  (a : Atom)
  (pi : IndicatorAssignment)
  :
  eval_test (C+[E; k]) a pi ->
  first_return_to_label E k a pi
    (chosen_first_return_assignment E k a pi).
Proof.
  intro HC.
  apply chosen_first_return_assignment_spec.
  exact (proj1 (goto_Cplus_invariant E k a pi HC)).
Qed.

Definition nonC_raw_branch_sum
  (E : label_environment CFGKATExpression)
  (k : Label)
  (body : CFGKATExpression)
  : CFGKATExpression :=
  guarded_sum_satisfying
    (not C+[E; k])
    (raw_fundamental_branch body).

Definition unproductive_cut_body
  (E : label_environment CFGKATExpression)
  (k : Label)
  (body : CFGKATExpression)
  : CFGKATExpression :=
  test (not C+[E; k]) ;; nonC_raw_branch_sum E k body.

Definition nonC_raw_env
  (E : label_environment CFGKATExpression)
  : label_environment CFGKATExpression :=
  environment_map_values E (fun k body => nonC_raw_branch_sum E k body).

Lemma resolved_transition_output_no_original_bound_jump
  (E : label_environment CFGKATExpression)
  (source target_body : CFGKATExpression)
  (a : Atom)
  (i j : IndicatorAssignment)
  (k : Label)
  :
  E k = Some target_body ->
  resolved_transition_output E source a i <>
    CFGKATAutomatonJump k j.
Proof.
  intros HE Hjump.
  pose proof (resolved_transition_output_spec E source a i) as Hres.
  rewrite Hjump in Hres.
  eapply (resolve_no_bound_jump
    CFGKATExpressionAutomaton (lift E) k j
    (CFGKATExpressionDynamics (source, i)) a).
  - rewrite lift_lookup, HE. discriminate.
  - exact Hres.
Qed.

Local Lemma transition_nonC_raw_sum_Cplus
  (E : label_environment CFGKATExpression)
  (k : Label)
  (body : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  eval_test (C+[E; k]) a i ->
  transition_output (nonC_raw_branch_sum E k body) a i =
    CFGKATAutomatonReject.
Proof.
  intro HC.
  pose proof (in_test_of_eval (C+[E; k]) (a, i) HC) as HC_bool.
  pose proof (in_test_not_true (C+[E; k]) (a, i) HC_bool)
    as HnotC_bool.
  unfold nonC_raw_branch_sum.
  change
    (transition_output
      (guarded_sum_satisfying (not C+[E; k])
        (raw_fundamental_branch body))
      (AtIY_atom (a, i)) (AtIY_assignment (a, i)) =
     CFGKATAutomatonReject).
  unfold guarded_sum_satisfying.
  apply transition_guarded_sum_on_miss.
  intros n Hn Htest.
  apply filter_In in Hn.
  destruct Hn as [_ Hn_sat].
  destruct n as [b_atom j].
  destruct (eval_AtIY_test_inv b_atom a j i Htest) as [-> ->].
  rewrite HnotC_bool in Hn_sat.
  discriminate.
Qed.

Local Lemma original_goto_resolved_transition
  (E : label_environment CFGKATExpression)
  (k : Label)
  (source : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  E k = Some source ->
  cfgkat_transitions
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
    (goto k, i)
    a
    (resolved_transition_output E source a i).
Proof.
  intro HE.
  eapply ResolveCFGKATAutomatonDynamicsBoundJump.
  - apply CFGKATExpressionDynamicsGoto.
  - apply lift_label_some. exact HE.
  - apply resolved_transition_output_spec.
  - apply cfgkat_dynamics_functional.
Qed.

Local Lemma nonC_raw_goto_Cplus_reject
  (E : label_environment CFGKATExpression)
  (k : Label)
  (source : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  E k = Some source ->
  eval_test (C+[E; k]) a i ->
  cfgkat_transitions
    (resolve_cfgkat_automaton
      CFGKATExpressionAutomaton (lift (nonC_raw_env E)))
    (goto k, i)
    a
    CFGKATAutomatonReject.
Proof.
  intros HE HC.
  simpl.
  eapply ResolveCFGKATAutomatonDynamicsBoundJump.
  - apply CFGKATExpressionDynamicsGoto.
  - rewrite lift_lookup.
    unfold nonC_raw_env, environment_map_values, mk_environment.
    simpl.
    rewrite HE.
    reflexivity.
  - apply ResolveCFGKATAutomatonDynamicsReject.
    apply (proj2
      (transition_output_exact
        (nonC_raw_branch_sum E k source) a i
        CFGKATAutomatonReject)).
    apply transition_nonC_raw_sum_Cplus.
    exact HC.
  - apply cfgkat_dynamics_functional.
Qed.


Local Lemma AtIY_assignment_then_not_test_annihilate
  (b : CFGKATTest)
  (a : Atom)
  (i j : IndicatorAssignment)
  :
  eval_test b a j ->
  test (AtIY_test (a, i)) ;;
      (complete_assignment j ;; test (not b)) == 0.
Proof.
  intro Hbj.
  cfgkat_rewrite <- (test_abort (AtIY_test (a, i))).
  apply AtIY_complete_assignment_branch_expr.
  - assert (Hfalse :
      TAnd (AtIY_test (a, j)) (not b) =BA (0 : CFGKATTest)).
    {
      apply minterm_test_false_right.
      apply in_test_not_true.
      apply in_test_of_eval.
      exact Hbj.
    }
    cfgkat_rewrite (test_seq_ba
      (AtIY_test (a, j)) (not b) 0 Hfalse).
    apply EqSym. apply test_abort.
  - apply complete_assignment_abort.
Qed.

Local Lemma guarded_sum_on_prefixed_dead
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  (m : At x I^Y)
  :
  (forall n,
    In n ms ->
    test (AtIY_test n) ;; body n == 0) ->
  test (AtIY_test m) ;; guarded_sum_on ms body == 0.
Proof.
  induction ms as [|n ms IH]; intro Hdead; simpl.
  - apply test_abort.
  - destruct (classic (n = m)) as [Hnm | Hnm].
    + subst n.
      cfgkat_rewrite branchsel.
      apply Hdead. left. reflexivity.
    + cfgkat_rewrite (branchskip_disjoint
        (AtIY_test m) (AtIY_test n) (body n)
        (guarded_sum_on ms body)
        ltac:(apply minterms_disagree;
          intro Hmn; apply Hnm; symmetry; exact Hmn)).
      apply IH.
      intros p Hp.
      apply Hdead. right. exact Hp.
Qed.

Local Lemma guarded_sum_on_minterm_not_in_annihilate
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  (m : At x I^Y)
  :
  ~ In m ms ->
  test (AtIY_test m) ;; guarded_sum_on ms body == 0.
Proof.
  induction ms as [|n ms IH]; intro Hnotin; simpl.
  - apply test_abort.
  - destruct (classic (n = m)) as [Hnm | Hnm].
    + subst n. exfalso. apply Hnotin. left. reflexivity.
    + cfgkat_rewrite (branchskip_disjoint
        (AtIY_test m) (AtIY_test n) (body n)
        (guarded_sum_on ms body)
        ltac:(apply minterms_disagree;
          intro Hmn; apply Hnm; symmetry; exact Hmn)).
      apply IH.
      intro Hin. apply Hnotin. right. exact Hin.
Qed.

Local Lemma nonC_raw_branch_sum_Cplus_zero
  (E : label_environment CFGKATExpression)
  (k : Label)
  (body : CFGKATExpression)
  (m : At x I^Y)
  :
  eval_test (C+[E; k]) (AtIY_atom m) (AtIY_assignment m) ->
  test (AtIY_test m) ;; nonC_raw_branch_sum E k body == 0.
Proof.
  intro HC.
  pose proof (in_test_of_eval (C+[E; k]) m HC) as HC_bool.
  pose proof (in_test_not_true (C+[E; k]) m HC_bool)
    as HnotC_bool.
  unfold nonC_raw_branch_sum, guarded_sum_satisfying.
  apply guarded_sum_on_minterm_not_in_annihilate.
  intro Hin.
  apply filter_In in Hin.
  rewrite HnotC_bool in Hin.
  discriminate (proj2 Hin).
Qed.

Local Lemma guarded_sum_on_dead_by_guards_early
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  :
  (forall m,
    In m ms ->
    test (AtIY_test m) ;; body m == 0) ->
  guarded_sum_on ms body == 0.
Proof.
  induction ms as [|m ms IH]; intro Hdead; simpl.
  - apply EqRefl.
  - assert (Hhead :
      test (AtIY_test m) ;; body m ==
        test (AtIY_test m) ;; 0).
    {
      cfgkat_rewrite (Hdead m (or_introl eq_refl)).
      apply EqSym. apply test_abort.
    }
    cfgkat_rewrite (choice_then_guarded_cong
      (AtIY_test m) (body m) 0 (guarded_sum_on ms body) Hhead).
    assert (Htail :
      test (AtIY_test m) ;; guarded_sum_on ms body == 0).
    {
      apply guarded_sum_on_prefixed_dead.
      intros n Hn.
      apply Hdead. right. exact Hn.
    }
    cfgkat_rewrite (choice_dead_branch
      (AtIY_test m) (guarded_sum_on ms body) Htail).
    apply IH.
    intros n Hn.
    apply Hdead. right. exact Hn.
Qed.

Definition processed_hit_pred
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  (a : Atom)
  (pi : IndicatorAssignment)
  : Prop :=
  exists hit prefix,
    In (fst hit) P /\
    eval_test (C+[E; fst hit]) a (snd hit) /\
    raw_label_path E a (k, pi) (prefix ++ [hit]) hit /\
    path_avoids_label k (prefix ++ [hit]).

Definition processed_hit_from
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (stop source : Label)
  (a : Atom)
  (pi : IndicatorAssignment)
  : Prop :=
  exists hit prefix,
    In (fst hit) P /\
    eval_test (C+[E; fst hit]) a (snd hit) /\
    raw_label_path E a (source, pi) (prefix ++ [hit]) hit /\
    path_avoids_label stop (prefix ++ [hit]).

Local Lemma processed_hit_from_cons
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (stop source mid_label : Label)
  (a : Atom)
  (pi mid_i : IndicatorAssignment)
  :
  mid_label <> stop ->
  raw_label_step E a (source, pi) (mid_label, mid_i) ->
  processed_hit_from E P stop mid_label a mid_i ->
  processed_hit_from E P stop source a pi.
Proof.
  intros Hmid_not_stop Hstep Hhit.
  destruct Hhit as [hit [prefix [Hin [HC [Hpath Havoid]]]]].
  exists hit, ((mid_label, mid_i) :: prefix).
  repeat split.
  - exact Hin.
  - exact HC.
  - simpl. apply raw_label_path_cons.
    + exact Hstep.
    + exact Hpath.
  - unfold path_avoids_label in *.
    intros s Hs.
    destruct Hs as [Hs | Hs].
    + subst s. simpl. exact Hmid_not_stop.
    + apply Havoid. exact Hs.
Qed.

Local Lemma no_processed_hit_tail
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (stop source mid_label : Label)
  (a : Atom)
  (pi mid_i : IndicatorAssignment)
  :
  ~ processed_hit_from E P stop source a pi ->
  mid_label <> stop ->
  raw_label_step E a (source, pi) (mid_label, mid_i) ->
  ~ processed_hit_from E P stop mid_label a mid_i.
Proof.
  intros Hno Hmid_not_stop Hstep Htail.
  apply Hno.
  eapply processed_hit_from_cons; eauto.
Qed.

Local Lemma no_processed_hit_step_not_Cplus_from
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (stop source target : Label)
  (a : Atom)
  (pi sigma : IndicatorAssignment)
  :
  ~ processed_hit_from E P stop source a pi ->
  target <> stop ->
  raw_label_step E a (source, pi) (target, sigma) ->
  In target P ->
  ~ eval_test (C+[E; target]) a sigma.
Proof.
  intros Hno Htarget_not_stop Hstep HinP HC.
  apply Hno.
  exists (target, sigma), [].
  repeat split.
  - exact HinP.
  - exact HC.
  - simpl. apply raw_label_path_cons.
    + exact Hstep.
    + apply raw_label_path_nil.
  - unfold path_avoids_label.
    intros s Hs.
    destruct Hs as [Hs | []].
    subst s. simpl. exact Htarget_not_stop.
Qed.

Definition processed_hit_dec
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  (a : Atom)
  (pi : IndicatorAssignment)
  :
  {processed_hit_pred E P k a pi} +
  {~ processed_hit_pred E P k a pi}.
Proof.
  destruct (excluded_middle_informative
    (processed_hit_pred E P k a pi)) as [H | H].
  - left. exact H.
  - right. exact H.
Defined.

Definition processed_Cplus_update
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  (m : At x I^Y)
  : CFGKATExpression :=
  match processed_hit_dec
    E P k (AtIY_atom m) (AtIY_assignment m) with
  | left _ => 0
  | right _ =>
      complete_assignment
        (chosen_first_return_assignment E k (AtIY_atom m) (AtIY_assignment m))
  end.

Definition processed_Cplus_update_sum
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  : CFGKATExpression :=
  guarded_sum_satisfying
    (C+[E; k])
    (processed_Cplus_update E P k).

Definition processed_unproductive_old_body
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  (body : CFGKATExpression)
  : CFGKATExpression :=
  if not C+[E; k]
  then nonC_raw_branch_sum E k body
  else processed_Cplus_update_sum E P k ;; goto k.

Definition processed_phase_env
  (E : label_environment CFGKATExpression)
  (P : list Label)
  : label_environment CFGKATExpression.
Proof.
  refine
    (mk_environment
      (fun k =>
        match E k with
        | Some body =>
            match in_dec Label_eq_dec k P with
            | left _ => Some (nonC_raw_branch_sum E k body)
            | right _ => Some (fundamental_normal_form body)
            end
        | None => None
        end)
      (env_support E)
      _).
  intros k body Hlookup.
  destruct (E k) as [source |] eqn:HE; [| discriminate Hlookup].
  eapply env_supported. exact HE.
Defined.

Local Lemma processed_phase_env_empty
  (E : label_environment CFGKATExpression)
  :
  processed_phase_env E [] = fundamental_branch_env E.
Proof.
  apply environment_eq.
  intro k.
  unfold processed_phase_env, fundamental_branch_env, environment_map_values,
    mk_environment.
  destruct (E k); reflexivity.
Qed.

Local Lemma processed_phase_env_all
  (E : label_environment CFGKATExpression)
  :
  processed_phase_env E (List.nodup Label_eq_dec (env_support E)) =
    nonC_raw_env E.
Proof.
  apply environment_eq.
  intro k.
  unfold processed_phase_env, nonC_raw_env, environment_map_values,
    mk_environment.
  simpl.
  destruct (E k) as [body |] eqn:HE; [| reflexivity].
  destruct (in_dec Label_eq_dec k
    (List.nodup Label_eq_dec (env_support E))) as [_ | Hnotin].
  - reflexivity.
  - exfalso. apply Hnotin. apply List.nodup_In.
    eapply env_supported. exact HE.
Qed.

Local Lemma processed_Cplus_update_hit
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  (m : At x I^Y)
  :
  processed_hit_pred E P k (AtIY_atom m) (AtIY_assignment m) ->
  processed_Cplus_update E P k m = 0.
Proof.
  intro Hhit.
  unfold processed_Cplus_update.
  destruct (processed_hit_dec E P k
    (AtIY_atom m) (AtIY_assignment m)) as [_ | Hnot].
  - reflexivity.
  - exfalso. apply Hnot. exact Hhit.
Qed.

Local Lemma processed_Cplus_update_no_hit
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  (m : At x I^Y)
  :
  ~ processed_hit_pred E P k
      (AtIY_atom m) (AtIY_assignment m) ->
  processed_Cplus_update E P k m =
    complete_assignment
      (chosen_first_return_assignment E k
        (AtIY_atom m) (AtIY_assignment m)).
Proof.
  intro Hnot.
  unfold processed_Cplus_update.
  destruct (processed_hit_dec E P k
    (AtIY_atom m) (AtIY_assignment m)) as [Hhit | _].
  - exfalso. apply Hnot. exact Hhit.
  - reflexivity.
Qed.

Local Lemma processed_Cplus_update_exits_false
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  (m : At x I^Y)
  :
  eval_test (C+[E; k]) (AtIY_atom m) (AtIY_assignment m) ->
  test (AtIY_test m) ;;
      (processed_Cplus_update E P k m ;;
       test (not C+[E; k])) == 0.
Proof.
  intro HC.
  destruct (processed_hit_dec E P k
    (AtIY_atom m) (AtIY_assignment m)) as [Hhit | Hnot].
  - rewrite processed_Cplus_update_hit by exact Hhit.
    cfgkat_rewrite EqS2.
    apply test_abort.
  - rewrite processed_Cplus_update_no_hit by exact Hnot.
    destruct m as [a pi].
    apply AtIY_assignment_then_not_test_annihilate.
    exact (proj2 (goto_Cplus_invariant E k a pi HC)
      (chosen_first_return_assignment E k a pi)
      (goto_Cplus_chosen_first_return E k a pi HC)).
Qed.

Local Lemma processed_Cplus_update_sum_exit_false_empty
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  :
  processed_Cplus_update_sum E P k ;;
      test (not C+[E; k]) == 0.
Proof.
  unfold processed_Cplus_update_sum, guarded_sum_satisfying.
  cfgkat_rewrite guarded_sum_on_seq_right.
  apply guarded_sum_on_dead_by_guards_early.
  intros m Hm.
  apply filter_In in Hm.
  destruct Hm as [_ Hsat].
  apply processed_Cplus_update_exits_false.
  pose proof (in_test_true (C+[E; k]) m Hsat) as HC.
  exact HC.
Qed.

Local Lemma processed_phase_env_step_given_body
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  (body e : CFGKATExpression)
  :
  ~ In k P ->
  E k = Some body ->
  label_remove (processed_phase_env E P) k |-
    fundamental_normal_form body ==
    processed_unproductive_old_body E P k body -|
    label_remove (processed_phase_env E P) k ->
  processed_phase_env E P |- e == e -|
    processed_phase_env E (k :: P).
Proof.
  intros Hnotin HE Hbody.
  set (Cur := processed_phase_env E P).
  set (Next := processed_phase_env E (k :: P)).
  set (old_body := fundamental_normal_form body).
  set (mid_body := processed_unproductive_old_body E P k body).
  set (cut_body := unproductive_cut_body E k body).
  set (new_body := nonC_raw_branch_sum E k body).
  assert (HCur_k : Cur k = Some old_body).
  { unfold Cur, old_body, processed_phase_env, mk_environment.
    simpl.
    rewrite HE.
    destruct (in_dec Label_eq_dec k P) as [Hin | _].
    - contradiction.
    - reflexivity. }
  assert (HCur_eq : Cur = label_set (label_remove Cur k) k old_body).
  { symmetry. apply label_remove_set_same. exact HCur_k. }
  assert (HNext_eq : Next = label_set (label_remove Cur k) k new_body).
  {
    apply environment_eq.
    intro l.
    unfold Next, Cur, old_body, mid_body, cut_body, new_body,
      processed_phase_env, label_set, label_remove, mk_environment.
    simpl.
    destruct (Label_eq_dec k l) as [Hkl | Hneq].
    - subst l.
      rewrite HE.
      destruct (in_dec Label_eq_dec k (k :: P)) as [_ | Hbad].
      + reflexivity.
      + exfalso. apply Hbad. left. reflexivity.
    - destruct (E l) as [lbody |] eqn:HEl; [| reflexivity].
      destruct (in_dec Label_eq_dec l (k :: P)) as [Hin_kP | Hnot_kP].
      + destruct Hin_kP as [Hlk | HinP].
        * exfalso. apply Hneq. exact Hlk.
        * destruct (in_dec Label_eq_dec l P) as [_ | Hbad].
          -- reflexivity.
          -- contradiction.
      + destruct (in_dec Label_eq_dec l P) as [HinP | _].
        * exfalso. apply Hnot_kP. right. exact HinP.
        * reflexivity.
  }
  rewrite HCur_eq.
  rewrite HNext_eq.
  set (Base := label_remove Cur k).
  assert (Hfresh : label_fresh Base k).
  { unfold Base. apply label_remove_fresh. }
  rewrite (@label_set_as_extend Base k old_body Hfresh).
  rewrite (@label_set_as_extend Base k new_body Hfresh).
  cfgkat_rewrite (@EqC2 Base e old_body mid_body k Hfresh
    ltac:(unfold old_body, mid_body;
      unfold Base, Cur;
      exact Hbody)).
  unfold mid_body, cut_body, processed_unproductive_old_body,
    unproductive_cut_body.
  cfgkat_rewrite (@EqC6 Base k (not C+[E; k])
    (processed_Cplus_update_sum E P k)
    (nonC_raw_branch_sum E k body) e Hfresh
    ltac:(apply weaken_empty_to_env;
      cfgkat_rewrite processed_Cplus_update_sum_exit_false_empty;
      apply test_abort)).
  unfold new_body.
  apply EqC2.
  apply weaken_empty_to_env.
  unfold unproductive_cut_body, nonC_raw_branch_sum.
  unfold guarded_sum_satisfying.
  cfgkat_rewrite biplusboollem_on.
  rewrite filter_all_true.
  - apply EqRefl.
  - intros m Hm.
    apply filter_In in Hm.
    exact (proj2 Hm).
Qed.

Local Lemma substitute_bound_jump_body
  (base : label_environment CFGKATExpression)
  (l : Label)
  (replacement : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  base l = Some replacement ->
  base |-
    complete_assignment i ;; goto l ==
    complete_assignment i ;; replacement -| base.
Proof.
  intro Hbase.
  assert (Hbase_eq : base = label_set (label_remove base l) l replacement).
  { symmetry. apply label_remove_set_same. exact Hbase. }
  rewrite Hbase_eq.
  set (Base := label_remove base l).
  assert (Hfresh : label_fresh Base l).
  { unfold Base. apply label_remove_fresh. }
  rewrite (@label_set_as_extend Base l replacement Hfresh).
  replace (complete_assignment i ;; replacement)
    with (subst_goto l replacement (complete_assignment i ;; goto l)).
  2:{
    simpl.
    rewrite subst_goto_no_goto.
    - destruct (Label_eq_dec l l) as [_ | Hbad].
      + reflexivity.
      + exfalso. apply Hbad. reflexivity.
    - apply complete_assignment_no_contains_goto.
  }
  apply EqSym.
  apply EqC5.
  apply RHS_assign_then_goto.
Qed.

Local Lemma processed_phase_removed_lookup_unprocessed
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (stop l : Label)
  (body : CFGKATExpression)
  :
  l <> stop ->
  ~ In l P ->
  E l = Some body ->
  label_remove (processed_phase_env E P) stop l =
  Some (fundamental_normal_form body).
Proof.
  intros Hneq Hnotin HE.
  unfold label_remove, processed_phase_env, mk_environment.
  simpl.
  destruct (Label_eq_dec stop l) as [Hsl | _].
  - exfalso. apply Hneq. symmetry. exact Hsl.
  - rewrite HE.
    destruct (in_dec Label_eq_dec l P) as [Hin | _].
    + contradiction.
    + reflexivity.
Qed.

Local Lemma processed_phase_removed_lookup_processed
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (stop l : Label)
  (body : CFGKATExpression)
  :
  l <> stop ->
  In l P ->
  E l = Some body ->
  label_remove (processed_phase_env E P) stop l =
  Some (nonC_raw_branch_sum E l body).
Proof.
  intros Hneq Hin HE.
  unfold label_remove, processed_phase_env, mk_environment.
  simpl.
  destruct (Label_eq_dec stop l) as [Hsl | _].
  - exfalso. apply Hneq. symmetry. exact Hsl.
  - rewrite HE.
    destruct (in_dec Label_eq_dec l P) as [_ | Hnot].
    + reflexivity.
    + contradiction.
Qed.

Local Lemma guarded_sum_satisfying_select
  (b : CFGKATTest)
  (body : (At x I^Y) -> CFGKATExpression)
  (m : At x I^Y)
  :
  (m \in b) = true ->
  test (AtIY_test m) ;; guarded_sum_satisfying b body == test (AtIY_test m) ;; body m.
Proof.
  intro Hsat.
  unfold guarded_sum_satisfying.
  apply branchsel_plus_on.
  apply filter_In.
  split; [| exact Hsat].
  destruct m as [a i].
  apply AtIY_in_all.
Qed.

Lemma AtIY_prefix_complete_assignment_strong_refl
  (E F : label_environment CFGKATExpression)
  (a : Atom)
  (i j : IndicatorAssignment)
  :
  E |- test (AtIY_test (a, i)) ;; complete_assignment j ==
    test (AtIY_test (a, i)) ;; complete_assignment j -| F.
Proof.
  apply strong_equiv_no_goto.
  intro target.
  intros [Hbad | Hgoto].
  - contradiction.
  - apply complete_assignment_no_contains_goto with (l := target) in Hgoto.
    exact Hgoto.
Qed.

Lemma AtIY_complete_assignment_branch_expr_ctx
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (i j : IndicatorAssignment)
  (f g : CFGKATExpression)
  :
  E |- test (AtIY_test (a, j)) ;; f ==
    test (AtIY_test (a, j)) ;; g -| E ->
  E |- complete_assignment j ;; g == g -| E ->
  E |- test (AtIY_test (a, i)) ;;
    (complete_assignment j ;; f) ==
    test (AtIY_test (a, i)) ;; g -| E.
Proof.
  intros Hbranch Hannih.
  set (P := test (AtIY_test (a, i)) ;; complete_assignment j).
  cfgkat_rewrite (weaken_empty_to_env E
    (test (AtIY_test (a, i)) ;; (complete_assignment j ;; f))
    (P ;; f)
    ltac:(apply EqSym; apply EqS1)).
  cfgkat_rewrite (weaken_empty_to_env E
    (P ;; f)
    ((P ;; test (AtIY_test (a, j))) ;; f)
    ltac:(apply EqSeqLeftEmptyCong;
      apply AtIY_prefix_complete_assignment_insert_AtIY_test)).
  cfgkat_rewrite (weaken_empty_to_env E
    ((P ;; test (AtIY_test (a, j))) ;; f)
    (P ;; (test (AtIY_test (a, j)) ;; f))
    (EqS1 P (test (AtIY_test (a, j))) f)).
  cfgkat_rewrite (@EqSeqRightCong E E
    (test (AtIY_test (a, j)) ;; f)
    (test (AtIY_test (a, j)) ;; g)
    P Hbranch
    ltac:(subst P; apply AtIY_prefix_complete_assignment_strong_refl)).
  cfgkat_rewrite <- (weaken_empty_to_env E
    ((P ;; test (AtIY_test (a, j))) ;; g)
    (P ;; (test (AtIY_test (a, j)) ;; g))
    (EqS1 P (test (AtIY_test (a, j))) g)).
  cfgkat_rewrite (weaken_empty_to_env E
    ((P ;; test (AtIY_test (a, j))) ;; g)
    (P ;; g)
    ltac:(apply EqSeqLeftEmptyCong;
      apply EqSym;
      apply AtIY_prefix_complete_assignment_insert_AtIY_test)).
  subst P.
  cfgkat_rewrite (weaken_empty_to_env E
    ((test (AtIY_test (a, i)) ;; complete_assignment j) ;; g)
    (test (AtIY_test (a, i)) ;; (complete_assignment j ;; g))
    (EqS1 (test (AtIY_test (a, i))) (complete_assignment j) g)).
  apply EqSeqRightCong.
  - exact Hannih.
  - apply EqRefl.
Qed.

Local Lemma raw_step_branch_direct
  (base : label_environment CFGKATExpression)
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (source target : Label * IndicatorAssignment)
  (body : CFGKATExpression)
  :
  E (fst source) = Some body ->
  raw_label_step E a source target ->
  base |-
    test (AtIY_test (a, snd source)) ;;
      raw_fundamental_branch body (a, snd source) ==
    test (AtIY_test (a, snd source)) ;;
      (complete_assignment (snd target) ;; goto (fst target)) -|
    base.
Proof.
  intros HE Hstep.
  unfold raw_label_step in Hstep.
  destruct Hstep as [body' [target_body [Hsource [_ Hout]]]].
  rewrite HE in Hsource.
  injection Hsource as Hbody_eq.
  subst body'.
  unfold raw_fundamental_branch.
  simpl.
  rewrite Hout.
  apply EqRefl.
Qed.

Local Lemma processed_phase_first_return_prefix_to_goto_no_hit
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (stop source : Label)
  (a : Atom)
  (pi sigma : IndicatorAssignment)
  (prefix : list (Label * IndicatorAssignment))
  (body : CFGKATExpression)
  :
  E source = Some body ->
  raw_label_path E a (source, pi)
    (prefix ++ [(stop, sigma)]) (stop, sigma) ->
  path_avoids_label stop prefix ->
  ~ processed_hit_from E P stop source a pi ->
  label_remove (processed_phase_env E P) stop |-
    test (AtIY_test (a, pi)) ;;
      raw_fundamental_branch body (a, pi) ==
    test (AtIY_test (a, pi)) ;;
      (complete_assignment sigma ;; goto stop) -|
    label_remove (processed_phase_env E P) stop.
Proof.
  revert source pi body.
  induction prefix as [|mid prefix IH];
    intros source pi body HE Hpath Havoid Hnohit.
  - simpl in Hpath.
    destruct (raw_label_path_cons_inv E a (source, pi)
      (stop, sigma) (stop, sigma) [] Hpath) as [Hstep _].
    exact (raw_step_branch_direct
      (label_remove (processed_phase_env E P) stop)
      E a (source, pi) (stop, sigma) body HE Hstep).
  - simpl in Hpath.
    destruct mid as [mid_label mid_i].
    destruct (raw_label_path_cons_inv E a (source, pi)
      (mid_label, mid_i) (stop, sigma)
      (prefix ++ [(stop, sigma)]) Hpath) as [Hstep Htail].
    unfold raw_label_step in Hstep.
    destruct Hstep as
      [source_body [mid_body [Hsource [Hmid Hout]]]].
    simpl in Hsource, Hmid, Hout.
    rewrite HE in Hsource.
    injection Hsource as Hsource_eq.
    subst source_body.
    assert (Hmid_not_stop : mid_label <> stop).
    { unfold path_avoids_label in Havoid.
      specialize (Havoid (mid_label, mid_i) (or_introl eq_refl)).
      simpl in Havoid. exact Havoid. }
    assert (Hstep_rebuilt :
      raw_label_step E a (source, pi) (mid_label, mid_i)).
    { unfold raw_label_step.
      exists body, mid_body.
      repeat split; assumption. }
    cfgkat_rewrite (raw_step_branch_direct
      (label_remove (processed_phase_env E P) stop)
      E a (source, pi) (mid_label, mid_i) body HE Hstep_rebuilt).
    destruct (in_dec Label_eq_dec mid_label P) as [HinP | HnotinP].
    + cfgkat_rewrite (@EqSeqRightCong
        (label_remove (processed_phase_env E P) stop)
        (label_remove (processed_phase_env E P) stop)
        (complete_assignment mid_i ;; goto mid_label)
        (complete_assignment mid_i ;;
          nonC_raw_branch_sum E mid_label mid_body)
        (test (AtIY_test (a, pi)))
        ltac:(apply substitute_bound_jump_body;
          exact (processed_phase_removed_lookup_processed
            E P stop mid_label mid_body Hmid_not_stop HinP Hmid))
          ltac:(apply EqRefl)).
      apply AtIY_complete_assignment_branch_expr_ctx.
      * cfgkat_rewrite (weaken_empty_to_env
          (label_remove (processed_phase_env E P) stop)
          (test (AtIY_test (a, mid_i)) ;;
            nonC_raw_branch_sum E mid_label mid_body)
          (test (AtIY_test (a, mid_i)) ;;
            raw_fundamental_branch mid_body (a, mid_i))
          ltac:(unfold nonC_raw_branch_sum;
            apply guarded_sum_satisfying_select;
            apply in_test_not_false;
            apply (in_test_false_of_not_eval'
              (C+[E; mid_label]) (a, mid_i));
            eapply no_processed_hit_step_not_Cplus_from;
            [exact Hnohit
            |exact Hmid_not_stop
            |exact Hstep_rebuilt
            |exact HinP])).
        apply (IH mid_label mid_i mid_body);
          [exact Hmid
          |exact Htail
          |intros s Hs; apply Havoid; right; exact Hs
          |eapply no_processed_hit_tail; eauto].
      * apply weaken_empty_to_env.
        apply indannih_plus_prefix.
    +
      cfgkat_rewrite (@EqSeqRightCong
        (label_remove (processed_phase_env E P) stop)
        (label_remove (processed_phase_env E P) stop)
        (complete_assignment mid_i ;; goto mid_label)
        (complete_assignment mid_i ;; fundamental_normal_form mid_body)
        (test (AtIY_test (a, pi)))
        ltac:(apply substitute_bound_jump_body;
          exact (processed_phase_removed_lookup_unprocessed
            E P stop mid_label mid_body Hmid_not_stop HnotinP Hmid))
          ltac:(apply EqRefl)).
      apply AtIY_complete_assignment_branch_expr_ctx.
      * cfgkat_rewrite (weaken_empty_to_env
          (label_remove (processed_phase_env E P) stop)
          (test (AtIY_test (a, mid_i)) ;;
            fundamental_normal_form mid_body)
          (test (AtIY_test (a, mid_i)) ;;
            raw_fundamental_branch mid_body (a, mid_i))
          ltac:(unfold fundamental_normal_form, fundamental_branch,
            raw_fundamental_branch;
            apply branchsel_plus)).
        apply (IH mid_label mid_i mid_body);
          [exact Hmid
          |exact Htail
          |intros s Hs; apply Havoid; right; exact Hs
          |eapply no_processed_hit_tail; eauto].
      * apply weaken_empty_to_env.
        apply indannih_plus_prefix.
Qed.

Local Lemma processed_phase_bound_jump_to_processed_Cplus_zero
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (stop l : Label)
  (body : CFGKATExpression)
  (a : Atom)
  (pi sigma : IndicatorAssignment)
  :
  l <> stop ->
  In l P ->
  E l = Some body ->
  eval_test (C+[E; l]) a sigma ->
  label_remove (processed_phase_env E P) stop |-
    test (AtIY_test (a, pi)) ;;
      (complete_assignment sigma ;; goto l) ==
    0 -|
    label_remove (processed_phase_env E P) stop.
Proof.
  intros Hneq HinP HE HC.
  cfgkat_rewrite (@EqSeqRightCong
    (label_remove (processed_phase_env E P) stop)
    (label_remove (processed_phase_env E P) stop)
    (complete_assignment sigma ;; goto l)
    (complete_assignment sigma ;; nonC_raw_branch_sum E l body)
    (test (AtIY_test (a, pi)))
    ltac:(apply substitute_bound_jump_body;
      exact (processed_phase_removed_lookup_processed
        E P stop l body Hneq HinP HE))
    ltac:(apply EqRefl)).
  cfgkat_rewrite (AtIY_complete_assignment_branch_expr_ctx
    (label_remove (processed_phase_env E P) stop)
    a pi sigma (nonC_raw_branch_sum E l body) 0
    ltac:(apply weaken_empty_to_env;
      cfgkat_rewrite (nonC_raw_branch_sum_Cplus_zero
        E l body (a, sigma) HC);
      apply EqSym; apply test_abort)
    ltac:(apply weaken_empty_to_env;
      apply complete_assignment_abort)).
  apply weaken_empty_to_env.
  apply test_abort.
Qed.

Local Lemma processed_phase_path_to_processed_hit_zero
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (stop source : Label)
  (a : Atom)
  (pi : IndicatorAssignment)
  (hit : Label * IndicatorAssignment)
  (prefix : list (Label * IndicatorAssignment))
  (body : CFGKATExpression)
  :
  E source = Some body ->
  In (fst hit) P ->
  eval_test (C+[E; fst hit]) a (snd hit) ->
  raw_label_path E a (source, pi) (prefix ++ [hit]) hit ->
  path_avoids_label stop (prefix ++ [hit]) ->
  label_remove (processed_phase_env E P) stop |-
    test (AtIY_test (a, pi)) ;;
      raw_fundamental_branch body (a, pi) ==
    0 -|
    label_remove (processed_phase_env E P) stop.
Proof.
  revert source pi body.
  induction prefix as [|mid prefix IH];
    intros source pi body HE HinHit HCHit Hpath Havoid.
  - simpl in Hpath.
    destruct hit as [hit_label hit_i].
    destruct (raw_label_path_cons_inv E a (source, pi)
      (hit_label, hit_i) (hit_label, hit_i) [] Hpath)
      as [Hstep _].
    unfold raw_label_step in Hstep.
    destruct Hstep as
      [source_body [hit_body [Hsource [Hhit_body Hout]]]].
    simpl in Hsource, Hhit_body, Hout.
    rewrite HE in Hsource.
    injection Hsource as Hsource_eq.
    subst source_body.
    assert (Hhit_not_stop : hit_label <> stop).
    { unfold path_avoids_label in Havoid.
      specialize (Havoid (hit_label, hit_i) (or_introl eq_refl)).
      simpl in Havoid. exact Havoid. }
    assert (Hstep_rebuilt :
      raw_label_step E a (source, pi) (hit_label, hit_i)).
    { unfold raw_label_step.
      exists body, hit_body.
      repeat split; assumption. }
    cfgkat_rewrite (raw_step_branch_direct
      (label_remove (processed_phase_env E P) stop)
      E a (source, pi) (hit_label, hit_i) body HE Hstep_rebuilt).
    apply processed_phase_bound_jump_to_processed_Cplus_zero with
        (body := hit_body).
    + exact Hhit_not_stop.
    + exact HinHit.
    + exact Hhit_body.
    + exact HCHit.
  - simpl in Hpath.
    destruct mid as [mid_label mid_i].
    destruct (raw_label_path_cons_inv E a (source, pi)
      (mid_label, mid_i) hit
      (prefix ++ [hit]) Hpath) as [Hstep Htail].
    unfold raw_label_step in Hstep.
    destruct Hstep as
      [source_body [mid_body [Hsource [Hmid Hout]]]].
    simpl in Hsource, Hmid, Hout.
    rewrite HE in Hsource.
    injection Hsource as Hsource_eq.
    subst source_body.
    assert (Hmid_not_stop : mid_label <> stop).
    { unfold path_avoids_label in Havoid.
      specialize (Havoid (mid_label, mid_i) (or_introl eq_refl)).
      simpl in Havoid. exact Havoid. }
    assert (Hstep_rebuilt :
      raw_label_step E a (source, pi) (mid_label, mid_i)).
    { unfold raw_label_step.
      exists body, mid_body.
      repeat split; assumption. }
    assert (Htail_avoid : path_avoids_label stop (prefix ++ [hit])).
    { intros s Hs. apply Havoid. right. exact Hs. }
    cfgkat_rewrite (raw_step_branch_direct
      (label_remove (processed_phase_env E P) stop)
      E a (source, pi) (mid_label, mid_i) body HE Hstep_rebuilt).
    destruct (in_dec Label_eq_dec mid_label P) as [HinMid | HnotinMid].
    + destruct (eval_test_dec (C+[E; mid_label]) a mid_i)
        as [HCMid | HnotCMid].
      * apply processed_phase_bound_jump_to_processed_Cplus_zero with
          (body := mid_body).
        -- exact Hmid_not_stop.
        -- exact HinMid.
        -- exact Hmid.
        -- exact HCMid.
      *
        cfgkat_rewrite (@EqSeqRightCong
          (label_remove (processed_phase_env E P) stop)
          (label_remove (processed_phase_env E P) stop)
          (complete_assignment mid_i ;; goto mid_label)
          (complete_assignment mid_i ;;
            nonC_raw_branch_sum E mid_label mid_body)
          (test (AtIY_test (a, pi)))
          ltac:(apply substitute_bound_jump_body;
            exact (processed_phase_removed_lookup_processed
              E P stop mid_label mid_body Hmid_not_stop HinMid Hmid))
          ltac:(apply EqRefl)).
        cfgkat_rewrite (AtIY_complete_assignment_branch_expr_ctx
          (label_remove (processed_phase_env E P) stop)
          a pi mid_i (nonC_raw_branch_sum E mid_label mid_body) 0
          ltac:(cfgkat_rewrite (weaken_empty_to_env
              (label_remove (processed_phase_env E P) stop)
              (test (AtIY_test (a, mid_i)) ;;
                nonC_raw_branch_sum E mid_label mid_body)
              (test (AtIY_test (a, mid_i)) ;;
                raw_fundamental_branch mid_body (a, mid_i))
              ltac:(unfold nonC_raw_branch_sum;
                apply guarded_sum_satisfying_select;
                apply in_test_not_false;
                apply (in_test_false_of_not_eval'
                  (C+[E; mid_label]) (a, mid_i));
                exact HnotCMid));
            cfgkat_rewrite (IH mid_label mid_i mid_body Hmid HinHit
              HCHit Htail Htail_avoid);
            [cfgkat_rewrite <- (weaken_empty_to_env
                (label_remove (processed_phase_env E P) stop) _ _
                (test_abort (AtIY_test (a, mid_i)))) at 1;
              apply EqRefl])
          ltac:(apply weaken_empty_to_env;
            apply complete_assignment_abort)).
        apply weaken_empty_to_env.
        apply test_abort.
    +
      cfgkat_rewrite (@EqSeqRightCong
        (label_remove (processed_phase_env E P) stop)
        (label_remove (processed_phase_env E P) stop)
        (complete_assignment mid_i ;; goto mid_label)
        (complete_assignment mid_i ;; fundamental_normal_form mid_body)
        (test (AtIY_test (a, pi)))
        ltac:(apply substitute_bound_jump_body;
          exact (processed_phase_removed_lookup_unprocessed
            E P stop mid_label mid_body Hmid_not_stop HnotinMid Hmid))
        ltac:(apply EqRefl)).
      cfgkat_rewrite (AtIY_complete_assignment_branch_expr_ctx
        (label_remove (processed_phase_env E P) stop)
        a pi mid_i (fundamental_normal_form mid_body) 0
        ltac:(cfgkat_rewrite (weaken_empty_to_env
            (label_remove (processed_phase_env E P) stop)
            (test (AtIY_test (a, mid_i)) ;;
              fundamental_normal_form mid_body)
            (test (AtIY_test (a, mid_i)) ;;
              raw_fundamental_branch mid_body (a, mid_i))
            ltac:(unfold fundamental_normal_form, fundamental_branch,
              raw_fundamental_branch;
              apply branchsel_plus));
          cfgkat_rewrite (IH mid_label mid_i mid_body Hmid HinHit
            HCHit Htail Htail_avoid);
          [cfgkat_rewrite <- (weaken_empty_to_env
              (label_remove (processed_phase_env E P) stop) _ _
              (test_abort (AtIY_test (a, mid_i)))) at 1;
            apply EqRefl])
        ltac:(apply weaken_empty_to_env;
          apply complete_assignment_abort)).
      apply weaken_empty_to_env.
      apply test_abort.
Qed.

Lemma minterm_ext_ctx
  (E F : label_environment CFGKATExpression)
  (x y : CFGKATExpression)
  :
  (forall m,
    In m all_AtIY ->
    E |- test (AtIY_test m) ;; x ==
      test (AtIY_test m) ;; y -| F) ->
  E |- x == y -| F.
Proof.
  intro Hbranches.
  cfgkat_rewrite (weaken_empty_to_env E x
    (guarded_sum_all (fun m => test (AtIY_test m) ;; x))
    ltac:(apply EqSym;
      cfgkat_rewrite <- (guardedness_plus (fun _ => x));
      apply idem_plus)).
  cfgkat_rewrite (guarded_sum_all_cong_ctx E F
    (fun m => test (AtIY_test m) ;; x)
    (fun m => test (AtIY_test m) ;; y)
    Hbranches).
  apply weaken_empty_to_env.
  cfgkat_rewrite <- (guardedness_plus (fun _ => y)).
  apply idem_plus.
Qed.

Local Lemma guarded_sum_satisfying_select_seq
  (b : CFGKATTest)
  (body : (At x I^Y) -> CFGKATExpression)
  (m : At x I^Y)
  (g : CFGKATExpression)
  :
  (m \in b) = true ->
  test (AtIY_test m) ;; (guarded_sum_satisfying b body ;; g) == test (AtIY_test m) ;; (body m ;; g).
Proof.
  intro Hsat.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite (guarded_sum_satisfying_select b body m Hsat).
  apply EqS1.
Qed.

Local Lemma processed_old_body_hit_zero_empty
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  (body : CFGKATExpression)
  (m : At x I^Y)
  :
  eval_test (C+[E; k]) (AtIY_atom m) (AtIY_assignment m) ->
  processed_hit_pred E P k (AtIY_atom m) (AtIY_assignment m) ->
  test (AtIY_test m) ;;
      processed_unproductive_old_body E P k body == 0.
Proof.
  intros HC Hhit.
  pose proof (in_test_of_eval (C+[E; k]) m HC) as HC_bool.
  pose proof (in_test_not_true (C+[E; k]) m HC_bool)
    as HnotC_bool.
  unfold processed_unproductive_old_body.
  cfgkat_rewrite (minterm_choice_select_false
    (not (C+[E; k])) (nonC_raw_branch_sum E k body)
    (processed_Cplus_update_sum E P k ;; goto k) m HnotC_bool).
  cfgkat_rewrite (guarded_sum_satisfying_select_seq
    (C+[E; k]) (processed_Cplus_update E P k) m (goto k) HC_bool).
  rewrite processed_Cplus_update_hit by exact Hhit.
  cfgkat_rewrite EqS2.
  apply test_abort.
Qed.

Local Lemma processed_old_body_no_hit_self_empty
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  (body : CFGKATExpression)
  (m : At x I^Y)
  :
  eval_test (C+[E; k]) (AtIY_atom m) (AtIY_assignment m) ->
  ~ processed_hit_pred E P k (AtIY_atom m) (AtIY_assignment m) ->
  test (AtIY_test m) ;;
      processed_unproductive_old_body E P k body == test (AtIY_test m) ;;
      (complete_assignment
        (chosen_first_return_assignment E k
          (AtIY_atom m) (AtIY_assignment m)) ;;
       goto k).
Proof.
  intros HC Hnohit.
  pose proof (in_test_of_eval (C+[E; k]) m HC) as HC_bool.
  pose proof (in_test_not_true (C+[E; k]) m HC_bool)
    as HnotC_bool.
  unfold processed_unproductive_old_body.
  cfgkat_rewrite (minterm_choice_select_false
    (not (C+[E; k])) (nonC_raw_branch_sum E k body)
    (processed_Cplus_update_sum E P k ;; goto k) m HnotC_bool).
  cfgkat_rewrite (guarded_sum_satisfying_select_seq
    (C+[E; k]) (processed_Cplus_update E P k) m (goto k) HC_bool).
  rewrite processed_Cplus_update_no_hit by exact Hnohit.
  apply EqRefl.
Qed.

Local Lemma processed_phase_fundamental_body_to_old_body
  (E : label_environment CFGKATExpression)
  (P : list Label)
  (k : Label)
  (body : CFGKATExpression)
  :
  E k = Some body ->
  label_remove (processed_phase_env E P) k |-
    fundamental_normal_form body ==
    processed_unproductive_old_body E P k body -|
    label_remove (processed_phase_env E P) k.
Proof.
  intro HE.
  apply minterm_ext_ctx.
  intros m Hm.
  destruct (goto_Cplus_dec E k (AtIY_atom m) (AtIY_assignment m))
    as [HCpred | HnotCpred].
  - pose proof (goto_Cplus_complete E k
      (AtIY_atom m) (AtIY_assignment m) HCpred) as HC.
    destruct m as [a pi].
    destruct (processed_hit_dec E P k
      a pi) as [Hhit | Hnohit].
    + destruct Hhit as [hit [prefix [HinHit [HCHit [Hpath Havoid]]]]].
      cfgkat_rewrite (weaken_empty_to_env
        (label_remove (processed_phase_env E P) k)
        (test (AtIY_test (a, pi)) ;; fundamental_normal_form body)
        (test (AtIY_test (a, pi)) ;;
          raw_fundamental_branch body (a, pi))
        ltac:(unfold fundamental_normal_form, fundamental_branch,
          raw_fundamental_branch;
          apply branchsel_plus)).
      cfgkat_rewrite (processed_phase_path_to_processed_hit_zero
        E P k k a pi hit prefix body
        HE HinHit HCHit Hpath Havoid).
      apply EqSym.
      apply weaken_empty_to_env.
      apply processed_old_body_hit_zero_empty.
      * exact HC.
      * exists hit, prefix.
        repeat split; assumption.
    + pose proof (goto_Cplus_chosen_first_return E k a pi HC) as Hret.
      destruct Hret as [prefix [Hpath Havoid]].
      cfgkat_rewrite (weaken_empty_to_env
        (label_remove (processed_phase_env E P) k)
        (test (AtIY_test (a, pi)) ;; fundamental_normal_form body)
        (test (AtIY_test (a, pi)) ;;
          raw_fundamental_branch body (a, pi))
        ltac:(unfold fundamental_normal_form, fundamental_branch,
          raw_fundamental_branch;
          apply branchsel_plus)).
      cfgkat_rewrite
        (processed_phase_first_return_prefix_to_goto_no_hit
          E P k k a pi
          (chosen_first_return_assignment E k a pi)
          prefix body HE Hpath Havoid
          (fun Hfrom => Hnohit Hfrom)).
      apply EqSym.
      apply weaken_empty_to_env.
      apply processed_old_body_no_hit_self_empty.
      * exact HC.
      * exact Hnohit.
  - assert (HnotC :
      ~ eval_test (C+[E; k])
          (AtIY_atom m) (AtIY_assignment m)).
    { intro HC. apply HnotCpred. apply goto_Cplus_sound. exact HC. }
    assert (HC_bool : (m \in C+[E; k]) = false).
    { unfold in_test.
      destruct (eval_test_dec (C+[E; k])
        (AtIY_atom m) (AtIY_assignment m)) as [HC | _].
      - exfalso. apply HnotC. exact HC.
      - reflexivity. }
    pose proof (in_test_not_false (C+[E; k]) m HC_bool)
      as HnotC_bool.
    cfgkat_rewrite (weaken_empty_to_env
      (label_remove (processed_phase_env E P) k)
      (test (AtIY_test m) ;; fundamental_normal_form body)
      (test (AtIY_test m) ;; raw_fundamental_branch body m)
      ltac:(unfold fundamental_normal_form, fundamental_branch,
        raw_fundamental_branch;
        apply branchsel_plus)).
    apply EqSym.
    apply weaken_empty_to_env.
    unfold processed_unproductive_old_body, nonC_raw_branch_sum.
    cfgkat_rewrite (minterm_choice_select_true
      (not (C+[E; k])) (nonC_raw_branch_sum E k body)
      (processed_Cplus_update_sum E P k ;; goto k) m HnotC_bool).
    apply guarded_sum_satisfying_select.
    exact HnotC_bool.
Qed.

Local Lemma processed_phase_env_chain_on
  (E : label_environment CFGKATExpression)
  (ls : list Label)
  (e : CFGKATExpression)
  :
  NoDup ls ->
  processed_phase_env E [] |- e == e -|
    processed_phase_env E ls.
Proof.
  induction ls as [|k ls IH]; intro Hnodup.
  - apply EqRefl.
  - inversion Hnodup as [|? ? Hnotin Hnodup_tail]; subst.
    cfgkat_rewrite (IH Hnodup_tail).
    destruct (E k) as [body |] eqn:HE.
    + eapply processed_phase_env_step_given_body.
      * exact Hnotin.
      * exact HE.
      * apply processed_phase_fundamental_body_to_old_body.
        exact HE.
    + assert (Hsame :
        processed_phase_env E (k :: ls) =
        processed_phase_env E ls).
	      {
	        apply environment_eq.
	        intro l.
	        unfold processed_phase_env, mk_environment.
	        simpl.
	        destruct (E l) as [lbody |] eqn:HEl; [| reflexivity].
        destruct (Label_eq_dec k l) as [Hkl | Hkl].
        - subst l. rewrite HE in HEl. discriminate.
        - destruct (in_dec Label_eq_dec l (k :: ls)) as [Hin_kls | Hnot_kls].
          + destruct Hin_kls as [Hlk | Hinls].
            * exfalso. apply Hkl. exact Hlk.
            * destruct (in_dec Label_eq_dec l ls) as [_ | Hbad].
              -- reflexivity.
              -- contradiction.
          + destruct (in_dec Label_eq_dec l ls) as [Hinls | _].
            * exfalso. apply Hnot_kls. right. exact Hinls.
            * reflexivity.
      }
      rewrite Hsame.
      apply EqRefl.
Qed.

Local Lemma gtnflem1_1
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  :
  E |- e == e -| nonC_raw_env E.
Proof.
  pose proof
    (fundamental_phase_env_chain_on E
      (List.nodup Label_eq_dec (env_support E)) e
      (List.NoDup_nodup Label_eq_dec (env_support E)))
    as Hfundamental.
  rewrite fundamental_phase_env_empty in Hfundamental.
  rewrite fundamental_phase_env_nodup_support in Hfundamental.
  cfgkat_rewrite Hfundamental.
  pose proof
    (processed_phase_env_chain_on
      E
      (List.nodup Label_eq_dec (env_support E)) e
      (List.NoDup_nodup Label_eq_dec (env_support E))) as Hchain.
  rewrite processed_phase_env_empty in Hchain.
  rewrite processed_phase_env_all in Hchain.
  exact Hchain.
Qed.



Local Lemma goto_Cplus_resolved_transition_reject
  (E : label_environment CFGKATExpression)
  (k : Label)
  (source : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  E k = Some source ->
  eval_test (C+[E; k]) a i ->
  resolved_transition_output E source a i = CFGKATAutomatonReject.
Proof.
  intros HE HC.
  pose proof (CFGKATEquiv_sound
    E (goto k) (goto k) (nonC_raw_env E)
    (gtnflem1_1 E (goto k)) i) as Hbisim.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar in Hbisim.
  destruct Hbisim as [R HR].
  pose proof
    (original_goto_resolved_transition E k source a i HE) as Hleft.
  pose proof
    (nonC_raw_goto_Cplus_reject E k source a i HE HC) as Hright.
  pose proof
    (cfgkat_bisimulation_step R
      (goto k, i) (goto k, i) a
      (resolved_transition_output E source a i)
      CFGKATAutomatonReject
      HR Hleft Hright) as Hlift.
  inversion Hlift; reflexivity.
Qed.

Local Lemma productive_resolution_contradicts_resolved_reject
  (E : label_environment CFGKATExpression)
  (source : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  (zeta : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  productive_resolution
    CFGKATExpressionAutomaton [lift E] a (source, i) zeta ->
  resolved_transition_output E source a i = CFGKATAutomatonReject ->
  False.
Proof.
  intros Hprod Hreject.
  pose proof
    (productive_resolution_resolves
      CFGKATExpressionAutomaton
      [lift E] a (source, i) zeta Hprod) as Hres.
  pose proof
    (resolved_transition_output_unique E source a i zeta Hres) as Hzeta.
  rewrite Hreject in Hzeta.
  eapply productive_resolution_not_reject.
  - exact Hprod.
  - exact (eq_sym Hzeta).
Qed.

Inductive resolved_reject_trace
  (E : label_environment CFGKATExpression)
  (a : Atom)
  : Label -> IndicatorAssignment -> Prop :=
| reject_trace_Cplus :
    forall k i body,
      E k = Some body ->
      eval_test (C+[E; k]) a i ->
      resolved_reject_trace E a k i
| reject_trace_raw :
    forall k i body,
      E k = Some body ->
      ~ eval_test (C+[E; k]) a i ->
      transition_output body a i = CFGKATAutomatonReject ->
      resolved_reject_trace E a k i
| reject_trace_bound :
    forall k i body j l target,
      E k = Some body ->
      ~ eval_test (C+[E; k]) a i ->
      transition_output body a i = CFGKATAutomatonJump l j ->
      E l = Some target ->
      resolved_reject_trace E a l j ->
      resolved_reject_trace E a k i.

Definition env_label_assignments
  (E : label_environment CFGKATExpression)
  : list (Label * IndicatorAssignment) :=
  flat_map
    (fun l => map (fun i => (l, i)) all_assignments)
    (env_support E).

Local Lemma env_label_assignments_complete
  (E : label_environment CFGKATExpression)
  (k : Label)
  (body : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  E k = Some body ->
  In (k, i) (env_label_assignments E).
Proof.
  intro HE.
  unfold env_label_assignments.
  apply in_flat_map.
  exists k.
  split.
  - eapply env_supported. exact HE.
  - apply in_map.
    apply all_assignments_complete.
Qed.

Local Lemma not_NoDup_duplicate_split
  {A : Type}
  (xs : list A)
  :
  ~ NoDup xs ->
  exists pre mid post s,
    xs = pre ++ s :: mid ++ s :: post.
Proof.
  induction xs as [|x xs IH]; intro Hnot.
  - exfalso. apply Hnot. constructor.
  - destruct (classic (In x xs)) as [Hin | Hnotin].
    + destruct (in_split x xs Hin) as [mid [post Hxs]].
      exists [], mid, post, x.
      simpl. rewrite Hxs. reflexivity.
    + assert (Htail : ~ NoDup xs).
      { intro Hnd. apply Hnot. constructor; assumption. }
      destruct (IH Htail) as [pre [mid [post [s Hxs]]]].
      exists (x :: pre), mid, post, s.
      simpl. rewrite Hxs. reflexivity.
Qed.

Local Lemma raw_label_path_append
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (source mid target : Label * IndicatorAssignment)
  (xs ys : list (Label * IndicatorAssignment))
  :
  raw_label_path E a source xs mid ->
  raw_label_path E a mid ys target ->
  raw_label_path E a source (xs ++ ys) target.
Proof.
  intro Hxs.
  revert ys target.
  induction Hxs; intros ys target0 Hys; simpl.
  - exact Hys.
  - apply raw_label_path_cons.
    + exact H.
    + apply IHHxs. exact Hys.
Qed.

Local Lemma raw_label_path_in_bound
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (source target s : Label * IndicatorAssignment)
  (path : list (Label * IndicatorAssignment))
  :
  raw_label_path E a source path target ->
  In s path ->
  exists body, E (fst s) = Some body.
Proof.
  intro Hpath.
  induction Hpath; simpl; intro Hin.
  - contradiction.
  - destruct Hin as [Hs | Hin].
    + subst mid.
      unfold raw_label_step in H.
      destruct H as [source_body [target_body [_ [Htarget _]]]].
      exists target_body. exact Htarget.
    + apply IHHpath. exact Hin.
Qed.

Local Lemma raw_label_path_drop_to
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (source s target : Label * IndicatorAssignment)
  (pre rest : list (Label * IndicatorAssignment))
  :
  raw_label_path E a source (pre ++ s :: rest) target ->
  raw_label_path E a s rest target.
Proof.
  revert source.
  induction pre as [|h pre IH]; intros source Hpath; simpl in Hpath.
  - destruct (raw_label_path_cons_inv E a source s target rest Hpath)
      as [_ Htail].
    exact Htail.
  - destruct (raw_label_path_cons_inv E a source h target
      (pre ++ s :: rest) Hpath) as [_ Htail].
    eapply IH. exact Htail.
Qed.

Local Lemma raw_label_path_take_to
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (source s target : Label * IndicatorAssignment)
  (pre rest : list (Label * IndicatorAssignment))
  :
  raw_label_path E a source (pre ++ s :: rest) target ->
  raw_label_path E a source (pre ++ [s]) s.
Proof.
  revert source.
  induction pre as [|h pre IH]; intros source Hpath; simpl in Hpath.
  - destruct (raw_label_path_cons_inv E a source s target rest Hpath)
      as [Hstep _].
    apply raw_label_path_cons.
    + exact Hstep.
    + apply raw_label_path_nil.
  - destruct (raw_label_path_cons_inv E a source h target
      (pre ++ s :: rest) Hpath) as [Hstep Htail].
    apply raw_label_path_cons.
    + exact Hstep.
    + eapply IH. exact Htail.
Qed.

Local Lemma raw_label_path_first_label_hit
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (source target : Label * IndicatorAssignment)
  (reached : list (Label * IndicatorAssignment))
  (stop : Label)
  :
  raw_label_path E a source reached target ->
  (exists sigma, In (stop, sigma) reached) ->
  exists sigma prefix,
    raw_label_path E a source (prefix ++ [(stop, sigma)]) (stop, sigma) /\
    path_avoids_label stop prefix /\
    In (stop, sigma) reached.
Proof.
  revert source.
  induction reached as [|h rest IH]; intros source Hpath Hhit.
  - destruct Hhit as [sigma []].
  - destruct (raw_label_path_cons_inv E a source h target rest Hpath)
      as [Hstep Htail].
    destruct h as [h_label h_i].
    destruct (Label_eq_dec h_label stop) as [-> | Hneq].
    + exists h_i, [].
      repeat split.
      * simpl. apply raw_label_path_cons.
        -- exact Hstep.
        -- apply raw_label_path_nil.
      * intros s [].
      * left. reflexivity.
    + assert (Hhit_tail : exists sigma, In (stop, sigma) rest).
      {
        destruct Hhit as [sigma [Hhead | Htail_in]].
        - inversion Hhead; subst.
          exfalso. apply Hneq. reflexivity.
        - exists sigma. exact Htail_in.
      }
      destruct (IH (h_label, h_i) Htail Hhit_tail)
        as [sigma [prefix [Hprefix [Havoid Hin]]]].
      exists sigma, ((h_label, h_i) :: prefix).
      repeat split.
      * simpl. apply raw_label_path_cons.
        -- exact Hstep.
        -- exact Hprefix.
      * intros s [Hs | Hs].
        -- subst s. simpl. exact Hneq.
        -- apply Havoid. exact Hs.
      * right. exact Hin.
Qed.

Local Lemma raw_cycle_rotation_path
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (start s : Label * IndicatorAssignment)
  (prefix : list (Label * IndicatorAssignment))
  :
  raw_label_path E a start (prefix ++ [start]) start ->
  In s (start :: prefix) ->
  exists reached,
    raw_label_path E a s reached s /\
    In s reached /\
    (forall t, In t reached -> In t (start :: prefix)).
Proof.
  intros Hcycle Hin.
  destruct Hin as [Hs | Hin_prefix].
  - subst s.
    exists (prefix ++ [start]).
    repeat split.
    + exact Hcycle.
    + apply in_or_app. right. left. reflexivity.
    + intros t Ht.
      apply in_app_or in Ht.
      destruct Ht as [Ht | [Ht | []]].
      * right. exact Ht.
      * left. exact Ht.
  - destruct (in_split s prefix Hin_prefix) as [before [after Hprefix]].
    subst prefix.
    rewrite <- app_assoc in Hcycle.
    pose proof
      (raw_label_path_drop_to E a start s start
        before (after ++ [start]) Hcycle) as Htail.
    pose proof
      (raw_label_path_take_to E a start s start
        before (after ++ [start]) Hcycle) as Hhead.
    exists ((after ++ [start]) ++ (before ++ [s])).
    repeat split.
    + eapply raw_label_path_append.
      * exact Htail.
      * exact Hhead.
    + apply in_or_app. right.
      apply in_or_app. right. left. reflexivity.
    + intros t Ht.
      apply in_app_or in Ht.
      destruct Ht as [Hafter_start | Hbefore_s].
      * apply in_app_or in Hafter_start.
        destruct Hafter_start as [Hafter | [Hstart | []]].
        -- right. apply in_or_app. right. simpl. right. exact Hafter.
        -- left. exact Hstart.
      * apply in_app_or in Hbefore_s.
        destruct Hbefore_s as [Hbefore | [Hs | []]].
        -- right. apply in_or_app. left. exact Hbefore.
        -- right. apply in_or_app. right. simpl. left. exact Hs.
Qed.

Local Lemma cycle_path_label_closed
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (start : Label * IndicatorAssignment)
  (prefix : list (Label * IndicatorAssignment))
  (l : Label)
  (pi : IndicatorAssignment)
  :
  raw_label_path E a start (prefix ++ [start]) start ->
  In (l, pi) (start :: prefix) ->
  exists sigma,
    first_return_to_label E l a pi sigma /\
    In (l, sigma) (start :: prefix).
Proof.
  intros Hcycle Hin.
  destruct (raw_cycle_rotation_path E a start (l, pi) prefix Hcycle Hin)
    as [reached [Hrot [Hin_reached Hall]]].
  destruct (raw_label_path_first_label_hit
    E a (l, pi) (l, pi) reached l Hrot)
    as [sigma [first [Hfirst [Havoid Hhit]]]].
  - exists pi. exact Hin_reached.
  - exists sigma.
    split.
    + exists first. split; assumption.
    + apply Hall. exact Hhit.
Qed.

Local Lemma cycle_path_in_goto_Cplus
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (k : Label)
  (i : IndicatorAssignment)
  (prefix : list (Label * IndicatorAssignment))
  :
  raw_label_path E a (k, i) (prefix ++ [(k, i)]) (k, i) ->
  eval_test (C+[E; k]) a i.
Proof.
  intro Hcycle.
  eapply cycle_label_in_goto_Cplus
    with (cycle := (k, i) :: prefix).
  - intros pi Hin.
    eapply cycle_path_label_closed.
    + exact Hcycle.
    + exact Hin.
  - left. reflexivity.
Qed.

Local Lemma reject_trace_from_path_to_Cplus
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (source target : Label * IndicatorAssignment)
  (path : list (Label * IndicatorAssignment))
  (body : CFGKATExpression)
  :
  E (fst source) = Some body ->
  raw_label_path E a source path target ->
  eval_test (C+[E; fst target]) a (snd target) ->
  resolved_reject_trace E a (fst source) (snd source).
Proof.
  revert source body.
  induction path as [|mid rest IH]; intros source body HE Hpath HC.
  - inversion Hpath; subst target.
    destruct source as [k i].
    apply reject_trace_Cplus with (body := body);
      assumption.
  - destruct (raw_label_path_cons_inv E a source mid target rest Hpath)
      as [Hstep Htail].
    unfold raw_label_step in Hstep.
    destruct Hstep as
      [source_body [mid_body [Hsource [Hmid Hout]]]].
    rewrite HE in Hsource.
    injection Hsource as <-.
    destruct source as [k i].
    destruct mid as [l j].
    destruct (eval_test_dec (C+[E; k]) a i) as [HCsource | HnotC].
    + apply reject_trace_Cplus with (body := body); assumption.
    + eapply reject_trace_bound.
      * exact HE.
      * exact HnotC.
      * exact Hout.
      * exact Hmid.
      * exact (IH (l, j) mid_body Hmid Htail HC).
Qed.

Local Lemma finite_resolved_reject_trace
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (k : Label)
  (body : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  E k = Some body ->
  ResolveCFGKATAutomatonFiniteDynamics
    CFGKATExpressionAutomaton
    (cfgkat_transitions CFGKATExpressionAutomaton (body, i))
    (lift E)
    a
    CFGKATAutomatonReject ->
  resolved_reject_trace E a k i.
Proof.
  intros HE Hfin.
  remember (cfgkat_transitions CFGKATExpressionAutomaton (body, i)) as d0
    eqn:Hd0 in Hfin.
  remember (lift E) as L eqn:HL in Hfin.
  remember CFGKATAutomatonReject as reject eqn:Hreject in Hfin.
  revert k body i HE Hd0 HL Hreject.
  induction Hfin; intros k0 body0 i0 HE0 Hd0 HL Hreject.
  - pose proof
      ltac:(rewrite Hd0 in H; rewrite Hreject in H; exact
      (transition_output_unique body0 a i0 CFGKATAutomatonReject H)
      ) as Hout.
    destruct (eval_test_dec (C+[E; k0]) a i0) as [HC | HnotC].
    + apply reject_trace_Cplus with (body := body0);
        assumption.
    + apply reject_trace_raw with (body := body0);
        assumption.
  - rewrite HL in H0.
    rewrite lift_lookup in H0.
    destruct (E l) as [target_body |] eqn:HEtarget; [| discriminate H0].
    injection H0 as <-.
    pose proof
      ltac:(rewrite Hd0 in H; exact
      (transition_output_unique body0 a i0
        (CFGKATAutomatonJump l i') H)) as Hout.
    destruct (eval_test_dec (C+[E; k0]) a i0) as [HC | HnotC].
    + apply reject_trace_Cplus with (body := body0);
        assumption.
    + eapply reject_trace_bound.
      * exact HE0.
      * exact HnotC.
      * exact Hout.
      * exact HEtarget.
      * eapply IHHfin.
        -- exact HEtarget.
        -- reflexivity.
        -- exact HL.
        -- exact Hreject.
Qed.

Local Ltac contradict_no_finite_direct Hno Hraw output :=
  exfalso;
  apply (Hno output);
  apply ResolveCFGKATAutomatonFiniteDynamicsDirect;
  [ exact Hraw
  | simpl; exact I ].

Local Lemma no_finite_raw_path
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (n : nat)
  (k : Label)
  (body : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  E k = Some body ->
  ResolveCFGKATAutomatonNoFiniteResult
    CFGKATExpressionAutomaton
    (cfgkat_transitions CFGKATExpressionAutomaton (body, i))
    (lift E)
    a ->
  exists target path,
    length path = n /\
    raw_label_path E a (k, i) path target.
Proof.
  revert k body i.
  induction n as [|n IH]; intros k body i HE Hno.
  - exists (k, i), [].
    split; [reflexivity | apply raw_label_path_nil].
  - pose proof (transition_output_spec body a i) as Hraw.
    remember (transition_output body a i) as out eqn:Hout.
    destruct out as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p next].
    + contradict_no_finite_direct Hno Hraw
        (@CFGKATAutomatonReject CFGKATSyntConfiguration).
    + contradict_no_finite_direct Hno Hraw
        (@CFGKATAutomatonAccept CFGKATSyntConfiguration i_accept).
    + contradict_no_finite_direct Hno Hraw
        (@CFGKATAutomatonBreak CFGKATSyntConfiguration i_break).
    + contradict_no_finite_direct Hno Hraw
        (@CFGKATAutomatonContinue CFGKATSyntConfiguration i_continue).
    + contradict_no_finite_direct Hno Hraw
        (@CFGKATAutomatonReturn CFGKATSyntConfiguration).
    + destruct (E l_jump) as [target_body |] eqn:HEtarget.
      * assert (Hno_target :
          ResolveCFGKATAutomatonNoFiniteResult
            CFGKATExpressionAutomaton
            (cfgkat_transitions
              CFGKATExpressionAutomaton (target_body, i_jump))
            (lift E)
            a).
        {
          unfold ResolveCFGKATAutomatonNoFiniteResult in *.
          intros r Hfin.
	          apply (Hno r).
	          eapply ResolveCFGKATAutomatonFiniteDynamicsBoundJump.
	          - exact Hraw.
	          - apply lift_label_some. exact HEtarget.
	          - exact Hfin.
        }
        destruct (IH l_jump target_body i_jump HEtarget Hno_target)
          as [target [path [Hlen Hpath]]].
        exists target, ((l_jump, i_jump) :: path).
        split.
        -- simpl. rewrite Hlen. reflexivity.
        -- apply raw_label_path_cons.
	           ++ unfold raw_label_step.
	              exists body, target_body.
	              repeat split; try assumption.
	              symmetry. exact Hout.
	           ++ exact Hpath.
      * exfalso. apply (Hno (CFGKATAutomatonJump l_jump i_jump)).
        apply ResolveCFGKATAutomatonFiniteDynamicsDirect.
        -- exact Hraw.
	        -- apply lift_label_none. exact HEtarget.
    + destruct next as [next_expr next_i].
      contradict_no_finite_direct Hno Hraw
        (@CFGKATAutomatonNext CFGKATSyntConfiguration
          p (next_expr, next_i)).
Qed.

Lemma resolved_reject_trace_from_rejection
  (E : label_environment CFGKATExpression)
  (k : Label)
  (body : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  E k = Some body ->
  resolved_transition_output E body a i = CFGKATAutomatonReject <->
    resolved_reject_trace E a k i.
Proof.
  intro HE.
  split.
  - intro Hreject.
    pose proof (resolved_transition_output_spec E body a i) as Hresolved.
    rewrite Hreject in Hresolved.
    inversion Hresolved as [a0 zeta Hfinite | a0 Hnofinite]; subst.
    + eapply finite_resolved_reject_trace; eauto.
    + pose (N := length (env_label_assignments E)).
      destruct (no_finite_raw_path E a (S N) k body i HE Hnofinite)
        as [target [path [Hlen Hpath]]].
      assert (Hnot_nd : ~ NoDup path).
      {
        intro Hnd.
        assert (Hin_all : incl path (env_label_assignments E)).
        {
          intros [l sigma] Hin_path.
          destruct (raw_label_path_in_bound E a (k, i) target
            (l, sigma) path Hpath Hin_path) as [path_body Hlookup].
          eapply env_label_assignments_complete.
          exact Hlookup.
        }
        pose proof (NoDup_incl_length Hnd Hin_all) as Hle.
        unfold N in Hlen.
        rewrite Hlen in Hle.
        lia.
      }
      destruct (not_NoDup_duplicate_split path Hnot_nd)
        as [pre [mid [post [s Hsplit]]]].
      subst path.
      pose proof
        (raw_label_path_take_to E a (k, i) s target pre
          (mid ++ s :: post) Hpath) as Hprefix.
      pose proof
        (raw_label_path_drop_to E a (k, i) s target pre
          (mid ++ s :: post) Hpath) as Htail.
      pose proof
        (raw_label_path_take_to E a s s target mid post Htail) as Hcycle.
      destruct s as [cycle_label cycle_i].
      pose proof
        (cycle_path_in_goto_Cplus E a cycle_label cycle_i mid Hcycle)
        as HCcycle.
      exact
        (reject_trace_from_path_to_Cplus
          E a (k, i) (cycle_label, cycle_i)
          (pre ++ [(cycle_label, cycle_i)]) body
          HE Hprefix HCcycle).
  - intro Htrace.
    revert body HE.
    induction Htrace as
      [k' i' trace_body Hlookup HC
      |k' i' trace_body Hlookup _ Hraw
      |k' i' trace_body j' l' target Hlookup _ Hraw Htarget
         Htail IHtail]; intros body0 HE0.
    + rewrite Hlookup in HE0.
      injection HE0 as <-.
      eapply goto_Cplus_resolved_transition_reject; eauto.
    + rewrite Hlookup in HE0.
      injection HE0 as <-.
      apply resolved_transition_output_unique.
      simpl.
      apply ResolveCFGKATAutomatonDynamicsFinite.
      apply ResolveCFGKATAutomatonFiniteDynamicsDirect.
      * apply (proj2
          (transition_output_exact trace_body a i'
            CFGKATAutomatonReject)).
        exact Hraw.
      * simpl. exact I.
    + rewrite Hlookup in HE0.
      injection HE0 as <-.
      pose proof (IHtail target Htarget) as Htarget_reject.
      apply resolved_transition_output_unique.
      simpl.
      eapply ResolveCFGKATAutomatonDynamicsBoundJump.
      * apply (proj2
          (transition_output_exact trace_body a i'
            (CFGKATAutomatonJump l' j'))).
        exact Hraw.
      * apply lift_label_some. exact Htarget.
      * rewrite <- Htarget_reject.
        apply resolved_transition_output_spec.
      * apply cfgkat_dynamics_functional.
Qed.


Local Lemma nonC_raw_env_same_domain
  (E : label_environment CFGKATExpression)
  :
  C7_same_domain E (nonC_raw_env E).
Proof.
  unfold C7_same_domain, label_in_dom, nonC_raw_env,
    environment_map_values, mk_environment.
  simpl.
  intro k.
  split.
  - intros [body HE].
    rewrite HE.
    exists (nonC_raw_branch_sum E k body).
    reflexivity.
  - intros [body Hraw].
    destruct (E k) as [source |] eqn:HE.
    + exists source. reflexivity.
    + discriminate.
Qed.

Local Lemma resolved_env_same_domain
  (E : label_environment CFGKATExpression)
  :
  C7_same_domain E (resolved_env E).
Proof.
  unfold C7_same_domain, label_in_dom, resolved_env,
    environment_map_values, mk_environment.
  simpl.
  intro k.
  split.
  - intros [body HE].
    rewrite HE.
    exists (resolved_body E body).
    reflexivity.
  - intros [body Hresolved].
    destruct (E k) as [source |] eqn:HE.
    + exists source. reflexivity.
    + discriminate.
Qed.

Local Lemma sys_resolved_no_original_label_transition
  (E : label_environment CFGKATExpression)
  (source target_body : CFGKATExpression)
  (source_a runtime_a : Atom)
  (source_i runtime_i j : IndicatorAssignment)
  (k : Label)
  :
  E k = Some target_body ->
  transition_output
    (sys (resolved_transition_output E source source_a source_i))
    runtime_a runtime_i <>
  CFGKATAutomatonJump k j.
Proof.
  intros HE Hjump.
  remember (resolved_transition_output E source source_a source_i) as r.
  destruct r as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p [f i_next]];
    simplify_sysc_transition_in Hjump; try discriminate.
  inversion Hjump; subst l_jump i_jump.
  eapply resolved_transition_output_no_original_bound_jump.
  - exact HE.
  - symmetry. exact Heqr.
Qed.

Local Lemma resolved_body_no_original_label_jump
  (E : label_environment CFGKATExpression)
  (source : CFGKATExpression)
  (k : Label)
  (target_body : CFGKATExpression)
  :
  E k = Some target_body ->
  guarded k (resolved_body E source).
Proof.
  intros HE a i j Hjump.
  apply transition_output_exact in Hjump.
  unfold resolved_body, guarded_sum_all in Hjump.
  change
    (transition_output
      (guarded_sum_on all_AtIY (resolved_branch E source))
      (AtIY_atom (a, i)) (AtIY_assignment (a, i)) =
     CFGKATAutomatonJump k j) in Hjump.
  rewrite (transition_guarded_sum_on_select
    all_AtIY (resolved_branch E source) (a, i)) in Hjump.
  - unfold resolved_branch in Hjump.
    eapply sys_resolved_no_original_label_transition.
    + exact HE.
    + exact Hjump.
  - apply AtIY_in_all.
Qed.

Local Lemma resolved_env_guarded
  (E : label_environment CFGKATExpression)
  :
  C7_guarded (resolved_env E).
Proof.
  unfold C7_guarded.
  intros l l' body target_body Hbody Htarget.
  unfold resolved_env, environment_map_values, mk_environment
    in Hbody, Htarget.
  simpl in Hbody, Htarget.
  destruct (E l) as [source |] eqn:HEsource; [| discriminate Hbody].
  destruct (E l') as [original_target |] eqn:HEtarget;
    [| discriminate Htarget].
  injection Hbody as <-.
  eapply resolved_body_no_original_label_jump.
  exact HEtarget.
Qed.

Local Lemma nonC_raw_sum_select_not_Cplus
  (E : label_environment CFGKATExpression)
  (k : Label)
  (body : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  ~ eval_test (C+[E; k]) a i ->
  test (AtIY_test (a, i)) ;; nonC_raw_branch_sum E k body ==
  test (AtIY_test (a, i)) ;; sys (transition_output body a i).
Proof.
  intro HnotC.
  unfold nonC_raw_branch_sum, raw_fundamental_branch,
    guarded_sum_satisfying.
  apply branchsel_plus_on.
  apply filter_In.
  split.
  - apply AtIY_in_all.
  - apply in_test_not_false.
    unfold in_test. simpl.
    destruct (eval_test_dec (C+[E; k]) a i) as [HC | _].
    + exfalso. apply HnotC. exact HC.
    + reflexivity.
Qed.

Local Lemma resolved_body_select
  (E : label_environment CFGKATExpression)
  (body : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  test (AtIY_test (a, i)) ;; resolved_body E body ==
  test (AtIY_test (a, i)) ;;
    sys (resolved_transition_output E body a i).
Proof.
  unfold resolved_body, resolved_branch.
  apply branchsel_plus.
Qed.

Local Lemma nonC_raw_productive_resolution_branch
  (E : label_environment CFGKATExpression)
  (a : Atom)
  (source : CFGKATExpression)
  (i : IndicatorAssignment)
  (zeta : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  productive_resolution
    CFGKATExpressionAutomaton [lift E] a (source, i) zeta ->
  nonC_raw_env E |-
    test (AtIY_test (a, i)) ;;
      sys (transition_output source a i) ==
    test (AtIY_test (a, i)) ;; sys zeta -|
  nonC_raw_env E.
Proof.
  intro Hprod.
  remember (source, i) as start eqn:Hstart.
  revert source i Hstart.
  induction Hprod; intros source0 i0 Hstart;
    inversion Hstart; subst x.
  - rewrite (transition_output_unique source0 a i0
      (CFGKATAutomatonAccept i) H).
    apply EqRefl.
  - rewrite (transition_output_unique source0 a i0
      (CFGKATAutomatonBreak i) H).
    apply EqRefl.
  - rewrite (transition_output_unique source0 a i0
      (CFGKATAutomatonContinue i) H).
    apply EqRefl.
  - rewrite (transition_output_unique source0 a i0
      CFGKATAutomatonReturn H).
    apply EqRefl.
  - rewrite (transition_output_unique source0 a i0
      (CFGKATAutomatonNext p s) H).
    apply EqRefl.
  - rewrite (transition_output_unique source0 a i0
      (CFGKATAutomatonJump l i) H).
    apply EqRefl.
  - inversion H0 as [y ys Hlookup | y ys Hnone Htail]; subst.
    + rewrite lift_lookup in Hlookup.
      destruct (E l) as [target |] eqn:HEtarget; [| discriminate Hlookup].
      injection Hlookup as Hs. subst s.
      rewrite (transition_output_unique source0 a i0
        (CFGKATAutomatonJump l i) H).
      assert (HnotC_target :
        ~ eval_test (C+[E; l]) a i).
      {
        intro HCtarget.
        pose proof
          (productive_resolution_resolves
            CFGKATExpressionAutomaton
            [lift E] a (target, i) zeta Hprod) as Hres.
        pose proof
          (resolved_transition_output_unique E target a i zeta Hres)
          as Hzeta.
        pose proof
          (goto_Cplus_resolved_transition_reject
            E l target a i HEtarget HCtarget) as Hreject.
        rewrite Hreject in Hzeta.
        eapply productive_resolution_not_reject.
        - exact Hprod.
        - symmetry. exact Hzeta.
      }
      cfgkat_rewrite (@EqSeqRightCong
        (nonC_raw_env E) (nonC_raw_env E)
        (complete_assignment i ;; goto l)
        (complete_assignment i ;; nonC_raw_branch_sum E l target)
        (test (AtIY_test (a, i0)))
        ltac:(apply substitute_bound_jump_body;
          unfold nonC_raw_env, environment_map_values, mk_environment;
          simpl;
          rewrite HEtarget;
          reflexivity)
        ltac:(apply EqRefl)).
      apply AtIY_complete_assignment_branch_expr_ctx.
      * cfgkat_rewrite (weaken_empty_to_env (nonC_raw_env E) _ _
          (nonC_raw_sum_select_not_Cplus E l target a i HnotC_target)).
        apply IHHprod.
        reflexivity.
      * apply weaken_empty_to_env.
        apply sysannih.
    + inversion Htail.
Qed.

Local Lemma nonC_raw_reject_trace_sum_zero
  (E : label_environment CFGKATExpression)
  (k : Label)
  (body : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  E k = Some body ->
  resolved_reject_trace E a k i ->
  nonC_raw_env E |-
    test (AtIY_test (a, i)) ;;
      nonC_raw_branch_sum E k body ==
    0 -| nonC_raw_env E.
Proof.
  intros HE0 Htrace.
  revert body HE0.
  induction Htrace as
    [k' i' trace_body Hlookup HC
    |k' i' trace_body Hlookup HnotC Hraw
    |k' i' trace_body j' l' target' Hlookup HnotC Hraw Htarget
       Htail IHtail]; intros body0 HE0.
  - rewrite Hlookup in HE0.
    injection HE0 as <-.
    apply weaken_empty_to_env.
    apply nonC_raw_branch_sum_Cplus_zero.
    exact HC.
  - rewrite Hlookup in HE0.
    injection HE0 as <-.
    cfgkat_rewrite (weaken_empty_to_env (nonC_raw_env E) _ _
      (nonC_raw_sum_select_not_Cplus E k' trace_body a i' HnotC)).
    rewrite Hraw.
    apply weaken_empty_to_env.
    apply test_abort.
  - rewrite Hlookup in HE0.
    injection HE0 as <-.
    cfgkat_rewrite (weaken_empty_to_env (nonC_raw_env E) _ _
      (nonC_raw_sum_select_not_Cplus E k' trace_body a i' HnotC)).
    rewrite Hraw.
    cfgkat_rewrite (@EqSeqRightCong
      (nonC_raw_env E) (nonC_raw_env E)
      (complete_assignment j' ;; goto l')
      (complete_assignment j' ;; nonC_raw_branch_sum E l' target')
      (test (AtIY_test (a, i')))
      ltac:(apply substitute_bound_jump_body;
        unfold nonC_raw_env, environment_map_values, mk_environment;
        simpl;
        rewrite Htarget;
        reflexivity)
      ltac:(apply EqRefl)).
    cfgkat_rewrite (AtIY_complete_assignment_branch_expr_ctx
      (nonC_raw_env E) a i' j'
      (nonC_raw_branch_sum E l' target') 0
      ltac:(cfgkat_rewrite (IHtail target' Htarget);
        cfgkat_rewrite <- (weaken_empty_to_env (nonC_raw_env E) _ _
          (test_abort (AtIY_test (a, j')))) at 1;
        apply EqRefl)
      ltac:(apply weaken_empty_to_env;
        apply complete_assignment_abort)).
    apply weaken_empty_to_env.
    apply test_abort.
Qed.

Local Lemma nonC_raw_reject_bound_branch_zero
  (E : label_environment CFGKATExpression)
  (k : Label)
  (source : CFGKATExpression)
  (a : Atom)
  (i j : IndicatorAssignment)
  (l : Label)
  (target : CFGKATExpression)
  :
  E k = Some source ->
  ~ eval_test (C+[E; k]) a i ->
  transition_output source a i = CFGKATAutomatonJump l j ->
  E l = Some target ->
  resolved_transition_output E source a i = CFGKATAutomatonReject ->
  nonC_raw_env E |-
    test (AtIY_test (a, i)) ;;
      sys (CFGKATAutomatonJump l j) ==
    test (AtIY_test (a, i)) ;;
      sys CFGKATAutomatonReject -|
  nonC_raw_env E.
Proof.
  intros HE HnotC Hraw HEtarget Hresolved.
  assert (Htarget_reject :
    resolved_transition_output E target a j = CFGKATAutomatonReject).
  {
    pose proof (resolved_transition_output_spec E target a j) as Htarget_res.
    assert (Hsource_to_target :
      cfgkat_transitions
        (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E))
        (source, i) a
        (resolved_transition_output E target a j)).
    { simpl.
      eapply ResolveCFGKATAutomatonDynamicsBoundJump.
      - apply (proj2
          (transition_output_exact source a i
            (CFGKATAutomatonJump l j))).
        exact Hraw.
      - apply lift_label_some. exact HEtarget.
      - exact Htarget_res.
      - apply cfgkat_dynamics_functional. }
    pose proof
      (resolved_transition_output_unique E source a i
        (resolved_transition_output E target a j)
        Hsource_to_target) as Heq.
    rewrite Hresolved in Heq.
    symmetry. exact Heq.
  }
  cfgkat_rewrite (@EqSeqRightCong
    (nonC_raw_env E) (nonC_raw_env E)
    (complete_assignment j ;; goto l)
    (complete_assignment j ;; nonC_raw_branch_sum E l target)
    (test (AtIY_test (a, i)))
    ltac:(apply substitute_bound_jump_body;
      unfold nonC_raw_env, environment_map_values, mk_environment;
      simpl;
      rewrite HEtarget;
      reflexivity)
    ltac:(apply EqRefl)).
  apply AtIY_complete_assignment_branch_expr_ctx.
  - cfgkat_rewrite (nonC_raw_reject_trace_sum_zero E l target
      a j HEtarget
      (proj1 (resolved_reject_trace_from_rejection
        E l target a j HEtarget) Htarget_reject)).
    cfgkat_rewrite <- (weaken_empty_to_env (nonC_raw_env E) _ _
      (test_abort (AtIY_test (a, j)))) at 1.
    apply EqRefl.
  - apply weaken_empty_to_env.
    apply complete_assignment_abort.
Qed.

Local Ltac solve_productive_resolved_branch Hresolved :=
  eapply nonC_raw_productive_resolution_branch;
  eapply productive_resolution_complete;
  [ rewrite <- Hresolved; apply resolved_transition_output_spec
  | discriminate ].

Local Ltac contradict_resolved_reject_productive Hresolved Hraw :=
  exfalso;
  eapply productive_resolution_contradicts_resolved_reject;
  [ first
      [ apply productive_resolution_accept;
        apply transition_output_exact; exact Hraw
      | apply productive_resolution_break;
        apply transition_output_exact; exact Hraw
      | apply productive_resolution_continue;
        apply transition_output_exact; exact Hraw
      | apply productive_resolution_return;
        apply transition_output_exact; exact Hraw
      | apply productive_resolution_next;
        apply transition_output_exact; exact Hraw ]
  | exact Hresolved ].

Local Lemma nonC_raw_branch_to_resolved
  (E : label_environment CFGKATExpression)
  (k : Label)
  (source : CFGKATExpression)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  E k = Some source ->
  ~ eval_test (C+[E; k]) a i ->
  nonC_raw_env E |-
    test (AtIY_test (a, i)) ;;
      sys (transition_output source a i) ==
    test (AtIY_test (a, i)) ;;
      sys (resolved_transition_output E source a i) -|
  nonC_raw_env E.
Proof.
  intros HE HnotC.
  destruct (resolved_transition_output E source a i) as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p next]
    eqn:Hresolved.
  - destruct (transition_output source a i) as
      [|j_accept|j_break|j_continue| |l_raw j_jump|p_raw next_raw]
      eqn:Hraw; try apply EqRefl.
    + contradict_resolved_reject_productive Hresolved Hraw.
    + contradict_resolved_reject_productive Hresolved Hraw.
    + contradict_resolved_reject_productive Hresolved Hraw.
    + contradict_resolved_reject_productive Hresolved Hraw.
    + destruct (E l_raw) as [target |] eqn:HEtarget.
      * eapply nonC_raw_reject_bound_branch_zero.
        -- exact HE.
        -- exact HnotC.
        -- exact Hraw.
        -- exact HEtarget.
        -- exact Hresolved.
      * exfalso.
        eapply productive_resolution_contradicts_resolved_reject.
        -- apply productive_resolution_free_jump.
           ++ apply (proj2
                (transition_output_exact source a i
                  (CFGKATAutomatonJump l_raw j_jump))).
              exact Hraw.
           ++ constructor.
              ** apply lift_label_none. exact HEtarget.
              ** constructor.
        -- exact Hresolved.
    + contradict_resolved_reject_productive Hresolved Hraw.
  - solve_productive_resolved_branch Hresolved.
  - solve_productive_resolved_branch Hresolved.
  - solve_productive_resolved_branch Hresolved.
  - solve_productive_resolved_branch Hresolved.
  - solve_productive_resolved_branch Hresolved.
  - solve_productive_resolved_branch Hresolved.
Qed.

Local Lemma nonC_raw_sum_to_resolved_body
  (E : label_environment CFGKATExpression)
  (k : Label)
  (source : CFGKATExpression)
  :
  E k = Some source ->
  nonC_raw_env E |-
    nonC_raw_branch_sum E k source ==
    resolved_body E source -|
  nonC_raw_env E.
Proof.
  intro HE.
  apply minterm_ext_ctx.
  intros m Hm.
  destruct m as [a i].
  destruct (eval_test_dec (C+[E; k]) a i) as [HC | HnotC].
  - cfgkat_rewrite (weaken_empty_to_env (nonC_raw_env E) _ _
      (nonC_raw_branch_sum_Cplus_zero E k source (a, i) HC)).
    cfgkat_rewrite (weaken_empty_to_env (nonC_raw_env E) _ _
      (resolved_body_select E source a i)).
    rewrite (goto_Cplus_resolved_transition_reject E k source a i HE HC).
    cfgkat_rewrite <- (weaken_empty_to_env (nonC_raw_env E) _ _
      (test_abort (AtIY_test (a, i)))) at 1.
    apply EqRefl.
  - cfgkat_rewrite (weaken_empty_to_env (nonC_raw_env E) _ _
      (nonC_raw_sum_select_not_Cplus E k source a i HnotC)).
    cfgkat_rewrite (nonC_raw_branch_to_resolved E
      k source a i HE HnotC).
    cfgkat_rewrite <- (weaken_empty_to_env (nonC_raw_env E) _ _
      (resolved_body_select E source a i)).
    apply EqRefl.
Qed.

Local Lemma nonC_raw_solution
  (E : label_environment CFGKATExpression)
  :
  C7_solution (resolved_env E) (nonC_raw_env E).
Proof.
  unfold C7_solution.
  intros k body Hbody.
  unfold resolved_env, environment_map_values, mk_environment
    in Hbody.
  simpl in Hbody.
  destruct (E k) as [source |] eqn:HE; [| discriminate Hbody].
  injection Hbody as <-.
  cfgkat_rewrite (unfold_bound_goto (nonC_raw_env E) k
    (nonC_raw_branch_sum E k source)
    ltac:(unfold nonC_raw_env, environment_map_values, mk_environment;
      simpl;
      rewrite HE;
      reflexivity)).
  apply nonC_raw_sum_to_resolved_body.
  exact HE.
Qed.

Lemma gtnflem1
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  :
  E |- e == e -| resolved_env E.
Proof.
  change (gtnflem1_statement E e).
  unfold gtnflem1_statement.
  cfgkat_rewrite (gtnflem1_1 E e).
  apply EqC7_from_side_condition.
  split.
  - intro k.
    transitivity (label_in_dom E k).
    + symmetry. apply resolved_env_same_domain.
    + apply nonC_raw_env_same_domain.
  - split.
    + apply nonC_raw_solution.
    + apply resolved_env_guarded.
Qed.
