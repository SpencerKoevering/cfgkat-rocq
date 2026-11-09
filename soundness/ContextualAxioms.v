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

From CFGKAT.Soundness Require Export ContextualDefinitions.

Local Open Scope type_scope.
Local Open Scope cfgkat_scope.



Ltac lift_raw_transition Hdyn :=
  match type of Hdyn with
  | CFGKATExpressionDynamics ?x ?a CFGKATAutomatonReject =>
      eapply Hlift_reject; exact Hdyn
  | CFGKATExpressionDynamics ?x ?a (CFGKATAutomatonAccept ?i) =>
      eapply Hlift_accept; exact Hdyn
  | CFGKATExpressionDynamics ?x ?a (CFGKATAutomatonBreak ?i) =>
      eapply Hlift_break; exact Hdyn
  | CFGKATExpressionDynamics ?x ?a (CFGKATAutomatonContinue ?i) =>
      eapply Hlift_continue; exact Hdyn
  | CFGKATExpressionDynamics ?x ?a CFGKATAutomatonReturn =>
      eapply Hlift_return; exact Hdyn
  | CFGKATExpressionDynamics ?x ?a (CFGKATAutomatonNext ?p ?s) =>
      eapply Hlift_next; exact Hdyn
  | cfgkat_synt_transitions ?aut ?x ?a CFGKATAutomatonReject =>
      eapply Hlift_reject; exact Hdyn
  | cfgkat_synt_transitions ?aut ?x ?a (CFGKATAutomatonAccept ?i) =>
      eapply Hlift_accept; exact Hdyn
  | cfgkat_synt_transitions ?aut ?x ?a (CFGKATAutomatonBreak ?i) =>
      eapply Hlift_break; exact Hdyn
  | cfgkat_synt_transitions ?aut ?x ?a (CFGKATAutomatonContinue ?i) =>
      eapply Hlift_continue; exact Hdyn
  | cfgkat_synt_transitions ?aut ?x ?a CFGKATAutomatonReturn =>
      eapply Hlift_return; exact Hdyn
  | cfgkat_synt_transitions ?aut ?x ?a (CFGKATAutomatonNext ?p ?s) =>
      eapply Hlift_next; exact Hdyn
  end.

Ltac strong_halt_output output Hleft Hright :=
  eapply CFGKATStrongStepHalt with (zeta := output);
  [ simpl; constructor
  | lift_raw_transition Hleft
  | lift_raw_transition Hright ].

Ltac strong_current_halt_output Hleft Hright :=
  match type of Hleft with
  | CFGKATExpressionDynamics _ _ (CFGKATAutomatonJump _ _) => fail
  | CFGKATExpressionDynamics _ _ (CFGKATAutomatonNext _ _) => fail
  | CFGKATExpressionDynamics _ _ ?output =>
      strong_halt_output output Hleft Hright
  | cfgkat_synt_transitions _ _ _ (CFGKATAutomatonJump _ _) => fail
  | cfgkat_synt_transitions _ _ _ (CFGKATAutomatonNext _ _) => fail
  | cfgkat_synt_transitions _ _ _ ?output =>
      strong_halt_output output Hleft Hright
  end.

Lemma lift_extend_old_some
  (E : label_environment CFGKATExpression)
  (l : Label)
  (f : CFGKATExpression)
  (Hfresh : label_fresh E l)
  :
  forall l0 i s,
    lift E l0 i = Some s ->
    lift (E ## l # f) l0 i = Some s.
Proof.
  intros l0 i s H. simpl in *.
  destruct (E l0) as [e0 |] eqn:HEold; try discriminate.
  inversion_clear H.
  destruct (Label_eq_dec l l0).
  - pose proof label_fresh_none as Hfresh_none.
    congruence.
  - reflexivity.
Qed.

Lemma lift_label_extend_same
  (E : label_environment CFGKATExpression)
  (l : Label)
  (body : CFGKATExpression)
  (Hfresh : label_fresh E l)
  (i : IndicatorAssignment)
  :
  lift (E ## l # body) l i = Some (body, i).
Proof.
  simpl. destruct (Label_eq_dec l l) as [_ | Hneq].
  - reflexivity.
  - congruence.
Qed.

Lemma lift_label_some
  (E : label_environment CFGKATExpression)
  (l : Label)
  (body : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  E l = Some body ->
  lift E l i = Some (body, i).
Proof.
  intro Hlookup. simpl.
  now rewrite Hlookup.
Qed.

Lemma lift_label_none
  (E : label_environment CFGKATExpression)
  (l : Label)
  (i : IndicatorAssignment)
  :
  E l = None ->
  lift E l i = None.
Proof.
  intro Hlookup. simpl.
  now rewrite Hlookup.
Qed.

Local Lemma lift_singleton_free
  (E : label_environment CFGKATExpression)
  (l : Label)
  (i : IndicatorAssignment)
  :
  E l = None ->
  Forall (fun y : environment CFGKATSyntConfiguration => y l i = None)
    [lift E].
Proof.
  intro Hlookup.
  constructor.
  - now apply lift_label_none.
  - constructor.
Qed.

Lemma lift_label_extend_other
  (E : label_environment CFGKATExpression)
  (l k : Label)
  (body : CFGKATExpression)
  (Hfresh : label_fresh E l)
  (i : IndicatorAssignment)
  :
  l <> k ->
  lift (E ## l # body) k i = lift E k i.
Proof.
  intro Hneq. simpl.
  destruct (Label_eq_dec l k) as [Heq | _].
  - contradiction.
  - reflexivity.
Qed.

Lemma lift_label_extend_other_some
  (E : label_environment CFGKATExpression)
  (l k : Label)
  (body old : CFGKATExpression)
  (Hfresh : label_fresh E l)
  (i : IndicatorAssignment)
  :
  l <> k ->
  E k = Some old ->
  lift (E ## l # body) k i = Some (old, i).
Proof.
  intros Hneq Hlookup.
  rewrite lift_label_extend_other; auto.
  now apply lift_label_some.
Qed.

Lemma lift_label_extend_other_none
  (E : label_environment CFGKATExpression)
  (l k : Label)
  (body : CFGKATExpression)
  (Hfresh : label_fresh E l)
  (i : IndicatorAssignment)
  :
  l <> k ->
  E k = None ->
  lift (E ## l # body) k i = None.
Proof.
  intros Hneq Hlookup.
  rewrite lift_label_extend_other; auto.
  now apply lift_label_none.
Qed.

Lemma lift_plus_some
  (E F : label_environment CFGKATExpression)
  (Hdisj : label_disjoint E F)
  (l : Label)
  (i : IndicatorAssignment)
  (body : CFGKATSyntConfiguration)
:
  lift E l i = Some body ->
  lift (E + F) l i = Some body
.
Proof.
  simpl. intros.
  destruct (E l); congruence.
Qed.

Definition relation_or_eq
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop :=
  fun x y => R x y \/ x = y.

Program Definition bisim_trans_syntactic_middle
  {A C : CFGKATAutomaton}
  (B : CFGKATSyntacticAutomaton)
  (R1 : CFGKATAutomatonBisimulation A B)
  (R2 : CFGKATAutomatonBisimulation B C)
  : CFGKATAutomatonBisimulation A C :=
  bisim_trans _ R1 R2.
Next Obligation.
  intros aut1 aut2 aut B1 B2.
  apply cfgkat_synt_dynamics_total.
Qed.

Local Lemma finite_contains_goto_next_back :
  forall
    (e e' : CFGKATExpression)
    (i i' : IndicatorAssignment)
    (p: Action)
    (a : Atom),
    CFGKATExpressionFiniteDynamics
      (e, i) a (CFGKATAutomatonNext p (e', i')) ->
    forall (k : Label),
      contains_goto k e' ->
      contains_goto k e.
Proof.
  intros e e' i i' p a Hstep.
  dependent induction Hstep;
  intros; try now simpl.
  -
    left. eapply IHHstep; eauto.

  -
    right. eapply IHHstep; eauto.

  -
    right. eapply IHHstep2; eauto.

  -
    destruct H as [Hcontains_left | Hcontains_right].
    + left. eapply IHHstep; eauto.
    + right. apply Hcontains_right.

  -
    right. eapply IHHstep2; eauto.

  -
    right. eapply IHHstep2; eauto.

  -
    destruct H as [Hcontains_head | Hcontains_body].
    + left. eapply IHHstep; eauto.
    + right. apply Hcontains_body.

  -
    simpl.
    assert (Hloop : contains_goto k (e0 |> while b do e0))
      by (eapply IHHstep; eauto).
    simpl in Hloop. intuition.
Qed.

Lemma contains_goto_next_back :
  forall
    (e e': CFGKATExpression)
    (i i': IndicatorAssignment)
    (a : Atom)
    (p : Action),
    CFGKATExpressionDynamics (e, i) a (CFGKATAutomatonNext p (e', i')) ->
    forall (k : Label),
      contains_goto k e' ->
      contains_goto k e.
Proof.
  intros e e' i i' a p Hstep k Hcontains.
  dependent destruction Hstep.
  eapply finite_contains_goto_next_back; eauto.
Qed.

Local Lemma finite_contains_goto_jump_back :
  forall
    (e : CFGKATExpression)
    (i j: IndicatorAssignment)
    (k : Label)
    (a : Atom),
    CFGKATExpressionFiniteDynamics (e, i) a (CFGKATAutomatonJump k j) ->
    contains_goto k e.
Proof.
  intros e i j k a Hstep.
  dependent induction Hstep.

  -
    reflexivity.

  -
    left. eapply IHHstep; eauto.

  -
    right. eapply IHHstep; eauto.

  -
    right. eapply IHHstep2; eauto.

  -
    left. eapply IHHstep; eauto.

  -
    right. eapply IHHstep2; eauto.

  -
    right. eapply IHHstep2; eauto.

  -
    left. eapply IHHstep; eauto.

  -
    assert (Hloop : contains_goto k (e0 |> while b do e0))
      by (eapply IHHstep; eauto).
    simpl in Hloop. intuition.
Qed.

Lemma contains_goto_jump_back :
  forall
    (e : CFGKATExpression)
    (i j: IndicatorAssignment)
    (a : Atom)
    (k : Label),
    CFGKATExpressionDynamics (e, i) a (CFGKATAutomatonJump k j) ->
    contains_goto k e.
Proof.
  intros e i j a k Hstep.
  dependent destruction Hstep.
  eapply finite_contains_goto_jump_back; eauto.
Qed.

Local Lemma no_goto_expr_next :
  forall
    (e e' : CFGKATExpression)
    (F : label_environment CFGKATExpression)
    (i i' : IndicatorAssignment)
    (a : Atom)
    (p : Action),
    no_goto_expr e F ->
    CFGKATExpressionDynamics (e, i) a
      (CFGKATAutomatonNext p (e', i')) ->
    no_goto_expr e' F.
Proof.
  intros e e' F i i' a p Hng Hstep.
  intros k Hdom Hcontains.
  eapply Hng; eauto.
  eapply contains_goto_next_back; eauto.
Qed.

Lemma no_goto_expr_no_jump :
  forall e F i a j l,
    no_goto_expr e F ->
    label_in_dom F l ->
    CFGKATExpressionDynamics (e, i) a (CFGKATAutomatonJump l j) ->
    False.
Proof.
  intros e F i a j l Hng Hdom Hjump.
  apply (Hng l Hdom).
  eapply contains_goto_jump_back; eauto.
Qed.

Local Lemma first_binding_extend_right
  (E : label_environment CFGKATExpression)
  (l : Label)
  (f : CFGKATExpression)
  (Hfresh : label_fresh E l)
  :
  forall l0 i s,
    lift (E ## l # f) l0 i = Some s ->
    first_binding l0 i s
      [lift E; lift (E ## l # f)].
Proof.
  intros l0 i s Hext.
  destruct (Label_eq_dec l l0); subst.
  - apply first_binding_tail.
    + now apply lift_label_none.
    + now apply first_binding_head.
  - apply first_binding_head.
    erewrite <- lift_label_extend_other; eauto.
Qed.

Local Lemma forall_none_extend_right
  (E : label_environment CFGKATExpression)
  (l : Label)
  (f : CFGKATExpression)
  (Hfresh : label_fresh E l)
  :
  forall l0 i,
    lift (E ## l # f) l0 i = None ->
    Forall
      (fun y : environment CFGKATSyntConfiguration => y l0 i = None)
      [lift E; lift (E ## l # f)].
Proof.
  intros l0 i Hnone.
  constructor.
  - simpl in Hnone.
    destruct (Label_eq_dec l l0); try discriminate.
    destruct (E l0) eqn:?.
    + discriminate.
    + now apply lift_label_none.
  - now repeat constructor.
Qed.

Local Lemma first_binding_two_silent
  (aut : CFGKATSyntacticAutomaton)
  (y1 y2 : environment CFGKATSyntConfiguration)
  (a : Atom)
  (x : CFGKATSyntConfiguration)
  (l : Label)
  (i : IndicatorAssignment)
  (s : CFGKATSyntConfiguration)
  :
  cfgkat_synt_transitions aut x a (CFGKATAutomatonJump l i) ->
  first_binding l i s [y1; y2] ->
  CFGKATSilentTransition aut [y1; y2] a x s.
Proof.
  intros Hjump Hbind.
  repeat dependent destruction Hbind.
  - replace [y1; y2] with ([y1] ++ [y2]) by reflexivity.
    apply CFGKATSilentWeaken.
    eapply CFGKATSilentBoundJump with (ys := []); eauto.
  - eapply CFGKATSilentBoundJump with (ys := [y1]); eauto.
    eapply Hlift_free_jump; eauto.
Qed.

Program Definition sup_sys_sol_sub_sys_synt_strong
  (E : label_environment CFGKATExpression)
  (l : Label)
  (f : CFGKATExpression)
  (Hfresh : label_fresh E l)
  : @CFGKATStrongBisimulation
      CFGKATExpressionAutomaton
      CFGKATExpressionAutomaton
      [lift (E ## l # f)]
      [lift E; lift (E ## l # f)]
:= {|
  cfgkat_strong_relation := eq
|}.
Next Obligation.
  intros E l f Hfresh x y a Heq. destruct Heq.
  destruct (cfgkat_synt_dynamics_total CFGKATExpressionAutomaton x a)
   as [zeta Hzeta].
  destruct (classic (cfgkat_lifts_easy zeta)); [
  destruct (classic (exists p e' i', zeta = CFGKATAutomatonNext p (e', i'))) |].
  - destruct H0 as [p [e' [i' ?]]]; subst.
    eapply CFGKATStrongStepNext; eauto.
    + apply Hlift_next; eauto.
    + apply Hlift_next; eauto.
  - eapply CFGKATStrongStepHalt with (zeta := zeta); eauto.
    + destruct zeta; try now do 2 constructor.
      destruct s. contradict H0. now repeat eexists.
    + apply Hlift_easy; auto.
    + apply Hlift_easy; auto.
  - destruct zeta; try now simpl in *.
    destruct (lift (E ## l # f) l0 i) as [s |] eqn:Hbind.
    + eapply CFGKATStrongStepSilent with (x1' := s) (x2' := s); eauto.
      * eapply CFGKATSilentBoundJump with (ys := []); eauto.
      * eapply first_binding_two_silent; eauto.
        now eapply first_binding_extend_right.
    + eapply CFGKATStrongStepHalt with (zeta := CFGKATAutomatonJump l0 i).
      * simpl. constructor.
      * eapply Hlift_free_jump; eauto.
      * eapply Hlift_free_jump with (ys := [lift E; lift (E ## l # f)]); eauto.
        now eapply forall_none_extend_right.
Qed.

Definition sup_sys_sol_sub_sys_synt_bisim
  (E : label_environment CFGKATExpression)
  (l : Label)
  (f : CFGKATExpression)
  (Hfresh : label_fresh E l)
  : CFGKATAutomatonBisimulation
      (resolve_list
         CFGKATExpressionAutomaton
         [lift (E ## l # f)])
      (resolve_list
         CFGKATExpressionAutomaton
         [lift E; lift (E ## l # f)]) :=
	  strong_bisim_to_bisim
	    [lift (E ## l # f)]
	    [lift E; lift (E ## l # f)]
	    (sup_sys_sol_sub_sys_synt_strong E l f Hfresh).

Local Lemma lifted_relation_to_strong_step_same_env
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (HR_refl : forall s, R s s)
  (aut : CFGKATSyntacticAutomaton)
  (y : environment CFGKATSyntConfiguration)
  (x1 x2 : CFGKATSyntConfiguration)
  (a : Atom)
  (zeta1 zeta2 : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  cfgkat_synt_transitions aut x1 a zeta1 ->
  cfgkat_synt_transitions aut x2 a zeta2 ->
  lifted_relation R zeta1 zeta2 ->
  CFGKATStrongStep aut aut [y] [y] R a x1 x2.
Proof.
  intros Hraw1 Hraw2 Hlift.
  destruct (classic (exists p e' i',
                       zeta1 = CFGKATAutomatonNext p (e', i'))); [|
  destruct (classic (cfgkat_lifts_easy zeta1)) ].
  - destruct H as [p [e' [i' Hzeta1]]]; subst.
    dependent destruction Hlift.
    eapply CFGKATStrongStepNext; eauto.
    + apply Hlift_next; eauto.
    + apply Hlift_next; eauto.
  - eapply CFGKATStrongStepHalt with (zeta := zeta1).
    + destruct zeta1; try now simpl in *.
      destruct s. exfalso. apply H. now repeat eexists.
    + apply Hlift_easy; eauto.
    + apply Hlift_easy; eauto.
      erewrite lifted_relation_transpose_halting; eauto.
      destruct zeta1; try now simpl in *.
      destruct s. apply H. now repeat eexists.
  - destruct zeta1; try now simpl in *.
    dependent destruction Hlift.
    destruct (y l i) as [s|] eqn:Hbind.
    + eapply CFGKATStrongStepSilent; eauto;
      eapply CFGKATSilentBoundJump with (ys := []); eauto.
    + eapply CFGKATStrongStepHalt
        with (zeta := CFGKATAutomatonJump l i).
      * now simpl.
      * apply Hlift_free_jump; eauto.
      * apply Hlift_free_jump; eauto.
Qed.

Program Definition base_bisim_lifted_once_strong
  (E : label_environment CFGKATExpression)
  (l : Label)
  (x : CFGKATExpression)
  (Hfresh : label_fresh E l)
  (R_base : CFGKATAutomatonBisimulation
             (resolve_list CFGKATExpressionAutomaton [lift E])
             (resolve_list CFGKATExpressionAutomaton [lift E]))
  : @CFGKATStrongBisimulation
      (resolve_list CFGKATExpressionAutomaton [lift E])
      (resolve_list CFGKATExpressionAutomaton [lift E])
      [lift (E ## l # x)]
      [lift (E ## l # x)]
 := {|
   cfgkat_strong_relation := relation_or_eq (cfgkat_relation R_base)
|}.
Next Obligation.
  intros E l e Hfresh R_base x1 x2 a Hrel.
  destruct (cfgkat_synt_dynamics_total
    (resolve_list CFGKATExpressionAutomaton [lift E]) x1 a)
    as [zeta1 Htr1].
  destruct (cfgkat_synt_dynamics_total
    (resolve_list CFGKATExpressionAutomaton [lift E]) x2 a)
    as [zeta2 Htr2].
  destruct Hrel as [Hbase | Heq].
  -
    eapply lifted_relation_to_strong_step_same_env; eauto.
    + intro s. now right.
    + eapply lifted_relation_mono.
      * intros. left; eauto.
      * eapply (cfgkat_bisimulation_step R_base); eauto.
  - destruct Heq.
    eapply lifted_relation_to_strong_step_same_env; eauto.
    + intro s. right. reflexivity.
    + apply lifted_relation_refl.
      intro s. right. reflexivity.
Qed.

Definition base_bisim_lifted_once
  (E : label_environment CFGKATExpression)
  (l : Label)
  (x : CFGKATExpression)
  (Hfresh : label_fresh E l)
  (R_base : CFGKATAutomatonBisimulation
             (resolve_list CFGKATExpressionAutomaton [lift E])
             (resolve_list CFGKATExpressionAutomaton [lift E])) :=
  strong_bisim_to_bisim
    [lift (E ## l # x)]
    [lift (E ## l # x)]
    (base_bisim_lifted_once_strong
       E l x Hfresh R_base).

Program Definition C1_bisim
  (E : label_environment CFGKATExpression)
  (l : Label)
  (x : CFGKATExpression)
  (Hfresh : label_fresh E l)
  (R_base : CFGKATAutomatonBisimulation
             (resolve_list CFGKATExpressionAutomaton [lift E])
             (resolve_list CFGKATExpressionAutomaton [lift E]))
:=
  let middle := resolve_list
    CFGKATExpressionAutomaton [lift E; lift (E ## l # x)] in
  bisim_trans_syntactic_middle middle
    (sup_sys_sol_sub_sys_synt_bisim E l x Hfresh)
    (bisim_trans_syntactic_middle middle
      (base_bisim_lifted_once E l x Hfresh R_base)
      (bisim_sym (sup_sys_sol_sub_sys_synt_bisim E l x Hfresh))).

Theorem C1_sound:
  forall e f i x E l,
  (e, i) ~[lift E] (f, i) ->
  forall (H: label_fresh E l),
  (e, i) ~[lift (E ## l # x)] (f, i).
Proof.
  intros e f i x E l Hbisim H.
  destruct Hbisim as [R_base HR_base].
  exists (C1_bisim E l x H R_base).
  exists (e, i). simpl in *; intuition.
  exists (f, i). simpl in *; intuition.
  now left.
Qed.

Definition C3_side_condition
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  (F : label_environment CFGKATExpression)
  : Prop :=
  forall l,
    label_in_dom F l ->
    (forall k body, E k = Some body -> ~ contains_goto l body) /\
    ~ contains_goto l e.

Definition C3_safe
  (F : label_environment CFGKATExpression)
  (s : CFGKATSyntConfiguration)
  : Prop :=
  let (e, _) := s in no_goto_expr e F.

Definition C3_relation
  (F : label_environment CFGKATExpression)
  (s1 s2: CFGKATSyntConfiguration) :=
  s1 = s2 /\ C3_safe F s1.

Program Definition C3_strong
  (E F : label_environment CFGKATExpression)
  (Hdisj : label_disjoint E F)
  (Henv : no_goto_env E F)
  : @CFGKATStrongBisimulation
      CFGKATExpressionAutomaton
      CFGKATExpressionAutomaton
      [lift E]
      [lift (E + F)]
  := {| cfgkat_strong_relation := C3_relation F |}.
Next Obligation.
  intros E F Hdisj Henv s1 s2 a [Heq Hsafe]. subst s2.
  destruct (cfgkat_synt_dynamics_total CFGKATExpressionAutomaton s1 a)
    as [zeta Hz].
  destruct (classic (cfgkat_lifts_easy zeta)); [
  destruct (classic (exists p e' i',
                       zeta = CFGKATAutomatonNext p (e', i'))) |].
  - destruct H0 as [p [e' [i' Hzeta]]]. subst.
    eapply CFGKATStrongStepNext.
    + eapply Hlift_next; eauto.
    + eapply Hlift_next; eauto.
    + split; auto.
      destruct s1 as [c i0].
      eapply no_goto_expr_next; eauto.
  - eapply CFGKATStrongStepHalt with (zeta := zeta).
    + destruct zeta; try now simpl in *.
      destruct s. exfalso. apply H0. repeat eexists.
    + eapply Hlift_easy; eauto.
    + eapply Hlift_easy; eauto.
  - destruct zeta; try now simpl in *.
    destruct (lift E l i) as [s_old |] eqn:Hold.
    +
      eapply lift_plus_some in Hold as Hnew; eauto.
      eapply CFGKATStrongStepSilent with (x1' := s_old) (x2' := s_old).
      * eapply CFGKATSilentBoundJump with (ys := []); eauto.
      * eapply CFGKATSilentBoundJump with (ys := []); eauto.
      * split; auto. simpl in Hold.
        destruct (E l) as [ek |] eqn:HEk; try discriminate.
        inversion_clear Hold.
        eapply Henv; eauto.
    +
      destruct (lift (E + F) l i) as [s_new |] eqn:Hnew.
      * exfalso. destruct s1.
        eapply no_goto_expr_no_jump; eauto.
  	    simpl in Hold, Hnew.
  	    destruct (E l) as [ek |] eqn:HEk; try discriminate.
  	    destruct (F l) as [fk |] eqn:HFk; try discriminate.
  	    now exists fk.
      * eapply CFGKATStrongStepHalt with
          (zeta := CFGKATAutomatonJump l i).
        -- constructor.
        -- eapply Hlift_free_jump; eauto.
        -- eapply Hlift_free_jump with (ys := [lift (E + F)]); eauto.
Qed.

Definition C3_bisim
  (E F : label_environment CFGKATExpression)
  (Hdisj : label_disjoint E F)
  (Henv : no_goto_env E F)
  : CFGKATAutomatonBisimulation
      (resolve_list CFGKATExpressionAutomaton [lift E])
      (resolve_list CFGKATExpressionAutomaton [lift (E + F)]) :=
	  strong_bisim_to_bisim
	    [lift E]
	    [lift (E + F)]
	    (C3_strong E F Hdisj Henv).

Theorem C3_sound :
  forall
    (e : CFGKATExpression)
    (E F : label_environment CFGKATExpression)
    `{label_disjoint E F},
    C3_side_condition E e F ->
    forall i,
      (e, i) ~[lift (E + F), lift E] (e, i).
Proof.
  intros e E F Hdisj Hside i.
  unshelve eexists.
  - apply bisim_sym, C3_bisim.
    intros k body Hbody l Hdom.
    destruct (Hside l Hdom) as [Henv _].
    exact (Henv k body Hbody).
  - simpl. unfold C3_relation. intuition.
    intros l Hdom.
    now destruct (Hside l Hdom).
Qed.

Local Lemma replacement_strong_step_from_lifted_outputs
  (E : label_environment CFGKATExpression)
  (l : Label)
  (e1 e2 : CFGKATExpression)
  (H1 H2 : label_fresh E l)
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (HR_l : forall i, R (e1, i) (e2, i))
  (HR_refl : forall s, R s s)
  :
  forall x1 x2 a zeta1 zeta2,
    cfgkat_synt_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      x1 a zeta1 ->
    cfgkat_synt_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      x2 a zeta2 ->
    lifted_relation R zeta1 zeta2 ->
    CFGKATStrongStep
		      (resolve_list CFGKATExpressionAutomaton [lift E])
		      (resolve_list CFGKATExpressionAutomaton [lift E])
		      [lift ((let Hfresh := H1 in E ## l # e1))]
		      [lift ((let Hfresh := H2 in E ## l # e2))]
      R
      a x1 x2.
Proof.
  intros x1 x2 a zeta1 zeta2 Htr1 Htr2 H.
  inversion H; subst.

  - strong_halt_output
      (@CFGKATAutomatonReject CFGKATSyntConfiguration) Htr1 Htr2.
  - strong_halt_output
      (@CFGKATAutomatonAccept CFGKATSyntConfiguration i) Htr1 Htr2.
  - strong_halt_output
      (@CFGKATAutomatonBreak CFGKATSyntConfiguration i) Htr1 Htr2.
  - strong_halt_output
      (@CFGKATAutomatonContinue CFGKATSyntConfiguration i) Htr1 Htr2.

  -
    destruct (Label_eq_dec l l0) as [Heq_l | Hneq_l].

    + subst l0.
      eapply CFGKATStrongStepSilent with
        (x1' := (e1, i))
        (x2' := (e2, i)).
		      * eapply CFGKATSilentBoundJump with (ys := []).
		        -- simpl. exact Htr1.
		        -- apply lift_label_extend_same.
		      * eapply CFGKATSilentBoundJump with (ys := []).
		        -- simpl. exact Htr2.
		        -- apply lift_label_extend_same.
      * apply HR_l.

    + destruct (E l0) as [eold |] eqn:HEold.

      * eapply CFGKATStrongStepSilent with
          (x1' := (eold, i))
          (x2' := (eold, i)).
		        -- eapply CFGKATSilentBoundJump with (ys := []).
		           ++ simpl. exact Htr1.
		           ++ eapply lift_label_extend_other_some; eauto.
		        -- eapply CFGKATSilentBoundJump with (ys := []).
		           ++ simpl. exact Htr2.
		           ++ eapply lift_label_extend_other_some; eauto.
        -- apply HR_refl.

      * eapply CFGKATStrongStepHalt with
          (zeta := CFGKATAutomatonJump l0 i).
        -- simpl. constructor.
        -- eapply Hlift_free_jump.
		           ++ exact Htr1.
			           ++ constructor.
			              ** eapply lift_label_extend_other_none; eauto.
			              ** constructor.
	        -- eapply Hlift_free_jump with (ys := [lift (let Hfresh : label_fresh E l := H2 in E ## l # e2)]).
		           ++ exact Htr2.
			           ++ constructor.
			              ** eapply lift_label_extend_other_none; eauto.
			              ** constructor.

  - strong_halt_output
      (@CFGKATAutomatonReturn CFGKATSyntConfiguration) Htr1 Htr2.

  -
    eapply CFGKATStrongStepNext.
    + lift_raw_transition Htr1.
    + lift_raw_transition Htr2.
    + exact H0.
Qed.
Definition replacement_lifted_once_strong
  (E : label_environment CFGKATExpression)
  (l : Label)
  (e1 e2 : CFGKATExpression)
  (H1 H2 : label_fresh E l)
  (R_base : CFGKATAutomatonBisimulation
             (resolve_list CFGKATExpressionAutomaton [lift E])
             (resolve_list CFGKATExpressionAutomaton [lift E]))
  (HR_l : forall i, cfgkat_relation R_base (e1, i) (e2, i))
	  : @CFGKATStrongBisimulation
	      (resolve_list CFGKATExpressionAutomaton [lift E])
	      (resolve_list CFGKATExpressionAutomaton [lift E])
	      [lift ((let Hfresh := H1 in E ## l # e1))]
	      [lift ((let Hfresh := H2 in E ## l # e2))].
Proof.
  unshelve econstructor.

  - exact (relation_or_eq (cfgkat_relation R_base)).

  - intros x1 x2 a Hrel.
    destruct Hrel as [Hbase | Heq].

    +
      destruct (cfgkat_synt_dynamics_total
        (resolve_list CFGKATExpressionAutomaton [lift E]) x1 a)
        as [zeta1 Htr1].
      destruct (cfgkat_synt_dynamics_total
        (resolve_list CFGKATExpressionAutomaton [lift E]) x2 a)
        as [zeta2 Htr2].

	      eapply (replacement_strong_step_from_lifted_outputs
          E l e1 e2 H1 H2
          (relation_or_eq (cfgkat_relation R_base))
          (fun i0 => or_introl (HR_l i0))
          (fun s => or_intror eq_refl)
          x1 x2 a zeta1 zeta2).
	      * exact Htr1.
	      * exact Htr2.
	      *
	        pose proof
	          (cfgkat_bisimulation_step
             R_base
             x1 x2 a
             zeta1 zeta2
             Hbase Htr1 Htr2) as Hlb.

        change
          (@lifted_relation
             CFGKATSyntConfiguration
             CFGKATSyntConfiguration
             (cfgkat_relation R_base)
             zeta1 zeta2)
          in Hlb.

        eapply lifted_relation_mono.
        -- intros u v Huv.
           left.
           exact Huv.
        -- exact Hlb.

    +
      subst x2.

      destruct (cfgkat_synt_dynamics_total
        (resolve_list CFGKATExpressionAutomaton [lift E]) x1 a)
        as [zeta Htr].

	      eapply (replacement_strong_step_from_lifted_outputs
          E l e1 e2 H1 H2
          (relation_or_eq (cfgkat_relation R_base))
          (fun i0 => or_introl (HR_l i0))
          (fun s => or_intror eq_refl)
          x1 x1 a zeta zeta).
	      * exact Htr.
	      * exact Htr.
	      *
	        apply lifted_relation_refl.
        intro s.
        right.
        reflexivity.
Defined.
Definition replacement_lifted_once
  (E : label_environment CFGKATExpression)
  (l : Label)
  (e1 e2 : CFGKATExpression)
  (H1 H2 : label_fresh E l)
  (R_base : CFGKATAutomatonBisimulation
             (resolve_list CFGKATExpressionAutomaton [lift E])
             (resolve_list CFGKATExpressionAutomaton [lift E]))
  (HR_l : forall i, cfgkat_relation R_base (e1, i) (e2, i))
	  : CFGKATAutomatonBisimulation
	      (resolve_list CFGKATExpressionAutomaton
	         [lift E; lift ((let Hfresh := H1 in E ## l # e1))])
	      (resolve_list CFGKATExpressionAutomaton
	         [lift E; lift ((let Hfresh := H2 in E ## l # e2))]).
Proof.
  change
    (CFGKATAutomatonBisimulation
      (resolve_list
         (resolve_list CFGKATExpressionAutomaton [lift E])
         [lift ((let Hfresh := H1 in E ## l # e1))])
      (resolve_list
         (resolve_list CFGKATExpressionAutomaton [lift E])
         [lift ((let Hfresh := H2 in E ## l # e2))])).

  exact
	    (strong_bisim_to_bisim
	      [lift ((let Hfresh := H1 in E ## l # e1))]
	      [lift ((let Hfresh := H2 in E ## l # e2))]
	      (replacement_lifted_once_strong
	         E l e1 e2 H1 H2 R_base HR_l)).
Defined.
Definition replacement_bisim
  (E : label_environment CFGKATExpression)
  (l : Label)
  (e1 e2 : CFGKATExpression)
  (H1 H2 : label_fresh E l)
  (R_base : CFGKATAutomatonBisimulation
             (resolve_list CFGKATExpressionAutomaton [lift E])
             (resolve_list CFGKATExpressionAutomaton [lift E]))
  (HR_l : forall i, cfgkat_relation R_base (e1, i) (e2, i))
  : CFGKATAutomatonBisimulation
      (resolve_list CFGKATExpressionAutomaton
        [lift ((let Hfresh := H1 in E ## l # e1))])
      (resolve_list CFGKATExpressionAutomaton
        [lift ((let Hfresh := H2 in E ## l # e2))]).
Proof.
  set (E1 := (let Hfresh := H1 in E ## l # e1)).
  set (E2 := (let Hfresh := H2 in E ## l # e2)).
  eapply (bisim_trans_syntactic_middle
    (resolve_list CFGKATExpressionAutomaton [lift E; lift E1])).
  - exact (sup_sys_sol_sub_sys_synt_bisim E l e1 H1).
  - eapply (bisim_trans_syntactic_middle
      (resolve_list CFGKATExpressionAutomaton [lift E; lift E2])).
    + exact (replacement_lifted_once E l e1 e2 H1 H2 R_base HR_l).
    + exact (bisim_sym
        (sup_sys_sol_sub_sys_synt_bisim E l e2 H2)).
Defined.
Theorem C2_sound :
  forall
    (e e1 e2 : CFGKATExpression)
    (E : label_environment CFGKATExpression)
    (l : Label),
    (forall i, (e1, i) ~[lift E] (e2, i)) ->
    forall
      (H1 : label_fresh E l)
      (H2 : label_fresh E l),
	    forall i,
	      (e, i) ~[
	        lift ((let Hfresh := H1 in E ## l # e1)),
	        lift ((let Hfresh := H2 in E ## l # e2))
	      ] (e, i).
Proof.
  intros e e1 e2 E l Hbisim H1 H2 i.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar in *.

  pose (R_base :=
    (@automaton_bisimilarity_bisim
       (resolve_list CFGKATExpressionAutomaton [lift E])
       (resolve_list CFGKATExpressionAutomaton [lift E]))).

  assert (HR_l : forall j, cfgkat_relation R_base (e1, j) (e2, j)).
  {
    intro j.
    unfold R_base.
    destruct (Hbisim j) as [Rj HRj].
    exists Rj.
    exact HRj.
  }

  exists (replacement_bisim E l e1 e2 H1 H2 R_base HR_l).

  unfold replacement_bisim.

  exists (e, i).
  split.
  - unfold sup_sys_sol_sub_sys_synt_bisim.
    unfold strong_bisim_to_bisim.
    reflexivity.

  - exists (e, i).
    split.
    + cbn.
      right.
      reflexivity.
    + cbn.
      unfold sup_sys_sol_sub_sys_synt_bisim.
      unfold strong_bisim_to_bisim.
      reflexivity.
Qed.



Definition substitution_relation
  (l : Label)
  (e1 : CFGKATExpression)
  : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop :=
  fun s1 s2 =>
    s1 = s2 \/
    exists e i,
      s1 = (e <[ l <- e1 ]>, i) /\
      s2 = (e, i) /\
      RHS l e.

Lemma subst_goto_no_goto :
  forall l e1 e,
    Expm_r l e ->
    e <[ l <- e1 ]> = e.
Proof.
  intros l e1 e.
  induction e as
    [b | p | x v | | | | k | b eL IHL eR IHR
     | eL IHL eR IHR | eL IHL eR IHR | b e IH];
    unfold Expm_r;
    simpl;
    intro Hng;
    try reflexivity.

  - destruct (Label_eq_dec k l) as [Heq | Hneq].
    + subst. exfalso. apply Hng. reflexivity.
    + reflexivity.

  - rewrite IHL.
    + rewrite IHR.
      * reflexivity.
      * intro Hc. apply Hng. right. exact Hc.
    + intro Hc. apply Hng. left. exact Hc.

  - rewrite IHL.
    + rewrite IHR.
      * reflexivity.
      * intro Hc. apply Hng. right. exact Hc.
    + intro Hc. apply Hng. left. exact Hc.

  - rewrite IHL.
    + rewrite IHR.
      * reflexivity.
      * intro Hc. apply Hng. right. exact Hc.
    + intro Hc. apply Hng. left. exact Hc.

  - rewrite IH.
    + reflexivity.
    + exact Hng.
Qed.

Local Lemma lifted_relation_substitution_relation_refl :
  forall l e1 zeta,
    lifted_relation (substitution_relation l e1) zeta zeta.
Proof.
  intros l e1 zeta.
  apply lifted_relation_refl.
  intro s.
  unfold substitution_relation.
  left.
  reflexivity.
Qed.

Local Lemma C5_resolved_functional :
  forall E l e1 (H : label_fresh E l) s,
    cfgkat_automaton_dynamics_functional
      (cfgkat_transitions
        (resolve_list CFGKATExpressionAutomaton
          [lift (E ## l # e1)]) s).
Proof.
  intros E l e1 H s.
  apply resolve_list_dynamics_functional.
Qed.

Local Lemma C5_same_dynamics_refl_output
  (E : label_environment CFGKATExpression)
  (l : Label)
  (e1 source target : CFGKATExpression)
  (Hfresh : label_fresh E l)
  (i : IndicatorAssignment)
  (a : Atom)
  (zeta : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  (forall r,
    CFGKATExpressionDynamics (source, i) a r <->
    CFGKATExpressionDynamics (target, i) a r) ->
  cfgkat_transitions
    (resolve_list CFGKATExpressionAutomaton [lift (E ## l # e1)])
    (source, i) a zeta ->
  exists zeta',
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift (E ## l # e1)])
      (target, i) a zeta' /\
    lifted_relation (substitution_relation l e1) zeta zeta'.
Proof.
  intros Hequiv Hz.
  exists zeta.
  split.
  - pose proof
      (resolve_list_same_dynamics
        [lift (E ## l # e1)]
        CFGKATExpressionAutomaton
        (source, i)
        (target, i)
        a
        Hequiv
        zeta) as Hsame.
    exact (proj1 Hsame Hz).
  - apply lifted_relation_substitution_relation_refl.
Qed.

Ltac C5_sequence_same_by_prefix Hg :=
  intro r;
  match type of Hg with
  | CFGKATExpressionDynamics (?g, ?i) ?a CFGKATAutomatonReject =>
      eapply (sequence_same_forced_output
        g _ _ i a CFGKATAutomatonReject);
      intro tail; apply CFGKATExpressionDynamicsSequenceReject; exact Hg
  | CFGKATExpressionDynamics (?g, ?i) ?a CFGKATAutomatonReturn =>
      eapply (sequence_same_forced_output
        g _ _ i a CFGKATAutomatonReturn);
      intro tail; apply CFGKATExpressionDynamicsSequenceReturn; exact Hg
  | CFGKATExpressionDynamics (?g, ?i) ?a (CFGKATAutomatonBreak ?i') =>
      eapply (sequence_same_forced_output
        g _ _ i a (CFGKATAutomatonBreak i'));
      intro tail; apply CFGKATExpressionDynamicsSequenceBreak; exact Hg
  | CFGKATExpressionDynamics (?g, ?i) ?a (CFGKATAutomatonContinue ?i') =>
      eapply (sequence_same_forced_output
        g _ _ i a (CFGKATAutomatonContinue i'));
      intro tail; apply CFGKATExpressionDynamicsSequenceContinue; exact Hg
  | CFGKATExpressionDynamics (?g, ?i) ?a (CFGKATAutomatonJump ?l ?i') =>
      eapply (sequence_same_forced_output
        g _ _ i a (CFGKATAutomatonJump l i'));
      intro tail; apply CFGKATExpressionDynamicsSequenceJump; exact Hg
  end.

Ltac C5_loopseq_same_by_prefix Hg :=
  intro r;
  match type of Hg with
  | CFGKATExpressionDynamics (?g, ?i) ?a CFGKATAutomatonReject =>
      eapply (loopseq_same_forced_output
        g _ _ i a CFGKATAutomatonReject);
      intro tail; apply CFGKATExpressionDynamicsLoopSeqReject; exact Hg
  | CFGKATExpressionDynamics (?g, ?i) ?a CFGKATAutomatonReturn =>
      eapply (loopseq_same_forced_output
        g _ _ i a CFGKATAutomatonReturn);
      intro tail; apply CFGKATExpressionDynamicsLoopSeqReturn; exact Hg
  | CFGKATExpressionDynamics (?g, ?i) ?a (CFGKATAutomatonBreak ?i') =>
      eapply (loopseq_same_forced_output
        g _ _ i a (CFGKATAutomatonAccept i'));
      intro tail; apply CFGKATExpressionDynamicsLoopSeqBreak; exact Hg
  | CFGKATExpressionDynamics (?g, ?i) ?a (CFGKATAutomatonJump ?l ?i') =>
      eapply (loopseq_same_forced_output
        g _ _ i a (CFGKATAutomatonJump l i'));
      intro tail; apply CFGKATExpressionDynamicsLoopSeqJump; exact Hg
  end.

Ltac C5_tail_case E l e1 Hfresh IH tail_i a zeta Hz
    left_equiv right_equiv :=
  pose proof
    (resolve_list_same_dynamics
      [lift (E ## l # e1)]
      CFGKATExpressionAutomaton
      _ _
      a
      left_equiv
      zeta) as Hleft;
  destruct (IH E Hfresh tail_i a zeta (proj1 Hleft Hz))
    as [zeta' [Hzeta' Hlift]];
  exists zeta';
  split;
  [ pose proof
      (resolve_list_same_dynamics
        [lift (E ## l # e1)]
        CFGKATExpressionAutomaton
        _ _
        a
      right_equiv
      zeta') as Hright;
	  exact (proj2 Hright Hzeta')
	  | exact Hlift ].

Ltac C5_same_sequence_case E l e1 Hfresh Hz Hprefix :=
  eapply (C5_same_dynamics_refl_output E l e1 _ _ Hfresh _ _ _);
    [ C5_sequence_same_by_prefix Hprefix | exact Hz ].

Ltac C5_same_loopseq_case E l e1 Hfresh Hz Hprefix :=
  eapply (C5_same_dynamics_refl_output E l e1 _ _ Hfresh _ _ _);
    [ C5_loopseq_same_by_prefix Hprefix | exact Hz ].

Lemma C5_no_goto_next :
  forall l g i a p g' i',
    Expm_r l g ->
    CFGKATExpressionDynamics (g, i) a
      (CFGKATAutomatonNext p (g', i')) ->
    Expm_r l g'.
Proof.
  intros l g i a p g' i' Hng Hnext.
  intro Hcontains.
  apply Hng.
  eapply contains_goto_next_back; eauto.
Qed.

Local Lemma C5_simulation :
  forall e e1 E l (H : label_fresh E l) i a zeta,
    RHS l e ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton
        [lift (E ## l # e1)])
      (e <[ l <- e1 ]>, i) a zeta ->
    exists zeta',
      cfgkat_transitions
        (resolve_list CFGKATExpressionAutomaton
          [lift (E ## l # e1)])
        (e, i) a zeta' /\
      lifted_relation (substitution_relation l e1) zeta zeta'.
Proof.
  intros e e1 E l H i a zeta HRHS.
  revert E H i a zeta.
  induction HRHS; intros E Hfresh i a zeta Hz.

  - simpl in Hz.
    destruct (Label_eq_dec l l) as [_ | Hneq].
    + exists zeta.
	      split.
	      * eapply (Hlift_bound_jump
              [lift (E ## l # e1)]
              CFGKATExpressionAutomaton
              (goto l, i)
              a
              i
              l
              (e1, i)
              zeta).
	        -- simpl.
	           apply CFGKATExpressionDynamicsGoto.
        -- apply first_binding_head.
           apply lift_label_extend_same.
        -- exact Hz.
      * apply lifted_relation_substitution_relation_refl.
    + contradiction Hneq. reflexivity.

  - rewrite subst_goto_no_goto in Hz.
    + exists zeta.
      split.
      * exact Hz.
      * apply lifted_relation_substitution_relation_refl.
    + exact H.

  - destruct (classic (eval_test b a i)) as [Hb | Hb].
    + C5_tail_case E l e1 Hfresh IHHRHS1 i a zeta Hz
        (choice_left_dynamics_iff
           b (h <[ l <- e1 ]>) (f <[ l <- e1 ]>) i a Hb)
        (choice_left_dynamics_iff b h f i a Hb).
    + C5_tail_case E l e1 Hfresh IHHRHS2 i a zeta Hz
        (choice_right_dynamics_iff
           b (h <[ l <- e1 ]>) (f <[ l <- e1 ]>) i a Hb)
        (choice_right_dynamics_iff b h f i a Hb).

  - simpl in Hz.
    rewrite (subst_goto_no_goto l e1 g H) in Hz.
    destruct (cfgkat_expression_dynamics_total (g, i) a)
        as [zg Hzg].
      destruct zg as
        [ | iacc | ibreak | icontinue | | ljump ijump | pnext snext ].

      all: try solve [C5_same_sequence_case E l e1 Hfresh Hz Hzg].
      * C5_tail_case E l e1 Hfresh IHHRHS iacc a zeta Hz
          (sequence_accept_iff g (h <[ l <- e1 ]>) i iacc a Hzg)
          (sequence_accept_iff g h i iacc a Hzg).

      * destruct snext as [g' i'].
        assert (Hz_expected :
          cfgkat_transitions
            (resolve_list CFGKATExpressionAutomaton
              [lift (E ## l # e1)])
            (g ;; h <[ l <- e1 ]>, i) a
            (CFGKATAutomatonNext pnext (g' ;; h <[ l <- e1 ]>, i'))).
        {
          apply Hlift_next.
          eapply CFGKATExpressionDynamicsSequenceNext.
          exact Hzg.
        }
        pose proof
          (C5_resolved_functional E l e1 Hfresh
            (g ;; h <[ l <- e1 ]>, i)
            a zeta
            (CFGKATAutomatonNext pnext (g' ;; h <[ l <- e1 ]>, i'))
            Hz Hz_expected) as Heq.
        subst zeta.
        exists (CFGKATAutomatonNext pnext (g' ;; h, i')).
        split.
        -- apply Hlift_next.
           eapply CFGKATExpressionDynamicsSequenceNext.
           exact Hzg.
        -- constructor.
           right.
           exists (g' ;; h), i'.
           split.
           ++ simpl.
              assert (Hg' : Expm_r l g').
              {
                eapply C5_no_goto_next.
                - exact H.
                - exact Hzg.
              }
              rewrite (subst_goto_no_goto l e1 g' Hg').
              reflexivity.
           ++ split.
              ** reflexivity.
              ** apply RHS_sequence.
                 --- eapply C5_no_goto_next.
                     + exact H.
                     + exact Hzg.
                 --- exact HRHS.

  - simpl in Hz.
    rewrite (subst_goto_no_goto l e1 g H) in Hz.
    destruct (cfgkat_expression_dynamics_total (g, i) a)
        as [zg Hzg].
      destruct zg as
        [ | iacc | ibreak | icontinue | | ljump ijump | pnext snext ].

      all: try solve [C5_same_loopseq_case E l e1 Hfresh Hz Hzg].
      * C5_tail_case E l e1 Hfresh IHHRHS iacc a zeta Hz
          (loopseq_accept_tail_dynamics
            g (h <[ l <- e1 ]>) i iacc a Hzg)
          (loopseq_accept_tail_dynamics g h i iacc a Hzg).

      * C5_tail_case E l e1 Hfresh IHHRHS icontinue a zeta Hz
          (loopseq_continue_tail_dynamics
            g (h <[ l <- e1 ]>) i icontinue a Hzg)
          (loopseq_continue_tail_dynamics g h i icontinue a Hzg).

      * destruct snext as [g' i'].
        assert (Hz_expected :
          cfgkat_transitions
            (resolve_list CFGKATExpressionAutomaton
              [lift (E ## l # e1)])
            (g |> h <[ l <- e1 ]>, i) a
            (CFGKATAutomatonNext pnext (g' |> h <[ l <- e1 ]>, i'))).
        {
          apply Hlift_next.
          eapply CFGKATExpressionDynamicsLoopSeqNext.
          exact Hzg.
        }
        pose proof
          (C5_resolved_functional E l e1 Hfresh
            (g |> h <[ l <- e1 ]>, i)
            a zeta
            (CFGKATAutomatonNext pnext (g' |> h <[ l <- e1 ]>, i'))
            Hz Hz_expected) as Heq.
        subst zeta.
        exists (CFGKATAutomatonNext pnext (g' |> h, i')).
        split.
        -- apply Hlift_next.
           eapply CFGKATExpressionDynamicsLoopSeqNext.
           exact Hzg.
        -- constructor.
           right.
           exists (g' |> h), i'.
           split.
           ++ simpl.
              assert (Hg' : Expm_r l g').
              {
                eapply C5_no_goto_next.
                - exact H.
                - exact Hzg.
              }
              rewrite (subst_goto_no_goto l e1 g' Hg').
              reflexivity.
           ++ split.
              ** reflexivity.
              ** apply RHS_loopseq.
                 --- eapply C5_no_goto_next.
                     + exact H.
                     + exact Hzg.
                 --- exact HRHS.
Qed.

Definition C5_bisim
  (E : label_environment CFGKATExpression)
  (l : Label)
  (e1 : CFGKATExpression)
  (H : label_fresh E l)
  : CFGKATAutomatonBisimulation
      (resolve_list CFGKATExpressionAutomaton
        [lift (E ## l # e1)])
      (resolve_list CFGKATExpressionAutomaton
        [lift (E ## l # e1)]).
Proof.
  unshelve econstructor.
  - exact (substitution_relation l e1).
  - intros x1 x2 a zeta1 zeta2 Hrel Hz1 Hz2.
    destruct Hrel as [Heq | [e [i [Hx1 [Hx2 HRHS]]]]].
    + subst x2.
      pose proof
        (C5_resolved_functional E l e1 H x1
          a zeta1 zeta2 Hz1 Hz2) as Heqz.
      subst zeta2.
      apply lifted_relation_substitution_relation_refl.
    + subst x1 x2.
      destruct (C5_simulation e e1 E l H i a zeta1 HRHS Hz1)
        as [zeta2' [Hz2' Hlift]].
      pose proof
        (C5_resolved_functional E l e1 H (e, i)
          a zeta2 zeta2' Hz2 Hz2') as Heqz.
      subst zeta2'.
      exact Hlift.
Defined.

Theorem C5_sound :
  forall
    (e e1 : CFGKATExpression)
    (E : label_environment CFGKATExpression)
    (l : Label),
    RHS l e ->
    forall (H : label_fresh E l),
    forall i,
      (subst_goto l e1 e, i)
        ~[ lift (E ## l # e1),
           lift (E ## l # e1) ]
      (e, i).
Proof.
  intros e e1 E l HRHS H i.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar.
  exists (C5_bisim E l e1 H).
  right.
  exists e, i.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + exact HRHS.
Qed.


Definition rename_label
  (old new k : Label)
  : Label :=
  match Label_eq_dec k old with
  | left _ => new
  | right _ => k
  end.

Definition rename_config
  (old new : Label)
  (s : CFGKATSyntConfiguration)
  : CFGKATSyntConfiguration :=
  match s with
  | (e, i) => (rename_goto old new e, i)
  end.

Definition rename_output
  (old new : Label)
  (zeta : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : CFGKATAutomatonOutputs CFGKATSyntConfiguration :=
  match zeta with
  | CFGKATAutomatonReject => CFGKATAutomatonReject
  | CFGKATAutomatonAccept i => CFGKATAutomatonAccept i
  | CFGKATAutomatonBreak i => CFGKATAutomatonBreak i
  | CFGKATAutomatonContinue i => CFGKATAutomatonContinue i
  | CFGKATAutomatonReturn => CFGKATAutomatonReturn
  | CFGKATAutomatonJump k i =>
      CFGKATAutomatonJump (rename_label old new k) i
  | CFGKATAutomatonNext p s =>
      CFGKATAutomatonNext p (rename_config old new s)
  end.

Local Lemma rename_goto_finite_dynamics :
  forall old new e i a zeta,
    CFGKATExpressionFiniteDynamics (e, i) a zeta ->
    CFGKATExpressionFiniteDynamics
      (rename_goto old new e, i)
      a
      (rename_output old new zeta).
Proof.
  intros old new e i a zeta Hfin.
  dependent induction Hfin;
    cbn [rename_goto rename_output rename_config subst_goto rename_label].
  - apply CFGKATExpressionFiniteDynamicsAssertTrue. exact H.
  - apply CFGKATExpressionFiniteDynamicsAssign.
  - apply CFGKATExpressionFiniteDynamicsAction.
  - apply CFGKATExpressionFiniteDynamicsBreak.
  - apply CFGKATExpressionFiniteDynamicsContinue.
  - apply CFGKATExpressionFiniteDynamicsReturn.
  - destruct (Label_eq_dec l old) as [Heq | Hneq]; subst.
    + unfold rename_label.
      destruct (Label_eq_dec old old) as [_ | Hbad].
      * apply CFGKATExpressionFiniteDynamicsGoto.
      * contradiction Hbad. reflexivity.
    + unfold rename_label.
      destruct (Label_eq_dec l old) as [Heq | _].
      * contradiction Hneq.
      * apply CFGKATExpressionFiniteDynamicsGoto.
  - eapply CFGKATExpressionFiniteDynamicsChoiceLeft; eauto.
  - eapply CFGKATExpressionFiniteDynamicsChoiceRight; eauto.
  - eapply CFGKATExpressionFiniteDynamicsSequenceSkip; eauto.
  - eapply CFGKATExpressionFiniteDynamicsSequenceReject; eauto.
  - eapply CFGKATExpressionFiniteDynamicsSequenceReturn; eauto.
  - eapply CFGKATExpressionFiniteDynamicsSequenceBreak; eauto.
  - eapply CFGKATExpressionFiniteDynamicsSequenceContinue; eauto.
  - eapply CFGKATExpressionFiniteDynamicsSequenceJump; eauto.
  - eapply CFGKATExpressionFiniteDynamicsSequenceNext; eauto.
  - eapply CFGKATExpressionFiniteDynamicsLoopSeqSkip; eauto.
  - eapply CFGKATExpressionFiniteDynamicsLoopSeqReject; eauto.
  - eapply CFGKATExpressionFiniteDynamicsLoopSeqReturn; eauto.
  - eapply CFGKATExpressionFiniteDynamicsLoopSeqBreak; eauto.
  - eapply CFGKATExpressionFiniteDynamicsLoopSeqContinue; eauto.
  - eapply CFGKATExpressionFiniteDynamicsLoopSeqJump; eauto.
  - eapply CFGKATExpressionFiniteDynamicsLoopSeqNext; eauto.
  - eapply CFGKATExpressionFiniteDynamicsLoopGuardTrue.
    + exact H.
    + exact (IHHfin (e0 |> while b do e0) i eq_refl).
  - eapply CFGKATExpressionFiniteDynamicsLoopGuardFalse; eauto.
Qed.

Local Lemma rename_goto_roundtrip_no_new :
  forall old new e,
    ~ contains_goto new e ->
    rename_goto new old (rename_goto old new e) = e.
Proof.
  intros old new e.
  induction e as
    [b | p | x v | | | | k | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b e IH];
    intro Hnone; cbn [rename_goto subst_goto contains_goto] in *;
    try reflexivity.
  - destruct (Label_eq_dec k old) as [Heq_old | Hneq_old]; subst.
    + destruct (Label_eq_dec old new) as [Heq | Hneq].
	      * subst. contradiction Hnone. reflexivity.
	      * destruct (Label_eq_dec new new) as [_ | Hbad].
	        -- cbn [rename_goto subst_goto].
	           destruct (Label_eq_dec new new) as [_ | Hbad].
	           ++ reflexivity.
	           ++ contradiction Hbad. reflexivity.
	        -- contradiction Hbad. reflexivity.
	    + destruct (Label_eq_dec k new) as [Heq_new | Hneq_new].
	      * subst. contradiction Hnone. reflexivity.
	      * cbn [rename_goto subst_goto].
	        destruct (Label_eq_dec k new) as [Hbad | _].
	        -- contradiction Hneq_new.
	        -- reflexivity.
  - f_equal.
    + apply IH1. intro Hc; apply Hnone; left; exact Hc.
    + apply IH2. intro Hc; apply Hnone; right; exact Hc.
  - f_equal.
    + apply IH1. intro Hc; apply Hnone; left; exact Hc.
    + apply IH2. intro Hc; apply Hnone; right; exact Hc.
  - f_equal.
    + apply IH1. intro Hc; apply Hnone; left; exact Hc.
    + apply IH2. intro Hc; apply Hnone; right; exact Hc.
  - f_equal.
    apply IH. exact Hnone.
Qed.

Local Lemma rename_goto_dynamics_output :
  forall old new e i a zeta,
    ~ contains_goto new e ->
    CFGKATExpressionDynamics (e, i) a zeta ->
    CFGKATExpressionDynamics
      (rename_goto old new e, i)
      a
      (rename_output old new zeta).
Proof.
  intros old new e i a zeta Hnonew Hdyn.
  inversion Hdyn; subst.
  - apply CFGKATExpressionDynamicsFinite.
    now apply rename_goto_finite_dynamics.
  - cbn [rename_output].
    apply CFGKATExpressionDynamicsDefaultReject.
    intros zeta' Hfin.
    pose proof
      (rename_goto_finite_dynamics new old
        (rename_goto old new e) i a zeta' Hfin) as Hback.
    rewrite rename_goto_roundtrip_no_new in Hback by exact Hnonew.
    unfold CFGKATExpressionNoFiniteResult in H.
    eapply H. exact Hback.
Qed.

Local Lemma rename_goto_dynamics :
  forall old new e i a sigma,
    CFGKATExpressionDynamics
      (e, i)
      a
      (CFGKATAutomatonJump old sigma) ->
    CFGKATExpressionDynamics
      (rename_goto old new e, i)
      a
      (CFGKATAutomatonJump new sigma).
Proof.
  intros old new e i a sigma Hdyn.
  inversion Hdyn; subst.
  apply CFGKATExpressionDynamicsFinite.
  pose proof
    (rename_goto_finite_dynamics old new e i a
      (CFGKATAutomatonJump old sigma) H) as Hrenamed.
  cbn [rename_output] in Hrenamed.
  unfold rename_label in Hrenamed.
  destruct (Label_eq_dec old old) as [_ | Hbad].
  - exact Hrenamed.
  - contradiction Hbad. reflexivity.
Qed.

Ltac lift_renamed_goto_output old new e i a Hnonew Hdyn :=
  match goal with
  | |- cfgkat_transitions _ _ _ ?output =>
      let Hrenamed := fresh "Hrenamed" in
      pose proof
        (rename_goto_dynamics_output old new e i a output Hnonew Hdyn)
        as Hrenamed;
      cbn [rename_output rename_config] in Hrenamed;
      lift_raw_transition Hrenamed
  end.

Ltac renamed_goto_halt_output output old new e i a Hnonew Hdyn :=
  eapply CFGKATStrongStepHalt with (zeta := output);
  [ simpl; constructor
  | lift_raw_transition Hdyn
  | lift_renamed_goto_output old new e i a Hnonew Hdyn ].

Ltac renamed_goto_current_halt_output old new e i a Hnonew Hdyn :=
  match type of Hdyn with
  | CFGKATExpressionDynamics _ _ (CFGKATAutomatonJump _ _) => fail
  | CFGKATExpressionDynamics _ _ (CFGKATAutomatonNext _ _) => fail
  | CFGKATExpressionDynamics _ _ ?output =>
      renamed_goto_halt_output output old new e i a Hnonew Hdyn
  end.

Definition C4_relation
  (old new : Label)
  : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop :=
  fun s1 s2 =>
    exists e i,
      s1 = (e, i) /\
      s2 = (rename_goto old new e, i) /\
      ~ contains_goto new e.

Local Lemma C4_strong_step_rename_output :
  forall E old new e i a zeta,
    label_rename_fresh E new ->
    (exists eold, E old = Some eold) ->
    ~ contains_goto new e ->
    CFGKATExpressionDynamics (e, i) a zeta ->
    CFGKATStrongStep
      CFGKATExpressionAutomaton
      CFGKATExpressionAutomaton
      [lift E]
      [lift (E <E[ old ~> new ]>)]
      (C4_relation old new)
      a
      (e, i)
      (rename_goto old new e, i).
Proof.
  intros E old new e i a zeta Hfresh Hdom Hnonew Hdyn.
  destruct Hfresh as [Hnew_not_dom Hnew_not_in].
  destruct Hdom as [eold Hold].
  destruct zeta as
    [ | iacc | ibreak | icont | | kjump ijump | p [enext inext] ].

  all: try solve [
    renamed_goto_current_halt_output old new e i a Hnonew Hdyn ].
  - simpl.
    destruct (Label_eq_dec kjump old) as [Hkold | Hkold].
    + subst kjump.
      pose proof (rename_goto_dynamics old new e i a ijump Hdyn) as Hrenamed.
      eapply CFGKATStrongStepSilent with
        (x1' := (eold, ijump))
        (x2' := (rename_goto old new eold, ijump)).
      * eapply CFGKATSilentBoundJump with (ys := []).
        -- simpl. exact Hdyn.
        -- apply lift_label_some. exact Hold.
      * eapply CFGKATSilentBoundJump with (ys := []).
        -- simpl. exact Hrenamed.
        -- apply lift_label_some.
           apply label_env_rename_new. exact Hold.
      * unfold C4_relation.
        exists eold, ijump.
        split; [reflexivity |].
        split; [reflexivity |].
        apply Hnew_not_in with (k := old).
        exact Hold.
    + destruct (Label_eq_dec kjump new) as [Hknew | Hknew].
      * subst kjump.
        exfalso.
        apply Hnonew.
        eapply contains_goto_jump_back; eauto.
      * assert (Hrenamed :
          CFGKATExpressionDynamics
            (rename_goto old new e, i)
            a
            (CFGKATAutomatonJump kjump ijump)).
        { inversion Hdyn; subst.
          apply CFGKATExpressionDynamicsFinite.
          pose proof
            (rename_goto_finite_dynamics old new e i a
              (CFGKATAutomatonJump kjump ijump) H) as Hrenamed.
          cbn [rename_output] in Hrenamed.
          unfold rename_label in Hrenamed.
          destruct (Label_eq_dec kjump old) as [Heq | _];
            [contradiction |].
          exact Hrenamed.
        }
        destruct (Label_eq_dec kjump old) as [Heq | _];
          [contradiction |].
        destruct (E kjump) as [ejump |] eqn:HEjump.
        -- eapply CFGKATStrongStepSilent with
             (x1' := (ejump, ijump))
             (x2' := (rename_goto old new ejump, ijump)).
	           ++ eapply CFGKATSilentBoundJump with (ys := []).
	              ** simpl. exact Hdyn.
	              ** apply lift_label_some. exact HEjump.
           ++ eapply CFGKATSilentBoundJump with (ys := []).
              ** simpl. exact Hrenamed.
              ** apply lift_label_some.
                 apply label_env_rename_other_some.
                 --- exact Hkold.
                 --- exact Hknew.
                 --- exact HEjump.
           ++ unfold C4_relation.
              exists ejump, ijump.
              split; [reflexivity |].
              split; [reflexivity |].
              apply Hnew_not_in with (k := kjump).
              exact HEjump.
        -- eapply CFGKATStrongStepHalt with
             (zeta := CFGKATAutomatonJump kjump ijump).
           ++ simpl. constructor.
           ++ eapply Hlift_free_jump.
	              ** exact Hdyn.
	              ** constructor.
	                 --- apply lift_label_none. exact HEjump.
	                 --- constructor.
           ++ eapply Hlift_free_jump with (ys := [lift (E <E[ old ~> new ]>)]).
              ** exact Hrenamed.
              ** constructor.
                 --- apply lift_label_none.
                     apply label_env_rename_other_none.
                     +++ exact Hkold.
                     +++ exact Hknew.
                     +++ exact HEjump.
                 --- constructor.

	  - eapply CFGKATStrongStepNext.
	    + lift_raw_transition Hdyn.
	    + eapply Hlift_next.
	      pose proof
	        (rename_goto_dynamics_output old new e i a
	          (CFGKATAutomatonNext p (enext, inext)) Hnonew Hdyn) as Hrenamed.
	      cbn [rename_output rename_config] in Hrenamed.
	      exact Hrenamed.
	    + unfold C4_relation.
      exists enext, inext.
      split; [reflexivity |].
      split; [reflexivity |].
      eapply C5_no_goto_next; eauto.
Qed.

Definition C4_strong_bisim
  (E : label_environment CFGKATExpression)
  (old new : Label)
  (Hfresh : label_rename_fresh E new)
  (Hdom : exists e, E old = Some e)
  : @CFGKATStrongBisimulation
      CFGKATExpressionAutomaton
      CFGKATExpressionAutomaton
      [lift E]
      [lift (E <E[ old ~> new ]>)].
Proof.
  unshelve econstructor.
  - exact (C4_relation old new).
  - intros x1 x2 a Hrel.
    destruct Hrel as [e [i [Hx1 [Hx2 Hnonew]]]].
    subst x1 x2.
    destruct (cfgkat_synt_dynamics_total CFGKATExpressionAutomaton (e, i) a)
      as [zeta Htr].
    eapply C4_strong_step_rename_output.
    + exact Hfresh.
    + exact Hdom.
    + exact Hnonew.
    + exact Htr.
Defined.

Definition C4_bisim
  (E : label_environment CFGKATExpression)
  (old new : Label)
  (Hfresh : label_rename_fresh E new)
  (Hdom : exists e, E old = Some e)
  : CFGKATAutomatonBisimulation
      (resolve_list CFGKATExpressionAutomaton [lift E])
      (resolve_list CFGKATExpressionAutomaton
        [lift (E <E[ old ~> new ]>)]) :=
  strong_bisim_to_bisim
    [lift E]
    [lift (E <E[ old ~> new ]>)]
    (C4_strong_bisim E old new Hfresh Hdom).

Theorem C4_sound :
  forall
    (E : label_environment CFGKATExpression)
    (l l' : Label)
    (i : IndicatorAssignment),
    label_rename_fresh E l' ->
    (exists e, E l = Some e) ->
    (goto l, i)
      ~[ lift E ,
         lift (E <E[ l ~> l' ]>) ]
    (goto l', i).
Proof.
  intros E l l' i Hfresh Hdom.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar.
  exists (C4_bisim E l l' Hfresh Hdom).
  unfold C4_bisim.
  unfold C4_relation.
  exists (goto l), i.
  split; [reflexivity |].
  split.
  - unfold rename_goto, subst_goto.
    destruct (Label_eq_dec l l) as [_ | Hneq].
    + reflexivity.
    + contradiction Hneq.
      reflexivity.
  - simpl.
    intro Heq.
    symmetry in Heq.
    subst.
    destruct Hfresh as [Hfresh _].
    destruct Hdom as [body Hbody].
    rewrite Hfresh in Hbody.
    discriminate.
Qed.


Local Lemma unproductive_branch_premise_rejects_tail :
  forall E b f a i,
    (forall j,
      (test (not b) ;; (f ;; test b), j)
        ~[ lift E ]
      (0, j)) ->
    ~ eval_test b a i ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      (f ;; test b, i) a CFGKATAutomatonReject.
Proof.
  intros E b f a i Hprem Hb.
  destruct (Hprem i) as [R HR].

  destruct
    (resolve_list_synt_dynamics_total_known
       CFGKATExpressionAutomaton
       [lift E]
	       (test (not b) ;; (f ;; test b), i)
	       a) as [zeta Hzeta].

  assert (Hzero :
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      (0, i) a CFGKATAutomatonReject).
  {
    apply Hlift_reject.
    apply CFGKATExpressionDynamicsAssertFalse.
    tauto.
  }
  pose proof
    (cfgkat_bisimulation_step
       R
       (test (not b) ;; (f ;; test b), i)
       (0, i)
       a
       zeta
       CFGKATAutomatonReject
       HR
       Hzeta
       Hzero) as Hlift.
  inversion Hlift; subst; try discriminate.

  pose proof
    (resolve_list_same_dynamics
       [lift E]
       CFGKATExpressionAutomaton
       (test (not b) ;; (f ;; test b), i)
       (f ;; test b, i)
       a
       (fun r =>
          sequence_accept_iff
            (test (not b)) (f ;; test b) i i a
            (CFGKATExpressionDynamicsAssertTrue a i (not b)
              (ltac:(simpl; exact Hb)))
            r)
       CFGKATAutomatonReject) as Hsame.
  exact (proj1 Hsame Hzeta).
Qed.

Definition C6_unproductive_branch_relation
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  (l : Label)
  : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop :=
  fun s_short s_long =>
    s_short = s_long \/
    exists i,
      s_short = ((test b ;; g), i) /\
      s_long = ((if b then g else (f ;; goto l)), i).

Definition UnproductiveBranchRejectingCandidateSet
  (E : label_environment CFGKATExpression)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  (l : Label)
  (a : Atom)
  : CFGKATSyntConfiguration -> Prop :=
  fun s =>
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      s a CFGKATAutomatonReject \/
    exists i,
      s = ((if b then g else (f ;; goto l)), i) /\
      ~ eval_test b a i.

Local Lemma resolved_reject_contradicts :
  forall E x a r,
    r <> CFGKATAutomatonReject ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      x a CFGKATAutomatonReject ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      x a r ->
    False.
Proof.
  intros E x a r Hneq Hreject Hr.
  pose proof
    (resolved_lift_functional E x a CFGKATAutomatonReject r Hreject Hr)
    as Heq.
	  symmetry in Heq.
	  contradiction.
Qed.

Ltac contradict_resolved_reject_output E x a output Hreject Hraw :=
  exfalso;
  eapply (resolved_reject_contradicts E x a output);
    [ discriminate | exact Hreject | lift_raw_transition Hraw ].

Ltac C6_contradict_tail_reject E f b i a output Htail_reject Hfraw :=
  let Htail := fresh "Htail" in
  assert (Htail :
    cfgkat_synt_transitions
      CFGKATExpressionAutomaton
      (f ;; test b, i)
      a
      output);
  [ match output with
    | CFGKATAutomatonAccept _ =>
        eapply CFGKATExpressionDynamicsSequenceSkip;
        [ exact Hfraw
        | apply CFGKATExpressionDynamicsAssertTrue; assumption ]
    | CFGKATAutomatonBreak _ =>
        apply CFGKATExpressionDynamicsSequenceBreak; exact Hfraw
    | CFGKATAutomatonContinue _ =>
        apply CFGKATExpressionDynamicsSequenceContinue; exact Hfraw
    | CFGKATAutomatonReturn =>
        apply CFGKATExpressionDynamicsSequenceReturn; exact Hfraw
    | CFGKATAutomatonNext _ _ =>
        apply CFGKATExpressionDynamicsSequenceNext; exact Hfraw
    end
  | contradict_resolved_reject_output
      E (f ;; test b, i) a output Htail_reject Htail ].

Local Lemma unproductive_branch_resolved_reject_step :
  forall E b f g l (Hfresh : label_fresh E l) a x,
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      x a CFGKATAutomatonReject ->
    cfgkat_synt_transitions
      CFGKATExpressionAutomaton x a CFGKATAutomatonReject \/
    exists i0 l0 s,
      cfgkat_synt_transitions
        CFGKATExpressionAutomaton x a (CFGKATAutomatonJump l0 i0) /\
      first_binding l0 i0 s
        [lift (E ## l # (if b then g else (f ;; goto l)))] /\
      UnproductiveBranchRejectingCandidateSet E b f g l a s.
Proof.
  intros E b f g l Hfresh a x Hreject.
  destruct (cfgkat_expression_dynamics_total x a)
    as [raw Hraw].
  destruct raw as [| i0 | i0 | i0 | | l0 i0 | p s0].
	  - left.
	    exact Hraw.
	  - contradict_resolved_reject_output
	      E x a (@CFGKATAutomatonAccept CFGKATSyntConfiguration i0)
	      Hreject Hraw.
	  - contradict_resolved_reject_output
	      E x a (@CFGKATAutomatonBreak CFGKATSyntConfiguration i0)
	      Hreject Hraw.
	  - contradict_resolved_reject_output
	      E x a (@CFGKATAutomatonContinue CFGKATSyntConfiguration i0)
	      Hreject Hraw.
	  - contradict_resolved_reject_output
	      E x a (@CFGKATAutomatonReturn CFGKATSyntConfiguration)
	      Hreject Hraw.
  - destruct (first_binding_dec [lift E] l0 i0)
      as [[s Hfb] | Hfree].
    + right.
      exists i0, l0, s.
      split; [exact Hraw |].
      split.
      * inversion Hfb as [y ys Hhead | y ys Hnone Htail]; subst.
        -- apply first_binding_head.
           eapply lift_extend_old_some.
           exact Hhead.
        -- inversion Htail.
      * left.
        pose proof
          (first_binding_resolved_correct
             CFGKATExpressionAutomaton
             a CFGKATAutomatonReject [lift E] l0 i0 s x
             Hfb Hraw) as Hiff.
        exact (proj1 Hiff Hreject).
    + exfalso.
      eapply (resolved_reject_contradicts
        E x a (CFGKATAutomatonJump l0 i0)); [discriminate | exact Hreject |].
      exact (Hlift_free_jump
        [lift E] CFGKATExpressionAutomaton x a i0 l0 Hraw Hfree).
	  - contradict_resolved_reject_output
	      E x a (@CFGKATAutomatonNext CFGKATSyntConfiguration p s0)
	      Hreject Hraw.
Qed.

Local Lemma unproductive_branch_long_false_rejecting_step :
  forall E b f g l (Hfresh : label_fresh E l) a i,
    (forall j,
      (test (not b) ;; (f ;; test b), j)
        ~[ lift E ]
      (0, j)) ->
    ~ eval_test b a i ->
    cfgkat_synt_transitions
      CFGKATExpressionAutomaton
      ((if b then g else (f ;; goto l)), i)
      a CFGKATAutomatonReject \/
    exists i0 l0 s,
      cfgkat_synt_transitions
        CFGKATExpressionAutomaton
        ((if b then g else (f ;; goto l)), i)
        a (CFGKATAutomatonJump l0 i0) /\
      first_binding l0 i0 s
        [lift (E ## l # (if b then g else (f ;; goto l)))] /\
      UnproductiveBranchRejectingCandidateSet E b f g l a s.
Proof.
  intros E b f g l Hfresh a i Hprem Hb.
  pose proof
    (unproductive_branch_premise_rejects_tail E b f a i Hprem Hb)
    as Htail_reject.
  destruct (cfgkat_expression_dynamics_total (f, i) a)
    as [fraw Hfraw].
  destruct fraw as [| i0 | i0 | i0 | | l0 i0 | p s0].
  - left.
    apply (proj2
      (choice_right_dynamics_iff
         b g (f ;; goto l) i a Hb CFGKATAutomatonReject)).
    apply CFGKATExpressionDynamicsSequenceReject.
    exact Hfraw.
  - destruct (classic (eval_test b a i0)) as [Hb_i0 | Hnb_i0].
    + exfalso.
      C6_contradict_tail_reject E f b i a
        (@CFGKATAutomatonAccept CFGKATSyntConfiguration i0)
        Htail_reject Hfraw.
    + right.
      exists i0, l, ((if b then g else (f ;; goto l)), i0).
      split.
      * apply (proj2
          (choice_right_dynamics_iff
             b g (f ;; goto l) i a Hb (CFGKATAutomatonJump l i0))).
        eapply CFGKATExpressionDynamicsSequenceSkip.
        -- exact Hfraw.
        -- apply CFGKATExpressionDynamicsGoto.
      * split.
		        -- apply first_binding_head.
		           apply lift_label_extend_same.
        -- right.
           exists i0.
           split; [reflexivity | exact Hnb_i0].
  - exfalso.
    C6_contradict_tail_reject E f b i a
      (@CFGKATAutomatonBreak CFGKATSyntConfiguration i0)
      Htail_reject Hfraw.
  - exfalso.
    C6_contradict_tail_reject E f b i a
      (@CFGKATAutomatonContinue CFGKATSyntConfiguration i0)
      Htail_reject Hfraw.
  - exfalso.
    C6_contradict_tail_reject E f b i a
      (@CFGKATAutomatonReturn CFGKATSyntConfiguration)
      Htail_reject Hfraw.
  - assert (Htail_jump :
      cfgkat_synt_transitions
        CFGKATExpressionAutomaton
        (f ;; test b, i) a (CFGKATAutomatonJump l0 i0)).
    {
      apply CFGKATExpressionDynamicsSequenceJump.
      exact Hfraw.
    }
    destruct (first_binding_dec [lift E] l0 i0)
      as [[s Hfb] | Hfree].
    + right.
      exists i0, l0, s.
      split.
      * apply (proj2
          (choice_right_dynamics_iff
             b g (f ;; goto l) i a Hb (CFGKATAutomatonJump l0 i0))).
        apply CFGKATExpressionDynamicsSequenceJump.
        exact Hfraw.
      * split.
        -- inversion Hfb as [y ys Hhead | y ys Hnone Htail]; subst.
           ++ apply first_binding_head.
              eapply lift_extend_old_some.
              exact Hhead.
           ++ inversion Htail.
        -- left.
           pose proof
             (first_binding_resolved_correct
                CFGKATExpressionAutomaton
                a CFGKATAutomatonReject [lift E] l0 i0 s
                (f ;; test b, i) Hfb Htail_jump) as Hiff.
           exact (proj1 Hiff Htail_reject).
    + exfalso.
      eapply (resolved_reject_contradicts
        E (f ;; test b, i) a (CFGKATAutomatonJump l0 i0));
        [discriminate | exact Htail_reject |].
      exact (Hlift_free_jump
        [lift E] CFGKATExpressionAutomaton (f ;; test b, i)
        a i0 l0 Htail_jump Hfree).
  - exfalso.
    destruct s0 as [f' i'].
    C6_contradict_tail_reject E f b i a
      (@CFGKATAutomatonNext CFGKATSyntConfiguration
        p (f' ;; test b, i'))
      Htail_reject Hfraw.
Qed.

Local Lemma unproductive_branch_long_false_rejects :
  forall E b f g l (Hfresh : label_fresh E l) a i,
    (forall j,
      (test (not b) ;; (f ;; test b), j)
        ~[ lift E ]
      (0, j)) ->
    ~ eval_test b a i ->
    cfgkat_transitions
      (resolve_list
         CFGKATExpressionAutomaton
         [lift (E ## l # (if b then g else (f ;; goto l)))])
      ((if b then g else (f ;; goto l)), i)
      a CFGKATAutomatonReject.
Proof.
  intros E b f g l Hfresh a i Hprem Hb.
  eapply rejecting_set_member_resolves_reject
    with
      (aut := CFGKATExpressionAutomaton)
      (ys := [lift (E ## l # (if b then g else (f ;; goto l)))])
      (N := UnproductiveBranchRejectingCandidateSet E b f g l a).
  - intros x HN.
    destruct HN as [Hold | [j [Hx Hj]]].
    + destruct
        (unproductive_branch_resolved_reject_step
           E b f g l Hfresh a x Hold)
        as [Hraw | [i0 [l0 [s [Hjump [Hfb HNs]]]]]].
      * left.
        eapply Hlift_reject. exact Hraw.
      * right.
        exists s.
        split.
        -- eapply CFGKATSilentBoundJump with (ys := []).
           ++ simpl. exact Hjump.
           ++ inversion Hfb as [y ys Hhead | y ys Hnone Htail]; subst.
              ** exact Hhead.
              ** inversion Htail.
        -- exact HNs.
    + subst x.
      destruct
        (unproductive_branch_long_false_rejecting_step
           E b f g l Hfresh a j Hprem Hj)
        as [Hraw | [i0 [l0 [s [Hjump [Hfb HNs]]]]]].
      * left.
        eapply Hlift_reject. exact Hraw.
      * right.
        exists s.
        split.
        -- eapply CFGKATSilentBoundJump with (ys := []).
           ++ simpl. exact Hjump.
           ++ inversion Hfb as [y ys Hhead | y ys Hnone Htail]; subst.
              ** exact Hhead.
              ** inversion Htail.
        -- exact HNs.
  - right.
    exists i.
    split; [reflexivity | exact Hb].
Qed.

Local Lemma unproductive_branch_short_false_rejects :
  forall E b g l (Hfresh : label_fresh E l) a i,
    ~ eval_test b a i ->
    cfgkat_transitions
      (resolve_list
         CFGKATExpressionAutomaton
         [lift (E ## l # (test b ;; g))])
      ((test b ;; g), i)
      a CFGKATAutomatonReject.
Proof.
  intros E b g l Hfresh a i Hb.
  apply Hlift_reject.
  apply CFGKATExpressionDynamicsSequenceReject.
  apply CFGKATExpressionDynamicsAssertFalse.
  exact Hb.
Qed.

Local Lemma C6_fresh_jump_silent_step :
  forall E body l (Hfresh : label_fresh E l) a x i,
    cfgkat_synt_transitions
      CFGKATExpressionAutomaton x a (CFGKATAutomatonJump l i) ->
    CFGKATSilentTransition
      CFGKATExpressionAutomaton
      [lift (E ## l # body)] a x (body, i).
Proof.
  intros E body l Hfresh a x i Hjump.
  eapply CFGKATSilentBoundJump with (ys := []).
  - simpl. exact Hjump.
  - apply lift_label_extend_same.
Qed.

Local Lemma C6_old_jump_silent_step :
  forall E body l (Hfresh : label_fresh E l) a x l0 e i,
    l <> l0 ->
    E l0 = Some e ->
    cfgkat_synt_transitions
      CFGKATExpressionAutomaton x a (CFGKATAutomatonJump l0 i) ->
    CFGKATSilentTransition
      CFGKATExpressionAutomaton
      [lift (E ## l # body)] a x (e, i).
Proof.
  intros E body l Hfresh a x l0 e i Hneq HE Hjump.
  eapply CFGKATSilentBoundJump with (ys := []).
  - simpl. exact Hjump.
  - eapply lift_label_extend_other_some; eauto.
Qed.

Local Lemma C6_free_jump_resolved_step :
  forall E body l (Hfresh : label_fresh E l) a x l0 i,
    l <> l0 ->
    E l0 = None ->
    cfgkat_synt_transitions
      CFGKATExpressionAutomaton x a (CFGKATAutomatonJump l0 i) ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift (E ## l # body)])
      x a (CFGKATAutomatonJump l0 i).
Proof.
  intros E body l Hfresh a x l0 i Hneq HE Hjump.
  eapply Hlift_free_jump.
  - exact Hjump.
  - constructor.
    + eapply lift_label_extend_other_none; eauto.
    + constructor.
Qed.

Local Lemma C6_fresh_bound_jump_resolved_step :
  forall E body l (Hfresh : label_fresh E l) a x i r,
    cfgkat_synt_transitions
      CFGKATExpressionAutomaton x a (CFGKATAutomatonJump l i) ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift (E ## l # body)])
      (body, i) a r ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift (E ## l # body)])
      x a r.
Proof.
  intros E body l Hfresh a x i r Hjump Hbody.
  eapply (Hlift_bound_jump
    [lift (E ## l # body)]
    CFGKATExpressionAutomaton
    x a i l (body, i) r).
  - exact Hjump.
  - apply first_binding_head.
    apply lift_label_extend_same.
  - exact Hbody.
Qed.

Local Lemma C6_common_source_strong_step :
  forall E b f g l (Hfresh : label_fresh E l)
    (Hprem : forall j,
      (test (not b) ;; (f ;; test b), j)
        ~[ lift E ]
      (0, j))
    a x_short x_long zeta,
    cfgkat_synt_transitions CFGKATExpressionAutomaton x_short a zeta ->
    cfgkat_synt_transitions CFGKATExpressionAutomaton x_long a zeta ->
    CFGKATStrongStep
      CFGKATExpressionAutomaton
      CFGKATExpressionAutomaton
      [lift (E ## l # (test b ;; g))]
      [lift (E ## l # (if b then g else (f ;; goto l)))]
      (C6_unproductive_branch_relation b f g l)
      a x_short x_long.
Proof.
  intros E b f g l Hfresh Hprem a x_short x_long zeta Hraw_short Hraw_long.
  destruct zeta as [| i | i | i | | l0 i | p s].
  all: try solve [strong_current_halt_output Hraw_short Hraw_long].
  - destruct (Label_eq_dec l l0) as [Heq | Hneq].
    + subst l0.
      destruct (classic (eval_test b a i)) as [Hb | Hb].
      * eapply CFGKATStrongStepSilent with
          (x1' := ((test b ;; g), i))
          (x2' := ((if b then g else (f ;; goto l)), i)).
        -- eapply C6_fresh_jump_silent_step. exact Hraw_short.
        -- eapply C6_fresh_jump_silent_step. exact Hraw_long.
        -- right.
           exists i.
           split; reflexivity.
      * eapply CFGKATStrongStepHalt with (zeta := CFGKATAutomatonReject).
        -- simpl. constructor.
        -- eapply C6_fresh_bound_jump_resolved_step.
           ++ exact Hraw_short.
           ++ eapply unproductive_branch_short_false_rejects; eauto.
        -- eapply C6_fresh_bound_jump_resolved_step.
           ++ exact Hraw_long.
           ++ eapply unproductive_branch_long_false_rejects; eauto.
    + destruct (E l0) as [eold |] eqn:HEold.
      * eapply CFGKATStrongStepSilent with
          (x1' := (eold, i))
          (x2' := (eold, i)).
        -- eapply C6_old_jump_silent_step; eauto.
        -- eapply C6_old_jump_silent_step; eauto.
        -- left. reflexivity.
      * eapply CFGKATStrongStepHalt with
          (zeta := CFGKATAutomatonJump l0 i).
        -- simpl. constructor.
        -- eapply C6_free_jump_resolved_step; eauto.
        -- eapply C6_free_jump_resolved_step with (body := if b then g else f;; goto l); eauto.
  - eapply CFGKATStrongStepNext.
    + lift_raw_transition Hraw_short.
    + lift_raw_transition Hraw_long.
    + left. reflexivity.
Qed.

Local Lemma C6_false_guard_strong_step :
  forall E b f g l (Hfresh : label_fresh E l) a i,
    (forall j,
      (test (not b) ;; (f ;; test b), j)
        ~[ lift E ]
      (0, j)) ->
    ~ eval_test b a i ->
    CFGKATStrongStep
      CFGKATExpressionAutomaton
      CFGKATExpressionAutomaton
      [lift (E ## l # (test b ;; g))]
      [lift (E ## l # (if b then g else (f ;; goto l)))]
      (C6_unproductive_branch_relation b f g l)
      a
      ((test b ;; g), i)
      ((if b then g else (f ;; goto l)), i).
Proof.
  intros E b f g l Hfresh a i Hprem Hb.
  eapply CFGKATStrongStepHalt with (zeta := CFGKATAutomatonReject).
  - simpl. constructor.
  - eapply unproductive_branch_short_false_rejects; eauto.
  - eapply unproductive_branch_long_false_rejects; eauto.
Qed.

Definition C6_unproductive_branch_strong_bisim
  (E : label_environment CFGKATExpression)
  (l : Label)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  (Hfresh : label_fresh E l)
  (Hprem : (forall j,
      (test (not b) ;; (f ;; test b), j)
        ~[ lift E ]
      (0, j)))
  : @CFGKATStrongBisimulation
      CFGKATExpressionAutomaton
      CFGKATExpressionAutomaton
      [lift (E ## l # (test b ;; g))]
      [lift (E ## l # (if b then g else (f ;; goto l)))].
Proof.
  unshelve econstructor.
  - exact (C6_unproductive_branch_relation b f g l).
  - intros x_short x_long a HR.
    destruct HR as [Heq | [i [Hshort Hlong]]].
    + subst x_long.
      destruct (cfgkat_expression_dynamics_total x_short a)
        as [zeta Hraw].
      eapply C6_common_source_strong_step; eauto.
    + subst x_short x_long.
      destruct (classic (eval_test b a i)) as [Hb | Hb].
      * destruct (cfgkat_expression_dynamics_total (g, i) a)
          as [zeta Hg].
        eapply C6_common_source_strong_step with (zeta := zeta).
        -- exact Hprem.
        -- apply (proj2
             (sequence_accept_iff
                (test b) g i i a
                (CFGKATExpressionDynamicsAssertTrue a i b Hb)
                zeta)).
           exact Hg.
        -- apply (proj2
             (choice_left_dynamics_iff
                b g (f ;; goto l) i a Hb zeta)).
           exact Hg.
      * eapply C6_false_guard_strong_step; eauto.
Defined.

Definition C6_short_to_long_bisim
  (E : label_environment CFGKATExpression)
  (l : Label)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  (Hfresh : label_fresh E l)
  (Hprem : (forall j,
      (test (not b) ;; (f ;; test b), j)
        ~[ lift E ]
      (0, j)))
  : CFGKATAutomatonBisimulation
      (resolve_list
         CFGKATExpressionAutomaton
         [lift (E ## l # (test b ;; g))])
      (resolve_list
         CFGKATExpressionAutomaton
         [lift (E ## l # (if b then g else (f ;; goto l)))]) :=
  strong_bisim_to_bisim
    [lift (E ## l # (test b ;; g))]
    [lift (E ## l # (if b then g else (f ;; goto l)))]
    (C6_unproductive_branch_strong_bisim E l b f g Hfresh Hprem).

Definition unproductive_branch_bisim
  (E : label_environment CFGKATExpression)
  (l : Label)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  (Hfresh : label_fresh E l)
  (Hprem : (forall j,
      (test (not b) ;; (f ;; test b), j)
        ~[ lift E ]
      (0, j)))
  : CFGKATAutomatonBisimulation
      (resolve_list
         CFGKATExpressionAutomaton
         [lift (E ## l # (if b then g else (f ;; goto l)))])
      (resolve_list
         CFGKATExpressionAutomaton
         [lift (E ## l # (test b ;; g))]) :=
  bisim_sym (C6_short_to_long_bisim E l b f g Hfresh Hprem).

Theorem C6_sound :
  forall
    (E : label_environment CFGKATExpression)
    (l : Label)
    (b : CFGKATTest)
    (f g e : CFGKATExpression)
    (i : IndicatorAssignment)
    (Hfresh : label_fresh E l),
    (forall j,
      (test (not b) ;; (f ;; test b), j)
        ~[ lift E ]
      (0, j)) ->
    (e, i)
      ~[
        lift (E ## l # if b then g else (f ;; goto l)),
        lift (E ## l # test b ;; g)
      ]
    (e, i).
Proof.
  intros E l b f g e i Hfresh Hprem.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar.
  exists (unproductive_branch_bisim E l b f g Hfresh Hprem).
  left.
  reflexivity.
Qed.


Definition C7_same_domain
  (E F : label_environment CFGKATExpression)
  : Prop :=
  forall l, label_in_dom E l <-> label_in_dom F l.

Definition C7_guarded
  (E : label_environment CFGKATExpression)
  : Prop :=
  forall l l' body target,
    E l = Some body ->
    E l' = Some target ->
    guarded l' body.

Definition C7_semantic_solution
  (E F : label_environment CFGKATExpression)
  : Prop :=
  forall l body i,
    E l = Some body ->
    CFGKATAutomatonBisimilar
      (resolve_list CFGKATExpressionAutomaton [lift F])
      (resolve_list CFGKATExpressionAutomaton [lift F])
      (goto l, i)
      (body, i).

Definition C7_goto_body_relation
  (l : Label)
  (body : CFGKATExpression)
  : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop :=
  fun s1 s2 =>
    s1 = s2 \/
    (exists i, s1 = (goto l, i) /\ s2 = (body, i)) \/
    (exists i, s1 = (body, i) /\ s2 = (goto l, i)).

Local Lemma C7_goto_body_relation_refl :
  forall l body s,
    C7_goto_body_relation l body s s.
Proof.
  intros l body s.
  unfold C7_goto_body_relation.
  left.
  reflexivity.
Qed.

Local Lemma C7_resolve_bound_body :
  forall (E : label_environment CFGKATExpression) source l body i a zeta,
    E l = Some body ->
    CFGKATExpressionDynamics source a (CFGKATAutomatonJump l i) ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      source a zeta ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      (body, i) a zeta.
Proof.
  intros E source l body i a zeta Hbody Hraw Hres.
  pose proof
    (first_binding_resolved_correct
       CFGKATExpressionAutomaton
       a zeta [lift E] l i (body, i) source
       ltac:(apply first_binding_head; apply lift_label_some; exact Hbody)
       Hraw) as Hiff.
  exact (proj1 Hiff Hres).
Qed.

Definition C7_goto_body_bisim
  (F : label_environment CFGKATExpression)
  (l : Label)
  (body : CFGKATExpression)
  (Hbody : F l = Some body)
  : CFGKATAutomatonBisimulation
      (resolve_list CFGKATExpressionAutomaton [lift F])
      (resolve_list CFGKATExpressionAutomaton [lift F]).
Proof.
  unshelve econstructor.
  - exact (C7_goto_body_relation l body).
  - intros x y a zeta1 zeta2 Hrel Hx Hy.
    destruct Hrel as [Heq | [[j [Hxj Hyj]] | [j [Hxj Hyj]]]].
    + subst y.
      assert (Hzeta : zeta1 = zeta2).
      {
        eapply resolve_list_dynamics_functional.
        - exact Hx.
        - exact Hy.
      }
      subst zeta2.
      apply lifted_relation_refl.
      apply C7_goto_body_relation_refl.
    + subst x y.
      pose proof
        (first_binding_resolved_correct
           CFGKATExpressionAutomaton
           a zeta1 [lift F] l j (body, j) (goto l, j)
           ltac:(apply first_binding_head; apply lift_label_some; exact Hbody)
           (CFGKATExpressionDynamicsGoto a j l)) as Hiff.
      pose proof (proj1 Hiff Hx) as Hbody_zeta1.
      assert (Hzeta : zeta1 = zeta2).
      {
        eapply resolve_list_dynamics_functional.
        - exact Hbody_zeta1.
        - exact Hy.
      }
      subst zeta2.
      apply lifted_relation_refl.
      apply C7_goto_body_relation_refl.
    + subst x y.
      pose proof
        (first_binding_resolved_correct
           CFGKATExpressionAutomaton
           a zeta2 [lift F] l j (body, j) (goto l, j)
           ltac:(apply first_binding_head; apply lift_label_some; exact Hbody)
           (CFGKATExpressionDynamicsGoto a j l)) as Hiff.
      pose proof (proj1 Hiff Hy) as Hbody_zeta2.
      assert (Hzeta : zeta1 = zeta2).
      {
        eapply resolve_list_dynamics_functional.
        - exact Hx.
        - exact Hbody_zeta2.
      }
      subst zeta2.
      apply lifted_relation_refl.
      apply C7_goto_body_relation_refl.
Defined.

Local Lemma C7_solution_target :
  forall E F l ebody fbody i,
    C7_semantic_solution E F ->
    E l = Some ebody ->
    F l = Some fbody ->
    (fbody, i) ~[lift F] (ebody, i).
Proof.
  intros E F l ebody fbody i Hsol HE HF.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar in *.
  destruct (Hsol l ebody i HE) as [Rsol HRsol].
  exists
    (bisim_trans
       (resolved_lift_total F)
       (bisim_sym (C7_goto_body_bisim F l fbody HF))
       Rsol).
  exists (goto l, i).
  split.
  - unfold C7_goto_body_relation.
    right.
    left.
    exists i.
    split; reflexivity.
  - exact HRsol.
Qed.

Definition C7_F_bisim_relation
  (_ : label_environment CFGKATExpression)
  (F : label_environment CFGKATExpression)
  : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop :=
  fun sF sE =>
    CFGKATAutomatonBisimilar
      (resolve_list CFGKATExpressionAutomaton [lift F])
      (resolve_list CFGKATExpressionAutomaton [lift F])
      sF sE.

Local Lemma C7_label_target_same_output :
  forall
    (E F : label_environment CFGKATExpression)
    (R : CFGKATAutomatonBisimulation
           (resolve_list CFGKATExpressionAutomaton [lift F])
           (resolve_list CFGKATExpressionAutomaton [lift F]))
    xF xE a zetaF zetaE out,
    cfgkat_relation R xF xE ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift F])
      xF a zetaF ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      xE a zetaE ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift F])
      xE a out ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      xE a out ->
    lifted_relation (C7_F_bisim_relation E F) zetaF zetaE.
Proof.
  intros E F R xF xE a zetaF zetaE out HR HresF HresE HoutF HoutE.
  assert (HzetaE : zetaE = out).
  {
    eapply resolve_list_dynamics_functional; eauto.
  }
  subst zetaE.
  pose proof (cfgkat_bisimulation_step R xF xE a zetaF out HR HresF HoutF)
    as Hlift.
  inversion Hlift; subst; constructor.
  unfold C7_F_bisim_relation, CFGKATAutomatonBisimilar.
  exists R.
  match goal with
  | Hrel : cfgkat_relation R _ _ |- _ => exact Hrel
  end.
Qed.

Local Lemma C7_same_source_same_output :
  forall
    (E F : label_environment CFGKATExpression)
    source a zetaF zetaE out,
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift F])
      source a zetaF ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      source a zetaE ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift F])
      source a out ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      source a out ->
    lifted_relation (C7_F_bisim_relation E F) zetaF zetaE.
Proof.
  intros E F source a zetaF zetaE out HresF HresE HoutF HoutE.
  assert (HzetaF : zetaF = out).
  {
    eapply resolve_list_dynamics_functional; eauto.
  }
  assert (HzetaE : zetaE = out).
  {
    eapply resolve_list_dynamics_functional; eauto.
  }
  subst zetaF zetaE.
  destruct out; constructor.
  unfold C7_F_bisim_relation, CFGKATAutomatonBisimilar.
  exists (bisim_refl (resolved_lift_functional F)).
  reflexivity.
Qed.

Ltac C7_lift_raw_output :=
  match goal with
  | |- cfgkat_transitions _ ?source ?a ?out =>
      match goal with
      | Hraw : CFGKATExpressionDynamics source a out |- _ =>
          first [
            lift_raw_transition Hraw
          | eapply Hlift_free_jump; [ exact Hraw | eauto ] ]
      end
  end.

Ltac C7_label_target_output E F R xF xE out :=
  eapply (C7_label_target_same_output E F R xF xE _ _ _ out);
  [ eassumption
  | eassumption
  | eassumption
  | C7_lift_raw_output
  | C7_lift_raw_output ].

Ltac C7_same_source_output E F source out :=
  eapply (C7_same_source_same_output E F source _ _ _ out);
  [ eassumption
  | eassumption
  | C7_lift_raw_output
  | C7_lift_raw_output ].

Ltac C7_label_target_current_output E F R xF xE :=
  match goal with
  | Hraw : CFGKATExpressionDynamics xE _ ?out |- _ =>
      C7_label_target_output E F R xF xE out
  end.

Ltac C7_same_source_current_output E F source :=
  match goal with
  | Hraw : CFGKATExpressionDynamics source _ ?out |- _ =>
      C7_same_source_output E F source out
  end.

Local Lemma C7_label_target_step :
  forall
    (E F : label_environment CFGKATExpression)
    (Hdom : C7_same_domain E F)
    (Hguard : C7_guarded E)
    (Hsol : C7_semantic_solution E F)
    l ebody fbody i a zetaF zetaE,
    E l = Some ebody ->
    F l = Some fbody ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift F])
      (fbody, i) a zetaF ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      (ebody, i) a zetaE ->
    lifted_relation (C7_F_bisim_relation E F) zetaF zetaE.
Proof.
  intros E F Hdom Hguard Hsol l ebody fbody i a zetaF zetaE HE HF HresF HresE.
  destruct (C7_solution_target E F l ebody fbody i Hsol HE HF)
    as [R HR].
  destruct (cfgkat_expression_dynamics_total (ebody, i) a)
    as [raw Hraw].
  destruct raw as [| iacc | ibreak | icontinue | | ljump ijump | p snext].
  all: try solve [
    C7_label_target_current_output E F R (fbody, i) (ebody, i) ].
  - destruct (E ljump) as [target |] eqn:HEjump.
    + exfalso.
      eapply Hguard.
      * exact HE.
      * exact HEjump.
      * exact Hraw.
    + assert (HFjump : F ljump = None).
      { destruct (F ljump) as [fbody' |] eqn:HFjump; [| reflexivity].
        destruct (proj2 (Hdom ljump)) as [ebody' HE'].
        - exists fbody'. exact HFjump.
        - rewrite HEjump in HE'. discriminate. }
      pose proof (lift_singleton_free F ljump ijump HFjump) as HfreeF.
      pose proof (lift_singleton_free E ljump ijump HEjump) as HfreeE.
      C7_label_target_current_output E F R (fbody, i) (ebody, i).
Qed.

Local Lemma C7_same_source_step :
  forall
    (E F : label_environment CFGKATExpression)
    (Hdom : C7_same_domain E F)
    (Hguard : C7_guarded E)
    (Hsol : C7_semantic_solution E F)
    source a zetaF zetaE,
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift F])
      source a zetaF ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      source a zetaE ->
    lifted_relation (C7_F_bisim_relation E F) zetaF zetaE.
Proof.
  intros E F Hdom Hguard Hsol [e i] a zetaF zetaE HresF HresE.
  destruct (cfgkat_expression_dynamics_total (e, i) a)
    as [raw Hraw].
  destruct raw as [| iacc | ibreak | icontinue | | ljump ijump | p snext].
  all: try solve [C7_same_source_current_output E F (e, i)].
  - destruct (F ljump) as [fbody |] eqn:HF.
    + destruct (proj2 (Hdom ljump)) as [ebody HE].
      * exists fbody. exact HF.
      * eapply C7_label_target_step; eauto using C7_resolve_bound_body.
    + assert (HE : E ljump = None).
      { destruct (E ljump) as [ebody |] eqn:HE; [| reflexivity].
        destruct (proj1 (Hdom ljump)) as [fbody HF'].
        - exists ebody. exact HE.
        - rewrite HF in HF'. discriminate. }
      pose proof (lift_singleton_free F ljump ijump HF) as HfreeF.
      pose proof (lift_singleton_free E ljump ijump HE) as HfreeE.
      C7_same_source_current_output E F (e, i).
Qed.

Local Lemma C7_related_pair_step :
  forall
    (E F : label_environment CFGKATExpression)
    (Hdom : C7_same_domain E F)
    (Hguard : C7_guarded E)
    (Hsol : C7_semantic_solution E F)
    xF xE a zetaF zetaE,
    C7_F_bisim_relation E F xF xE ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift F])
      xF a zetaF ->
    cfgkat_transitions
      (resolve_list CFGKATExpressionAutomaton [lift E])
      xE a zetaE ->
    lifted_relation (C7_F_bisim_relation E F) zetaF zetaE.
Proof.
  intros E F Hdom Hguard Hsol xF xE a zetaF zetaE Hrel HresF HresE.
  destruct Hrel as [R HR].
  destruct (resolved_lift_total F xE a)
    as [zeta_source HsourceF].
  pose proof
    (cfgkat_bisimulation_step
       R xF xE a zetaF zeta_source HR HresF HsourceF)
    as Hleft.
  pose proof
    (C7_same_source_step
       E F Hdom Hguard Hsol xE a zeta_source zetaE
       HsourceF HresE)
    as Hright.
  inversion Hleft; subst; inversion Hright; subst; constructor.
  unfold C7_F_bisim_relation, CFGKATAutomatonBisimilar in *.
  repeat match goal with
  | H : exists Rsource, cfgkat_relation Rsource _ _ |- _ =>
      destruct H
  end.
  eexists (bisim_trans (resolved_lift_total F) R _).
  eexists.
  split; eassumption.
Qed.

Definition C7_bisim
  (E F : label_environment CFGKATExpression)
  (Hdom : C7_same_domain E F)
  (Hguard : C7_guarded E)
  (Hsol : C7_semantic_solution E F)
  : CFGKATAutomatonBisimulation
      (resolve_list CFGKATExpressionAutomaton [lift F])
      (resolve_list CFGKATExpressionAutomaton [lift E]).
Proof.
  unshelve econstructor.
  - exact (C7_F_bisim_relation E F).
  - eapply C7_related_pair_step; eauto.
Defined.

Theorem C7_sound :
  forall
    (E F : label_environment CFGKATExpression)
    (e : CFGKATExpression)
    (i : IndicatorAssignment),
    (forall l, label_in_dom E l <-> label_in_dom F l) ->
    (forall l l' body target,
      E l = Some body ->
      E l' = Some target ->
      guarded l' body) ->
    (forall l body,
      E l = Some body ->
      forall i, (goto l, i) ~[lift F] (body, i)) ->
    (e, i) ~[lift F, lift E] (e, i).
Proof.
  intros E F e i Hdom Hguard Hsol.
  unfold CFGKATExpressionBisimilar, CFGKATAutomatonBisimilar.
  exists
    (C7_bisim E F Hdom Hguard
      (fun l body i Hbody => Hsol l body Hbody i)).
  unfold C7_F_bisim_relation, CFGKATAutomatonBisimilar.
  exists (bisim_refl (resolved_lift_functional F)).
  reflexivity.
Qed.
