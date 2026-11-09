Require Import Stdlib.Program.Equality.
Require Import Stdlib.Setoids.Setoid.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.Logic.ClassicalEpsilon.
Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.

From CFGKAT.Semantics Require Export SyntacticAutomata.

Local Open Scope type_scope.

Inductive lifted_relation {X Y : Type} (R : X -> Y -> Prop)
: CFGKATAutomatonOutputs X -> CFGKATAutomatonOutputs Y -> Prop :=
  | lifted_relation_reject :
    lifted_relation R CFGKATAutomatonReject CFGKATAutomatonReject
  | lifted_relation_accept :
    forall i, lifted_relation R (CFGKATAutomatonAccept i)
                                (CFGKATAutomatonAccept i)
  | lifted_relation_break :
    forall i, lifted_relation R (CFGKATAutomatonBreak i)
                                (CFGKATAutomatonBreak i)
  | lifted_relation_continue :
    forall i, lifted_relation R (CFGKATAutomatonContinue i)
                                (CFGKATAutomatonContinue i)
  | lifted_relation_jump :
    forall i l, lifted_relation R (CFGKATAutomatonJump l i)
                                  (CFGKATAutomatonJump l i)
  | lifted_relation_return :
    lifted_relation R CFGKATAutomatonReturn CFGKATAutomatonReturn
  | lifted_relation_next : forall x y p,
    R x y ->
    lifted_relation R (CFGKATAutomatonNext p x) (CFGKATAutomatonNext p y).

Record CFGKATAutomatonBisimulation {aut1 aut2: CFGKATAutomaton} := {
  cfgkat_relation: cfgkat_states aut1 -> cfgkat_states aut2 -> Prop;
  cfgkat_bisimulation_step:
    forall x1 x2 a zeta1 zeta2,
      cfgkat_relation x1 x2 ->
      cfgkat_transitions aut1 x1 a zeta1 ->
      cfgkat_transitions aut2 x2 a zeta2 ->
      lifted_relation cfgkat_relation zeta1 zeta2;
}.

Arguments CFGKATAutomatonBisimulation : clear implicits.

Lemma lifted_relation_sym
  {X Y : Type}
  (R : X -> Y -> Prop)
  :
  forall
    (zeta1 : CFGKATAutomatonOutputs X)
    (zeta2 : CFGKATAutomatonOutputs Y),
    lifted_relation R zeta1 zeta2 ->
    lifted_relation
      (fun y x => R x y)
      zeta2 zeta1.
Proof.
  intros zeta1 zeta2 H.
  inversion H; subst; constructor; auto.
Qed.

Program Definition bisim_sym
  {A B : CFGKATAutomaton}
  (R : CFGKATAutomatonBisimulation A B)
  : CFGKATAutomatonBisimulation B A
:= {|
  cfgkat_relation x y := cfgkat_relation R y x;
|}.
Next Obligation.
  apply lifted_relation_sym.
  eapply cfgkat_bisimulation_step; eauto.
Qed.

Definition CFGKATAutomatonBisimilar
  (aut1 aut2: CFGKATAutomaton)
  (x1: cfgkat_states aut1)
  (x2: cfgkat_states aut2)
:=
  exists R, cfgkat_relation R x1 x2
.

Definition CFGKATExpressionBisimilar
  (E F : environment CFGKATSyntConfiguration)
  (e1 e2 : CFGKATSyntConfiguration) :=
  CFGKATAutomatonBisimilar
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton E)
    (resolve_cfgkat_automaton CFGKATExpressionAutomaton F)
    e1 e2.

Definition empty_label_context : label_environment CFGKATExpression :=
  empty_environment.

Local Unset Program Cases.

Program Definition lift (E : label_environment CFGKATExpression)
  : environment CFGKATSyntConfiguration
  := mk_resolution_environment
      (fun l i =>
        match E l with
        | Some e => Some (e, i)
        | None => None
        end)
      (env_support E)
      _.
Next Obligation.
  intros l i s Hlookup.
  destruct (E l) as [body |] eqn:HE; inversion Hlookup; subst.
  eapply env_supported; eauto.
Qed.

Lemma lift_lookup
  (E : label_environment CFGKATExpression)
  (l : Label)
  (i : IndicatorAssignment)
  :
  lift E l i =
    match E l with
    | Some e => Some (e, i)
    | None => None
    end.
Proof.
  unfold lift, mk_resolution_environment.
  cbn [environment_lookup].
  destruct (E l); reflexivity.
Qed.

Definition empty_syntactic_context : environment CFGKATSyntConfiguration :=
  lift empty_label_context.

Notation "e1 '~~' e2" :=
  (CFGKATExpressionBisimilar
    empty_syntactic_context
    empty_syntactic_context
    e1 e2)
  (at level 70).

Definition CFGKATL11Premise (e: CFGKATExpression) (b: CFGKATTest) :=
  forall i,
    ((test b ;; e) |> test (not b), i) ~~ (0, i)
.

Lemma cfgkat_dynamics_functional
  (e: CFGKATExpression)
  (i: IndicatorAssignment)
:
  cfgkat_automaton_dynamics_functional (CFGKATExpressionDynamics (e, i)).
Proof.
  apply cfgkat_expression_dynamics_functional.
Qed.

Lemma cfgkat_expression_dynamics_total
  (s: CFGKATSyntConfiguration)
:
  cfgkat_automaton_dynamics_total (CFGKATExpressionDynamics s).
Proof.
  apply CFGKATExpressionDynamics_total.
Qed.

Definition ExprAutEmpty : CFGKATAutomaton :=
  resolve_cfgkat_automaton CFGKATExpressionAutomaton empty_syntactic_context.

Lemma ExprAutEmpty_functional :
  forall x,
    cfgkat_automaton_dynamics_functional
      (cfgkat_transitions ExprAutEmpty x).
Proof.
  intro x. simpl.
  apply resolve_dynamics_preserves_functionality
    with (aut := CFGKATSyntacticToAutomaton CFGKATExpressionAutomaton).
  - constructor.
    intros [e0 i0].
    apply cfgkat_expression_dynamics_functional.
  - destruct x as [e0 i0].
    apply cfgkat_expression_dynamics_functional.
Qed.

Lemma resolve_syntactic_empty_identity x1 a r :
    ResolveCFGKATAutomatonDynamics
      CFGKATExpressionAutomaton
      (CFGKATExpressionDynamics x1)
      empty_syntactic_context a r <->
    CFGKATExpressionDynamics x1 a r.
Proof.
  apply resolve_empty_identity; auto.
  apply CFGKATExpressionDynamics_total.
Qed.

Program Definition bisimulation_by_outputs
  {aut1 aut2 : CFGKATAutomaton}
  (R : cfgkat_states aut1 -> cfgkat_states aut2 -> Prop)
  (Hfunc2 :
     forall x2,
       cfgkat_automaton_dynamics_functional
         (cfgkat_transitions aut2 x2))
  (Hreject :
    forall x1 x2 a,
      R x1 x2 ->
      cfgkat_transitions aut1 x1 a CFGKATAutomatonReject ->
      cfgkat_transitions aut2 x2 a CFGKATAutomatonReject)
  (Haccept :
    forall x1 x2 i' a,
      R x1 x2 ->
      cfgkat_transitions aut1 x1 a (CFGKATAutomatonAccept i') ->
      cfgkat_transitions aut2 x2 a (CFGKATAutomatonAccept i'))
  (Hbreak :
    forall x1 x2 i' a,
      R x1 x2 ->
      cfgkat_transitions aut1 x1 a (CFGKATAutomatonBreak i') ->
      cfgkat_transitions aut2 x2 a (CFGKATAutomatonBreak i'))
  (Hcontinue :
    forall x1 x2 i' a,
      R x1 x2 ->
      cfgkat_transitions aut1 x1 a (CFGKATAutomatonContinue i') ->
      cfgkat_transitions aut2 x2 a (CFGKATAutomatonContinue i'))
  (Hreturn :
    forall x1 x2 a,
      R x1 x2 ->
      cfgkat_transitions aut1 x1 a CFGKATAutomatonReturn ->
      cfgkat_transitions aut2 x2 a CFGKATAutomatonReturn)
  (Hjump :
    forall x1 x2 i' l a,
      R x1 x2 ->
      cfgkat_transitions aut1 x1 a (CFGKATAutomatonJump l i') ->
      cfgkat_transitions aut2 x2 a (CFGKATAutomatonJump l i'))
  (Hnext :
    forall x1 x2 x1' p a,
      R x1 x2 ->
      cfgkat_transitions aut1 x1 a (CFGKATAutomatonNext p x1') ->
      exists x2',
        cfgkat_transitions aut2 x2 a (CFGKATAutomatonNext p x2') /\
        R x1' x2')
  : CFGKATAutomatonBisimulation aut1 aut2
:= {|
    cfgkat_relation := R;
|}.
Next Obligation.
  rename H into HR, H0 into Hzeta1, H1 into Hzeta2.
  destruct zeta1 as [| i | i | i | | l i | p x1'].
  - pose proof (Hreject x1 x2 a HR Hzeta1) as Hmatch.
    pose proof (Hfunc2 x2 a zeta2 _ Hzeta2 Hmatch) as Heq.
    subst zeta2. constructor.
  - pose proof (Haccept x1 x2 i a HR Hzeta1) as Hmatch.
    pose proof (Hfunc2 x2 a zeta2 _ Hzeta2 Hmatch) as Heq.
    subst zeta2. constructor.
  - pose proof (Hbreak x1 x2 i a HR Hzeta1) as Hmatch.
    pose proof (Hfunc2 x2 a zeta2 _ Hzeta2 Hmatch) as Heq.
    subst zeta2. constructor.
  - pose proof (Hcontinue x1 x2 i a HR Hzeta1) as Hmatch.
    pose proof (Hfunc2 x2 a zeta2 _ Hzeta2 Hmatch) as Heq.
    subst zeta2. constructor.
  - pose proof (Hreturn x1 x2 a HR Hzeta1) as Hmatch.
    pose proof (Hfunc2 x2 a zeta2 _ Hzeta2 Hmatch) as Heq.
    subst zeta2. constructor.
  - pose proof (Hjump x1 x2 i l a HR Hzeta1) as Hmatch.
    pose proof (Hfunc2 x2 a zeta2 _ Hzeta2 Hmatch) as Heq.
    subst zeta2. constructor.
  - destruct (Hnext x1 x2 x1' p a HR Hzeta1) as [x2' [Hmatch HRnext]].
    pose proof (Hfunc2 x2 a zeta2 _ Hzeta2 Hmatch) as Heq.
    subst zeta2. constructor. exact HRnext.
Qed.

Lemma cfgkat_dynamics_nonreject_finite
  (s: CFGKATSyntConfiguration)
  (a: Atom)
  (r: CFGKATAutomatonOutputs CFGKATSyntConfiguration)
:
  r <> CFGKATAutomatonReject ->
  CFGKATExpressionDynamics s a r ->
  CFGKATExpressionFiniteDynamics s a r.
Proof.
  intros Hnot Hdyn.
  inversion Hdyn; now subst.
Qed.

Lemma cfgkat_l11_premise_stuck
  (e: CFGKATExpression)
  (i: IndicatorAssignment)
  (b: CFGKATTest)
:
  CFGKATL11Premise e b ->
  Stuck e b.
Proof.
  intros Hinv i' a Hb.
  specialize (CFGKATExpressionDynamics_total (e, i') a) as [r Hr].
  destruct r.
  - now left.
  - specialize (Hinv i') as [R HR].
    destruct (classic (eval_test b a i0)) as [Hb0 | Hb0]; eauto.
    enough (lifted_relation (cfgkat_relation R)
                            (CFGKATAutomatonAccept i0)
                            CFGKATAutomatonReject) as Hbad
      by inversion Hbad.
    eapply cfgkat_bisimulation_step; eauto.
    + apply resolve_syntactic_empty_identity.
      apply CFGKATExpressionDynamicsFinite.
      repeat econstructor;
      try eapply cfgkat_dynamics_nonreject_finite;
      eauto; discriminate.
    + apply resolve_syntactic_empty_identity.
      now apply CFGKATExpressionDynamicsAssertFalse.
  - specialize (Hinv i') as [R HR].
    enough (lifted_relation (cfgkat_relation R)
                            (CFGKATAutomatonAccept i0)
                            CFGKATAutomatonReject) as Hbad
      by inversion Hbad.
    eapply cfgkat_bisimulation_step; eauto.
    + apply resolve_syntactic_empty_identity.
      repeat econstructor;
      try eapply cfgkat_dynamics_nonreject_finite;
      eauto; discriminate.
    + apply resolve_syntactic_empty_identity.
      now apply CFGKATExpressionDynamicsAssertFalse.
  - right. exists i0. intuition.
    destruct (classic (eval_test b a i0)) as [Hb_i0 | Hnot_b_i0]; auto.
    specialize (Hinv i') as [R HR].
    enough (lifted_relation (cfgkat_relation R)
                            (CFGKATAutomatonAccept i0)
                            CFGKATAutomatonReject) as Hbad
      by inversion Hbad.
    eapply cfgkat_bisimulation_step; eauto.
    + apply resolve_syntactic_empty_identity.
      apply CFGKATExpressionDynamicsFinite.
      repeat econstructor; eauto;
      now eapply cfgkat_dynamics_nonreject_finite; eauto.
    + apply resolve_syntactic_empty_identity.
      now apply CFGKATExpressionDynamicsAssertFalse.
  - specialize (Hinv i') as [R HR].
    enough (lifted_relation (cfgkat_relation R)
                            CFGKATAutomatonReturn
                            CFGKATAutomatonReject) as Hbad
      by inversion Hbad.
    eapply cfgkat_bisimulation_step; eauto.
    + apply resolve_syntactic_empty_identity.
      apply CFGKATExpressionDynamicsFinite.
      repeat econstructor;
      try eapply cfgkat_dynamics_nonreject_finite;
      eauto; discriminate.
    + apply resolve_syntactic_empty_identity.
      now apply CFGKATExpressionDynamicsAssertFalse.
  - specialize (Hinv i') as [R HR].
    enough (lifted_relation (cfgkat_relation R)
                            (CFGKATAutomatonJump l i0)
                            CFGKATAutomatonReject) as Hbad
      by inversion Hbad.
    eapply cfgkat_bisimulation_step; eauto.
    + apply resolve_syntactic_empty_identity.
      apply CFGKATExpressionDynamicsFinite.
      repeat econstructor;
      try eapply cfgkat_dynamics_nonreject_finite;
      eauto; discriminate.
    + apply resolve_syntactic_empty_identity.
      now apply CFGKATExpressionDynamicsAssertFalse.
  - destruct s as [e0 i0].
    specialize (Hinv i') as [R HR].
    enough (lifted_relation (cfgkat_relation R)
                            (CFGKATAutomatonNext p (e0 |> test not b, i0))
                            CFGKATAutomatonReject) as Hbad
      by inversion Hbad.
    eapply cfgkat_bisimulation_step; eauto.
    + apply resolve_syntactic_empty_identity.
      apply CFGKATExpressionDynamicsFinite.
      repeat econstructor;
      try eapply cfgkat_dynamics_nonreject_finite;
      eauto; discriminate.
    + apply resolve_syntactic_empty_identity.
      now apply CFGKATExpressionDynamicsAssertFalse.
Qed.

Definition resolve_list
  (aut : CFGKATSyntacticAutomaton)
  (ys : list (environment CFGKATSyntConfiguration))
  : CFGKATSyntacticAutomaton :=
  fold_left resolve_cfgkat_synt_automaton ys aut.

Local Lemma resolve_list_step
  (aut : CFGKATSyntacticAutomaton)
  (y : environment CFGKATSyntConfiguration)
  (ys : list (environment CFGKATSyntConfiguration))
  (s : CFGKATSyntConfiguration)
  (a : Atom)
  (zeta : CFGKATAutomatonOutputs CFGKATSyntConfiguration) :
  cfgkat_transitions
    (resolve_list aut (y :: ys)) s a zeta <->
  cfgkat_transitions
    (resolve_list (resolve_cfgkat_synt_automaton aut y) ys) s a zeta.
Proof.
  reflexivity.
Qed.

Lemma resolve_list_dynamics_functional
  (ys : list (environment CFGKATSyntConfiguration))
  (aut : CFGKATSyntacticAutomaton)
  (s : CFGKATSyntConfiguration) :
  cfgkat_automaton_dynamics_functional
    (cfgkat_transitions (resolve_list aut ys) s).
Proof.
  apply cfgkat_synt_dynamics_functional.
Qed.

Lemma resolve_list_synt_dynamics_total_known
  (aut : CFGKATSyntacticAutomaton)
  (ys : list (environment CFGKATSyntConfiguration))
  (s: CFGKATSyntConfiguration)
:
  cfgkat_automaton_dynamics_total
    (cfgkat_synt_transitions (resolve_list aut ys) s).
Proof.
  apply cfgkat_synt_dynamics_total.
Qed.

Local Lemma resolve_finite_change_atom
  (aut : CFGKATSyntacticAutomaton)
  (d1 d2 : CFGKATAutomatonDynamics CFGKATSyntConfiguration)
  (E : environment CFGKATSyntConfiguration)
  (a : Atom) :
  (forall r, d1 a r -> d2 a r) ->
  forall r, ResolveCFGKATAutomatonFiniteDynamics aut d1 E a r ->
            ResolveCFGKATAutomatonFiniteDynamics aut d2 E a r.
Proof.
  intros Heq r Hfin.
  induction Hfin.
  - apply ResolveCFGKATAutomatonFiniteDynamicsDirect; firstorder.
  - eapply ResolveCFGKATAutomatonFiniteDynamicsBoundJump; eauto.
Qed.

Local Lemma resolve_change_atom
  (aut : CFGKATSyntacticAutomaton)
  (d1 d2 : CFGKATAutomatonDynamics CFGKATSyntConfiguration)
  (E : environment CFGKATSyntConfiguration)
  (a : Atom) :
  (forall r, d1 a r <-> d2 a r) ->
  forall r, ResolveCFGKATAutomatonDynamics aut d1 E a r ->
            ResolveCFGKATAutomatonDynamics aut d2 E a r.
Proof.
  intros Heq r H.
  inversion H; subst.
  - apply ResolveCFGKATAutomatonDynamicsFinite.
    apply resolve_finite_change_atom with (d1 := d1); eauto.
    firstorder.
  - apply ResolveCFGKATAutomatonDynamicsDefaultReject.
    intros r' Hfin. eapply H0.
    eapply resolve_finite_change_atom with (d1 := d2); eauto.
    firstorder.
Qed.

Lemma resolve_list_same_dynamics :
  forall (ys : list (environment CFGKATSyntConfiguration))
         (aut : CFGKATSyntacticAutomaton)
         (x s : CFGKATSyntConfiguration)
         (a : Atom),
  (forall r, cfgkat_synt_transitions aut x a r <->
             cfgkat_synt_transitions aut s a r) ->
  forall r, cfgkat_transitions (resolve_list aut ys) x a r <->
            cfgkat_transitions (resolve_list aut ys) s a r.
Proof.
  induction ys as [|y' ys' IH]; intros aut x s a Hequiv r.
  - apply Hequiv.
  - apply IH.
    intro r'. split; intro H.
    + eapply resolve_change_atom.
      * exact Hequiv.
      * exact H.
    + eapply resolve_change_atom.
      * intro r0. symmetry. apply Hequiv.
      * exact H.
Qed.

Lemma first_binding_resolved_correct :
  forall (aut : CFGKATSyntacticAutomaton)
         (a : Atom)
         (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
         (ys : list (environment CFGKATSyntConfiguration))
         (l : Label) (i : IndicatorAssignment) (s : CFGKATSyntConfiguration)
         (x : CFGKATSyntConfiguration),
    first_binding l i s ys ->
    cfgkat_synt_transitions aut x a (CFGKATAutomatonJump l i) ->
    cfgkat_transitions (resolve_list aut ys) x a r <->
    cfgkat_transitions (resolve_list aut ys) s a r.
Proof.
  intros aut a r ys l i s x Hfb; revert aut.
  induction Hfb as [y ys' Hy | y ys' Hy Hfb' IH]; intros aut Hjump.
  -
    do 2 rewrite resolve_list_step.
    apply resolve_list_same_dynamics.
    intro r'. simpl. split.
    + intro H. inversion H as [
        a0 zeta0 [a1 zeta1 Hbase Hnot |
                  a1 l0 i0 zeta1 s0 Hjump0 Hbind Hchild] |
        a0 Hnofinite
      ]; subst.
      * pose proof (cfgkat_synt_dynamics_functional _ _ _ _ _ Hjump Hbase)
          as Heq_ij; subst.
        simpl in Hnot. congruence.
      * apply ResolveCFGKATAutomatonDynamicsFinite.
        pose proof (cfgkat_synt_dynamics_functional _ _ _ _ _ Hjump Hjump0)
          as Heq_ij; inversion Heq_ij; subst.
        change (environment_lookup y l0 i0 = Some s) in Hy.
        change (environment_lookup y l0 i0 = Some s0) in Hbind.
        rewrite Hy in Hbind. inversion Hbind; now subst.
      * apply ResolveCFGKATAutomatonDynamicsDefaultReject.
        intros zeta Hfinite_s. apply (Hnofinite zeta).
        eapply ResolveCFGKATAutomatonFiniteDynamicsBoundJump; eauto.
    + intro H.
      eapply ResolveCFGKATAutomatonDynamicsBoundJump; eauto.
      apply cfgkat_synt_dynamics_functional.
  -
    apply IH.
    eapply ResolveCFGKATAutomatonDynamicsFreeJump; eauto.
Qed.

Lemma Hlift_reject (ys : list (environment CFGKATSyntConfiguration)):
  forall aut x a,
    cfgkat_synt_transitions aut x a CFGKATAutomatonReject ->
    cfgkat_transitions (resolve_list aut ys) x a CFGKATAutomatonReject.
Proof.
  induction ys as [|y ys' IH]; intros aut x a H; simpl; eauto.
  apply IH. now apply ResolveCFGKATAutomatonDynamicsReject.
Qed.

Lemma Hlift_accept (ys : list (environment CFGKATSyntConfiguration)):
  forall aut x a i,
    cfgkat_synt_transitions aut x a (CFGKATAutomatonAccept i) ->
    cfgkat_transitions (resolve_list aut ys) x a (CFGKATAutomatonAccept i).
Proof.
  induction ys as [|y ys' IH]; intros aut x a i H; simpl; eauto.
  apply IH. now apply ResolveCFGKATAutomatonDynamicsAccept.
Qed.

Lemma Hlift_break (ys : list (environment CFGKATSyntConfiguration)):
  forall aut x a i,
    cfgkat_synt_transitions aut x a (CFGKATAutomatonBreak i) ->
    cfgkat_transitions (resolve_list aut ys) x a (CFGKATAutomatonBreak i).
Proof.
  induction ys as [|y ys' IH]; intros aut x a i H; simpl; eauto.
  apply IH. now apply ResolveCFGKATAutomatonDynamicsBreak.
Qed.

Lemma Hlift_continue (ys : list (environment CFGKATSyntConfiguration)):
  forall aut x a i,
    cfgkat_synt_transitions aut x a (CFGKATAutomatonContinue i) ->
    cfgkat_transitions (resolve_list aut ys) x a (CFGKATAutomatonContinue i).
Proof.
  induction ys as [|y ys' IH]; intros aut x a i H; simpl; eauto.
  apply IH. now apply ResolveCFGKATAutomatonDynamicsContinue.
Qed.

Lemma Hlift_return (ys : list (environment CFGKATSyntConfiguration)):
  forall aut x a,
    cfgkat_synt_transitions aut x a CFGKATAutomatonReturn ->
    cfgkat_transitions (resolve_list aut ys) x a CFGKATAutomatonReturn.
Proof.
  induction ys as [|y ys' IH]; intros aut x a H; simpl; eauto.
  apply IH. now apply ResolveCFGKATAutomatonDynamicsReturn.
Qed.

Lemma Hlift_next (ys : list (environment CFGKATSyntConfiguration)):
  forall aut x a p s,
    cfgkat_synt_transitions aut x a (CFGKATAutomatonNext p s) ->
    cfgkat_transitions (resolve_list aut ys) x a (CFGKATAutomatonNext p s).
Proof.
  induction ys as [|y ys' IH]; intros aut x a p s H; simpl; eauto.
  apply IH. now apply ResolveCFGKATAutomatonDynamicsNext.
Qed.

Lemma Hlift_free_jump (ys : list (environment CFGKATSyntConfiguration)):
  forall aut x a i l,
    cfgkat_synt_transitions aut x a (CFGKATAutomatonJump l i) ->
    Forall (fun y : environment CFGKATSyntConfiguration => y l i = None) ys ->
    cfgkat_transitions (resolve_list aut ys) x a (CFGKATAutomatonJump l i).
Proof.
  induction ys as [|y ys' IH]; intros aut x a i l H Hfa; simpl; eauto.
  inversion Hfa as [|y0 ys'' Hhead Htail]; subst.
  apply IH; eauto. now apply ResolveCFGKATAutomatonDynamicsFreeJump.
Qed.

Lemma Hlift_bound_jump (ys : list (environment CFGKATSyntConfiguration)):
  forall aut x a i l s r,
    cfgkat_synt_transitions aut x a (CFGKATAutomatonJump l i) ->
    first_binding l i s ys ->
    cfgkat_transitions (resolve_list aut ys) s a r ->
    cfgkat_transitions (resolve_list aut ys) x a r.
Proof.
  intros aut x a i l s r Hjump Hbind Hres.
  eapply first_binding_resolved_correct; eauto.
Qed.

Class label_fresh
  (E : label_environment CFGKATExpression)
  (l : Label) : Prop :=
  label_fresh_none : E l = None.

Program Definition label_extend
  (E : label_environment CFGKATExpression)
  (l : Label)
  (e : CFGKATExpression)
  `{label_fresh E l} :
  label_environment CFGKATExpression
:= mk_environment
      (fun l' =>
        match Label_eq_dec l l' with
        | left _  => Some e
        | right _ => E l'
      end)
      (l :: env_support E)
      _.
Next Obligation.
  intros l' body Hlookup.
  destruct (Label_eq_dec l l') as [Heq | Hneq].
  - subst. simpl in *; intuition.
  - right. eapply env_supported; eauto.
Qed.

Notation "e '~[' E ',' F ']' f" :=
  (@CFGKATExpressionBisimilar E F e f)
  (at level 70).

Notation "e '~[' E ']' f" :=
  (@CFGKATExpressionBisimilar E E e f)
  (at level 70).

Notation "E ## l # e" :=
  (label_extend E l e) (at level 70).

Lemma resolved_lift_functional
  (E : label_environment CFGKATExpression)
  (s: cfgkat_states (resolve_cfgkat_automaton
                       CFGKATExpressionAutomaton (lift E)))
:
  cfgkat_automaton_dynamics_functional
    (cfgkat_transitions
      (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E)) s).
Proof.
  apply resolve_list_dynamics_functional with (ys := [lift E]).
Qed.

Lemma resolved_lift_total
  (E : label_environment CFGKATExpression)
  (s: cfgkat_states (resolve_cfgkat_automaton
                       CFGKATExpressionAutomaton (lift E)))
:
  cfgkat_automaton_dynamics_total
    (cfgkat_transitions
      (resolve_cfgkat_automaton CFGKATExpressionAutomaton (lift E)) s).
Proof.
  apply resolve_list_synt_dynamics_total_known with (ys := [lift E]).
Qed.

Lemma first_binding_dec :
  forall (ys : list (environment CFGKATSyntConfiguration))
         (l : Label) (i : IndicatorAssignment),
    (exists s, first_binding l i s ys) \/
    Forall (fun y : environment CFGKATSyntConfiguration => y l i = None) ys.
Proof.
  induction ys as [| y ys' IH]; intros l i.
  - right. constructor.
  - destruct (y l i) as [s|] eqn:Hy.
    + left. exists s. now constructor.
    + destruct (IH l i) as [[s Hs] | Hfree].
      * left.  exists s. now apply first_binding_tail.
      * right. now constructor.
Qed.

Inductive productive_resolution
  (aut : CFGKATSyntacticAutomaton)
  (ys : list (environment CFGKATSyntConfiguration))
  (a : Atom)
  : CFGKATSyntConfiguration ->
    CFGKATAutomatonOutputs CFGKATSyntConfiguration -> Prop :=
| productive_resolution_accept : forall x i,
    cfgkat_synt_transitions aut x a (CFGKATAutomatonAccept i) ->
    productive_resolution aut ys a x (CFGKATAutomatonAccept i)
| productive_resolution_break : forall x i,
    cfgkat_synt_transitions aut x a (CFGKATAutomatonBreak i) ->
    productive_resolution aut ys a x (CFGKATAutomatonBreak i)
| productive_resolution_continue : forall x i,
    cfgkat_synt_transitions aut x a (CFGKATAutomatonContinue i) ->
    productive_resolution aut ys a x (CFGKATAutomatonContinue i)
| productive_resolution_return : forall x,
    cfgkat_synt_transitions aut x a CFGKATAutomatonReturn ->
    productive_resolution aut ys a x CFGKATAutomatonReturn
| productive_resolution_next : forall x p s,
    cfgkat_synt_transitions aut x a (CFGKATAutomatonNext p s) ->
    productive_resolution aut ys a x (CFGKATAutomatonNext p s)
| productive_resolution_free_jump : forall x i l,
    cfgkat_synt_transitions aut x a (CFGKATAutomatonJump l i) ->
    Forall (fun y : environment CFGKATSyntConfiguration => y l i = None) ys ->
    productive_resolution aut ys a x (CFGKATAutomatonJump l i)
| productive_resolution_bound_jump : forall x i l s zeta,
    cfgkat_synt_transitions aut x a (CFGKATAutomatonJump l i) ->
    first_binding l i s ys ->
    productive_resolution aut ys a s zeta ->
    productive_resolution aut ys a x zeta.

Lemma productive_resolution_not_reject :
  forall aut ys a x zeta,
    productive_resolution aut ys a x zeta ->
    zeta <> CFGKATAutomatonReject.
Proof.
  intros aut ys a x zeta Hprod.
  induction Hprod; try discriminate.
  apply IHHprod.
Qed.

Lemma productive_resolution_resolves :
  forall aut
    ys a x zeta,
    productive_resolution aut ys a x zeta ->
    cfgkat_transitions (resolve_list aut ys) x a zeta.
Proof.
  intros aut ys a x zeta Hprod.
  induction Hprod.
  - eapply Hlift_accept; eauto.
  - eapply Hlift_break; eauto.
  - eapply Hlift_continue; eauto.
  - eapply Hlift_return; eauto.
  - eapply Hlift_next; eauto.
  - eapply Hlift_free_jump; eauto.
  - eapply Hlift_bound_jump; eauto.
Qed.

Definition cfgkat_halting_output
  {X: Type}
  (zeta : CFGKATAutomatonOutputs X)
  : Prop :=
  match zeta with
  | CFGKATAutomatonNext _ _ => False
  | _ => True
  end.

Definition cfgkat_loop_silent_body
  (e : CFGKATExpression)
  (i sigma : IndicatorAssignment)
  (a : Atom)
  : Prop :=
  CFGKATExpressionFiniteDynamics (e, i) a
    (CFGKATAutomatonAccept sigma) \/
  CFGKATExpressionFiniteDynamics (e, i) a
    (CFGKATAutomatonContinue sigma).

Inductive CFGKATSilentTransition
  (aut : CFGKATSyntacticAutomaton)
  : list (environment CFGKATSyntConfiguration) ->
    Atom ->
    CFGKATSyntConfiguration ->
    CFGKATSyntConfiguration ->
    Prop :=
| CFGKATSilentLoop :
    forall (ys : list (environment CFGKATSyntConfiguration)) a b e i sigma,
      eval_test b a i ->
      cfgkat_loop_silent_body e i sigma a ->
      CFGKATSilentTransition aut ys a
        (while b do e, i)
        (while b do e, sigma)
| CFGKATSilentLoopSeq :
    forall (ys : list (environment CFGKATSyntConfiguration)) a b e e' i sigma,
      cfgkat_loop_silent_body e' i sigma a ->
      CFGKATSilentTransition aut ys a
        (e' |> while b do e, i)
        (while b do e, sigma)
| CFGKATSilentBoundJump :
    forall (ys : list (environment CFGKATSyntConfiguration))
           (zeta : environment CFGKATSyntConfiguration) a x i l s,
      cfgkat_transitions (resolve_list aut ys) x a
        (CFGKATAutomatonJump l i) ->
      zeta l i = Some s ->
      CFGKATSilentTransition aut (ys ++ [zeta]) a x s
| CFGKATSilentWeaken :
    forall (ys : list (environment CFGKATSyntConfiguration))
           (zeta : environment CFGKATSyntConfiguration) a x s,
      CFGKATSilentTransition aut ys a x s ->
      CFGKATSilentTransition aut (ys ++ [zeta]) a x s.

Definition cfgkat_rejecting_set
  (aut : CFGKATSyntacticAutomaton)
  (ys : list (environment CFGKATSyntConfiguration))
  (a : Atom)
  (N : CFGKATSyntConfiguration -> Prop)
  : Prop :=
  forall s,
    N s ->
    cfgkat_transitions (resolve_list aut ys) s a CFGKATAutomatonReject \/
    exists s',
      CFGKATSilentTransition aut ys a s s' /\ N s'.

Inductive CFGKATStrongStep
  (aut1 aut2 : CFGKATSyntacticAutomaton)
  (ys1 ys2 : list (environment CFGKATSyntConfiguration))
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (a : Atom)
  (x1 x2 : CFGKATSyntConfiguration)
  : Prop :=
| CFGKATStrongStepHalt :
    forall zeta,
      cfgkat_halting_output zeta ->
      cfgkat_transitions (resolve_list aut1 ys1) x1 a zeta ->
      cfgkat_transitions (resolve_list aut2 ys2) x2 a zeta ->
      CFGKATStrongStep aut1 aut2 ys1 ys2 R a x1 x2
| CFGKATStrongStepNext :
    forall p x1' x2',
      cfgkat_transitions (resolve_list aut1 ys1) x1 a
        (CFGKATAutomatonNext p x1') ->
      cfgkat_transitions (resolve_list aut2 ys2) x2 a
        (CFGKATAutomatonNext p x2') ->
      R x1' x2' ->
      CFGKATStrongStep aut1 aut2 ys1 ys2 R a x1 x2
| CFGKATStrongStepSilent :
    forall x1' x2',
      CFGKATSilentTransition aut1 ys1 a x1 x1' ->
      CFGKATSilentTransition aut2 ys2 a x2 x2' ->
      R x1' x2' ->
      CFGKATStrongStep aut1 aut2 ys1 ys2 R a x1 x2.

Record CFGKATStrongBisimulation
  {aut1 aut2 : CFGKATSyntacticAutomaton}
  {ys1 ys2 : list (environment CFGKATSyntConfiguration)}
:= {
  cfgkat_strong_relation:
    CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop;
  cfgkat_strong_bisimulation_cond:
    forall x1 x2 a,
      cfgkat_strong_relation x1 x2 ->
      CFGKATStrongStep aut1 aut2 ys1 ys2
        cfgkat_strong_relation a x1 x2
}.

Local Lemma cfgkat_expression_dynamics_of_finite_equiv_directional :
  forall s t a,
    (forall r,
      CFGKATExpressionFiniteDynamics s a r <->
      CFGKATExpressionFiniteDynamics t a r) ->
    forall r,
      CFGKATExpressionDynamics s a r ->
      CFGKATExpressionDynamics t a r.
Proof.
  intros s t a Hfinite r Hdyn.
  inversion Hdyn; subst.
  + apply CFGKATExpressionDynamicsFinite.
    apply Hfinite. exact H.
  + apply CFGKATExpressionDynamicsDefaultReject.
    intros r' Hr'.
    unfold CFGKATExpressionNoFiniteResult in H.
    apply (H r').
    apply Hfinite. exact Hr'.
Qed.

Lemma cfgkat_expression_dynamics_of_finite_equiv :
  forall s t a,
    (forall r,
      CFGKATExpressionFiniteDynamics s a r <->
      CFGKATExpressionFiniteDynamics t a r) ->
    forall r,
      CFGKATExpressionDynamics s a r <->
      CFGKATExpressionDynamics t a r.
Proof.
  intuition;
  now eapply cfgkat_expression_dynamics_of_finite_equiv_directional; eauto.
Qed.

Lemma CFGKATExpressionDynamicsLoopGuardTrueInv :
  forall a i b e r,
    eval_test b a i ->
    CFGKATExpressionDynamics (while b do e, i) a r ->
    CFGKATExpressionDynamics (e |> while b do e, i) a r.
Proof.
  intros a i b e r Hb Hloop.
  inversion Hloop; subst.
  - dependent destruction H; intuition.
    now apply CFGKATExpressionDynamicsFinite.
  - apply CFGKATExpressionDynamicsDefaultReject. intros r' Hfin.
    eapply H, CFGKATExpressionFiniteDynamicsLoopGuardTrue; eauto.
Qed.

Lemma loopseq_accept_tail_dynamics :
  forall g h i i' a,
    CFGKATExpressionDynamics (g, i) a (CFGKATAutomatonAccept i') ->
    forall r,
      CFGKATExpressionDynamics (g |> h, i) a r <->
      CFGKATExpressionDynamics (h, i') a r.
Proof.
  intros g h i i' a Hg r.
  split.
  - intro Hloop.
    inversion Hg; inversion Hloop; subst.
    + dependent destruction H3; enforce_functionality_cfgkat_finite_dynamics.
      now apply CFGKATExpressionDynamicsFinite.
    + apply CFGKATExpressionDynamicsDefaultReject. intros r' Hr'.
      eapply H3, CFGKATExpressionFiniteDynamicsLoopSeqSkip; eauto.
  - eapply CFGKATExpressionDynamicsLoopSeqSkip; eauto.
Qed.

Lemma loopseq_continue_tail_dynamics :
  forall g h i i' a,
    CFGKATExpressionDynamics (g, i) a (CFGKATAutomatonContinue i') ->
    forall r,
      CFGKATExpressionDynamics (g |> h, i) a r <->
      CFGKATExpressionDynamics (h, i') a r.
Proof.
  intros g h i i' a Hg r.
  split.
  - intro Hloop.
    inversion Hg; inversion Hloop; subst.
    + dependent destruction H3; enforce_functionality_cfgkat_finite_dynamics.
      now apply CFGKATExpressionDynamicsFinite.
    + apply CFGKATExpressionDynamicsDefaultReject. intros r' Hr'.
      eapply H3, CFGKATExpressionFiniteDynamicsLoopSeqContinue; eauto.
  - intro Hh. eapply CFGKATExpressionDynamicsLoopSeqContinue; eauto.
Qed.

Local Lemma cfgkat_synt_expression_dynamics_equiv :
  forall aut s t a,
    (forall r, CFGKATExpressionDynamics s a r <->
               CFGKATExpressionDynamics t a r) ->
    forall r,
      cfgkat_synt_transitions aut s a r <->
      cfgkat_synt_transitions aut t a r.
Proof.
  induction aut as [| aut IH y]; intros s t a Hequiv r; eauto; intuition.
  - eapply resolve_change_atom; eauto.
  - eapply resolve_change_atom; eauto.
    now apply IH.
Qed.

Local Lemma cfgkat_loop_silent_body_dynamics_equiv :
  forall e i sigma a,
    cfgkat_loop_silent_body e i sigma a ->
    forall h r,
      CFGKATExpressionDynamics (e |> h, i) a r <->
      CFGKATExpressionDynamics (h, sigma) a r.
Proof.
  intros e i sigma a [Haccept | Hcontinue] h r.
  - apply loopseq_accept_tail_dynamics.
    now apply CFGKATExpressionDynamicsFinite.
  - apply loopseq_continue_tail_dynamics.
    now apply CFGKATExpressionDynamicsFinite.
Qed.

Local Lemma cfgkat_loop_silent_expression_equiv :
  forall b e i sigma a,
    eval_test b a i ->
    cfgkat_loop_silent_body e i sigma a ->
    forall r,
      CFGKATExpressionDynamics (while b do e, i) a r <->
      CFGKATExpressionDynamics (while b do e, sigma) a r.
Proof.
  intros b e i sigma a Hb Hbody r.
  split; intro Hdyn.
  - apply CFGKATExpressionDynamicsLoopGuardTrueInv in Hdyn; eauto.
    eapply cfgkat_loop_silent_body_dynamics_equiv; eauto.
  - eapply CFGKATExpressionDynamicsLoopGuardTrue; eauto.
    eapply cfgkat_loop_silent_body_dynamics_equiv; eauto.
Qed.

Local Lemma cfgkat_loopseq_silent_expression_equiv :
  forall b e e' i sigma a,
    cfgkat_loop_silent_body e' i sigma a ->
    forall r,
      CFGKATExpressionDynamics (e' |> while b do e, i) a r <->
      CFGKATExpressionDynamics (while b do e, sigma) a r.
Proof.
  intros b e e' i sigma a Hbody r.
  now apply cfgkat_loop_silent_body_dynamics_equiv.
Qed.

Local Lemma resolve_list_app_single :
  forall aut ys zeta s a r,
    cfgkat_transitions (resolve_list aut (ys ++ [zeta])) s a r <->
    cfgkat_transitions
      (resolve_cfgkat_synt_automaton (resolve_list aut ys) zeta)
      s a r.
Proof.
  intros aut ys zeta s a r.
  unfold resolve_list.
  now rewrite fold_left_app.
Qed.

Local Lemma CFGKATSilentWeakenSuffix suffix :
  forall aut ys a x s,
    CFGKATSilentTransition aut ys a x s ->
    CFGKATSilentTransition aut (ys ++ suffix) a x s.
Proof.
  induction suffix as [| y suffix IH]; intros aut ys a x s Hsilent.
  - now rewrite app_nil_r.
  - replace (ys ++ y :: suffix) with ((ys ++ [y]) ++ suffix)
      by (rewrite <- app_assoc; reflexivity).
    now apply IH, CFGKATSilentWeaken.
Qed.

Local Lemma first_binding_silent_transition_prefix
:
  forall aut prefix suffix a
    (x : CFGKATSyntConfiguration)
    l i
    (s : CFGKATSyntConfiguration),
    cfgkat_transitions (resolve_list aut prefix) x a
      (CFGKATAutomatonJump l i) ->
    first_binding l i s suffix ->
    CFGKATSilentTransition aut (prefix ++ suffix) a x s.
Proof.
  intros aut prefix suffix a x l i s Hjump Hfb.
  revert prefix Hjump; induction Hfb; intros.
  + replace (prefix ++ y :: ys) with ((prefix ++ [y]) ++ ys)
      by (rewrite <- app_assoc; reflexivity).
    eapply CFGKATSilentWeakenSuffix
      with (ys := prefix ++ [y]) (suffix := ys).
    eapply CFGKATSilentBoundJump with (ys := prefix); eauto.
  + replace (prefix ++ y :: ys) with ((prefix ++ [y]) ++ ys)
      by (rewrite <- app_assoc; reflexivity).
    apply IHHfb, resolve_list_app_single; simpl.
    eapply ResolveCFGKATAutomatonDynamicsFreeJump; eauto.
Qed.

Lemma first_binding_silent_transition :
  forall aut ys a x l i s,
    cfgkat_synt_transitions aut x a (CFGKATAutomatonJump l i) ->
    first_binding l i s ys ->
    CFGKATSilentTransition aut ys a x s.
Proof.
  intros aut ys a x l i s Hjump Hfb.
  change ys with ([] ++ ys).
  eapply first_binding_silent_transition_prefix; eauto.
Qed.

Local Lemma one_step_bound_jump_dynamics_equiv :
  forall
    (aut : CFGKATSyntacticAutomaton)
    (zeta : environment CFGKATSyntConfiguration)
    (d : CFGKATAutomatonDynamics CFGKATSyntConfiguration)
    a l i s,
    d a (CFGKATAutomatonJump l i) ->
    zeta l i = Some s ->
    cfgkat_automaton_dynamics_functional d ->
    forall r,
      ResolveCFGKATAutomatonDynamics aut d zeta a r <->
      ResolveCFGKATAutomatonDynamics aut
        (cfgkat_transitions aut s) zeta a r.
Proof.
  intros aut zeta d a l i s Hjump Hbind Hfunc r.
  split; intro Hres.
  - inversion Hres; subst.
    + inversion H; subst; enforce_functionality; simpl in H1.
      * congruence.
      * apply ResolveCFGKATAutomatonDynamicsFinite.
        rewrite Hbind in H1; inversion H1; congruence.
    + apply ResolveCFGKATAutomatonDynamicsDefaultReject.
      intros r' Hfin. apply (H r').
      eapply ResolveCFGKATAutomatonFiniteDynamicsBoundJump; eauto.
  - eapply ResolveCFGKATAutomatonDynamicsBoundJump; eauto.
Qed.

Lemma CFGKATSilentTransition_preserves_dynamics :
  forall
    (aut : CFGKATSyntacticAutomaton)
    (ys : list (environment CFGKATSyntConfiguration))
    (a : Atom)
    (s t : CFGKATSyntConfiguration),
    CFGKATSilentTransition aut ys a s t ->
    forall r,
      cfgkat_transitions (resolve_list aut ys) s a r <->
      cfgkat_transitions (resolve_list aut ys) t a r.
Proof.
  intros aut ys a s t Hsilent.
  induction Hsilent; intro r.
  - apply resolve_list_same_dynamics. intro r'.
    apply cfgkat_synt_expression_dynamics_equiv.
    now apply cfgkat_loop_silent_expression_equiv.
  - apply resolve_list_same_dynamics. intro r'.
    apply cfgkat_synt_expression_dynamics_equiv.
    now apply cfgkat_loopseq_silent_expression_equiv.
  - do 2 rewrite resolve_list_app_single; simpl.
    eapply one_step_bound_jump_dynamics_equiv; eauto.
    apply resolve_list_dynamics_functional.
  - do 2 rewrite resolve_list_app_single.
    change
      (cfgkat_transitions (resolve_list (resolve_list aut ys) [zeta]) x a r <->
       cfgkat_transitions (resolve_list (resolve_list aut ys) [zeta]) s a r).
    apply resolve_list_same_dynamics, IHHsilent.
Qed.

Inductive CFGKATExpressionFiniteSized :
  nat ->
  CFGKATSyntConfiguration ->
  Atom ->
  CFGKATAutomatonOutputs CFGKATSyntConfiguration ->
  Prop :=
| CFGKATExpressionFiniteSizedAssertTrue :
    forall a i b,
      eval_test b a i ->
      CFGKATExpressionFiniteSized 1 (test b, i) a
        (CFGKATAutomatonAccept i)
| CFGKATExpressionFiniteSizedAssign :
    forall a i x v,
      CFGKATExpressionFiniteSized 1 (assign v to x, i) a
        (CFGKATAutomatonAccept (update i x v))
| CFGKATExpressionFiniteSizedAction :
    forall a i p,
      CFGKATExpressionFiniteSized 1 (do p, i) a
        (CFGKATAutomatonNext p (1, i))
| CFGKATExpressionFiniteSizedBreak :
    forall a i,
      CFGKATExpressionFiniteSized 1 (break, i) a
        (CFGKATAutomatonBreak i)
| CFGKATExpressionFiniteSizedContinue :
    forall a i,
      CFGKATExpressionFiniteSized 1 (continue, i) a
        (CFGKATAutomatonContinue i)
| CFGKATExpressionFiniteSizedReturn :
    forall a i,
      CFGKATExpressionFiniteSized 1 (return, i) a
        CFGKATAutomatonReturn
| CFGKATExpressionFiniteSizedGoto :
    forall a i l,
      CFGKATExpressionFiniteSized 1 (goto l, i) a
        (CFGKATAutomatonJump l i)
| CFGKATExpressionFiniteSizedChoiceLeft :
    forall n a i e1 e2 b r,
      eval_test b a i ->
      CFGKATExpressionFiniteSized n (e1, i) a r ->
      CFGKATExpressionFiniteSized (S n) (if b then e1 else e2, i) a r
| CFGKATExpressionFiniteSizedChoiceRight :
    forall n a i e1 e2 b r,
      ~ eval_test b a i ->
      CFGKATExpressionFiniteSized n (e2, i) a r ->
      CFGKATExpressionFiniteSized (S n) (if b then e1 else e2, i) a r
| CFGKATExpressionFiniteSizedSequenceSkip :
    forall n1 n2 a i i' e1 e2 r,
      CFGKATExpressionFiniteSized n1 (e1, i) a
        (CFGKATAutomatonAccept i') ->
      CFGKATExpressionFiniteSized n2 (e2, i') a r ->
      CFGKATExpressionFiniteSized (S (n1 + n2)) (e1 ;; e2, i) a r
| CFGKATExpressionFiniteSizedSequenceReject :
    forall n a i e1 e2,
      CFGKATExpressionFiniteSized n (e1, i) a CFGKATAutomatonReject ->
      CFGKATExpressionFiniteSized (S n) (e1 ;; e2, i) a
        CFGKATAutomatonReject
| CFGKATExpressionFiniteSizedSequenceReturn :
    forall n a i e1 e2,
      CFGKATExpressionFiniteSized n (e1, i) a CFGKATAutomatonReturn ->
      CFGKATExpressionFiniteSized (S n) (e1 ;; e2, i) a
        CFGKATAutomatonReturn
| CFGKATExpressionFiniteSizedSequenceBreak :
    forall n a i i' e1 e2,
      CFGKATExpressionFiniteSized n (e1, i) a
        (CFGKATAutomatonBreak i') ->
      CFGKATExpressionFiniteSized (S n) (e1 ;; e2, i) a
        (CFGKATAutomatonBreak i')
| CFGKATExpressionFiniteSizedSequenceContinue :
    forall n a i i' e1 e2,
      CFGKATExpressionFiniteSized n (e1, i) a
        (CFGKATAutomatonContinue i') ->
      CFGKATExpressionFiniteSized (S n) (e1 ;; e2, i) a
        (CFGKATAutomatonContinue i')
| CFGKATExpressionFiniteSizedSequenceJump :
    forall n a i i' e1 e2 l,
      CFGKATExpressionFiniteSized n (e1, i) a
        (CFGKATAutomatonJump l i') ->
      CFGKATExpressionFiniteSized (S n) (e1 ;; e2, i) a
        (CFGKATAutomatonJump l i')
| CFGKATExpressionFiniteSizedSequenceNext :
    forall n a i i' e1 e1' e2 p,
      CFGKATExpressionFiniteSized n (e1, i) a
        (CFGKATAutomatonNext p (e1', i')) ->
      CFGKATExpressionFiniteSized (S n) (e1 ;; e2, i) a
        (CFGKATAutomatonNext p (e1' ;; e2, i'))
| CFGKATExpressionFiniteSizedLoopSeqSkip :
    forall n1 n2 a i i' e1 e2 r,
      CFGKATExpressionFiniteSized n1 (e1, i) a
        (CFGKATAutomatonAccept i') ->
      CFGKATExpressionFiniteSized n2 (e2, i') a r ->
      CFGKATExpressionFiniteSized (S (n1 + n2)) (e1 |> e2, i) a r
| CFGKATExpressionFiniteSizedLoopSeqReject :
    forall n a i e1 e2,
      CFGKATExpressionFiniteSized n (e1, i) a CFGKATAutomatonReject ->
      CFGKATExpressionFiniteSized (S n) (e1 |> e2, i) a
        CFGKATAutomatonReject
| CFGKATExpressionFiniteSizedLoopSeqReturn :
    forall n a i e1 e2,
      CFGKATExpressionFiniteSized n (e1, i) a CFGKATAutomatonReturn ->
      CFGKATExpressionFiniteSized (S n) (e1 |> e2, i) a
        CFGKATAutomatonReturn
| CFGKATExpressionFiniteSizedLoopSeqBreak :
    forall n a i i' e1 e2,
      CFGKATExpressionFiniteSized n (e1, i) a
        (CFGKATAutomatonBreak i') ->
      CFGKATExpressionFiniteSized (S n) (e1 |> e2, i) a
        (CFGKATAutomatonAccept i')
| CFGKATExpressionFiniteSizedLoopSeqContinue :
    forall n1 n2 a i i' e1 e2 r,
      CFGKATExpressionFiniteSized n1 (e1, i) a
        (CFGKATAutomatonContinue i') ->
      CFGKATExpressionFiniteSized n2 (e2, i') a r ->
      CFGKATExpressionFiniteSized (S (n1 + n2)) (e1 |> e2, i) a r
| CFGKATExpressionFiniteSizedLoopSeqJump :
    forall n a i i' e1 e2 l,
      CFGKATExpressionFiniteSized n (e1, i) a
        (CFGKATAutomatonJump l i') ->
      CFGKATExpressionFiniteSized (S n) (e1 |> e2, i) a
        (CFGKATAutomatonJump l i')
| CFGKATExpressionFiniteSizedLoopSeqNext :
    forall n a i i' e1 e1' e2 p,
      CFGKATExpressionFiniteSized n (e1, i) a
        (CFGKATAutomatonNext p (e1', i')) ->
      CFGKATExpressionFiniteSized (S n) (e1 |> e2, i) a
        (CFGKATAutomatonNext p (e1' |> e2, i'))
| CFGKATExpressionFiniteSizedLoopGuardTrue :
    forall n a i b e r,
      eval_test b a i ->
      CFGKATExpressionFiniteSized n (e |> while b do e, i) a r ->
      CFGKATExpressionFiniteSized (S n) (while b do e, i) a r
| CFGKATExpressionFiniteSizedLoopGuardFalse :
    forall a i b e,
      ~ eval_test b a i ->
      CFGKATExpressionFiniteSized 1 (while b do e, i) a
        (CFGKATAutomatonAccept i).

Local Lemma CFGKATExpressionFiniteSized_sound :
  forall n s a r,
    CFGKATExpressionFiniteSized n s a r ->
    CFGKATExpressionFiniteDynamics s a r.
Proof.
  intros n s a r Hsized.
  induction Hsized; try now constructor; eauto.
  - eapply CFGKATExpressionFiniteDynamicsSequenceSkip; eauto.
  - eapply CFGKATExpressionFiniteDynamicsLoopSeqSkip; eauto.
  - eapply CFGKATExpressionFiniteDynamicsLoopSeqContinue; eauto.
Qed.

Local Lemma CFGKATExpressionFiniteDynamics_sized :
  forall s a r,
    CFGKATExpressionFiniteDynamics s a r ->
    exists n, CFGKATExpressionFiniteSized n s a r.
Proof.
  intros s a r Hfin.
  induction Hfin;
    repeat match goal with
    | [ H: exists _ : nat, _ |- _ ] => destruct H
    end; eexists; try now (constructor || econstructor); eauto.
Qed.

Definition is_productive
  {states: Type}
  (zeta: CFGKATAutomatonOutputs states) : Prop
:=
  match zeta with
  | CFGKATAutomatonAccept _
  | CFGKATAutomatonContinue _ =>
    False
  | _ => True
  end.

Lemma contradict_sized_body
  (e' : CFGKATExpression)
  (i j : IndicatorAssignment)
  (a : Atom)
  (n : nat)
  zeta
:
  cfgkat_loop_silent_body e' i j a ->
  CFGKATExpressionFiniteSized n (e', i) a zeta ->
  ~ is_productive zeta
.
Proof.
  intros. apply CFGKATExpressionFiniteSized_sound in H0 as Hhead.
  destruct H as [Haccept | Hcontinue];
  now enforce_functionality_cfgkat_finite_dynamics.
Qed.

Local Lemma cfgkat_expression_loopseq_finite_smaller :
  forall n b e e' i sigma a r,
    CFGKATExpressionFiniteSized n (e' |> while b do e, i) a r ->
    cfgkat_loop_silent_body e' i sigma a ->
    exists m,
      m < n /\
      CFGKATExpressionFiniteSized m (while b do e, sigma) a r.
Proof.
  intros n b e e' i sigma a r Hfin Hbody.
  inversion Hfin; subst;
    try (exfalso; eapply contradict_sized_body; now eauto).
  - apply CFGKATExpressionFiniteSized_sound in H5.
    destruct Hbody as [Haccept | Hcontinue];
    enforce_functionality_cfgkat_finite_dynamics.
    exists n2; intuition; lia.
  - apply CFGKATExpressionFiniteSized_sound in H5.
    destruct Hbody as [Haccept | Hcontinue];
    enforce_functionality_cfgkat_finite_dynamics.
    exists n2; intuition; lia.
Qed.

Local Lemma cfgkat_expression_loop_finite_smaller :
  forall n b e i sigma a r,
    CFGKATExpressionFiniteSized n (while b do e, i) a r ->
    eval_test b a i ->
    cfgkat_loop_silent_body e i sigma a ->
    exists m,
      m < n /\
      CFGKATExpressionFiniteSized m (while b do e, sigma) a r.
Proof.
  intros n b e i sigma a r Hfin Hb Hbody.
  inversion Hfin; subst.
  - eapply cfgkat_expression_loopseq_finite_smaller
      with (n := n0) in Hbody; eauto; firstorder.
  - contradiction.
Qed.

Inductive CFGKATSyntacticFiniteDynamics :
  nat ->
  CFGKATSyntacticAutomaton ->
  CFGKATSyntConfiguration ->
  Atom ->
  CFGKATAutomatonOutputs CFGKATSyntConfiguration ->
  Prop :=
| CFGKATSyntacticFiniteExpression :
    forall n s a r,
      CFGKATExpressionFiniteSized n s a r ->
      CFGKATSyntacticFiniteDynamics n CFGKATSyntacticExpressionAutomaton s a r
| CFGKATSyntacticFiniteResolvedDirect :
    forall n aut (y : environment CFGKATSyntConfiguration) s a r,
      CFGKATSyntacticFiniteDynamics n aut s a r ->
      ResolveCFGKATAutomatonNotBound y r ->
      CFGKATSyntacticFiniteDynamics
        (S n)
        (CFGKATSyntacticResolvedAutomaton aut y) s a r
| CFGKATSyntacticFiniteResolvedBound :
    forall n1 n2 aut (y : environment CFGKATSyntConfiguration) s a l i t r,
      CFGKATSyntacticFiniteDynamics n1 aut s a
        (CFGKATAutomatonJump l i) ->
      y l i = Some t ->
      CFGKATSyntacticFiniteDynamics n2
        (CFGKATSyntacticResolvedAutomaton aut y) t a r ->
      CFGKATSyntacticFiniteDynamics
        (S (n1 + n2))
        (CFGKATSyntacticResolvedAutomaton aut y) s a r.

Local Lemma CFGKATSyntacticFiniteDynamics_sound :
  forall n aut s a r,
    CFGKATSyntacticFiniteDynamics n aut s a r ->
    cfgkat_synt_transitions aut s a r.
Proof.
  intros n aut s a r Hfin.
  induction Hfin; simpl.
  - apply CFGKATExpressionDynamicsFinite.
    eapply CFGKATExpressionFiniteSized_sound; eauto.
  - apply ResolveCFGKATAutomatonDynamicsFinite.
    apply ResolveCFGKATAutomatonFiniteDynamicsDirect; eauto.
  - eapply ResolveCFGKATAutomatonDynamicsBoundJump; eauto.
    apply cfgkat_synt_dynamics_functional.
Qed.

Local Lemma resolve_finite_to_syntactic_finite :
  forall aut y,
    (forall s a r,
      r <> CFGKATAutomatonReject ->
      cfgkat_synt_transitions aut s a r ->
      exists n, CFGKATSyntacticFiniteDynamics n aut s a r) ->
    forall s a r,
      r <> CFGKATAutomatonReject ->
      ResolveCFGKATAutomatonFiniteDynamics
        aut (cfgkat_synt_transitions aut s) y a r ->
      exists n,
        CFGKATSyntacticFiniteDynamics n
          (CFGKATSyntacticResolvedAutomaton aut y) s a r.
Proof.
  intros aut y Hcomplete s a r Hnot Hfin.
  remember (cfgkat_synt_transitions aut s) as d eqn:Hd.
  revert s Hnot Hd.
  induction Hfin; intros x Hnot Hd; subst d.
  - destruct (Hcomplete x a zeta Hnot H) as [n Hbase].
    exists (S n).
    eapply CFGKATSyntacticFiniteResolvedDirect; eauto.
  - destruct (Hcomplete x a (CFGKATAutomatonJump l i')
      ltac:(discriminate) H) as [n1 Hjump].
    destruct (IHHfin s Hnot eq_refl) as [n2 Hchild].
    exists (S (n1 + n2)).
    eapply CFGKATSyntacticFiniteResolvedBound; eauto.
Qed.

Local Lemma cfgkat_synt_dynamics_nonreject_finite :
  forall aut s a r,
    r <> CFGKATAutomatonReject ->
    cfgkat_synt_transitions aut s a r ->
    exists n, CFGKATSyntacticFiniteDynamics n aut s a r.
Proof.
  induction aut as [| aut IH y]; intros s a r Hnot Hdyn.
  - simpl in Hdyn.
    destruct (CFGKATExpressionFiniteDynamics_sized s a r
      (cfgkat_dynamics_nonreject_finite s a r Hnot Hdyn))
      as [n Hsized].
    exists n. constructor. exact Hsized.
  - simpl in Hdyn.
    inversion Hdyn; subst.
    + eapply resolve_finite_to_syntactic_finite; eauto.
    + contradiction.
Qed.

Inductive CFGKATSyntacticSilentTransition :
  CFGKATSyntacticAutomaton ->
  Atom ->
  CFGKATSyntConfiguration ->
  CFGKATSyntConfiguration ->
  Prop :=
| CFGKATSyntacticSilentLoop :
    forall aut a b e i sigma,
      eval_test b a i ->
      cfgkat_loop_silent_body e i sigma a ->
      CFGKATSyntacticSilentTransition aut a
        (while b do e, i)
        (while b do e, sigma)
| CFGKATSyntacticSilentLoopSeq :
    forall aut a b e e' i sigma,
      cfgkat_loop_silent_body e' i sigma a ->
      CFGKATSyntacticSilentTransition aut a
        (e' |> while b do e, i)
        (while b do e, sigma)
| CFGKATSyntacticSilentBoundJump :
    forall aut (zeta : environment CFGKATSyntConfiguration) a x l i s,
      cfgkat_synt_transitions aut x a (CFGKATAutomatonJump l i) ->
      zeta l i = Some s ->
      CFGKATSyntacticSilentTransition
        (CFGKATSyntacticResolvedAutomaton aut zeta) a x s
| CFGKATSyntacticSilentWeaken :
    forall aut (zeta : environment CFGKATSyntConfiguration) a x s,
      CFGKATSyntacticSilentTransition aut a x s ->
      CFGKATSyntacticSilentTransition
        (CFGKATSyntacticResolvedAutomaton aut zeta) a x s.

Local Lemma CFGKATSilentTransition_syntactic :
  forall aut ys a s t,
    CFGKATSilentTransition aut ys a s t ->
    CFGKATSyntacticSilentTransition (resolve_list aut ys) a s t.
Proof.
  intros aut ys a s t Hsilent.
  induction Hsilent.
  - now apply CFGKATSyntacticSilentLoop.
  - now apply CFGKATSyntacticSilentLoopSeq.
  - unfold resolve_list.
    rewrite fold_left_app. simpl.
    eapply CFGKATSyntacticSilentBoundJump; eauto.
  - unfold resolve_list.
    rewrite fold_left_app. simpl.
    now apply CFGKATSyntacticSilentWeaken.
Qed.

Ltac enforce_functionality_cfgkat_synt_dynamics :=
  match goal with
  | [ Hleft: cfgkat_synt_transitions ?aut ?s ?a ?z0,
      Hright: cfgkat_synt_transitions ?aut ?s ?a ?z1 |- _ ] =>
    let Hequal := fresh "H" in
    pose proof (cfgkat_synt_dynamics_functional
                aut s a _ _ Hleft Hright) as Hequal;
    inversion Hequal; clear Hequal; subst;
    try intuition
  end.

Local Lemma CFGKATSyntacticSilentTransition_finite_smaller :
  forall n aut s t a r,
    CFGKATSyntacticSilentTransition aut a s t ->
    CFGKATSyntacticFiniteDynamics n aut s a r ->
    r <> CFGKATAutomatonReject ->
    exists m,
      m < n /\
      CFGKATSyntacticFiniteDynamics m aut t a r.
Proof.
  intros n aut s t a r Hsilent Hfin Hnot.
  revert t Hsilent Hnot.
  induction Hfin; intros t0 Hsilent Hnot.
  - inversion Hsilent; subst.
    + destruct (cfgkat_expression_loop_finite_smaller
        n b e i sigma a r H H0 H1) as [m [Hlt Htarget]].
      exists m. intuition. now constructor.
    + destruct (cfgkat_expression_loopseq_finite_smaller
        n b e e' i sigma a r H H0) as [m [Hlt Htarget]].
      exists m. intuition. now constructor.
  - inversion Hsilent; subst.
    + destruct (IHHfin (while b do e, sigma)) as [m [Hlt Hsmaller]]; eauto.
      * now apply CFGKATSyntacticSilentLoop.
      * exists (S m). intuition; try lia.
        eapply CFGKATSyntacticFiniteResolvedDirect; eauto.
    + destruct (IHHfin (while b do e, sigma)) as [m [Hlt Hsmaller]]; eauto.
      * now apply CFGKATSyntacticSilentLoopSeq.
      * exists (S m). intuition; try lia.
        eapply CFGKATSyntacticFiniteResolvedDirect; eauto.
    + apply CFGKATSyntacticFiniteDynamics_sound in Hfin as Hbase.
      enforce_functionality_cfgkat_synt_dynamics.
      congruence.
    + destruct (IHHfin t0) as [m [Hlt Hsmaller]]; eauto.
      exists (S m); intuition try lia.
      eapply CFGKATSyntacticFiniteResolvedDirect; eauto.
  - inversion Hsilent; subst.
    + destruct (IHHfin1 (while b do e, sigma)) as [m [Hlt Hsmaller]].
      * now apply CFGKATSyntacticSilentLoop.
      * discriminate.
      * exists (S (m + n2)). intuition try lia.
        eapply CFGKATSyntacticFiniteResolvedBound; eauto.
    + destruct (IHHfin1 (while b do e, sigma)) as [m [Hlt Hsmaller]].
      * now apply CFGKATSyntacticSilentLoopSeq.
      * discriminate.
      * exists (S (m + n2)). intuition try lia.
        eapply CFGKATSyntacticFiniteResolvedBound; eauto.
    + apply CFGKATSyntacticFiniteDynamics_sound in Hfin1 as Hbase.
      enforce_functionality_cfgkat_synt_dynamics.
      rewrite H6 in H; inversion H; subst.
      exists n2. intuition try lia.
    + destruct (IHHfin1 t0) as [m [Hlt Hsmaller]]; eauto.
      * discriminate.
      * exists (S (m + n2)). intuition try lia.
        eapply CFGKATSyntacticFiniteResolvedBound; eauto.
Qed.

Local Lemma rejecting_set_no_nonreject_finite :
  forall n aut ys a N s r,
    cfgkat_rejecting_set aut ys a N ->
    N s ->
    r <> CFGKATAutomatonReject ->
    CFGKATSyntacticFiniteDynamics n (resolve_list aut ys) s a r ->
    False.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros aut ys a N s r Hrej HNs Hnot Hfin.
  destruct (Hrej s HNs) as [Hreject | [t [Hsilent HNt]]].
  - apply CFGKATSyntacticFiniteDynamics_sound in Hfin. apply Hnot.
    now eapply resolve_list_dynamics_functional; eauto.
  - apply CFGKATSilentTransition_syntactic in Hsilent as Hsynt_silent.
    destruct (CFGKATSyntacticSilentTransition_finite_smaller
      n (resolve_list aut ys) s t a r Hsynt_silent Hfin Hnot)
      as [m [Hlt Hsmaller]].
    eapply IH; eauto.
Qed.

Lemma rejecting_set_resolves_reject :
  forall
    (aut : CFGKATSyntacticAutomaton)
    (ys : list (environment CFGKATSyntConfiguration))
    (a : Atom)
    (s : CFGKATSyntConfiguration),
    cfgkat_transitions (resolve_list aut ys) s a CFGKATAutomatonReject <->
    exists N,
      cfgkat_rejecting_set aut ys a N /\ N s.
Proof.
  intros aut ys a s. split.
  - intros Hreject.
    exists (fun t => t = s). split.
    + intros t Ht. subst. left. exact Hreject.
    + reflexivity.
  - intros [N [Hrej HNs]].
    destruct (resolve_list_synt_dynamics_total_known aut ys s a) as [r Hr].
    destruct (classic (r = CFGKATAutomatonReject)).
    + simpl. congruence.
    + destruct (cfgkat_synt_dynamics_nonreject_finite
        (resolve_list aut ys) s a r H Hr) as [n Hfin].
      exfalso. now eapply rejecting_set_no_nonreject_finite; eauto.
Qed.

Corollary rejecting_set_member_resolves_reject :
  forall
    (aut : CFGKATSyntacticAutomaton)
    (ys : list (environment CFGKATSyntConfiguration))
    (a : Atom)
    (N : CFGKATSyntConfiguration -> Prop)
    (s : CFGKATSyntConfiguration),
    cfgkat_rejecting_set aut ys a N ->
    N s ->
    cfgkat_transitions (resolve_list aut ys) s a CFGKATAutomatonReject.
Proof.
  intros aut ys a N s Hrej HNs.
  apply (proj2 (rejecting_set_resolves_reject aut ys a s)).
  exists N. split; assumption.
Qed.

Lemma productive_resolution_complete :
  forall
    (aut : CFGKATSyntacticAutomaton)
    (ys : list (environment CFGKATSyntConfiguration))
    a x zeta,
    cfgkat_transitions (resolve_list aut ys) x a zeta ->
    zeta <> CFGKATAutomatonReject ->
    productive_resolution aut ys a x zeta.
Proof.
  intros aut ys a x zeta Hres Hnz.
  pose (N := fun s => forall zeta', ~ productive_resolution aut ys a s zeta').
  destruct (classic (exists zeta',
      productive_resolution aut ys a x zeta')) as [[zeta' Hprod] | Hnone].
  - erewrite resolve_list_dynamics_functional; eauto.
    now apply productive_resolution_resolves.
  - exfalso. apply Hnz.
    erewrite resolve_list_dynamics_functional; eauto.
    eapply rejecting_set_member_resolves_reject with (N := N); try firstorder.
    intros s HNs.
    destruct (cfgkat_synt_dynamics_total aut s a) as [raw Hraw].
    destruct raw; try (exfalso; eapply HNs; constructor; now eauto).
    + left. subst.
      now eapply Hlift_reject.
    + destruct (first_binding_dec ys l i) as [[t Hfb] | Hfree].
      * right. exists t. intuition.
        -- eapply first_binding_silent_transition; eauto.
        -- intros zeta' Hprod_t. eapply HNs.
           eapply productive_resolution_bound_jump; eauto.
      * exfalso. eapply HNs.
        eapply productive_resolution_free_jump; eassumption.
Qed.

Inductive CFGKATStrongTerminalStep
  (aut1 aut2 : CFGKATSyntacticAutomaton)
  (ys1 ys2 : list (environment CFGKATSyntConfiguration))
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (a : Atom)
  (s u : CFGKATSyntConfiguration)
  : Prop :=
| CFGKATStrongTerminalHalt :
    forall zeta,
      cfgkat_halting_output zeta ->
      cfgkat_transitions (resolve_list aut1 ys1) s a zeta ->
      cfgkat_transitions (resolve_list aut2 ys2) u a zeta ->
      CFGKATStrongTerminalStep aut1 aut2 ys1 ys2 R a s u
| CFGKATStrongTerminalNext :
    forall p s' u',
      cfgkat_transitions (resolve_list aut1 ys1) s a
        (CFGKATAutomatonNext p s') ->
      cfgkat_transitions (resolve_list aut2 ys2) u a
        (CFGKATAutomatonNext p u') ->
      R s' u' ->
      CFGKATStrongTerminalStep aut1 aut2 ys1 ys2 R a s u.

Inductive CFGKATStrongSilentReach
  (aut1 aut2 : CFGKATSyntacticAutomaton)
  (ys1 ys2 : list (environment CFGKATSyntConfiguration))
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (a : Atom)
  (s0 u0 : CFGKATSyntConfiguration)
  : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop :=
| CFGKATStrongSilentReachRefl :
    R s0 u0 ->
    CFGKATStrongSilentReach aut1 aut2 ys1 ys2 R a s0 u0 s0 u0
| CFGKATStrongSilentReachStep :
    forall s u s' u',
      CFGKATStrongSilentReach aut1 aut2 ys1 ys2 R a s0 u0 s u ->
      CFGKATSilentTransition aut1 ys1 a s s' ->
      CFGKATSilentTransition aut2 ys2 a u u' ->
      R s' u' ->
      CFGKATStrongSilentReach aut1 aut2 ys1 ys2 R a s0 u0 s' u'.

Local Lemma CFGKATStrongSilentReach_relation :
  forall aut1 aut2 ys1 ys2 R a s0 u0 s u,
    CFGKATStrongSilentReach aut1 aut2 ys1 ys2 R a s0 u0 s u ->
    R s u.
Proof.
  intros aut1 aut2 ys1 ys2 R a s0 u0 s u Hreach.
  induction Hreach; assumption.
Qed.

Local Lemma CFGKATStrongSilentReach_left_dynamics :
  forall aut1 aut2 ys1 ys2 R a s0 u0 s u,
    CFGKATStrongSilentReach aut1 aut2 ys1 ys2 R a s0 u0 s u ->
    forall r,
      cfgkat_transitions (resolve_list aut1 ys1) s0 a r <->
      cfgkat_transitions (resolve_list aut1 ys1) s a r.
Proof.
  intros aut1 aut2 ys1 ys2 R a s0 u0 s u Hreach.
  induction Hreach; intro r.
  - split; intro Htrans; exact Htrans.
  - rewrite IHHreach.
    now apply CFGKATSilentTransition_preserves_dynamics.
Qed.

Local Lemma CFGKATStrongSilentReach_right_dynamics :
  forall aut1 aut2 ys1 ys2 R a s0 u0 s u,
    CFGKATStrongSilentReach aut1 aut2 ys1 ys2 R a s0 u0 s u ->
    forall r,
      cfgkat_transitions (resolve_list aut2 ys2) u0 a r <->
      cfgkat_transitions (resolve_list aut2 ys2) u a r.
Proof.
  intros aut1 aut2 ys1 ys2 R a s0 u0 s u Hreach.
  induction Hreach; intro r.
  - split; intro Htrans; exact Htrans.
  - rewrite IHHreach.
    now apply CFGKATSilentTransition_preserves_dynamics.
Qed.

Local Lemma CFGKATStrongTerminalStep_lifted :
  forall aut1 aut2 ys1 ys2 R a s u zeta1 zeta2,
    CFGKATStrongTerminalStep aut1 aut2 ys1 ys2 R a s u ->
    cfgkat_transitions (resolve_list aut1 ys1) s a zeta1 ->
    cfgkat_transitions (resolve_list aut2 ys2) u a zeta2 ->
    lifted_relation R zeta1 zeta2.
Proof.
  intros aut1 aut2 ys1 ys2 R a s u zeta1 zeta2 Hterm Hleft Hright.
  destruct Hterm as [zeta Hhalt Hterm_left Hterm_right
                    | p s' u' Hterm_left Hterm_right HRnext].
  - pose proof (resolve_list_dynamics_functional ys1 aut1 s) as Hfun.
    enforce_functionality. clear Hfun.
    pose proof (resolve_list_dynamics_functional ys2 aut2 u) as Hfun.
    enforce_functionality. clear Hfun.
    destruct zeta2; now constructor.
  - pose proof (resolve_list_dynamics_functional ys1 aut1 s) as Hfun.
    enforce_functionality. clear Hfun.
    pose proof (resolve_list_dynamics_functional ys2 aut2 u) as Hfun.
    enforce_functionality. clear Hfun.
    constructor.
    exact HRnext.
Qed.

Local Definition CFGKATStrongTerminalReach
  (aut1 aut2 : CFGKATSyntacticAutomaton)
  (ys1 ys2 : list (environment CFGKATSyntConfiguration))
  (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
  (a : Atom)
  (s0 u0 : CFGKATSyntConfiguration)
  : Prop :=
  exists s u,
    CFGKATStrongSilentReach aut1 aut2 ys1 ys2 R a s0 u0 s u /\
    CFGKATStrongTerminalStep aut1 aut2 ys1 ys2 R a s u.

Local Lemma CFGKATStrongNoTerminal_rejecting_left :
  forall aut1 aut2 ys1 ys2 R a s0 u0,
    (forall s u,
      R s u ->
      CFGKATStrongStep aut1 aut2 ys1 ys2 R a s u) ->
    (forall s u,
      CFGKATStrongSilentReach aut1 aut2 ys1 ys2 R a s0 u0 s u ->
      ~ CFGKATStrongTerminalStep aut1 aut2 ys1 ys2 R a s u) ->
    cfgkat_rejecting_set aut1 ys1 a
      (fun s =>
        exists u,
          CFGKATStrongSilentReach aut1 aut2 ys1 ys2 R a s0 u0 s u).
Proof.
  intros aut1 aut2 ys1 ys2 R a s0 u0 Hstrong Hnot_terminal.
  intros s [u Hreach].
  apply CFGKATStrongSilentReach_relation in Hreach as HR.
  destruct (Hstrong s u HR) as
    [zeta Hhalt Hleft Hright |
     p s' u' Hleft Hright HRnext |
     s' u' Hsilent_left Hsilent_right HRnext].
  - exfalso. eapply Hnot_terminal; eauto.
    eapply CFGKATStrongTerminalHalt; eauto.
  - exfalso. eapply Hnot_terminal; eauto.
    eapply CFGKATStrongTerminalNext; eauto.
  - right. exists s'. intuition.
    exists u'. eapply CFGKATStrongSilentReachStep; eauto.
Qed.

Local Lemma CFGKATStrongNoTerminal_rejecting_right :
  forall aut1 aut2 ys1 ys2 R a s0 u0,
    (forall s u,
      R s u ->
      CFGKATStrongStep aut1 aut2 ys1 ys2 R a s u) ->
    (forall s u,
      CFGKATStrongSilentReach aut1 aut2 ys1 ys2 R a s0 u0 s u ->
      ~ CFGKATStrongTerminalStep aut1 aut2 ys1 ys2 R a s u) ->
    cfgkat_rejecting_set aut2 ys2 a
      (fun u =>
        exists s,
          CFGKATStrongSilentReach aut1 aut2 ys1 ys2 R a s0 u0 s u).
Proof.
  intros aut1 aut2 ys1 ys2 R a s0 u0 Hstrong Hnot_terminal.
  intros s [u Hreach].
  apply CFGKATStrongSilentReach_relation in Hreach as HR.
  destruct (Hstrong u s HR) as
    [zeta Hhalt Hleft Hright |
     p s' u' Hleft Hright HRnext |
     s' u' Hsilent_left Hsilent_right HRnext].
  - exfalso. eapply Hnot_terminal; eauto.
    eapply CFGKATStrongTerminalHalt; eauto.
  - exfalso. eapply Hnot_terminal; eauto.
    eapply CFGKATStrongTerminalNext; eauto.
  - right. exists u'. intuition.
    exists s'. eapply CFGKATStrongSilentReachStep; eauto.
Qed.

Local Lemma CFGKATStrong_terminal_or_reject :
  forall aut1 aut2 ys1 ys2 R a s0 u0,
    R s0 u0 ->
    (forall s u,
      R s u ->
      CFGKATStrongStep aut1 aut2 ys1 ys2 R a s u) ->
    CFGKATStrongTerminalReach aut1 aut2 ys1 ys2 R a s0 u0 \/
    (cfgkat_transitions (resolve_list aut1 ys1) s0 a CFGKATAutomatonReject /\
     cfgkat_transitions (resolve_list aut2 ys2) u0 a CFGKATAutomatonReject).
Proof.
  intros aut1 aut2 ys1 ys2 R a s0 u0 HR0 Hstrong.
  destruct (classic
    (CFGKATStrongTerminalReach aut1 aut2 ys1 ys2 R a s0 u0))
    as [Hterminal | Hno_terminal]; eauto; right.
  assert (Hnot_terminal :
    forall s u,
      CFGKATStrongSilentReach aut1 aut2 ys1 ys2 R a s0 u0 s u ->
      ~ CFGKATStrongTerminalStep aut1 aut2 ys1 ys2 R a s u)
    by firstorder.
  split.
  + eapply rejecting_set_member_resolves_reject.
    * eapply CFGKATStrongNoTerminal_rejecting_left; eauto.
    * exists u0. now constructor.
  + eapply rejecting_set_member_resolves_reject.
    * eapply CFGKATStrongNoTerminal_rejecting_right; eauto.
    * exists s0. now constructor.
Qed.

Local Lemma strong_bisim_step :
  forall
        (aut1 aut2 : CFGKATSyntacticAutomaton)
        (ys1 ys2 : list (environment CFGKATSyntConfiguration))
    (R : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop)
    (Hstrong :
      forall s u a,
        R s u ->
        CFGKATStrongStep aut1 aut2 ys1 ys2 R a s u),
  forall s u a zeta1 zeta2,
    R s u ->
    cfgkat_transitions (resolve_list aut1 ys1) s a zeta1 ->
    cfgkat_transitions (resolve_list aut2 ys2) u a zeta2 ->
    lifted_relation R zeta1 zeta2.
Proof.
  intros aut1 aut2 ys1 ys2 R Hstrong s u a zeta1 zeta2 HR Hleft Hright.
  destruct (CFGKATStrong_terminal_or_reject
    aut1 aut2 ys1 ys2 R a s u HR (fun s u HR => Hstrong s u a HR)) as [
    [s' [u' [Hreach Hterminal]]] |
    [Hreject_left Hreject_right]
  ].
  - eapply CFGKATStrongTerminalStep_lifted.
    + apply Hterminal.
    + rewrite CFGKATStrongSilentReach_left_dynamics in Hleft; eauto.
    + rewrite CFGKATStrongSilentReach_right_dynamics in Hright; eauto.
  - pose proof (resolve_list_dynamics_functional ys1 aut1 s) as Hfun.
    enforce_functionality. clear Hfun.
    pose proof (resolve_list_dynamics_functional ys2 aut2 u) as Hfun.
    enforce_functionality. clear Hfun.
    now constructor.
Qed.

Obligation Tactic := idtac.

Program Definition strong_bisim_to_bisim
      {aut1 aut2 : CFGKATSyntacticAutomaton}
      (ys1 ys2 : list (environment CFGKATSyntConfiguration))
  (B : @CFGKATStrongBisimulation aut1 aut2 ys1 ys2)
  : @CFGKATAutomatonBisimulation (resolve_list aut1 ys1)
                                 (resolve_list aut2 ys2) := {|
  cfgkat_relation := cfgkat_strong_relation B;
|}.
Next Obligation.
  destruct B; simpl in *.
  eapply strong_bisim_step; eauto.
Qed.
