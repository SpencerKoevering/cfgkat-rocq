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

From CFGKAT.Semantics Require Export FiniteModels.

Local Open Scope type_scope.

Inductive CFGKATSyntacticAutomaton : Type :=
| CFGKATSyntacticExpressionAutomaton :
    CFGKATSyntacticAutomaton
| CFGKATSyntacticResolvedAutomaton :
    CFGKATSyntacticAutomaton ->
    (environment CFGKATSyntConfiguration) ->
    CFGKATSyntacticAutomaton.

Fixpoint cfgkat_synt_transitions
  (a : CFGKATSyntacticAutomaton)
  : CFGKATSyntConfiguration ->
    CFGKATAutomatonDynamics CFGKATSyntConfiguration :=
  match a with
  | CFGKATSyntacticExpressionAutomaton =>
      CFGKATExpressionDynamics
  | CFGKATSyntacticResolvedAutomaton aut y =>
      fun s =>
        ResolveCFGKATAutomatonDynamics
          {| cfgkat_transitions := cfgkat_synt_transitions aut; |}
          (cfgkat_synt_transitions aut s)
          y
  end.

Definition CFGKATSyntacticToAutomaton
  (a : CFGKATSyntacticAutomaton)
  : CFGKATAutomaton :=
{|
  cfgkat_states := CFGKATSyntConfiguration;
  cfgkat_transitions := cfgkat_synt_transitions a;
|}.

Coercion CFGKATSyntacticToAutomaton :
  CFGKATSyntacticAutomaton >-> CFGKATAutomaton.

Definition CFGKATExpressionAutomaton : CFGKATSyntacticAutomaton :=
  CFGKATSyntacticExpressionAutomaton.

Definition resolve_cfgkat_synt_automaton
  (aut : CFGKATSyntacticAutomaton)
  (y : environment CFGKATSyntConfiguration)
  : CFGKATSyntacticAutomaton :=
  CFGKATSyntacticResolvedAutomaton aut y.

Lemma cfgkat_expression_dynamics_functional
  (s : CFGKATSyntConfiguration)
  :
  cfgkat_automaton_dynamics_functional (CFGKATExpressionDynamics s).
Proof.
  unfold cfgkat_automaton_dynamics_functional.
  intros a zeta1 zeta2 Hleft Hright.
  inversion Hleft; subst; inversion Hright; subst; auto.
  - eapply cfgkat_finite_dynamics_functional; eauto.
  - exfalso. eapply H0; eauto.
  - exfalso. eapply H; eauto.
Qed.

Lemma resolve_dynamics_preserves_totality
  (aut : CFGKATAutomaton)
  (d : CFGKATAutomatonDynamics (cfgkat_states aut))
  (E : environment (cfgkat_states aut))
  :
  cfgkat_automaton_dynamics_total d ->
  (forall s, cfgkat_automaton_dynamics_total (cfgkat_transitions aut s)) ->
  cfgkat_automaton_dynamics_total
    (ResolveCFGKATAutomatonDynamics aut d E).
Proof.
  intros Htotal Htotal_states a.
  destruct (classic (exists zeta,
      ResolveCFGKATAutomatonFiniteDynamics aut d E a zeta))
    as [[zeta Hfinite] | Hnone].
  - exists zeta.
    now apply ResolveCFGKATAutomatonDynamicsFinite.
  - exists CFGKATAutomatonReject.
    apply ResolveCFGKATAutomatonDynamicsDefaultReject; firstorder.
Qed.

Lemma cfgkat_synt_dynamics_functional
  (aut : CFGKATSyntacticAutomaton)
  :
  forall s,
    cfgkat_automaton_dynamics_functional
      (cfgkat_synt_transitions aut s).
Proof.
  induction aut as [| aut IH y]; intros s.
  - apply cfgkat_expression_dynamics_functional.
  - now apply (resolve_dynamics_preserves_functionality
      {| cfgkat_transitions := cfgkat_synt_transitions aut; |}
      (cfgkat_synt_transitions aut s)
      y).
Qed.

Lemma cfgkat_synt_dynamics_total
  (aut : CFGKATSyntacticAutomaton)
  :
  forall s,
    cfgkat_automaton_dynamics_total
      (cfgkat_synt_transitions aut s).
Proof.
  induction aut as [| aut IH y]; intros s.
  - apply CFGKATExpressionDynamics_total.
  - unfold cfgkat_automaton_dynamics_total; intro.
    eapply (resolve_dynamics_preserves_totality
            {| cfgkat_transitions := cfgkat_synt_transitions aut; |})
      in IH; apply IH.
Qed.

Ltac getResolve H :=
  unfold resolve_cfgkat_automaton in H;
  simpl cfgkat_transitions in H.

Tactic Notation "getResolve" :=
  unfold resolve_cfgkat_automaton;
  simpl cfgkat_transitions.

Tactic Notation "getResolve" "in" hyp(H) :=
  unfold resolve_cfgkat_automaton in H;
  simpl cfgkat_transitions in H.

Lemma resolve_no_bound_jump :
  forall (aut : CFGKATAutomaton)
    (y : environment (cfgkat_states aut)) l i d a,
    y l i <> None ->
    ~ ResolveCFGKATAutomatonDynamics aut d y a (CFGKATAutomatonJump l i).
Proof.
  intros aut y l i d a Hne Hres.
  inversion Hres as [a0 zeta Hfin | a0 Hnofin]; subst.
  dependent induction Hfin; subst.
  - intuition.
  - eapply IHHfin; eauto.
    now apply ResolveCFGKATAutomatonDynamicsFinite.
Qed.

Inductive first_binding
  (l : Label) (i : IndicatorAssignment) (s : CFGKATSyntConfiguration)
  : list (environment CFGKATSyntConfiguration) -> Prop :=
  | first_binding_head :
      forall (y : environment CFGKATSyntConfiguration)
        (ys : list (environment CFGKATSyntConfiguration)),
      y l i = Some s ->
      first_binding l i s (y :: ys)
  | first_binding_tail :
      forall (y : environment CFGKATSyntConfiguration)
        (ys : list (environment CFGKATSyntConfiguration)),
      y l i = None ->
      first_binding l i s ys ->
      first_binding l i s (y :: ys).

Program Definition env_union
  (E F : environment CFGKATSyntConfiguration)
  : environment CFGKATSyntConfiguration :=
  mk_resolution_environment
      (fun l i =>
        match E l i with
        | Some s => Some s
        | None => F l i
        end)
      (environment_support E ++ environment_support F) _.
Next Obligation.
  intros l i s Hlookup.
  destruct (E l i) as [e |] eqn:HE.
  - apply in_or_app. left.
    eapply environment_supported. exact HE.
  - apply in_or_app. right.
    eapply environment_supported. exact Hlookup.
Qed.
