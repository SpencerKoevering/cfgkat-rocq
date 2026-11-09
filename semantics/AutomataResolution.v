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

From CFGKAT.Syntax Require Export Preliminaries.

Local Open Scope type_scope.


Variant CFGKATAutomatonOutputs {state: Type} :=
| CFGKATAutomatonReject
| CFGKATAutomatonAccept (i: IndicatorAssignment)
| CFGKATAutomatonBreak (i: IndicatorAssignment)
| CFGKATAutomatonContinue (i: IndicatorAssignment)
| CFGKATAutomatonReturn
| CFGKATAutomatonJump (l: Label) (i: IndicatorAssignment)
| CFGKATAutomatonNext (p: Action) (s: state)
.

Arguments CFGKATAutomatonOutputs : clear implicits.

Definition CFGKATAutomatonDynamics (states: Type) :=
  Atom ->
  CFGKATAutomatonOutputs states ->
  Prop
.

Definition cfgkat_automaton_dynamics_functional
    {states: Type}
    (d: CFGKATAutomatonDynamics states)
:=
  forall a zeta1 zeta2,
    d a zeta1 ->
    d a zeta2 ->
    zeta1 = zeta2
.

Definition cfgkat_automaton_dynamics_total
    {states: Type}
    (d: CFGKATAutomatonDynamics states)
:=
  forall a,
    exists zeta,
      d a zeta
.

Record CFGKATAutomaton := {
  cfgkat_states:
    Type;
  cfgkat_transitions:
    cfgkat_states -> CFGKATAutomatonDynamics cfgkat_states;
}.

Record CFGKATAutomatonWlFormed (aut: CFGKATAutomaton) := {
  cfgkat_transitions_functional:
    forall s, cfgkat_automaton_dynamics_functional
                (cfgkat_transitions aut s);
}.


Definition ResolveCFGKATAutomatonNotBound
    {states: Type}
    (E: environment states)
    (zeta: CFGKATAutomatonOutputs states)
  : Prop :=
  match zeta with
  | CFGKATAutomatonJump l i => E l i = None
  | _ => True
  end.

Inductive ResolveCFGKATAutomatonFiniteDynamics
    (aut: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (E: environment (cfgkat_states aut))
:
    CFGKATAutomatonDynamics (cfgkat_states aut)
:=
| ResolveCFGKATAutomatonFiniteDynamicsDirect:
    forall a zeta,
      d a zeta ->
      ResolveCFGKATAutomatonNotBound E zeta ->
      ResolveCFGKATAutomatonFiniteDynamics aut d E a zeta
| ResolveCFGKATAutomatonFiniteDynamicsBoundJump:
    forall a l i' zeta s,
      d a (CFGKATAutomatonJump l i') ->
      E l i' = Some s ->
      ResolveCFGKATAutomatonFiniteDynamics aut
        (cfgkat_transitions aut s) E a zeta ->
      ResolveCFGKATAutomatonFiniteDynamics aut d E a zeta
.

Definition ResolveCFGKATAutomatonNoFiniteResult
    (aut: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (E: environment (cfgkat_states aut))
    (a: Atom)
  : Prop :=
  forall r, ~ ResolveCFGKATAutomatonFiniteDynamics aut d E a r.

Inductive ResolveCFGKATAutomatonDynamics
    (aut: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (E: environment (cfgkat_states aut))
:
    CFGKATAutomatonDynamics (cfgkat_states aut)
:=
| ResolveCFGKATAutomatonDynamicsFinite:
    forall a zeta,
      ResolveCFGKATAutomatonFiniteDynamics aut d E a zeta ->
      ResolveCFGKATAutomatonDynamics aut d E a zeta
| ResolveCFGKATAutomatonDynamicsDefaultReject:
    forall a,
      ResolveCFGKATAutomatonNoFiniteResult aut d E a ->
      ResolveCFGKATAutomatonDynamics aut d E a CFGKATAutomatonReject
.

Lemma ResolveCFGKATAutomatonDynamicsReject:
  forall (aut : CFGKATAutomaton) d
    (E : environment (cfgkat_states aut)) a,
    d a CFGKATAutomatonReject ->
    ResolveCFGKATAutomatonDynamics aut d E a CFGKATAutomatonReject.
Proof.
  intros aut d E a H.
  apply ResolveCFGKATAutomatonDynamicsFinite.
  apply ResolveCFGKATAutomatonFiniteDynamicsDirect; simpl; auto.
Qed.

Lemma ResolveCFGKATAutomatonDynamicsAccept:
  forall (aut : CFGKATAutomaton) d
    (E : environment (cfgkat_states aut)) a i',
    d a (CFGKATAutomatonAccept i') ->
    ResolveCFGKATAutomatonDynamics aut d E a (CFGKATAutomatonAccept i').
Proof.
  intros aut d E a i' H.
  apply ResolveCFGKATAutomatonDynamicsFinite.
  apply ResolveCFGKATAutomatonFiniteDynamicsDirect; simpl; auto.
Qed.

Lemma ResolveCFGKATAutomatonDynamicsBreak:
  forall (aut : CFGKATAutomaton) d
    (E : environment (cfgkat_states aut)) a i',
    d a (CFGKATAutomatonBreak i') ->
    ResolveCFGKATAutomatonDynamics aut d E a (CFGKATAutomatonBreak i').
Proof.
  intros aut d E a i' H.
  apply ResolveCFGKATAutomatonDynamicsFinite.
  apply ResolveCFGKATAutomatonFiniteDynamicsDirect; simpl; auto.
Qed.

Lemma ResolveCFGKATAutomatonDynamicsContinue:
  forall (aut : CFGKATAutomaton) d
    (E : environment (cfgkat_states aut)) a i',
    d a (CFGKATAutomatonContinue i') ->
    ResolveCFGKATAutomatonDynamics aut d E a (CFGKATAutomatonContinue i').
Proof.
  intros aut d E a i' H.
  apply ResolveCFGKATAutomatonDynamicsFinite.
  apply ResolveCFGKATAutomatonFiniteDynamicsDirect; simpl; auto.
Qed.

Lemma ResolveCFGKATAutomatonDynamicsReturn:
  forall (aut : CFGKATAutomaton) d
    (E : environment (cfgkat_states aut)) a,
    d a CFGKATAutomatonReturn ->
    ResolveCFGKATAutomatonDynamics aut d E a CFGKATAutomatonReturn.
Proof.
  intros aut d E a H.
  apply ResolveCFGKATAutomatonDynamicsFinite.
  apply ResolveCFGKATAutomatonFiniteDynamicsDirect; simpl; auto.
Qed.

Lemma ResolveCFGKATAutomatonDynamicsNext:
  forall (aut : CFGKATAutomaton) d
    (E : environment (cfgkat_states aut)) a p s,
    d a (CFGKATAutomatonNext p s) ->
    ResolveCFGKATAutomatonDynamics aut d E a (CFGKATAutomatonNext p s).
Proof.
  intros aut d E a p s H.
  apply ResolveCFGKATAutomatonDynamicsFinite.
  apply ResolveCFGKATAutomatonFiniteDynamicsDirect; simpl; auto.
Qed.

Lemma ResolveCFGKATAutomatonDynamicsFreeJump:
  forall (aut : CFGKATAutomaton) d
    (E : environment (cfgkat_states aut)) a l i',
    d a (CFGKATAutomatonJump l i') ->
    E l i' = None ->
    ResolveCFGKATAutomatonDynamics aut d E a (CFGKATAutomatonJump l i').
Proof.
  intros aut d E a l i' Hjump Hfree.
  apply ResolveCFGKATAutomatonDynamicsFinite.
  apply ResolveCFGKATAutomatonFiniteDynamicsDirect; simpl; auto.
Qed.

Local Lemma resolve_finite_empty_identity :
  forall (aut : CFGKATAutomaton) d a x
    (E : environment (cfgkat_states aut)),
    (forall l i, E l i = None) ->
    ResolveCFGKATAutomatonFiniteDynamics aut d E a x <-> d a x.
Proof.
  intros aut d a x E Hempty; intuition.
  - induction H; auto.
    rewrite Hempty in H0. discriminate.
  - apply ResolveCFGKATAutomatonFiniteDynamicsDirect; auto.
    destruct x; simpl; auto.
Qed.

Lemma resolve_empty_identity :
  forall (aut : CFGKATAutomaton) d a x
    (E : environment (cfgkat_states aut)),
    cfgkat_automaton_dynamics_total d ->
    (forall l i, E l i = None) ->
    ResolveCFGKATAutomatonDynamics aut d E a x <-> d a x.
Proof.
  intros aut d a x E Htotal Hempty; intuition.
  - inversion H; subst.
    + now apply (proj1 (resolve_finite_empty_identity aut d a x E Hempty)).
    + exfalso.
      destruct (Htotal a) as [zeta Hzeta].
      unfold ResolveCFGKATAutomatonNoFiniteResult in H0.
      apply (H0 zeta).
      now apply (proj2 (resolve_finite_empty_identity aut d a zeta E Hempty)).
  - apply ResolveCFGKATAutomatonDynamicsFinite.
    now apply (proj2 (resolve_finite_empty_identity aut d a x E Hempty)).
Qed.

Ltac enforce_functionality :=
  match goal with
  | [ Hfunctional: cfgkat_automaton_dynamics_functional ?d,
      Hleft: ?d ?a ?z0,
      Hright: ?d ?a ?z1 |- _ ] =>
    let Hequal := fresh "H" in
    pose proof (Hfunctional _ _ _ Hleft Hright) as Hequal;
    inversion Hequal; clear Hequal; subst;
    try intuition
  | [ Hfunctional: cfgkat_automaton_dynamics_functional ?d,
      Hleft: ?d ?a ?z0,
      Hright: ?d ?a (CFGKATAutomatonJump _ _) |- _ ] =>
    let Hequal := fresh "H" in
    pose proof (Hfunctional _ _ _ Hleft Hright) as Hequal;
    inversion Hequal; clear Hequal; subst;
    try intuition
  end.

Local Lemma resolve_finite_dynamics_preserves_functionality
    (aut: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (E: environment (cfgkat_states aut))
:
    CFGKATAutomatonWlFormed aut ->
    cfgkat_automaton_dynamics_functional d ->
    cfgkat_automaton_dynamics_functional
        (ResolveCFGKATAutomatonFiniteDynamics aut d E)
.
Proof.
  intros Hwf Hfunc.
  unfold cfgkat_automaton_dynamics_functional.
  intros a zeta1 zeta2 Hleft.
  revert zeta2.
  dependent induction Hleft; intros zeta2 Hright;
    dependent destruction Hright.
  - eapply Hfunc; eauto.
  - enforce_functionality.
    inversion H0. congruence.
  - enforce_functionality.
    inversion H2. congruence.
  - enforce_functionality.
    rewrite H0 in H2; inversion H2; subst.
    eapply IHHleft; eauto; apply Hwf.
Qed.

Lemma ResolveCFGKATAutomatonDynamicsBoundJump:
  forall (aut : CFGKATAutomaton) d
    (E : environment (cfgkat_states aut)) a l i' zeta s,
    d a (CFGKATAutomatonJump l i') ->
    E l i' = Some s ->
    ResolveCFGKATAutomatonDynamics aut
      (cfgkat_transitions aut s) E a zeta ->
    cfgkat_automaton_dynamics_functional d ->
    ResolveCFGKATAutomatonDynamics aut d E a zeta.
Proof.
  intros aut d E a l i' zeta s Hjump Hbind Hchild Hfunc.
  inversion Hchild; subst.
  - apply ResolveCFGKATAutomatonDynamicsFinite.
    eapply ResolveCFGKATAutomatonFiniteDynamicsBoundJump; eauto.
  - apply ResolveCFGKATAutomatonDynamicsDefaultReject.
    intros r Hfinite.
    inversion Hfinite as
      [a0 zeta0 Hbase Hnot | a0 l0 i0 zeta0 s0 Hjump0 Hbind0 Hchildfin];
      subst.
    + enforce_functionality.
      simpl in Hnot. rewrite Hnot in Hbind. discriminate.
    + enforce_functionality.
      rewrite Hbind in Hbind0. inversion Hbind0; subst.
      apply (H r). exact Hchildfin.
Qed.

Lemma resolve_dynamics_preserves_functionality
    (aut: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (E: environment (cfgkat_states aut))
:
    CFGKATAutomatonWlFormed aut ->
    cfgkat_automaton_dynamics_functional d ->
    cfgkat_automaton_dynamics_functional
        (ResolveCFGKATAutomatonDynamics aut d E)
.
Proof.
  unfold cfgkat_automaton_dynamics_functional.
  intros Hwf Hfunc a zeta1 zeta2 Hleft Hright.
  inversion Hleft; subst; inversion Hright; subst; auto.
  - eapply resolve_finite_dynamics_preserves_functionality; eauto.
  - exfalso. apply (H0 zeta1). exact H.
  - exfalso. apply (H zeta2). exact H0.
Qed.

Program Definition resolve_cfgkat_automaton
    (aut: CFGKATAutomaton)
    (E: environment (cfgkat_states aut))
:
    CFGKATAutomaton
:= {|
  cfgkat_states := cfgkat_states aut;
  cfgkat_transitions s :=
    ResolveCFGKATAutomatonDynamics aut (cfgkat_transitions aut s) E;
|}.
