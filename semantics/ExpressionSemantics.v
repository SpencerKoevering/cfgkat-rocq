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

From CFGKAT.Semantics Require Export AutomataResolution.

Local Open Scope type_scope.

Inductive CFGKATExpression :=
| CFGKATAssert:
    CFGKATTest ->
    CFGKATExpression
| CFGKATAction:
    Action ->
    CFGKATExpression
| CFGKATAssign:
    IndicatorVariable ->
    IndicatorValue ->
    CFGKATExpression
| CFGKATBreak:
    CFGKATExpression
| CFGKATContinue:
    CFGKATExpression
| CFGKATReturn:
    CFGKATExpression
| CFGKATGoto:
    Label ->
    CFGKATExpression
| CFGKATChoice:
    CFGKATTest ->
    CFGKATExpression ->
    CFGKATExpression ->
    CFGKATExpression
| CFGKATSequence:
    CFGKATExpression ->
    CFGKATExpression ->
    CFGKATExpression
| CFGKATLoopSeq:
    CFGKATExpression ->
    CFGKATExpression ->
    CFGKATExpression
| CFGKATLoop:
    CFGKATTest ->
    CFGKATExpression ->
    CFGKATExpression
.

Definition CFGKATSyntConfiguration := CFGKATExpression * IndicatorAssignment.

Open Scope cfgkat_scope.

Notation "'test' b" :=
  (CFGKATAssert b)
  (at level 40)
.
Notation "'0'" :=
  (CFGKATAssert (0 : CFGKATTest))
.
Notation "'1'" :=
  (CFGKATAssert (1 : CFGKATTest))
.
Notation "'assign' v 'to' x" :=
  (CFGKATAssign x v)
  (at level 40)
.
Notation "'do' p" :=
  (CFGKATAction p)
  (at level 40)
.
Notation "'break'" :=
  CFGKATBreak
.
Notation "'return'" :=
  CFGKATReturn
.
Notation "'continue'"
  := CFGKATContinue
.
Notation "'goto' l" :=
  (CFGKATGoto l)
  (at level 40)
.
Notation "e ';;' f" :=
  (CFGKATSequence e f)
  (at level 50)
.
Notation "e '|>' f" :=
  (CFGKATLoopSeq e f)
  (at level 45)
.
Notation "'if' b 'then' e 'else' f" :=
  (CFGKATChoice b e f)
  (at level 200, b at level 200, e at level 200, f at level 200,
   right associativity)
.
Notation "'while' b 'do' e" :=
  (CFGKATLoop b e)
  (at level 80)
.

Definition update
  (i : IndicatorAssignment)
  (x : IndicatorVariable)
  (v : IndicatorValue)
: IndicatorAssignment :=
  fun y => match Var_eq_dec x y with
  | left _  => v
  | right _ => i y
  end.

Lemma update_same
  (i : IndicatorAssignment)
  (x : IndicatorVariable)
  (v : IndicatorValue)
  :
  update i x v x = v.
Proof.
  unfold update.
  destruct (Var_eq_dec x x) as [_ | Hneq].
  - reflexivity.
  - contradiction.
Qed.

Lemma update_other
  (i : IndicatorAssignment)
  (x y : IndicatorVariable)
  (v : IndicatorValue)
  :
  x <> y ->
  update i x v y = i y.
Proof.
  intro Hxy.
  unfold update.
  destruct (Var_eq_dec x y) as [Heq | _].
  - contradiction.
  - reflexivity.
Qed.

Lemma update_same_value
  (i : IndicatorAssignment)
  (x : IndicatorVariable)
  (v : IndicatorValue)
  :
  i x = v ->
  update i x v = i.
Proof.
  intro Hx.
  apply functional_extensionality.
  intro y.
  destruct (Var_eq_dec x y) as [Heq | Hneq].
  - subst y. rewrite update_same. symmetry. exact Hx.
  - rewrite update_other by exact Hneq. reflexivity.
Qed.

Lemma update_noop
  (i : IndicatorAssignment)
  (x : IndicatorVariable)
  :
  update i x (i x) = i.
Proof.
  apply update_same_value.
  reflexivity.
Qed.

Lemma update_shadow
  (i : IndicatorAssignment)
  (x : IndicatorVariable)
  (v v' : IndicatorValue)
  :
  update (update i x v') x v = update i x v.
Proof.
  apply functional_extensionality.
  intro y.
  destruct (Var_eq_dec x y) as [Heq | Hneq].
  - subst y. repeat rewrite update_same. reflexivity.
  - repeat rewrite update_other by exact Hneq. reflexivity.
Qed.

Lemma update_commute
  (i : IndicatorAssignment)
  (x y : IndicatorVariable)
  (vx vy : IndicatorValue)
  :
  x <> y ->
  update (update i y vy) x vx = update (update i x vx) y vy.
Proof.
  intro Hxy.
  apply functional_extensionality.
  intro z.
  destruct (Var_eq_dec x z) as [Hxz | Hxz].
  - subst z.
    rewrite update_same.
    rewrite update_other by congruence.
    rewrite update_same.
    reflexivity.
  - destruct (Var_eq_dec y z) as [Hyz | Hyz].
    + subst z.
      rewrite update_other by exact Hxz.
      rewrite update_same.
      rewrite update_same.
      reflexivity.
    + rewrite update_other by exact Hxz.
      rewrite update_other by exact Hyz.
      rewrite update_other by exact Hyz.
      rewrite update_other by exact Hxz.
      reflexivity.
Qed.

Inductive CFGKATExpressionFiniteDynamics:
  CFGKATExpression * IndicatorAssignment ->
  CFGKATAutomatonDynamics (CFGKATExpression * IndicatorAssignment)
:=
| CFGKATExpressionFiniteDynamicsAssertTrue:
    forall a i b,
      eval_test b a i ->
      CFGKATExpressionFiniteDynamics (test b, i) a
        (CFGKATAutomatonAccept i)
| CFGKATExpressionFiniteDynamicsAssign:
    forall a i x v,
      CFGKATExpressionFiniteDynamics (assign v to x, i) a
        (CFGKATAutomatonAccept (update i x v))
| CFGKATExpressionFiniteDynamicsAction:
    forall a i p,
      CFGKATExpressionFiniteDynamics (do p, i) a
        (CFGKATAutomatonNext p (1, i))
| CFGKATExpressionFiniteDynamicsBreak:
    forall a i,
      CFGKATExpressionFiniteDynamics (break, i) a
        (CFGKATAutomatonBreak i)
| CFGKATExpressionFiniteDynamicsContinue:
    forall a i,
      CFGKATExpressionFiniteDynamics (continue, i) a
        (CFGKATAutomatonContinue i)
| CFGKATExpressionFiniteDynamicsReturn:
    forall a i,
      CFGKATExpressionFiniteDynamics (return, i) a
        CFGKATAutomatonReturn
| CFGKATExpressionFiniteDynamicsGoto:
    forall a i l,
      CFGKATExpressionFiniteDynamics (goto l, i) a
        (CFGKATAutomatonJump l i)
| CFGKATExpressionFiniteDynamicsChoiceLeft:
    forall a i e1 e2 b r,
      eval_test b a i ->
      CFGKATExpressionFiniteDynamics (e1, i) a r ->
      CFGKATExpressionFiniteDynamics (if b then e1 else e2, i) a r
| CFGKATExpressionFiniteDynamicsChoiceRight:
    forall a i e1 e2 b r,
      ~ eval_test b a i ->
      CFGKATExpressionFiniteDynamics (e2, i) a r ->
      CFGKATExpressionFiniteDynamics (if b then e1 else e2, i) a r
| CFGKATExpressionFiniteDynamicsSequenceSkip:
    forall a i i' e1 e2 r,
      CFGKATExpressionFiniteDynamics (e1, i) a
        (CFGKATAutomatonAccept i') ->
      CFGKATExpressionFiniteDynamics (e2, i') a r ->
      CFGKATExpressionFiniteDynamics (e1;; e2, i) a r
| CFGKATExpressionFiniteDynamicsSequenceReject:
    forall a i e1 e2,
      CFGKATExpressionFiniteDynamics (e1, i) a
        CFGKATAutomatonReject ->
      CFGKATExpressionFiniteDynamics (e1;; e2, i) a
        CFGKATAutomatonReject
| CFGKATExpressionFiniteDynamicsSequenceReturn:
    forall a i e1 e2,
      CFGKATExpressionFiniteDynamics (e1, i) a
        CFGKATAutomatonReturn ->
      CFGKATExpressionFiniteDynamics (e1;; e2, i) a
        CFGKATAutomatonReturn
| CFGKATExpressionFiniteDynamicsSequenceBreak:
    forall a i i' e1 e2,
      CFGKATExpressionFiniteDynamics (e1, i) a
        (CFGKATAutomatonBreak i') ->
      CFGKATExpressionFiniteDynamics (e1;; e2, i) a
        (CFGKATAutomatonBreak i')
| CFGKATExpressionFiniteDynamicsSequenceContinue:
    forall a i i' e1 e2,
      CFGKATExpressionFiniteDynamics (e1, i) a
        (CFGKATAutomatonContinue i') ->
      CFGKATExpressionFiniteDynamics (e1;; e2, i) a
        (CFGKATAutomatonContinue i')
| CFGKATExpressionFiniteDynamicsSequenceJump:
    forall a i i' e1 e2 l,
      CFGKATExpressionFiniteDynamics (e1, i) a
        (CFGKATAutomatonJump l i') ->
      CFGKATExpressionFiniteDynamics (e1;; e2, i) a
        (CFGKATAutomatonJump l i')
| CFGKATExpressionFiniteDynamicsSequenceNext:
    forall a i i' e1 e1' e2 p,
      CFGKATExpressionFiniteDynamics (e1, i) a
        (CFGKATAutomatonNext p (e1', i')) ->
      CFGKATExpressionFiniteDynamics (e1;; e2, i) a
        (CFGKATAutomatonNext p (e1';; e2, i'))
| CFGKATExpressionFiniteDynamicsLoopSeqSkip:
    forall a i i' e1 e2 r,
      CFGKATExpressionFiniteDynamics (e1, i) a
        (CFGKATAutomatonAccept i') ->
      CFGKATExpressionFiniteDynamics (e2, i') a r ->
      CFGKATExpressionFiniteDynamics (e1 |> e2, i) a r
| CFGKATExpressionFiniteDynamicsLoopSeqReject:
    forall a i e1 e2,
      CFGKATExpressionFiniteDynamics (e1, i) a
        CFGKATAutomatonReject ->
      CFGKATExpressionFiniteDynamics (e1 |> e2, i) a
        CFGKATAutomatonReject
| CFGKATExpressionFiniteDynamicsLoopSeqReturn:
    forall a i e1 e2,
      CFGKATExpressionFiniteDynamics (e1, i) a
        CFGKATAutomatonReturn ->
      CFGKATExpressionFiniteDynamics (e1 |> e2, i) a
        CFGKATAutomatonReturn
| CFGKATExpressionFiniteDynamicsLoopSeqBreak:
    forall a i i' e1 e2,
      CFGKATExpressionFiniteDynamics (e1, i) a
        (CFGKATAutomatonBreak i') ->
      CFGKATExpressionFiniteDynamics (e1 |> e2, i) a
        (CFGKATAutomatonAccept i')
| CFGKATExpressionFiniteDynamicsLoopSeqContinue:
    forall a i i' e1 e2 r,
      CFGKATExpressionFiniteDynamics (e1, i) a
        (CFGKATAutomatonContinue i') ->
      CFGKATExpressionFiniteDynamics (e2, i') a r ->
      CFGKATExpressionFiniteDynamics (e1 |> e2, i) a r
| CFGKATExpressionFiniteDynamicsLoopSeqJump:
    forall a i i' e1 e2 l,
      CFGKATExpressionFiniteDynamics (e1, i) a
        (CFGKATAutomatonJump l i') ->
      CFGKATExpressionFiniteDynamics (e1 |> e2, i) a
        (CFGKATAutomatonJump l i')
| CFGKATExpressionFiniteDynamicsLoopSeqNext:
    forall a i i' e1 e1' e2 p,
      CFGKATExpressionFiniteDynamics (e1, i) a
        (CFGKATAutomatonNext p (e1', i')) ->
      CFGKATExpressionFiniteDynamics (e1 |> e2, i) a
        (CFGKATAutomatonNext p (e1' |> e2, i'))
| CFGKATExpressionFiniteDynamicsLoopGuardTrue:
  forall a i b e r,
    eval_test b a i ->
      CFGKATExpressionFiniteDynamics (e |> (while b do e), i) a r ->
      CFGKATExpressionFiniteDynamics (while b do e, i) a r
| CFGKATExpressionFiniteDynamicsLoopGuardFalse:
  forall a i b e,
    ~ eval_test b a i ->
      CFGKATExpressionFiniteDynamics (while b do e, i) a
        (CFGKATAutomatonAccept i)
.

Definition CFGKATExpressionNoFiniteResult
  (s : CFGKATSyntConfiguration)
  (a : Atom)
  : Prop :=
  forall r, ~ CFGKATExpressionFiniteDynamics s a r.

Inductive CFGKATExpressionDynamics :
  CFGKATExpression * IndicatorAssignment ->
  CFGKATAutomatonDynamics (CFGKATExpression * IndicatorAssignment)
:=
| CFGKATExpressionDynamicsFinite:
    forall s a r,
      CFGKATExpressionFiniteDynamics s a r ->
      CFGKATExpressionDynamics s a r
| CFGKATExpressionDynamicsDefaultReject:
    forall s a,
      CFGKATExpressionNoFiniteResult s a ->
      CFGKATExpressionDynamics s a CFGKATAutomatonReject
.

Lemma CFGKATExpressionDynamics_total :
  forall s,
    cfgkat_automaton_dynamics_total
      (CFGKATExpressionDynamics s).
Proof.
  unfold cfgkat_automaton_dynamics_total,
         CFGKATExpressionNoFiniteResult.
  intros s a.
  destruct (classic (exists r, CFGKATExpressionFiniteDynamics s a r))
    as [[r Hr] | Hnone].
  - exists r. now apply CFGKATExpressionDynamicsFinite.
  - exists CFGKATAutomatonReject.
    apply CFGKATExpressionDynamicsDefaultReject.
    intros r Hr.
    apply Hnone. exists r. exact Hr.
Qed.

Ltac use_finite_dynamics_ih :=
  match goal with
  | [ IH : forall zeta2,
        CFGKATExpressionFiniteDynamics ?s ?a zeta2 -> ?z = zeta2,
      H : CFGKATExpressionFiniteDynamics ?s ?a ?z' |- _ ] =>
      let Heq := fresh "Heq" in
      pose proof (IH z' H) as Heq;
      first [exact Heq | inversion Heq; subst; clear Heq]
  end.

Lemma cfgkat_finite_dynamics_functional
  (s: CFGKATSyntConfiguration)
:
  cfgkat_automaton_dynamics_functional (CFGKATExpressionFiniteDynamics s).
Proof.
  unfold cfgkat_automaton_dynamics_functional.
  intros a zeta1 zeta2 Hleft.
  revert zeta2.
  dependent induction Hleft; intros zeta2 Hright;
    dependent destruction Hright;
    try contradiction;
    try solve [repeat use_finite_dynamics_ih; reflexivity].
Qed.

Lemma CFGKATExpressionDynamicsAssertTrue :
  forall a i b,
    eval_test b a i ->
    CFGKATExpressionDynamics (test b, i) a (CFGKATAutomatonAccept i).
Proof.
  intros a i b Hb.
  apply CFGKATExpressionDynamicsFinite.
  apply CFGKATExpressionFiniteDynamicsAssertTrue.
  exact Hb.
Qed.

Lemma CFGKATExpressionDynamicsAssertFalse :
  forall a i b,
    ~ eval_test b a i ->
    CFGKATExpressionDynamics (test b, i) a CFGKATAutomatonReject.
Proof.
  intros a i b Hb.
  apply CFGKATExpressionDynamicsDefaultReject.
  intros r Hfin.
  dependent destruction Hfin.
  contradiction.
Qed.

Lemma CFGKATExpressionDynamicsAssign :
  forall a i x v,
    CFGKATExpressionDynamics (assign v to x, i) a
      (CFGKATAutomatonAccept (update i x v)).
Proof.
  intros. apply CFGKATExpressionDynamicsFinite.
  apply CFGKATExpressionFiniteDynamicsAssign.
Qed.

Lemma CFGKATExpressionDynamicsAction :
  forall a i p,
    CFGKATExpressionDynamics (do p, i) a
      (CFGKATAutomatonNext p (1, i)).
Proof.
  intros. apply CFGKATExpressionDynamicsFinite.
  apply CFGKATExpressionFiniteDynamicsAction.
Qed.

Lemma CFGKATExpressionDynamicsBreak :
  forall a i,
    CFGKATExpressionDynamics (break, i) a (CFGKATAutomatonBreak i).
Proof.
  intros. apply CFGKATExpressionDynamicsFinite.
  apply CFGKATExpressionFiniteDynamicsBreak.
Qed.

Lemma CFGKATExpressionDynamicsContinue :
  forall a i,
    CFGKATExpressionDynamics (continue, i) a (CFGKATAutomatonContinue i).
Proof.
  intros. apply CFGKATExpressionDynamicsFinite.
  apply CFGKATExpressionFiniteDynamicsContinue.
Qed.

Lemma CFGKATExpressionDynamicsReturn :
  forall a i,
    CFGKATExpressionDynamics (return, i) a CFGKATAutomatonReturn.
Proof.
  intros. apply CFGKATExpressionDynamicsFinite.
  apply CFGKATExpressionFiniteDynamicsReturn.
Qed.

Lemma CFGKATExpressionDynamicsGoto :
  forall a i l,
    CFGKATExpressionDynamics (goto l, i) a (CFGKATAutomatonJump l i).
Proof.
  intros. apply CFGKATExpressionDynamicsFinite.
  apply CFGKATExpressionFiniteDynamicsGoto.
Qed.

Lemma CFGKATExpressionDynamicsChoiceLeft :
  forall a i e1 e2 b r,
    eval_test b a i ->
    CFGKATExpressionDynamics (e1, i) a r ->
    CFGKATExpressionDynamics (if b then e1 else e2, i) a r.
Proof.
  intros a i e1 e2 b r Hb Hdyn.
  inversion Hdyn; subst.
  - apply CFGKATExpressionDynamicsFinite.
    eapply CFGKATExpressionFiniteDynamicsChoiceLeft; eauto.
  - apply CFGKATExpressionDynamicsDefaultReject.
    intros r' Hfin.
    dependent destruction Hfin.
    + eapply H; eauto.
    + contradiction.
Qed.

Lemma CFGKATExpressionDynamicsChoiceRight :
  forall a i e1 e2 b r,
    ~ eval_test b a i ->
    CFGKATExpressionDynamics (e2, i) a r ->
    CFGKATExpressionDynamics (if b then e1 else e2, i) a r.
Proof.
  intros a i e1 e2 b r Hb Hdyn.
  inversion Hdyn; subst.
  - apply CFGKATExpressionDynamicsFinite.
    eapply CFGKATExpressionFiniteDynamicsChoiceRight; eauto.
  - apply CFGKATExpressionDynamicsDefaultReject.
    intros r' Hfin.
    dependent destruction Hfin.
    + contradiction.
    + eapply H; eauto.
Qed.

Ltac enforce_functionality_cfgkat_finite_dynamics :=
  match goal with
  | [ Hleft: CFGKATExpressionFiniteDynamics ?e ?a ?z0,
      Hright: CFGKATExpressionFiniteDynamics ?e ?a ?z1 |- _ ] =>
    let Hequal := fresh "H" in
    pose proof (cfgkat_finite_dynamics_functional
                e a _ _ Hleft Hright) as Hequal;
    inversion Hequal; clear Hequal; subst;
    try intuition
  end.

Lemma CFGKATExpressionDynamicsSequenceSkip :
  forall a i i' e1 e2 r,
    CFGKATExpressionDynamics (e1, i) a (CFGKATAutomatonAccept i') ->
    CFGKATExpressionDynamics (e2, i') a r ->
    CFGKATExpressionDynamics (e1 ;; e2, i) a r.
Proof.
  intros a i i' e1 e2 r Hhead Htail.
  inversion Hhead; subst.
  inversion Htail; subst.
  - apply CFGKATExpressionDynamicsFinite.
    eapply CFGKATExpressionFiniteDynamicsSequenceSkip; eauto.
  - apply CFGKATExpressionDynamicsDefaultReject.
    intros r' Hfin.
    dependent destruction Hfin;
      enforce_functionality_cfgkat_finite_dynamics.
    eapply H0; eauto.
Qed.

Lemma CFGKATExpressionDynamicsSequenceReject :
  forall a i e1 e2,
    CFGKATExpressionDynamics (e1, i) a CFGKATAutomatonReject ->
    CFGKATExpressionDynamics (e1 ;; e2, i) a CFGKATAutomatonReject.
Proof.
  intros a i e1 e2 Hhead.
  inversion Hhead; subst.
  - apply CFGKATExpressionDynamicsFinite.
    eapply CFGKATExpressionFiniteDynamicsSequenceReject; eauto.
  - apply CFGKATExpressionDynamicsDefaultReject.
    intros r Hfin.
    dependent destruction Hfin;
      eapply H; eauto.
Qed.

Lemma CFGKATExpressionDynamicsSequenceReturn :
  forall a i e1 e2,
    CFGKATExpressionDynamics (e1, i) a CFGKATAutomatonReturn ->
    CFGKATExpressionDynamics (e1 ;; e2, i) a CFGKATAutomatonReturn.
Proof.
  intros. inversion H; subst.
  apply CFGKATExpressionDynamicsFinite.
  eapply CFGKATExpressionFiniteDynamicsSequenceReturn; eauto.
Qed.

Lemma CFGKATExpressionDynamicsSequenceBreak :
  forall a i i' e1 e2,
    CFGKATExpressionDynamics (e1, i) a (CFGKATAutomatonBreak i') ->
    CFGKATExpressionDynamics (e1 ;; e2, i) a (CFGKATAutomatonBreak i').
Proof.
  intros. inversion H; subst.
  apply CFGKATExpressionDynamicsFinite.
  eapply CFGKATExpressionFiniteDynamicsSequenceBreak; eauto.
Qed.

Lemma CFGKATExpressionDynamicsSequenceContinue :
  forall a i i' e1 e2,
    CFGKATExpressionDynamics (e1, i) a (CFGKATAutomatonContinue i') ->
    CFGKATExpressionDynamics (e1 ;; e2, i) a (CFGKATAutomatonContinue i').
Proof.
  intros. inversion H; subst.
  apply CFGKATExpressionDynamicsFinite.
  eapply CFGKATExpressionFiniteDynamicsSequenceContinue; eauto.
Qed.

Lemma CFGKATExpressionDynamicsSequenceJump :
  forall a i i' e1 e2 l,
    CFGKATExpressionDynamics (e1, i) a (CFGKATAutomatonJump l i') ->
    CFGKATExpressionDynamics (e1 ;; e2, i) a (CFGKATAutomatonJump l i').
Proof.
  intros. inversion H; subst.
  apply CFGKATExpressionDynamicsFinite.
  eapply CFGKATExpressionFiniteDynamicsSequenceJump; eauto.
Qed.

Lemma CFGKATExpressionDynamicsSequenceNext :
  forall a i i' e1 e1' e2 p,
    CFGKATExpressionDynamics (e1, i) a
      (CFGKATAutomatonNext p (e1', i')) ->
    CFGKATExpressionDynamics (e1 ;; e2, i) a
      (CFGKATAutomatonNext p (e1' ;; e2, i')).
Proof.
  intros. inversion H; subst.
  apply CFGKATExpressionDynamicsFinite.
  eapply CFGKATExpressionFiniteDynamicsSequenceNext; eauto.
Qed.

Lemma CFGKATExpressionDynamicsLoopSeqSkip :
  forall a i i' e1 e2 r,
    CFGKATExpressionDynamics (e1, i) a (CFGKATAutomatonAccept i') ->
    CFGKATExpressionDynamics (e2, i') a r ->
    CFGKATExpressionDynamics (e1 |> e2, i) a r.
Proof.
  intros a i i' e1 e2 r Hhead Htail.
  inversion Hhead; subst.
  inversion Htail; subst.
  - apply CFGKATExpressionDynamicsFinite.
    eapply CFGKATExpressionFiniteDynamicsLoopSeqSkip; eauto.
  - apply CFGKATExpressionDynamicsDefaultReject.
    intros r' Hfin.
    dependent destruction Hfin;
      enforce_functionality_cfgkat_finite_dynamics.
    eapply H0; eauto.
Qed.

Lemma CFGKATExpressionDynamicsLoopSeqReject :
  forall a i e1 e2,
    CFGKATExpressionDynamics (e1, i) a CFGKATAutomatonReject ->
    CFGKATExpressionDynamics (e1 |> e2, i) a CFGKATAutomatonReject.
Proof.
  intros a i e1 e2 Hhead.
  inversion Hhead; subst.
  - apply CFGKATExpressionDynamicsFinite.
    eapply CFGKATExpressionFiniteDynamicsLoopSeqReject; eauto.
  - apply CFGKATExpressionDynamicsDefaultReject.
    intros r Hfin.
    dependent destruction Hfin;
      eapply H; eauto.
Qed.

Lemma CFGKATExpressionDynamicsLoopSeqReturn :
  forall a i e1 e2,
    CFGKATExpressionDynamics (e1, i) a CFGKATAutomatonReturn ->
    CFGKATExpressionDynamics (e1 |> e2, i) a CFGKATAutomatonReturn.
Proof.
  intros. inversion H; subst.
  apply CFGKATExpressionDynamicsFinite.
  eapply CFGKATExpressionFiniteDynamicsLoopSeqReturn; eauto.
Qed.

Lemma CFGKATExpressionDynamicsLoopSeqBreak :
  forall a i i' e1 e2,
    CFGKATExpressionDynamics (e1, i) a (CFGKATAutomatonBreak i') ->
    CFGKATExpressionDynamics (e1 |> e2, i) a (CFGKATAutomatonAccept i').
Proof.
  intros. inversion H; subst.
  apply CFGKATExpressionDynamicsFinite.
  eapply CFGKATExpressionFiniteDynamicsLoopSeqBreak; eauto.
Qed.

Lemma CFGKATExpressionDynamicsLoopSeqContinue :
  forall a i i' e1 e2 r,
    CFGKATExpressionDynamics (e1, i) a (CFGKATAutomatonContinue i') ->
    CFGKATExpressionDynamics (e2, i') a r ->
    CFGKATExpressionDynamics (e1 |> e2, i) a r.
Proof.
  intros a i i' e1 e2 r Hhead Htail.
  inversion Hhead; subst.
  inversion Htail; subst.
  - apply CFGKATExpressionDynamicsFinite.
    eapply CFGKATExpressionFiniteDynamicsLoopSeqContinue; eauto.
  - apply CFGKATExpressionDynamicsDefaultReject.
    intros r' Hfin.
    dependent destruction Hfin;
      enforce_functionality_cfgkat_finite_dynamics.
    eapply H0; eauto.
Qed.

Lemma CFGKATExpressionDynamicsLoopSeqJump :
  forall a i i' e1 e2 l,
    CFGKATExpressionDynamics (e1, i) a (CFGKATAutomatonJump l i') ->
    CFGKATExpressionDynamics (e1 |> e2, i) a (CFGKATAutomatonJump l i').
Proof.
  intros. inversion H; subst.
  apply CFGKATExpressionDynamicsFinite.
  eapply CFGKATExpressionFiniteDynamicsLoopSeqJump; eauto.
Qed.

Lemma CFGKATExpressionDynamicsLoopSeqNext :
  forall a i i' e1 e1' e2 p,
    CFGKATExpressionDynamics (e1, i) a
      (CFGKATAutomatonNext p (e1', i')) ->
    CFGKATExpressionDynamics (e1 |> e2, i) a
      (CFGKATAutomatonNext p (e1' |> e2, i')).
Proof.
  intros. inversion H; subst.
  apply CFGKATExpressionDynamicsFinite.
  eapply CFGKATExpressionFiniteDynamicsLoopSeqNext; eauto.
Qed.

Lemma CFGKATExpressionDynamicsLoopGuardTrue :
  forall a i b e r,
    eval_test b a i ->
    CFGKATExpressionDynamics (e |> while b do e, i) a r ->
    CFGKATExpressionDynamics (while b do e, i) a r.
Proof.
  intros a i b e r Hb Hbody.
  inversion Hbody; subst.
  - apply CFGKATExpressionDynamicsFinite.
    eapply CFGKATExpressionFiniteDynamicsLoopGuardTrue; eauto.
  - apply CFGKATExpressionDynamicsDefaultReject.
    intros r' Hfin.
    dependent destruction Hfin.
    + eapply H; eauto.
    + contradiction.
Qed.

Lemma CFGKATExpressionDynamicsLoopGuardFalse :
  forall a i b e,
    ~ eval_test b a i ->
    CFGKATExpressionDynamics (while b do e, i) a (CFGKATAutomatonAccept i).
Proof.
  intros a i b e Hb.
  apply CFGKATExpressionDynamicsFinite.
  apply CFGKATExpressionFiniteDynamicsLoopGuardFalse.
  exact Hb.
Qed.

Lemma cfgkat_expression_dynamics_next_finite
  (s : CFGKATSyntConfiguration)
  (a : Atom)
  (p : Action)
  (next : CFGKATSyntConfiguration)
  :
  CFGKATExpressionDynamics s a (CFGKATAutomatonNext p next) ->
  CFGKATExpressionFiniteDynamics s a (CFGKATAutomatonNext p next).
Proof.
  intro H.
  inversion H; subst; try discriminate.
  exact H0.
Qed.

Definition Stuck (e: CFGKATExpression) (b: CFGKATTest) : Prop :=
  forall i a,
    eval_test b a i ->
    CFGKATExpressionDynamics (e, i) a CFGKATAutomatonReject \/
    exists i',
      (CFGKATExpressionDynamics (e, i) a (CFGKATAutomatonAccept i') \/
       CFGKATExpressionDynamics (e, i) a (CFGKATAutomatonContinue i')) /\
      eval_test b a i'.
