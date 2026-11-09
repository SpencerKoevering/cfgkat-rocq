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

From CFGKAT.Semantics Require Export TransitionFunction.

Local Open Scope type_scope.

Lemma same_dynamics_implies_bisim
  (e1 e2: CFGKATExpression) (i: IndicatorAssignment)
:
  (forall a r,
    CFGKATExpressionDynamics (e1, i) a r <->
    CFGKATExpressionDynamics (e2, i) a r) ->
  (e1, i) ~~ (e2, i)
.
Proof.
  intros same_dynamics.
  set (R := fun (x y: cfgkat_states ExprAutEmpty) =>
            x = y \/ (x = (e1, i) /\ y = (e2, i))).
  unshelve eexists .
  - apply (bisimulation_by_outputs R ExprAutEmpty_functional); simpl;
    intros; rewrite resolve_syntactic_empty_identity in *;
    do 2 destruct H; subst; auto; try now eapply same_dynamics; eauto.
    + exists x1'. split.
      * now apply resolve_syntactic_empty_identity.
      * destruct x1'; now constructor.
    + exists x1'. split.
      * apply resolve_syntactic_empty_identity.
        now eapply same_dynamics; eauto.
      * destruct x1'; now constructor.
  - simpl. unfold R. intuition.
Qed.

Theorem G1_sound:
  forall e b i,
    (if b then e else e, i) ~~ (e, i).
Proof.
  intros e b i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite transition_choice.
  now destruct (eval_test_dec b a i).
Qed.

Theorem G2_sound:
  forall e b f i,
       (if b then e else f, i) ~~
       (if (not b) then f else e, i).
Proof.
  intros e b f i.
  apply same_dynamics_implies_bisim. intros.
  apply transition_output_eq_dynamics_iff.
  rewrite! transition_choice.
  destruct (eval_test_dec b a i) as [Hb | Hnb];
    destruct (eval_test_dec (not b) a i) as [Hnot | Hnnot];
    simpl in *; try contradiction; try reflexivity.
Qed.

Theorem G3_sound:
  forall e f g b c i,
      (if c then (if b then e else f) else g, i) ~~
      (if c and b then e else (if c then f else g), i).
Proof.
  intros. apply same_dynamics_implies_bisim.
  intros. apply transition_output_eq_dynamics_iff.
  rewrite !transition_choice.
  destruct (eval_test_dec b a i) as [Hb | Hnb];
    destruct (eval_test_dec c a i) as [Hc | Hnc];
    destruct (eval_test_dec (c and b) a i) as [Hcb | Hncb];
    simpl in *; try tauto; reflexivity.
Qed.

Theorem G4_sound:
  forall e f b i,
      (if b then e else f, i) ~~
      (if b then test b ;; e else f, i).
Proof.
  intros. apply same_dynamics_implies_bisim.
  intros. apply transition_output_eq_dynamics_iff.
  rewrite !transition_choice.
  rewrite transition_sequence, transition_assert.
  destruct (eval_test_dec b a i) as [Hb | Hnb]; auto.
Qed.

Inductive G5Relation : CFGKATSyntConfiguration -> CFGKATSyntConfiguration -> Prop :=
| G5_refl :
    forall e,
      G5Relation e e
| G5_plus_same :
    forall b e f g i,
      G5Relation ((if b then e else f);;g, i) ((if b then e ;; g else f ;; g), i).

Theorem G5_sound:
  forall e f g b i,
      ((if b then e else f);;g, i) ~~
      (if b then e;;g else f;;g, i).
Proof.
  intros. apply same_dynamics_implies_bisim.
  intros. apply transition_output_eq_dynamics_iff.
  rewrite transition_sequence.
  rewrite !transition_choice.
  rewrite !transition_sequence.
  destruct (eval_test_dec b a i); auto.
Qed.
