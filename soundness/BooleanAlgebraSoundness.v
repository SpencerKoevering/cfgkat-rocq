Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Classes.RelationClasses.
Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Lists.List.

From CFGKAT.Syntax Require Export Preliminaries.

Local Open Scope test_scope.

Definition CFGKATTestDenotationEquivalent
  (b c : CFGKATTest)
  : Prop
:=
  forall a i, eval_test b a i <-> eval_test c a i.

Reserved Notation "b '=BA' c" (at level 95, no associativity).

Inductive CFGKATBooleanAlgebraEquivalent :
  CFGKATTest -> CFGKATTest -> Prop
:=
  | BARefl :
      forall b,
        b =BA b
  | BASym :
      forall b c,
        b =BA c ->
        c =BA b
  | BATrans :
      forall b c d,
        b =BA c ->
        c =BA d ->
        b =BA d
  | BAAndCong :
      forall b b' c c',
        b =BA b' ->
        c =BA c' ->
        b and c =BA b' and c'
  | BAOrCong :
      forall b b' c c',
        b =BA b' ->
        c =BA c' ->
        b or c =BA b' or c'
  | BANotCong :
      forall b c,
        b =BA c ->
        not b =BA not c
  | BAOrAssoc :
      forall b c d,
        b or (c or d) =BA (b or c) or d
  | BAAndAssoc :
      forall b c d,
        b and (c and d) =BA (b and c) and d
  | BAOrComm :
      forall b c,
        b or c =BA c or b
  | BAAndComm :
      forall b c,
        b and c =BA c and b
  | BAOrAbsorption :
      forall b c,
        b or (b and c) =BA b
  | BAAndAbsorption :
      forall b c,
        b and (b or c) =BA b
  | BAOrIdem :
      forall b,
        b or b =BA b
  | BAAndIdem :
      forall b,
        b and b =BA b
  | BAOrDistrib :
      forall b c d,
        b or (c and d) =BA (b or c) and (b or d)
  | BAAndDistrib :
      forall b c d,
        b and (c or d) =BA (b and c) or (b and d)
  | BAOrComplement :
      forall b,
        b or not b =BA 1
  | BAAndComplement :
      forall b,
        b and not b =BA 0
  | BAIndicatorExclusivity :
      forall x v w,
        v <> w ->
        x is v and x is w =BA 0
  | BAIndicatorSum :
      forall x,
        big_TOr (fun v => x is v) =BA 1
where "b '=BA' c" := (CFGKATBooleanAlgebraEquivalent b c).

#[export] Instance BA_equivalence :
  Equivalence CFGKATBooleanAlgebraEquivalent
.
Proof.
  split.
  - intro x. apply BARefl.
  - intros x y H. exact (BASym x y H).
  - intros x y z Hxy Hyz. exact (BATrans x y z Hxy Hyz).
Qed.

#[export] Instance TAnd_proper :
  Proper (CFGKATBooleanAlgebraEquivalent ==>
          CFGKATBooleanAlgebraEquivalent ==>
          CFGKATBooleanAlgebraEquivalent) TAnd.
Proof.
  intros x x' Hx y y' Hy.
  exact (BAAndCong x x' y y' Hx Hy).
Qed.

#[export] Instance TOr_proper :
  Proper (CFGKATBooleanAlgebraEquivalent ==>
          CFGKATBooleanAlgebraEquivalent ==>
          CFGKATBooleanAlgebraEquivalent) TOr.
Proof.
  intros x x' Hx y y' Hy.
  exact (BAOrCong x x' y y' Hx Hy).
Qed.

#[export] Instance TNot_proper :
  Proper (CFGKATBooleanAlgebraEquivalent ==>
          CFGKATBooleanAlgebraEquivalent) TNot.
Proof.
  intros x x' Hx.
  exact (BANotCong x x' Hx).
Qed.

Theorem BA_indicator_exclusivity_sound :
  forall x v w,
    v <> w ->
    CFGKATTestDenotationEquivalent
      (x is v and x is w)
      0.
Proof.
  unfold CFGKATTestDenotationEquivalent.
  simpl. intuition congruence.
Qed.

Theorem BA_indicator_sum_sound :
  forall x,
    CFGKATTestDenotationEquivalent
      (big_TOr (fun v => x is v))
      1.
Proof.
  unfold CFGKATTestDenotationEquivalent.
  simpl; intros.
  rewrite eval_test_big_TOr.
  intuition.
  now exists (i x).
Qed.

Theorem BooleanAlgebra_sound :
  forall b c,
    b =BA c ->
    CFGKATTestDenotationEquivalent b c.
Proof.
  intros b c HBA.
  unfold CFGKATTestDenotationEquivalent.
  induction HBA; simpl; intros a i;
    try (now tauto) || firstorder.
  - now rewrite <- IHHBA2, <- IHHBA1.
  - now rewrite IHHBA1, IHHBA2.
  - congruence.
  - now apply BA_indicator_sum_sound.
Qed.
