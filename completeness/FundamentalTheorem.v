Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Logic.ClassicalEpsilon.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Program.Equality.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.Permutation.
Import ListNotations.

From CFGKAT.Semantics Require Export TransitionFunction.
From CFGKAT.Completeness Require Export BooleanAlgebraCompleteness.
From CFGKAT.Soundness Require Export Soundness.

Local Open Scope cfgkat_scope.
Local Open Scope cfgkat_setoid_scope.

Lemma CFGKATL11Premise_comm
  (e : CFGKATExpression)
  (b c : CFGKATTest)
  :
  CFGKATL11Premise e (b and c) ->
  CFGKATL11Premise e (c and b).
Proof.
  intros Hinv i.
  eapply (CFGKATCongruenceTrans_sound
    empty_label_context empty_label_context empty_label_context
    (((test (c and b) ;; e) |> test (not (c and b))))
    (((test (b and c) ;; e) |> test (not (b and c))))
    0).
  - eapply (CFGKATCongruenceTrans_sound
      empty_label_context empty_label_context empty_label_context
      (((test (c and b) ;; e) |> test (not (c and b))))
      (((test (b and c) ;; e) |> test (not (c and b))))
      (((test (b and c) ;; e) |> test (not (b and c))))).
	    + apply CFGKATCongruenceLoopSeqLeftEmpty_sound. intros.
	      apply CFGKATCongruenceSequenceLeftEmpty_sound.
	      apply CFGKATCongruenceBooleanAssert_sound.
	      apply BAAndComm.
	    + apply CFGKATCongruenceLoopSeqRight_sound.
	      * apply CFGKATCongruenceBooleanAssert_sound.
	        apply BANotCong.
	        apply BAAndComm.
	      * apply CFGKATCongruenceRefl_sound.
	  - apply Hinv.
Qed.

Fixpoint complete_assignment_on
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  : CFGKATExpression :=
  match xs with
  | [] => 1
  | x :: xs' => assign (i x) to x ;; complete_assignment_on xs' i
  end.

Definition complete_assignment
  (i : IndicatorAssignment)
  : CFGKATExpression :=
  complete_assignment_on (elements IndicatorVariable) i.

Lemma complete_assignment_on_permutation
  (xs ys : list IndicatorVariable)
  (i : IndicatorAssignment)
  :
  Permutation xs ys ->
  complete_assignment_on xs i == complete_assignment_on ys i.
Proof.
  intro Hperm.
  induction Hperm; simpl.
  - apply EqRefl.
  - cfgkat_rewrite IHHperm.
    apply EqRefl.
  - destruct (Var_eq_dec x y) as [Hxy | Hxy].
    + subst y. apply EqRefl.
    + assert (Hyx : y <> x).
      { intro Heq. apply Hxy. symmetry. exact Heq. }
      apply EqSym.
      eapply (EqTrans
        empty_label_context empty_label_context empty_label_context
        (assign (i x) to x ;;
          (assign (i y) to y ;; complete_assignment_on l i))
        ((assign (i x) to x ;; assign (i y) to y) ;;
          complete_assignment_on l i)
        (assign (i y) to y ;;
          (assign (i x) to x ;; complete_assignment_on l i))).
      * apply EqSym. apply EqS1.
      * eapply (EqTrans
          empty_label_context empty_label_context empty_label_context
          ((assign (i x) to x ;; assign (i y) to y) ;;
            complete_assignment_on l i)
          ((assign (i y) to y ;; assign (i x) to x) ;;
            complete_assignment_on l i)
          (assign (i y) to y ;;
            (assign (i x) to x ;; complete_assignment_on l i))).
        -- apply EqSeqLeftEmptyCong.
           exact (EqA8 y x (i y) (i x) Hyx).
        -- apply EqS1.
  - eapply EqTrans; eauto.
Qed.

Fixpoint apply_complete_assignment_on
  (xs : list IndicatorVariable)
  (target current : IndicatorAssignment)
  : IndicatorAssignment :=
  match xs with
  | [] => current
  | x :: xs' =>
      apply_complete_assignment_on xs' target
        (update current x (target x))
  end.

Local Lemma apply_complete_assignment_on_notin
  (xs : list IndicatorVariable)
  (target current : IndicatorAssignment)
  (x : IndicatorVariable)
  :
  ~ In x xs ->
  apply_complete_assignment_on xs target current x = current x.
Proof.
  revert current.
  induction xs as [|y ys IH]; intros current Hnotin.
  - reflexivity.
  - simpl.
    rewrite IH.
    + apply update_other.
      intro Heq. subst y. apply Hnotin. left. reflexivity.
    + intro Hin. apply Hnotin. right. exact Hin.
Qed.

Local Lemma apply_complete_assignment_on_in
  (xs : list IndicatorVariable)
  (target current : IndicatorAssignment)
  (x : IndicatorVariable)
  :
  In x xs ->
  apply_complete_assignment_on xs target current x = target x.
Proof.
  revert current.
  induction xs as [|y ys IH]; intros current Hin.
  - contradiction.
  - simpl.
    destruct Hin as [Heq | Hin].
    + subst y.
      destruct (in_dec Var_eq_dec x ys) as [Hin_tail | Hnot_tail].
      * apply IH. exact Hin_tail.
      * rewrite apply_complete_assignment_on_notin by exact Hnot_tail.
        apply update_same.
    + apply IH. exact Hin.
Qed.

Local Lemma transition_complete_assignment_on
  (xs : list IndicatorVariable)
  (target current : IndicatorAssignment)
  (a : Atom)
  :
  transition_output (complete_assignment_on xs target) a current =
    CFGKATAutomatonAccept
      (apply_complete_assignment_on xs target current).
Proof.
  revert current.
  induction xs as [|x xs IH]; intro current.
  - simpl.
    rewrite transition_assert.
    destruct (eval_test_dec (1 : CFGKATTest) a current) as [_ | Hfalse].
    + reflexivity.
    + exfalso. apply Hfalse. exact I.
  - simpl.
    rewrite transition_sequence.
    rewrite transition_assign.
    apply IH.
Qed.

Lemma transition_complete_assignment
  (target current : IndicatorAssignment)
  (a : Atom)
  :
  transition_output (complete_assignment target) a current =
    CFGKATAutomatonAccept target.
Proof.
  unfold complete_assignment.
  rewrite transition_complete_assignment_on.
  apply f_equal.
  apply functional_extensionality.
  intro x.
  apply apply_complete_assignment_on_in.
  apply all_in.
Qed.

Lemma complete_assignment_no_contains_goto
  (i : IndicatorAssignment)
  (l : Label)
  :
  ~ contains_goto l (complete_assignment i).
Proof.
  unfold complete_assignment.
  induction (elements IndicatorVariable) as [|x xs IH]; simpl.
  - tauto.
  - intros [Hbad | Hbad].
    + exact Hbad.
    + exact (IH Hbad).
Qed.

Fixpoint guarded_sum_on
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  : CFGKATExpression :=
  match ms with
  | [] => 0
  | m :: ms' =>
      if AtIY_test m then body m else guarded_sum_on ms' body
  end.

Definition guarded_sum_all
  (body : (At x I^Y) -> CFGKATExpression)
  : CFGKATExpression :=
  guarded_sum_on all_AtIY body.

Fixpoint guarded_assignment_sum_on
  (assignments : list IndicatorAssignment)
  (body : IndicatorAssignment -> CFGKATExpression)
  : CFGKATExpression :=
  match assignments with
  | [] => 0
  | i :: assignments' =>
      if complete_test i then body i
      else guarded_assignment_sum_on assignments' body
  end.

Definition guarded_assignment_sum_all
  (body : IndicatorAssignment -> CFGKATExpression)
  : CFGKATExpression :=
  guarded_assignment_sum_on all_assignments body.

Fixpoint guarded_atom_sum_on
  (atoms : list (Test -> bool))
  (body : Atom -> CFGKATExpression)
  : CFGKATExpression :=
  match atoms with
  | [] => 0
  | ba :: atoms' =>
      if atom_to_test (bool_to_atom ba)
      then body (bool_to_atom ba)
      else guarded_atom_sum_on atoms' body
  end.

Definition guarded_atom_sum_all
  (body : Atom -> CFGKATExpression)
  : CFGKATExpression :=
  guarded_atom_sum_on all_bool_atoms body.

Fixpoint guarded_atom_product_indices
  (atoms : list (Test -> bool))
  : list (At x I^Y) :=
  match atoms with
  | [] => []
  | ba :: atoms' =>
      map (fun i => (bool_to_atom ba, i)) all_assignments ++
      guarded_atom_product_indices atoms'
  end.

Fixpoint guarded_assignment_product_indices
  (assignments : list IndicatorAssignment)
  : list (At x I^Y) :=
  match assignments with
  | [] => []
  | i :: assignments' =>
      map (fun ba => (bool_to_atom ba, i)) all_bool_atoms ++
      guarded_assignment_product_indices assignments'
  end.



Local Lemma loopseqisseqact
  (p : Action)
  (e : CFGKATExpression)
  :
  (do p |> e) == (do p ;; e).
Proof.
  cfgkat_rewrite <- (EqS4 (do p)) at 1.
  cfgkat_rewrite EqL7.
  cfgkat_rewrite EqL1.
  apply EqRefl.
Qed.
Local Lemma loopseqisseqassign_on
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  (e : CFGKATExpression)
  :
  (complete_assignment_on xs i |> e) == (complete_assignment_on xs i ;; e).
Proof.
  induction xs as [|x xs IH]; simpl.
  - cfgkat_rewrite EqL1.
    cfgkat_rewrite <- (EqS3 e) at 1.
    apply EqRefl.
  - cfgkat_rewrite EqL8.
    cfgkat_rewrite IH.
    cfgkat_rewrite <- EqS1.
    apply EqRefl.
Qed.

Local Lemma loopseqisseqassign
  (i : IndicatorAssignment)
  (e : CFGKATExpression)
  :
  (complete_assignment i |> e) == (complete_assignment i ;; e).
Proof.
  apply loopseqisseqassign_on.
Qed.

Local Lemma test_as_choice
  (b : CFGKATTest)
  :
  test b == if b then 1 else 0.
Proof.
  cfgkat_change_preferred_equiv.
  transitivity (if b then 1 else test b).
  - apply EqSym.
    cfgkat_rewrite EqG4;
    cfgkat_rewrite EqS4;
    apply EqG1.
  - cfgkat_rewrite EqG2 at 1.
    cfgkat_rewrite EqG4 at 1.
    cfgkat_rewrite EqS5.
    cfgkat_rewrite (EqBoolAssertCong ((not b) and b) 0
      (BAAndComplementLeft b)).
    cfgkat_rewrite EqG2.
    apply EqBoolChoiceCong.
    apply BANotNot.
Qed.

Lemma neutralright
  (b : CFGKATTest)
  (e : CFGKATExpression)
  :
  (if b then e else 0) == test b ;; e.
Proof.
  cfgkat_rewrite test_as_choice at 2.
  cfgkat_rewrite EqG5.
  cfgkat_rewrite EqS3.
  cfgkat_rewrite EqS2.
  apply EqRefl.
Qed.

Local Lemma choice_false_guard
  (e f : CFGKATExpression)
  :
  (if (0 : CFGKATTest) then e else f) == f.
Proof.
  cfgkat_rewrite EqG4.
  cfgkat_rewrite EqS2.
  cfgkat_rewrite EqG2.
  cfgkat_rewrite
    (EqBoolChoiceCong f 0
      (not (0 : CFGKATTest)) (1 : CFGKATTest) BANotFalse).
  cfgkat_rewrite neutralright.
  apply EqS3.
Qed.

Local Lemma choice_true_guard
  (e f : CFGKATExpression)
  :
  (if (1 : CFGKATTest) then e else f) == e.
Proof.
  cfgkat_rewrite EqG2.
  cfgkat_rewrite
    (EqBoolChoiceCong f e
      (not (1 : CFGKATTest)) (0 : CFGKATTest) BANotTrue).
  apply choice_false_guard.
Qed.

Lemma test_abort
  (b : CFGKATTest)
  :
  test b ;; 0 == 0.
Proof.
  cfgkat_rewrite <- neutralright.
  apply EqG1.
Qed.
Lemma choice_else_guarded_abort
  (b : CFGKATTest)
  (e f : CFGKATExpression)
  :
  (if b then e else test b ;; f) == (if b then e else 0).
Proof.
  cfgkat_rewrite EqG2 at 1.
  cfgkat_rewrite <- (neutralright b f) at 1.
  cfgkat_rewrite EqG3.
  cfgkat_rewrite (EqBoolChoiceCong f (if not b then 0 else e)
    ((not b) and b) 0 (BAAndComplementLeft b)).
  cfgkat_rewrite choice_false_guard.
  cfgkat_rewrite <- EqG2.
  apply EqRefl.
Qed.

Lemma branchsel
  (b : CFGKATTest)
  (e f : CFGKATExpression)
  :
  test b ;; (if b then e else f) == test b ;; e.
Proof.
  cfgkat_rewrite <- (neutralright b (if b then e else f)) at 1.
  cfgkat_rewrite EqG3.
  cfgkat_rewrite (EqBoolChoiceCong e (if b then f else 0)
    (b and b) b (BAAndIdem b)).
  cfgkat_rewrite neutralright.
  cfgkat_rewrite choice_else_guarded_abort.
  cfgkat_rewrite neutralright.
  apply EqRefl.
Qed.

Lemma branchskip_disjoint
  (a b : CFGKATTest)
  (e f : CFGKATExpression)
  :
  TAnd a b =BA 0 ->
  test a ;; (if b then e else f) == test a ;; f.
Proof.
  intro Hab.
  cfgkat_rewrite <- (neutralright a (if b then e else f)) at 1.
  cfgkat_rewrite EqG3.
  cfgkat_rewrite (EqBoolChoiceCong e (if a then f else 0)
    (a and b) 0 Hab).
  cfgkat_rewrite choice_false_guard.
  cfgkat_rewrite neutralright.
  apply EqRefl.
Qed.

Local Lemma guarded_choice_swap_disjoint
  (b c : CFGKATTest)
  (e f g : CFGKATExpression)
  :
  (b and c) =BA 0 ->
  (if b then e else if c then f else g) ==
    (if c then f else if b then e else g).
Proof.
  intro Hbc.
  cfgkat_rewrite EqG2 at 1.
  cfgkat_rewrite EqG3.
  cfgkat_rewrite
    (EqBoolChoiceCong f (if not b then g else e)
      ((not b) and c) c
      ltac:(rewrite BAAndComm;
        apply BA_leq_to_and_right;
        apply BA_disjoint_to_leq_complement;
        now rewrite BAAndComm)).
  cfgkat_rewrite <- (EqG2 e b g).
  apply EqRefl.
Qed.

Lemma test_choice_split
  (b g : CFGKATTest)
  (e f : CFGKATExpression)
  :
  test b ;; (if g then e else f) == if b and g then e else test b ;; f.
Proof.
  cfgkat_rewrite <- (neutralright b (if g then e else f)) at 1.
  cfgkat_rewrite EqG3.
  cfgkat_rewrite neutralright.
  apply EqRefl.
Qed.

Lemma testdistr
  (b c : CFGKATTest)
  (e f : CFGKATExpression)
  :
  test b ;; (if c then e else f) ==
    if c then test b ;; e else test b ;; f.
Proof.
  cfgkat_rewrite test_choice_split.
  cfgkat_rewrite
    (EqBoolChoiceCong e (test b ;; f)
      (b and c) (c and b) (BAAndComm b c)).
  cfgkat_rewrite <- (EqG1 (test b ;; f) c) at 1.
  cfgkat_rewrite <- (EqG3 e (test b ;; f) (test b ;; f) b c).
  cfgkat_rewrite choice_else_guarded_abort.
  cfgkat_rewrite neutralright.
  apply EqRefl.
Qed.

Lemma test_seq_ba
  (a b c : CFGKATTest)
  :
  TAnd a b =BA c ->
  test a ;; test b == test c.
Proof.
  intro H.
  cfgkat_rewrite EqS5.
  cfgkat_rewrite (EqBoolAssertCong (a and b) c H).
  apply EqRefl.
Qed.

Lemma test_seq_absorb_right
  (a b : CFGKATTest)
  :
  TAnd a b =BA a ->
  forall e,
    test a ;; (test b ;; e) == test a ;; e.
Proof.
  intros Hab e.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite (test_seq_ba a b a Hab).
  apply EqRefl.
Qed.

Lemma test_seq_annihilate_right
  (a b : CFGKATTest)
  :
  TAnd a b =BA 0 ->
  forall e,
    test a ;; (test b ;; e) == 0.
Proof.
  intros Hab e.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite (test_seq_ba a b 0 Hab).
  apply EqS2.
Qed.

Lemma choice_then_guarded_cong
  (g : CFGKATTest)
  (e e' f : CFGKATExpression)
  :
  test g ;; e == test g ;; e' ->
  (if g then e else f) == (if g then e' else f).
Proof.
  intro Hguarded.
  cfgkat_rewrite EqG4 at 1.
  cfgkat_rewrite Hguarded.
  cfgkat_rewrite <- EqG4 at 1.
  apply EqRefl.
Qed.

Lemma choice_dead_branch
  (g : CFGKATTest)
  (h : CFGKATExpression)
  :
  test g ;; h == 0 ->
  (if g then 0 else h) == h.
Proof.
  intro Hdead.
  cfgkat_rewrite <- Hdead at 1.
  cfgkat_rewrite <- EqG4 at 1.
  apply EqG1.
Qed.

Lemma antiskewcom
  (b c : CFGKATTest)
  (e f g : CFGKATExpression)
  :
  (if b then e else (if c then f else g)) ==
    (if b or c then (if b then e else f) else g).
Proof.
  cfgkat_rewrite EqG2 at 1.
  cfgkat_rewrite EqG2 at 2.
  cfgkat_rewrite EqG3.
  cfgkat_rewrite EqG2 at 2.
  cfgkat_rewrite EqG2.
  cfgkat_rewrite (EqBoolChoiceCong e f (not (not b)) b
    (BANotNot b)).
  cfgkat_rewrite (EqBoolChoiceCong (if b then e else f) g
    (not ((not b) and (not c))) (b or c) (BANotAndNot b c)).
  apply EqRefl.
Qed.

Lemma choice_or_test_seq
  (b c : CFGKATTest)
  (e : CFGKATExpression)
  :
  (if b then e else test c ;; e) == test (b or c) ;; e.
Proof.
  cfgkat_rewrite <- (neutralright c e) at 1.
  cfgkat_rewrite antiskewcom.
  cfgkat_rewrite EqG1.
  apply neutralright.
Qed.

Lemma loopassoctest
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  :
  test b ;; (f |> g) == (test b ;; f) |> g.
Proof.
  cfgkat_rewrite <- neutralright at 1.
  cfgkat_rewrite <- EqL2.
  cfgkat_rewrite <- EqL9.
  cfgkat_rewrite neutralright.
  apply EqRefl.
Qed.

Local Lemma loopseqisseqtest
  (b : CFGKATTest)
  (e : CFGKATExpression)
  :
  test b |> e == test b ;; e.
Proof.
  cfgkat_rewrite <- (EqS4 (test b)) at 1.
  cfgkat_rewrite <- (loopassoctest b 1 e).
  cfgkat_rewrite EqL1.
  apply EqRefl.
Qed.

Lemma inddistr
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  (e f : CFGKATExpression)
  :
  test_indicator_free x b ->
  assign v to x ;; (if b then e else f) ==
    (if b then assign v to x ;; e else assign v to x ;; f).
Proof.
  revert e f.
  induction b as
    [t | y vy | | | b1 IH1 b2 IH2 | b1 IH1 b2 IH2 | b' IH];
    simpl; intros e f Hfree.
  - apply EqA6.
  - apply EqA9.
    intro Hxy. apply Hfree. symmetry. exact Hxy.
  - cfgkat_rewrite choice_true_guard.
    cfgkat_rewrite choice_true_guard.
    apply EqRefl.
  - cfgkat_rewrite choice_false_guard.
    cfgkat_rewrite choice_false_guard.
    apply EqRefl.
  - destruct Hfree as [Hfree1 Hfree2].
    cfgkat_rewrite (EqBoolChoiceCong e f (b1 and b2) (b2 and b1)
      (BAAndComm b1 b2)).
    cfgkat_rewrite <- (EqG1 f b2) at 1.
    cfgkat_rewrite <- EqG3.
    cfgkat_rewrite (IH2 (if b1 then e else f) f Hfree2).
    cfgkat_rewrite (IH1 e f Hfree1).
    cfgkat_rewrite EqG3.
    cfgkat_rewrite EqG1.
    apply EqBoolChoiceCong. apply BAAndComm.
  - destruct Hfree as [Hfree1 Hfree2].
    cfgkat_rewrite <- (EqG1 e b1) at 1.
    cfgkat_rewrite <- antiskewcom.
    cfgkat_rewrite (IH1 e (if b2 then e else f) Hfree1).
    cfgkat_rewrite (IH2 e f Hfree2).
    cfgkat_rewrite antiskewcom.
    cfgkat_rewrite EqG1.
    apply EqRefl.
  - cfgkat_rewrite <- EqG2.
    cfgkat_rewrite (IH f e Hfree).
    apply EqG2.
Qed.

Lemma indcommtest
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (b : CFGKATTest)
  :
  test_indicator_free x b ->
  assign v to x ;; test b == test b ;; assign v to x.
Proof.
  intro Hfree.
  cfgkat_rewrite test_as_choice at 1.
  cfgkat_rewrite (inddistr x v b 1 0 Hfree).
  cfgkat_rewrite EqS4.
  cfgkat_rewrite EqA7.
  apply neutralright.
Qed.
Lemma atom_to_test_indicator_free
  (x : IndicatorVariable)
  (a : Atom)
  :
  test_indicator_free x (atom_to_test a).
Proof.
  unfold atom_to_test, big_TAnd.
  generalize (elements Test).
  induction l as [|t ts IH]; simpl.
  - exact I.
  - split.
    + destruct (atom_dec a t); simpl; exact I.
    + exact IH.
Qed.

Local Lemma complete_assignment_on_comm_indicator_free_test
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  (b : CFGKATTest)
  :
  (forall x, In x xs -> test_indicator_free x b) ->
  complete_assignment_on xs i ;; test b == test b ;; complete_assignment_on xs i.
Proof.
  induction xs as [|x xs IH]; simpl.
  - intro Hfree.
    cfgkat_rewrite EqS3.
    cfgkat_rewrite EqS4.
    apply EqRefl.
  - intro Hfree.
    cfgkat_rewrite EqS1.
    cfgkat_rewrite (IH (fun y Hy => Hfree y (or_intror Hy))).
    cfgkat_rewrite <- EqS1.
    cfgkat_rewrite (indcommtest x (i x) b
      (Hfree x (or_introl eq_refl))).
    apply EqS1.
Qed.
Lemma loopassocassign_plus_on
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  (e f : CFGKATExpression)
  :
  (complete_assignment_on xs i ;; e) |> f == complete_assignment_on xs i ;; (e |> f).
Proof.
  induction xs as [|x xs IH]; simpl.
  - cfgkat_rewrite EqS3.
    cfgkat_rewrite EqS3.
    apply EqRefl.
  - cfgkat_rewrite EqS1 at 1.
    cfgkat_rewrite EqL8.
    cfgkat_rewrite IH.
    cfgkat_rewrite EqS1.
    apply EqRefl.
Qed.

Local Lemma loopassocassign_plus
  (i : IndicatorAssignment)
  (e f : CFGKATExpression)
  :
  (complete_assignment i ;; e) |> f == complete_assignment i ;; (e |> f).
Proof.
  apply loopassocassign_plus_on.
Qed.

Lemma complete_assignment_abort
  (i : IndicatorAssignment)
  :
  complete_assignment i ;; 0 == 0.
Proof.
  unfold complete_assignment.
  induction (elements IndicatorVariable) as [|x xs IH]; simpl.
  - apply EqS3.
  - cfgkat_rewrite EqS1.
    cfgkat_rewrite IH.
    apply EqA7.
Qed.

Lemma complete_assignment_return
  (i : IndicatorAssignment)
  :
  complete_assignment i ;; return == return.
Proof.
  unfold complete_assignment.
  induction (elements IndicatorVariable) as [|x xs IH]; simpl.
  - apply EqS3.
  - cfgkat_rewrite EqS1.
    cfgkat_rewrite IH.
    apply EqA5.
Qed.

Local Lemma complete_assignment_on_comm_action
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  (p : Action)
  :
  complete_assignment_on xs i ;; do p == do p ;; complete_assignment_on xs i.
Proof.
  induction xs as [|x xs IH]; simpl.
  - cfgkat_rewrite EqS3.
    cfgkat_rewrite EqS4.
    apply EqRefl.
  - cfgkat_rewrite EqS1.
    cfgkat_rewrite IH.
    cfgkat_rewrite <- EqS1.
    cfgkat_rewrite EqA1.
    apply EqS1.
Qed.

Lemma complete_assignment_comm_action
  (i : IndicatorAssignment)
  (p : Action)
  :
  complete_assignment i ;; do p == do p ;; complete_assignment i.
Proof.
  apply complete_assignment_on_comm_action.
Qed.

Local Lemma complete_assignment_on_comm_assign_notin
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  (x : IndicatorVariable)
  (v : IndicatorValue)
  :
  ~ In x xs ->
  complete_assignment_on xs i ;; assign v to x == assign v to x ;; complete_assignment_on xs i.
Proof.
  induction xs as [|y ys IH]; simpl.
  - intro Hnotin.
    cfgkat_rewrite EqS3.
    cfgkat_rewrite EqS4.
    apply EqRefl.
  - intro Hnotin.
    assert (Hyx : x <> y).
    { intro Hxy. apply Hnotin. left. symmetry. exact Hxy. }
    cfgkat_rewrite EqS1.
    cfgkat_rewrite (IH (fun Hin => Hnotin (or_intror Hin))).
    cfgkat_rewrite <- EqS1.
    cfgkat_rewrite (EqA8 x y v (i y) Hyx).
    apply EqS1.
Qed.

Lemma indannih_plus_on
  (xs : list IndicatorVariable)
  (i j : IndicatorAssignment)
  :
  NoDup xs ->
  complete_assignment_on xs i ;;
    complete_assignment_on xs j == complete_assignment_on xs j.
Proof.
  induction xs as [|x xs IH]; simpl.
  - intro Hnodup. apply EqS3.
  - intro Hnodup.
    inversion Hnodup as [|? ? Hnotin Hnodup_tail]. subst.
    cfgkat_rewrite EqS1.
    cfgkat_rewrite <- EqS1 at 2.
    cfgkat_rewrite
      (complete_assignment_on_comm_assign_notin xs i x (j x) Hnotin).
    cfgkat_rewrite EqS1.
    cfgkat_rewrite <- EqS1 at 1.
    cfgkat_rewrite EqA4.
    cfgkat_rewrite (IH Hnodup_tail) at 1.
    apply EqRefl.
Qed.

Lemma indannih_plus
  (i j : IndicatorAssignment)
  :
  complete_assignment i ;; complete_assignment j == complete_assignment j.
Proof.
  unfold complete_assignment.
  apply indannih_plus_on.
  apply nodup.
Qed.

Local Lemma complete_assignment_on_ext
  (xs : list IndicatorVariable)
  (i j : IndicatorAssignment)
  :
  (forall x, In x xs -> i x = j x) ->
  complete_assignment_on xs i = complete_assignment_on xs j.
Proof.
  induction xs as [|x xs IH]; simpl; intro Heq.
  - reflexivity.
  - rewrite (Heq x (or_introl eq_refl)).
    rewrite IH.
    + reflexivity.
    + intros y Hy. apply Heq. right. exact Hy.
Qed.

Local Lemma complete_assignment_on_update_notin
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  (x : IndicatorVariable)
  (v : IndicatorValue)
  :
  ~ In x xs ->
  complete_assignment_on xs (update i x v) =
    complete_assignment_on xs i.
Proof.
  intro Hnotin.
  apply complete_assignment_on_ext.
  intros y Hy.
  apply update_other.
  intro Hxy. subst y. contradiction.
Qed.

Local Lemma complete_assignment_on_assign_update
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  (x : IndicatorVariable)
  (v : IndicatorValue)
  :
  NoDup xs ->
  In x xs ->
  complete_assignment_on xs i ;; assign v to x == complete_assignment_on xs (update i x v).
Proof.
  induction xs as [|y ys IH]; simpl.
  - intros _ [].
  - intros Hnodup Hin.
    inversion Hnodup as [|? ? Hnotin Hnodup_tail]. subst.
    destruct (Var_eq_dec x y) as [Hxy | Hxy].
    + subst y.
      rewrite update_same.
      rewrite complete_assignment_on_update_notin.
      * cfgkat_rewrite EqS1.
        cfgkat_rewrite
          (complete_assignment_on_comm_assign_notin ys i x v Hnotin).
        cfgkat_rewrite <- EqS1.
        cfgkat_rewrite EqA4.
        apply EqRefl.
      * exact Hnotin.
    + destruct Hin as [Hy | Hin_tail].
      * symmetry in Hy. contradiction.
      * rewrite update_other by exact Hxy.
        cfgkat_rewrite EqS1.
        cfgkat_rewrite (IH Hnodup_tail Hin_tail).
        apply EqRefl.
Qed.

Local Lemma assign_comm_indicator_test
  (y x : IndicatorVariable)
  (vy vx : IndicatorValue)
  :
  y <> x ->
  assign vy to y ;; test x is vx == test x is vx ;; assign vy to y.
Proof.
  intro Hyx.
  apply indcommtest.
  intro Hxy.
  apply Hyx.
  symmetry.
  exact Hxy.
Qed.

Local Lemma complete_assignment_on_comm_indicator_test_notin
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  (x : IndicatorVariable)
  (vx : IndicatorValue)
  :
  ~ In x xs ->
  complete_assignment_on xs i ;; test x is vx == test x is vx ;; complete_assignment_on xs i.
Proof.
  induction xs as [|y ys IH]; simpl.
  - intro Hnotin.
    cfgkat_rewrite EqS3.
    cfgkat_rewrite EqS4.
    apply EqRefl.
  - intro Hnotin.
    assert (Hyx : y <> x).
    { intro Hyx_eq. apply Hnotin. left. exact Hyx_eq. }
    cfgkat_rewrite EqS1.
    cfgkat_rewrite (IH (fun Hin => Hnotin (or_intror Hin))).
    cfgkat_rewrite <- EqS1.
    cfgkat_rewrite (assign_comm_indicator_test y x (i y) vx Hyx).
    apply EqS1.
Qed.

Local Lemma assignment_head_test_after_tail
  (x : IndicatorVariable)
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  :
  ~ In x xs ->
  assign (i x) to x ;; complete_assignment_on xs i == (assign (i x) to x ;; complete_assignment_on xs i) ;;
      test x is i x.
Proof.
  intro Hnotin.
  cfgkat_rewrite <- EqA2 at 1.
  cfgkat_rewrite EqS1 at 1.
  cfgkat_rewrite <-
    (complete_assignment_on_comm_indicator_test_notin xs i x (i x) Hnotin).
  cfgkat_rewrite <- EqS1.
  apply EqRefl.
Qed.

Lemma indval_plus_on
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  :
  NoDup xs ->
  complete_assignment_on xs i == complete_assignment_on xs i ;; test (complete_test_on xs i).
Proof.
  induction xs as [|x xs IH]; simpl.
  - intro Hnodup.
    apply EqSym. apply EqS3.
  - intro Hnodup.
    inversion Hnodup as [|? ? Hnotin Hnodup_tail]. subst.
    cfgkat_rewrite (IH Hnodup_tail) at 1.
    cfgkat_rewrite <- EqS1.
    cfgkat_rewrite (assignment_head_test_after_tail x xs i Hnotin) at 1.
    cfgkat_rewrite EqS1.
    cfgkat_rewrite EqS5.
    apply EqRefl.
Qed.

Local Lemma indval_plus
  (i : IndicatorAssignment)
  :
  complete_assignment i == complete_assignment i ;; test (complete_test i).
Proof.
  unfold complete_assignment.
  change (complete_test i) with
    (complete_test_on (elements IndicatorVariable) i).
  apply indval_plus_on.
  apply nodup.
Qed.

Local Lemma assign_comm_complete_test_on_notin
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  (x : IndicatorVariable)
  (vx : IndicatorValue)
  :
  ~ In x xs ->
  assign vx to x ;; test (complete_test_on xs i) == test (complete_test_on xs i) ;; assign vx to x.
Proof.
  induction xs as [|y ys IH]; simpl.
  - intro Hnotin.
    cfgkat_rewrite EqS4.
    cfgkat_rewrite EqS3.
    apply EqRefl.
  - intro Hnotin.
    assert (Hxy : x <> y).
    { intro Hxy_eq. apply Hnotin. left. symmetry. exact Hxy_eq. }
    cfgkat_rewrite <- EqS5 at 1.
    cfgkat_rewrite <- EqS1.
    cfgkat_rewrite (assign_comm_indicator_test x y vx (i y) Hxy).
    cfgkat_rewrite EqS1.
    cfgkat_rewrite (IH (fun Hin => Hnotin (or_intror Hin))).
    cfgkat_rewrite <- EqS1.
    cfgkat_rewrite EqS5.
    apply EqRefl.
Qed.

Lemma indred_plus_on
  (xs : list IndicatorVariable)
  (i : IndicatorAssignment)
  :
  NoDup xs ->
  test (complete_test_on xs i) == test (complete_test_on xs i) ;; complete_assignment_on xs i.
Proof.
  induction xs as [|x xs IH]; simpl.
  - intro Hnodup.
    apply EqSym. apply EqS3.
  - intro Hnodup.
    inversion Hnodup as [|? ? Hnotin Hnodup_tail]. subst.
    cfgkat_rewrite <- EqS5 at 1.
    cfgkat_rewrite (IH Hnodup_tail) at 1.
    cfgkat_rewrite <- EqS1.
    cfgkat_rewrite (EqSeqLeftEmptyCong
      (test x is i x ;; test (complete_test_on xs i))
      ((test x is i x ;; test (complete_test_on xs i)) ;;
        assign (i x) to x)
      (complete_assignment_on xs i)
      ltac:(cfgkat_rewrite <- EqA3 at 1;
        cfgkat_rewrite EqS1;
        cfgkat_rewrite
          (assign_comm_complete_test_on_notin xs i x (i x) Hnotin);
        cfgkat_rewrite <- EqS1;
        apply EqRefl)).
    cfgkat_rewrite EqS1.
    cfgkat_rewrite EqS5.
    apply EqRefl.
Qed.

Lemma indred_plus
  (i : IndicatorAssignment)
  :
  test (complete_test i) == test (complete_test i) ;; complete_assignment i.
Proof.
  unfold complete_assignment.
  change (complete_test i) with
    (complete_test_on (elements IndicatorVariable) i).
  apply indred_plus_on.
  apply nodup.
Qed.

Local Lemma minterm_indred_plus
  (m : (At x I^Y))
  :
  test (AtIY_test m) == test (AtIY_test m) ;; complete_assignment (AtIY_assignment m).
Proof.
  destruct m as [ba i].
  unfold AtIY_test, AtIY_assignment, minterm.
  cfgkat_rewrite <- EqS5 at 1.
  unfold complete_test.
  cfgkat_rewrite indred_plus.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite EqS5.
  apply EqRefl.
Qed.

Local Lemma guardedness_plus_on
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  :
  guarded_sum_on ms body == guarded_sum_on ms
      (fun m => test (AtIY_test m) ;; body m).
Proof.
  induction ms as [|m ms IH]; simpl.
  - apply EqRefl.
  - cfgkat_rewrite EqG4.
    cfgkat_rewrite IH.
    apply EqRefl.
Qed.

Lemma guardedness_plus
  (body : (At x I^Y) -> CFGKATExpression)
  :
  guarded_sum_all body == guarded_sum_all
      (fun m => test (AtIY_test m) ;; body m).
Proof.
  unfold guarded_sum_all.
  apply guardedness_plus_on.
Qed.

Lemma guarded_sum_well_defined
  (ms ns : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  :
  Permutation ms ns ->
  guarded_sum_on ms body == guarded_sum_on ns body.
Proof.
  intro Hperm.
  induction Hperm.
  - simpl. apply EqRefl.
  - simpl.
    cfgkat_rewrite IHHperm.
    apply EqRefl.
  - simpl.
    destruct (classic (x = y)) as [Heq | Hneq].
    + subst y. apply EqRefl.
    + apply guarded_choice_swap_disjoint.
      apply minterms_disagree.
      intro Heq. apply Hneq. symmetry. exact Heq.
  - eapply EqTrans; eauto.
Qed.

Local Lemma guarded_sum_on_const_prefix_choice
  (ms ns : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  (e : CFGKATExpression)
  :
  (forall m, In m ms -> body m == e) ->
  guarded_sum_on (ms ++ ns) body ==
    if fold_TOr (map AtIY_test ms) then e else guarded_sum_on ns body.
Proof.
  revert ns.
  induction ms as [|m ms IH]; intros ns Hbody; simpl.
  - apply EqSym. apply choice_false_guard.
  - cfgkat_rewrite (Hbody m (or_introl eq_refl)).
    cfgkat_rewrite (IH ns (fun n Hn => Hbody n (or_intror Hn))).
    cfgkat_rewrite antiskewcom.
    cfgkat_rewrite EqG1.
    apply EqRefl.
Qed.

Local Lemma guarded_atom_product_guard
  (ba : Test -> bool)
  :
  fold_TOr
    (map AtIY_test
      (map (fun i => (bool_to_atom ba, i)) all_assignments))
    =BA atom_to_test (bool_to_atom ba).
Proof.
  apply Boolean_denotation_completeness.
  unfold CFGKATTestDenotationEquivalent.
  intros a i.
  rewrite eval_fold_TOr.
  split.
  - intros [t [Ht Ht_eval]].
    apply in_map_iff in Ht as [m [Ht_eq Hm]].
    subst t.
    apply in_map_iff in Hm as [j [Hm_eq _]].
    subst m.
    unfold AtIY_test in Ht_eval. simpl in Ht_eval.
    exact (proj1 Ht_eval).
  - intro Ha.
    exists (AtIY_test (bool_to_atom ba, i)).
    split.
    + apply in_map_iff.
      exists (bool_to_atom ba, i). split; [reflexivity |].
      apply in_map_iff.
      exists i. split; [reflexivity | apply all_assignments_complete].
    + unfold AtIY_test. simpl.
      split.
      * exact Ha.
      * apply eval_complete_test. intro x. reflexivity.
Qed.

Local Lemma guarded_assignment_product_guard
  (i : IndicatorAssignment)
  :
  fold_TOr
    (map AtIY_test
      (map (fun ba => (bool_to_atom ba, i)) all_bool_atoms))
    =BA complete_test i.
Proof.
  apply Boolean_denotation_completeness.
  unfold CFGKATTestDenotationEquivalent.
  intros a j.
  rewrite eval_fold_TOr.
  split.
  - intros [t [Ht Ht_eval]].
    apply in_map_iff in Ht as [m [Ht_eq Hm]].
    subst t.
    apply in_map_iff in Hm as [ba [Hm_eq _]].
    subst m.
    unfold AtIY_test in Ht_eval. simpl in Ht_eval.
    exact (proj2 Ht_eval).
  - intro Hcomplete.
    destruct (bool_to_atom_eq a) as [ba [Hba Hatom]].
    exists (AtIY_test (bool_to_atom ba, i)).
    split.
    + apply in_map_iff.
      exists (bool_to_atom ba, i). split; [reflexivity |].
      apply in_map_iff.
      exists ba. split; [reflexivity | exact Hba].
    + pose proof (proj1 (eval_complete_test i j a) Hcomplete) as Hcomplete_eq.
      assert (Hij : j = i).
      { extensionality x. symmetry. apply Hcomplete_eq. }
      subst j.
      rewrite Hatom.
      apply eval_AtIY_test_refl.
Qed.

Lemma guarded_atom_sum_product_injection
  (atoms : list (Test -> bool))
  (body : Atom -> CFGKATExpression)
  :
  guarded_atom_sum_on atoms body ==
    guarded_sum_on
      (guarded_atom_product_indices atoms)
      (fun m => body (AtIY_atom m)).
Proof.
  induction atoms as [|ba atoms IH]; simpl.
  - apply EqRefl.
  - eapply EqTrans.
    + apply EqChoiceCong.
      * apply EqRefl.
      * exact IH.
    + apply EqSym.
      eapply EqTrans.
      * apply guarded_sum_on_const_prefix_choice.
        intros [a i] Hin.
        apply in_map_iff in Hin as [j [Heq _]].
        inversion Heq. subst a i.
        unfold AtIY_atom. simpl.
        apply EqRefl.
      * apply EqBoolChoiceCong.
        apply guarded_atom_product_guard.
Qed.

Lemma guarded_assignment_sum_product_injection
  (assignments : list IndicatorAssignment)
  (body : IndicatorAssignment -> CFGKATExpression)
  :
  guarded_assignment_sum_on assignments body ==
    guarded_sum_on
      (guarded_assignment_product_indices assignments)
      (fun m => body (AtIY_assignment m)).
Proof.
  induction assignments as [|i assignments IH]; simpl.
  - apply EqRefl.
  - eapply EqTrans.
    + apply EqChoiceCong.
      * apply EqRefl.
      * exact IH.
    + apply EqSym.
      eapply EqTrans.
      * apply guarded_sum_on_const_prefix_choice.
        intros [a j] Hin.
        apply in_map_iff in Hin as [ba [Heq _]].
        inversion Heq. subst a j.
        unfold AtIY_assignment. simpl.
        apply EqRefl.
      * apply EqBoolChoiceCong.
        apply guarded_assignment_product_guard.
Qed.

Lemma ggdedsumprodinj :
  (forall atoms body,
    guarded_atom_sum_on atoms body ==
      guarded_sum_on
        (guarded_atom_product_indices atoms)
        (fun m => body (AtIY_atom m))) /\
  (forall assignments body,
    guarded_assignment_sum_on assignments body ==
      guarded_sum_on
        (guarded_assignment_product_indices assignments)
        (fun m => body (AtIY_assignment m))).
Proof.
  split.
  - apply guarded_atom_sum_product_injection.
  - apply guarded_assignment_sum_product_injection.
Qed.

Local Lemma guarded_sum_on_cong
  (ms : list (At x I^Y))
  (body body' : (At x I^Y) -> CFGKATExpression)
  :
  (forall m,
    In m ms ->
    body m == body' m) ->
  guarded_sum_on ms body == guarded_sum_on ms body'.
Proof.
  induction ms as [|m ms IH]; simpl; intro Hpointwise.
  - apply EqRefl.
  - cfgkat_rewrite (Hpointwise m (or_introl eq_refl)).
    cfgkat_rewrite (IH
      (fun n Hn => Hpointwise n (or_intror Hn))).
    apply EqRefl.
Qed.

Local Lemma guarded_sum_on_zero
  (ms : list (At x I^Y))
  :
  guarded_sum_on ms (fun _ => 0) == 0.
Proof.
  induction ms as [|m ms IH]; simpl.
  - apply EqRefl.
  - cfgkat_rewrite IH.
    apply EqG1.
Qed.

Lemma guarded_sum_on_seq_right
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  (g : CFGKATExpression)
  :
  guarded_sum_on ms body ;; g == guarded_sum_on ms (fun m => body m ;; g).
Proof.
  induction ms as [|m ms IH]; simpl.
  - apply EqS2.
  - cfgkat_rewrite EqG5.
    cfgkat_rewrite IH.
    apply EqRefl.
Qed.

Lemma testdistr_plus_on
  (b : CFGKATTest)
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  :
  test b ;; guarded_sum_on ms body ==
    guarded_sum_on ms (fun m => test b ;; body m).
Proof.
  induction ms as [|m ms IH]; simpl.
  - apply test_abort.
  - cfgkat_rewrite testdistr.
    cfgkat_rewrite IH.
    apply EqRefl.
Qed.

Lemma testdistr_plus
  (b : CFGKATTest)
  (body : (At x I^Y) -> CFGKATExpression)
  :
  test b ;; guarded_sum_all body ==
    guarded_sum_all (fun m => test b ;; body m).
Proof.
  unfold guarded_sum_all.
  apply testdistr_plus_on.
Qed.

Local Lemma guarded_sum_on_loopseq_right
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  (g : CFGKATExpression)
  :
  guarded_sum_on ms body |> g == guarded_sum_on ms (fun m => body m |> g).
Proof.
  induction ms as [|m ms IH]; simpl.
  - apply EqL2.
  - cfgkat_rewrite EqL9.
    cfgkat_rewrite IH.
    apply EqRefl.
Qed.

Lemma branchsel_plus_on
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  (m : (At x I^Y))
  :
  In m ms ->
  test (AtIY_test m) ;;
    guarded_sum_on ms body == test (AtIY_test m) ;; body m.
Proof.
  induction ms as [|n ms IH]; simpl.
  - intros [].
  - intro Hm_in.
    destruct (classic (n = m)) as [Hnm | Hnm].
    + subst n. apply branchsel.
	    + destruct Hm_in as [Hhead | Htail].
	      * exfalso. apply Hnm. exact Hhead.
	      * cfgkat_rewrite (branchskip_disjoint
	          (AtIY_test m) (AtIY_test n) (body n)
	          (guarded_sum_on ms body)
	          (minterms_disagree m n
	            (fun Hmn => Hnm (eq_sym Hmn)))).
	        apply IH. exact Htail.
Qed.

Lemma branchsel_plus
  (body : (At x I^Y) -> CFGKATExpression)
  (m : (At x I^Y))
  :
  test (AtIY_test m) ;;
    guarded_sum_all body == test (AtIY_test m) ;; body m.
Proof.
  unfold guarded_sum_all.
  apply branchsel_plus_on.
  destruct m as [a i].
  apply AtIY_in_all.
Qed.

Definition guarded_sum_satisfying
  (b : CFGKATTest)
  (body : (At x I^Y) -> CFGKATExpression)
  : CFGKATExpression :=
  guarded_sum_on
    (filter (fun m => m \in b) all_AtIY)
    body.

Lemma biplusboollem_on
  (b : CFGKATTest)
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  :
  test b ;; guarded_sum_on ms body == guarded_sum_on (filter (fun m => m \in b) ms) body.
Proof.
  induction ms as [|m ms IH]; simpl.
  - apply test_abort.
  - destruct (m \in b) eqn:Hsat; simpl.
    + cfgkat_rewrite test_choice_split.
      cfgkat_rewrite (EqBoolChoiceCong (body m)
        (test b ;; guarded_sum_on ms body)
        (b and AtIY_test m) (AtIY_test m)
        (minterm_test_true_left b m Hsat)).
      cfgkat_rewrite IH.
      apply EqRefl.
    + cfgkat_rewrite test_choice_split.
      cfgkat_rewrite (EqBoolChoiceCong (body m)
        (test b ;; guarded_sum_on ms body)
        (b and AtIY_test m) (0 : CFGKATTest)
        (minterm_test_false_left b m Hsat)).
      cfgkat_rewrite choice_false_guard.
      apply IH.
Qed.

Local Lemma biplusboollem
  (b : CFGKATTest)
  (body : (At x I^Y) -> CFGKATExpression)
  :
  test b ;; guarded_sum_all body == guarded_sum_satisfying b body.
Proof.
  unfold guarded_sum_all, guarded_sum_satisfying.
  apply biplusboollem_on.
Qed.
Local Lemma guarded_sum_on_const_as_test
  (ms : list (At x I^Y))
  (e : CFGKATExpression)
  :
  guarded_sum_on ms (fun _ => e) == test (fold_TOr (map AtIY_test ms)) ;; e.
Proof.
  induction ms as [|m ms IH]; simpl.
  - apply EqSym. apply EqS2.
  - cfgkat_rewrite IH.
    apply choice_or_test_seq.
Qed.

Lemma idem_plus
  (e : CFGKATExpression)
  :
  guarded_sum_all (fun _ => e) == e.
Proof.
  unfold guarded_sum_all.
  cfgkat_rewrite guarded_sum_on_const_as_test.
  cfgkat_rewrite (EqBoolAssertCong
    (fold_TOr (map AtIY_test all_AtIY))
    (1 : CFGKATTest) minterm_partition).
  apply EqS3.
Qed.

Definition sys
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : CFGKATExpression :=
  match r with
  | CFGKATAutomatonReject => 0
  | CFGKATAutomatonAccept i => complete_assignment i
  | CFGKATAutomatonBreak i => complete_assignment i ;; break
  | CFGKATAutomatonContinue i => complete_assignment i ;; continue
  | CFGKATAutomatonReturn => return
  | CFGKATAutomatonJump l i => complete_assignment i ;; goto l
  | CFGKATAutomatonNext p (f, i) => complete_assignment i ;; do p ;; f
  end.

Definition fundamental_branch
  (e : CFGKATExpression)
  (m : (At x I^Y))
  : CFGKATExpression :=
  sys (transition_output e (AtIY_atom m) (AtIY_assignment m)).

Definition fundamental_normal_form
  (e : CFGKATExpression)
  : CFGKATExpression :=
  guarded_sum_all (fundamental_branch e).

Lemma sysannih
  (i : IndicatorAssignment)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  complete_assignment i ;; sys r == sys r.
Proof.
  destruct r as
    [|j_accept|j_break|j_continue| |l_jump j_jump|p next_state];
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
	  - destruct next_state as [f j_next].
	    cfgkat_rewrite <- EqS1.
	    cfgkat_rewrite <- EqS1.
	    cfgkat_rewrite indannih_plus.
	    apply EqRefl.
Qed.

Lemma indannih_plus_prefix
  (i j : IndicatorAssignment)
  (e : CFGKATExpression)
  :
  complete_assignment i ;; (complete_assignment j ;; e) == complete_assignment j ;; e.
Proof.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite indannih_plus.
  apply EqRefl.
Qed.


Local Lemma minterm_prefix_complete_assignment
  (m : (At x I^Y))
  (e : CFGKATExpression)
  :
  test (AtIY_test m) ;; e == (test (AtIY_test m) ;; complete_assignment (AtIY_assignment m)) ;; e.
Proof.
  cfgkat_rewrite minterm_indred_plus at 1.
  apply EqRefl.
Qed.

Local Lemma minterm_prefix_complete_assignment_right
  (m : (At x I^Y))
  (e : CFGKATExpression)
  :
  test (AtIY_test m) ;; e == test (AtIY_test m) ;;
      (complete_assignment (AtIY_assignment m) ;; e).
Proof.
  cfgkat_rewrite minterm_prefix_complete_assignment at 1.
  apply EqS1.
Qed.

Lemma AtIY_prefix_complete_assignment_insert_AtIY_test
  (a : Atom)
  (i j : IndicatorAssignment)
  :
  test (AtIY_test (a, i)) ;; complete_assignment j == (test (AtIY_test (a, i)) ;; complete_assignment j) ;;
      test (AtIY_test (a, j)).
Proof.
  cfgkat_rewrite <- (test_seq_ba (AtIY_test (a, i))
    (atom_to_test a) (AtIY_test (a, i))
    (BA_leq_to_and_right _ _
      (AtIY_test_leq_atom_to_test a i))) at 1.
  cfgkat_rewrite EqS1 at 1.
  cfgkat_rewrite <- (complete_assignment_on_comm_indicator_free_test
    (elements IndicatorVariable) j (atom_to_test a)
    ltac:(intros x _; apply atom_to_test_indicator_free)).
  cfgkat_rewrite <- EqS1.
  unfold complete_test.
  cfgkat_rewrite indval_plus at 1.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite EqS5.
  cfgkat_rewrite (EqBoolAssertCong
    (complete_test j and atom_to_test a)
    (atom_to_test a and complete_test j)
    (BAAndComm (complete_test j) (atom_to_test a))).
  cfgkat_rewrite <- EqS5.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite EqS5.
  apply EqRefl.
Qed.

Local Lemma AtIY_complete_assignment_branch
  (a : Atom)
  (i j : IndicatorAssignment)
  (f : CFGKATExpression)
  :
  test (AtIY_test (a, j)) ;; f == test (AtIY_test (a, j)) ;;
      sys (transition_output f a j) ->
  test (AtIY_test (a, i)) ;;
    (complete_assignment j ;; f) == test (AtIY_test (a, i)) ;;
      sys (transition_output f a j).
Proof.
  intro Hbranch.
  cfgkat_rewrite <- EqS1 at 1.
  cfgkat_rewrite (AtIY_prefix_complete_assignment_insert_AtIY_test a i j) at 1.
  cfgkat_rewrite EqS1 at 1.
  cfgkat_rewrite Hbranch.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite <- (AtIY_prefix_complete_assignment_insert_AtIY_test a i j) at 1.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite sysannih.
  apply EqRefl.
Qed.

Lemma AtIY_complete_assignment_branch_expr
  (a : Atom)
  (i j : IndicatorAssignment)
  (f g : CFGKATExpression)
  :
  test (AtIY_test (a, j)) ;; f == test (AtIY_test (a, j)) ;; g ->
  complete_assignment j ;; g == g ->
  test (AtIY_test (a, i)) ;;
    (complete_assignment j ;; f) == test (AtIY_test (a, i)) ;; g.
Proof.
  intros Hbranch Hannih.
  cfgkat_rewrite <- EqS1 at 1.
  cfgkat_rewrite (AtIY_prefix_complete_assignment_insert_AtIY_test a i j) at 1.
  cfgkat_rewrite EqS1 at 1.
  cfgkat_rewrite Hbranch.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite <- (AtIY_prefix_complete_assignment_insert_AtIY_test a i j) at 1.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite Hannih.
  apply EqRefl.
Qed.

Lemma minterm_choice_select_true
  (b : CFGKATTest)
  (e f : CFGKATExpression)
  (m : (At x I^Y))
  :
  (m \in b) = true ->
  test (AtIY_test m) ;;
    (if b then e else f) == test (AtIY_test m) ;; e.
Proof.
  intro Hsat.
  cfgkat_rewrite test_choice_split.
  cfgkat_rewrite (EqBoolChoiceCong e (test (AtIY_test m) ;; f)
    (AtIY_test m and b) (AtIY_test m)
    (minterm_test_true_right b m Hsat)).
  cfgkat_rewrite choice_else_guarded_abort.
  apply neutralright.
Qed.

Lemma minterm_choice_select_false
  (b : CFGKATTest)
  (e f : CFGKATExpression)
  (m : (At x I^Y))
  :
  (m \in b) = false ->
  test (AtIY_test m) ;;
    (if b then e else f) == test (AtIY_test m) ;; f.
Proof.
  intro Hsat.
  apply branchskip_disjoint.
  apply minterm_test_false_right. exact Hsat.
Qed.

Local Lemma fundamental_branch_choice
  (b : CFGKATTest)
  (e f : CFGKATExpression)
  (m : (At x I^Y))
  :
  test (AtIY_test m) ;; e == test (AtIY_test m) ;; fundamental_branch e m ->
  test (AtIY_test m) ;; f == test (AtIY_test m) ;; fundamental_branch f m ->
  test (AtIY_test m) ;;
    (if b then e else f) == test (AtIY_test m) ;;
      fundamental_branch (if b then e else f) m.
Proof.
  intros He Hf.
  unfold fundamental_branch.
  destruct (m \in b) eqn:Hsat.
  - rewrite (transition_choice_in_true b e f m Hsat).
    cfgkat_rewrite (minterm_choice_select_true b e f m Hsat).
    exact He.
  - rewrite (transition_choice_in_false b e f m Hsat).
    cfgkat_rewrite (minterm_choice_select_false b e f m Hsat).
    exact Hf.
Qed.

Local Lemma fundamental_branch_sequence
  (e f : CFGKATExpression)
  (m : (At x I^Y))
  :
  test (AtIY_test m) ;; e == test (AtIY_test m) ;; fundamental_branch e m ->
  (forall n,
    In n all_AtIY ->
    test (AtIY_test n) ;; f == test (AtIY_test n) ;; fundamental_branch f n) ->
  test (AtIY_test m) ;; (e ;; f) == test (AtIY_test m) ;; fundamental_branch (e ;; f) m.
Proof.
  destruct m as [ba i].
  intros He Hf.
  unfold fundamental_branch.
  rewrite transition_sequence.
  remember (transition_output e (AtIY_atom (ba, i)) (AtIY_assignment (ba, i)))
    as r eqn:Hr.
  unfold sequence_output.
  unfold fundamental_branch in He.
  rewrite <- Hr in He.
  cfgkat_rewrite <- EqS1 at 1.
  cfgkat_rewrite He at 1.
  destruct r as
    [|j_accept|j_break|j_continue| |l_jump j_jump|p next_state];
    simpl.
  - cfgkat_rewrite test_abort at 1.
    cfgkat_rewrite EqS2.
    apply EqSym. apply test_abort.
  - cfgkat_rewrite EqS1 at 1.
    apply AtIY_complete_assignment_branch.
    unfold fundamental_branch.
    apply Hf.
    apply (AtIY_same_atom_assignment_in (ba, i) j_accept).
  - cfgkat_rewrite EqS1.
    cfgkat_rewrite EqS1.
    cfgkat_rewrite EqS8.
    apply EqRefl.
  - cfgkat_rewrite EqS1.
    cfgkat_rewrite EqS1.
    cfgkat_rewrite EqS7.
    apply EqRefl.
  - cfgkat_rewrite EqS1.
    cfgkat_rewrite EqS6.
    apply EqRefl.
  - cfgkat_rewrite EqS1.
    cfgkat_rewrite EqS1.
    cfgkat_rewrite EqS9.
    apply EqRefl.
  - destruct next_state as [e' j_next].
    cfgkat_rewrite EqS1.
    cfgkat_rewrite EqS1.
    apply EqRefl.
Qed.

Local Lemma branchwise_fundamental
  (e : CFGKATExpression)
  :
  (forall m,
    In m all_AtIY ->
    test (AtIY_test m) ;; e == test (AtIY_test m) ;; fundamental_branch e m) ->
  e == fundamental_normal_form e.
Proof.
  intro Hbranches.
  unfold fundamental_normal_form.
  cfgkat_rewrite <- (idem_plus e) at 1.
  cfgkat_rewrite (guardedness_plus (fun _ => e)).
  cfgkat_rewrite (guarded_sum_on_cong all_AtIY
    (fun m => test (AtIY_test m) ;; e)
    (fun m => test (AtIY_test m) ;; fundamental_branch e m)
    Hbranches).
  cfgkat_rewrite <- (guardedness_plus (fundamental_branch e)).
  apply EqRefl.
Qed.
Local Lemma fundamental_branch_loopseq
  (e f : CFGKATExpression)
  (m : (At x I^Y))
  :
  test (AtIY_test m) ;; e == test (AtIY_test m) ;; fundamental_branch e m ->
  (forall n,
    In n all_AtIY ->
    test (AtIY_test n) ;; f == test (AtIY_test n) ;; fundamental_branch f n) ->
  test (AtIY_test m) ;; (e |> f) == test (AtIY_test m) ;; fundamental_branch (e |> f) m.
Proof.
  destruct m as [ba i].
  intros He Hf.
  unfold fundamental_branch.
  rewrite transition_loopseq.
  remember (transition_output e (AtIY_atom (ba, i)) (AtIY_assignment (ba, i)))
    as r eqn:Hr.
  unfold loopseq_output.
  unfold fundamental_branch in He.
  rewrite <- Hr in He.
  cfgkat_rewrite loopassoctest at 1.
  cfgkat_rewrite He at 1.
  destruct r as
    [|j_accept|j_break|j_continue| |l_jump j_jump|p next_state];
    simpl.
  - cfgkat_rewrite test_abort at 1.
    cfgkat_rewrite EqL2.
    apply EqSym. apply test_abort.
  - cfgkat_rewrite <- loopassoctest at 1.
    cfgkat_rewrite loopseqisseqassign.
    apply AtIY_complete_assignment_branch.
    unfold fundamental_branch.
    apply Hf.
    apply (AtIY_same_atom_assignment_in (ba, i) j_accept).
  - cfgkat_rewrite <- loopassoctest at 1.
    cfgkat_rewrite loopassocassign_plus.
    cfgkat_rewrite EqL5.
    cfgkat_rewrite EqS4.
    apply EqRefl.
  - cfgkat_rewrite <- loopassoctest at 1.
    cfgkat_rewrite loopassocassign_plus.
    cfgkat_rewrite EqL6.
    apply AtIY_complete_assignment_branch.
    unfold fundamental_branch.
    apply Hf.
    apply (AtIY_same_atom_assignment_in (ba, i) j_continue).
  - cfgkat_rewrite <- loopassoctest at 1.
    cfgkat_rewrite EqL3.
    apply EqRefl.
  - cfgkat_rewrite <- loopassoctest at 1.
    cfgkat_rewrite loopassocassign_plus.
    cfgkat_rewrite EqL4.
    apply EqRefl.
  - destruct next_state as [e' j_next].
    cfgkat_rewrite <- loopassoctest at 1.
    cfgkat_rewrite EqS1.
    cfgkat_rewrite loopassocassign_plus.
    cfgkat_rewrite EqL7.
    cfgkat_rewrite EqS1 at 1.
    cfgkat_rewrite <-
      (EqS1 (complete_assignment j_next) (do p) (e' |> f)).
    apply EqRefl.
Qed.

Local Lemma fundamental_branch_loopseq_local
  (e f : CFGKATExpression)
  (m : (At x I^Y))
  :
  test (AtIY_test m) ;; e == test (AtIY_test m) ;; fundamental_branch e m ->
  (forall j,
    transition_output e (AtIY_atom m) (AtIY_assignment m) =
      CFGKATAutomatonAccept j ->
    test (AtIY_test (fst m, j)) ;; f == test (AtIY_test (fst m, j)) ;; fundamental_branch f (fst m, j)) ->
  (forall j,
    transition_output e (AtIY_atom m) (AtIY_assignment m) =
      CFGKATAutomatonContinue j ->
    test (AtIY_test (fst m, j)) ;; f == test (AtIY_test (fst m, j)) ;; fundamental_branch f (fst m, j)) ->
  test (AtIY_test m) ;; (e |> f) == test (AtIY_test m) ;; fundamental_branch (e |> f) m.
Proof.
  destruct m as [ba i].
  intros He Hf_accept Hf_continue.
  unfold fundamental_branch.
  rewrite transition_loopseq.
  remember (transition_output e (AtIY_atom (ba, i)) (AtIY_assignment (ba, i)))
    as r eqn:Hr.
  unfold loopseq_output.
  unfold fundamental_branch in He.
  rewrite <- Hr in He.
  cfgkat_rewrite loopassoctest at 1.
  cfgkat_rewrite He at 1.
  destruct r as
    [|j_accept|j_break|j_continue| |l_jump j_jump|p next_state];
    simpl.
  - cfgkat_rewrite test_abort at 1.
    cfgkat_rewrite EqL2.
    apply EqSym. apply test_abort.
  - cfgkat_rewrite <- loopassoctest at 1.
    cfgkat_rewrite loopseqisseqassign.
    apply AtIY_complete_assignment_branch.
    unfold fundamental_branch.
    apply Hf_accept.
    reflexivity.
  - cfgkat_rewrite <- loopassoctest at 1.
    cfgkat_rewrite loopassocassign_plus.
    cfgkat_rewrite EqL5.
    cfgkat_rewrite EqS4.
    apply EqRefl.
  - cfgkat_rewrite <- loopassoctest at 1.
    cfgkat_rewrite loopassocassign_plus.
    cfgkat_rewrite EqL6.
    apply AtIY_complete_assignment_branch.
    unfold fundamental_branch.
    apply Hf_continue.
    reflexivity.
  - cfgkat_rewrite <- loopassoctest at 1.
    cfgkat_rewrite EqL3.
    apply EqRefl.
  - cfgkat_rewrite <- loopassoctest at 1.
    cfgkat_rewrite loopassocassign_plus.
    cfgkat_rewrite EqL4.
    apply EqRefl.
  - destruct next_state as [e' j_next].
    cfgkat_rewrite <- loopassoctest at 1.
    cfgkat_rewrite EqS1.
    cfgkat_rewrite loopassocassign_plus.
    cfgkat_rewrite EqL7.
    cfgkat_rewrite EqS1 at 1.
    cfgkat_rewrite <-
      (EqS1 (complete_assignment j_next) (do p) (e' |> f)).
    apply EqRefl.
Qed.

Local Lemma L11lemmaFTloop_premise_branch
  (e : CFGKATExpression)
  (b c : CFGKATTest)
  (m : (At x I^Y))
  :
  BA_leq c b ->
  acc_cont_loop_invariant e c ->
  (m \in (c and b)) = true ->
  test (AtIY_test m) ;;
    (fundamental_branch e m |> test (not (c and b))) == 0.
Proof.
  destruct m as [a i].
  intros Hle Hinv Hm.
  pose proof (in_test_true (c and b) (a, i) Hm) as [Hc _].
  pose proof (Hinv a i Hc) as [j [Hout Hc_j]].
  pose proof (BA_leq_eval c b a j Hle Hc_j) as Hb_j.
  assert (Hcb_j : ((a, j) \in (c and b)) = true).
  {
    apply in_test_of_eval.
    split; assumption.
  }
  assert (Hnot_cb_j : ((a, j) \in not (c and b)) = false).
  {
    apply in_test_not_true. exact Hcb_j.
  }
  assert (Htest_branch :
    test (AtIY_test (a, j)) ;; test (not (c and b)) ==
	      test (AtIY_test (a, j)) ;; 0).
  {
    cfgkat_rewrite (test_seq_ba (AtIY_test (a, j))
      (not (c and b)) (0 : CFGKATTest)
      (minterm_test_false_right (not (c and b))
        (a, j) Hnot_cb_j)).
    apply EqSym. apply test_abort.
  }
  destruct Hout as [Haccept | Hcontinue].
  - change (fundamental_branch e (a, i)) with (sys (transition_output e a i)).
    rewrite Haccept. simpl.
    cfgkat_rewrite loopseqisseqassign.
    cfgkat_rewrite (AtIY_complete_assignment_branch_expr
      a i j (test (not (c and b))) 0
      Htest_branch (complete_assignment_abort j)).
    apply test_abort.
  - change (fundamental_branch e (a, i)) with (sys (transition_output e a i)).
    rewrite Hcontinue. simpl.
    cfgkat_rewrite loopassocassign_plus.
    cfgkat_rewrite EqL6.
    cfgkat_rewrite (AtIY_complete_assignment_branch_expr
      a i j (test (not (c and b))) 0
      Htest_branch (complete_assignment_abort j)).
    apply test_abort.
Qed.

Local Lemma L11lemmaFTloop_premise
  (e : CFGKATExpression)
  (b c : CFGKATTest)
  :
  BA_leq c b ->
  acc_cont_loop_invariant e c ->
  (forall m,
    In m all_AtIY ->
    test (AtIY_test m) ;; e == test (AtIY_test m) ;; fundamental_branch e m) ->
  ((test (c and b) ;; e) |> test (not (c and b))) == 0.
Proof.
  intros Hle Hinv IH.
  cfgkat_rewrite (EqLoopSeqLeftEmptyCong
    (test (c and b) ;; e)
    (test (c and b) ;; fundamental_normal_form e)
    (test (not (c and b)))
    ltac:(eapply EqSeqRightCong;
      [apply branchwise_fundamental; exact IH | apply EqRefl])).
  unfold fundamental_normal_form.
  cfgkat_rewrite biplusboollem.
  unfold guarded_sum_satisfying.
  cfgkat_rewrite guarded_sum_on_loopseq_right.
  cfgkat_rewrite guardedness_plus_on.
  cfgkat_rewrite (guarded_sum_on_cong
    (filter (fun m => m \in c and b) all_AtIY)
    _ (fun _ => 0)
    ltac:(intros m Hm;
      apply filter_In in Hm;
      eapply L11lemmaFTloop_premise_branch;
      [exact Hle | exact Hinv | exact (proj2 Hm)])).
  apply guarded_sum_on_zero.
Qed.

Lemma L11lemmaFTloop
  (e : CFGKATExpression)
  (b c : CFGKATTest)
  :
  BA_leq c b ->
  acc_cont_loop_invariant e c ->
  (forall m,
    In m all_AtIY ->
    test (AtIY_test m) ;; e == test (AtIY_test m) ;; fundamental_branch e m) ->
  (while b do e) ==
    (while b do (test (not c) ;; e)).
Proof.
  intros Hle Hinv IH.
  apply EqL11.
  eapply L11lemmaFTloop_premise; eauto.
Qed.

Lemma L11lemmaFTloop_largest
  (e : CFGKATExpression)
  (b : CFGKATTest)
  :
  (forall m,
    In m all_AtIY ->
    test (AtIY_test m) ;; e == test (AtIY_test m) ;; fundamental_branch e m) ->
  (while b do e) ==
    (while b do (test (not C+[e, b]) ;; e)).
Proof.
  intro IH.
  eapply L11lemmaFTloop.
  - apply largest_loop_invariant_test_leq_guard.
  - apply largest_loop_invariant_test_acc_cont_invariant.
  - exact IH.
Qed.

Local Lemma fundamental_branch_loop_guard_false
  (b : CFGKATTest)
  (e : CFGKATExpression)
  (m : (At x I^Y))
  :
  (m \in b) = false ->
  test (AtIY_test m) ;; (while b do e) ==
    test (AtIY_test m) ;; fundamental_branch (while b do e) m.
Proof.
  intro Hsat.
  unfold fundamental_branch.
  rewrite (transition_loop_in_false b e m Hsat). simpl.
  cfgkat_rewrite EqL10 at 1.
  cfgkat_rewrite (minterm_choice_select_false b
    (e |> while b do e) 1 m Hsat).
  cfgkat_rewrite EqS4.
  apply minterm_indred_plus.
Qed.

Local Lemma fundamental_branch_loop_guard_true
  (b : CFGKATTest)
  (e : CFGKATExpression)
  (m : (At x I^Y))
  :
  (m \in b) = true ->
  test (AtIY_test m) ;; (e |> while b do e) == test (AtIY_test m) ;; fundamental_branch (e |> while b do e) m ->
  test (AtIY_test m) ;; (while b do e) ==
    test (AtIY_test m) ;; fundamental_branch (while b do e) m.
Proof.
  intros Hsat Hloopseq.
  unfold fundamental_branch.
  rewrite (transition_loop_in_true b e m Hsat).
  cfgkat_rewrite EqL10 at 1.
  cfgkat_rewrite (minterm_choice_select_true b
    (e |> while b do e) 1 m Hsat).
  exact Hloopseq.
Qed.

Local Lemma fundamental_branch_loop_cplus_invariant
  (b : CFGKATTest)
  (e : CFGKATExpression)
  (m : (At x I^Y))
  :
  (while b do e) ==
    (while b do (test (not C+[e, b]) ;; e)) ->
  (m \in b) = true ->
  (m \in largest_loop_invariant_test e b) = true ->
  test (AtIY_test m) ;; (while b do e) ==
    test (AtIY_test m) ;; fundamental_branch (while b do e) m.
Proof.
  intros Htighten Hb Hc.
  pose proof
    (in_test_true (largest_loop_invariant_test e b) m Hc)
    as Hc_eval.
  pose proof (in_test_true b m Hb) as Hb_eval.
  assert (Hbc :
    eval_test (largest_loop_invariant_test e b and b)
      (AtIY_atom m) (AtIY_assignment m)).
  {
    split; assumption.
  }
  pose proof
    (cfgkat_invariant_while_dynamics_reject
      e b (largest_loop_invariant_test e b)
      (AtIY_assignment m) (AtIY_atom m)
      (CFGKATL11Premise_comm e b (largest_loop_invariant_test e b)
        (largest_loop_invariant_l11_premise e b))
      Hbc)
    as Hloop_reject_dyn.
  pose proof
    (transition_output_unique
      (while b do e) (AtIY_atom m) (AtIY_assignment m)
      CFGKATAutomatonReject Hloop_reject_dyn)
    as Hloop_reject.
  unfold fundamental_branch.
  rewrite Hloop_reject. simpl.
  cfgkat_rewrite Htighten at 1.
  cfgkat_rewrite EqL10 at 1.
  cfgkat_rewrite (minterm_choice_select_true b
    ((test (not C+[e, b]) ;; e) |>
      while b do (test (not C+[e, b]) ;; e)) 1 m Hb).
  cfgkat_rewrite loopassoctest.
  cfgkat_rewrite (test_seq_annihilate_right
    (AtIY_test m) (not C+[e, b])
    (minterm_test_false_right (not C+[e, b]) m
      (in_test_not_true C+[e, b] m Hc))).
  cfgkat_rewrite EqL2.
  apply EqSym. apply test_abort.
Qed.

Theorem fundamental_theorem
  (e : CFGKATExpression)
  :
  e == fundamental_normal_form e.
Proof.
  apply branchwise_fundamental.
  induction e as
    [b | p | x v | | | | l | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b e IH].
  -
    intros m _. unfold fundamental_branch.
    destruct (m \in b) eqn:Hsat.
    + rewrite (transition_assert_in_true b m Hsat). simpl.
      cfgkat_rewrite (test_seq_ba (AtIY_test m) b
        (AtIY_test m) (minterm_test_true_right b m Hsat)).
      apply minterm_indred_plus.
    + rewrite (transition_assert_in_false b m Hsat). simpl.
      cfgkat_rewrite (test_seq_ba (AtIY_test m) b
        0 (minterm_test_false_right b m Hsat)).
      apply EqSym. apply test_abort.
  -
    intros m _. unfold fundamental_branch.
    rewrite transition_action. simpl.
    cfgkat_rewrite minterm_prefix_complete_assignment at 1.
    cfgkat_rewrite <- (EqS4 (do p)) at 1.
    cfgkat_rewrite EqS1 at 1.
    cfgkat_rewrite <- EqS1 at 2.
    apply EqRefl.
  -
    intros m _. unfold fundamental_branch.
    rewrite transition_assign. simpl.
    cfgkat_rewrite minterm_prefix_complete_assignment at 1.
    cfgkat_rewrite EqS1.
    cfgkat_rewrite (complete_assignment_on_assign_update
      (elements IndicatorVariable) (AtIY_assignment m) x v
      ltac:(apply nodup)
      ltac:(apply all_in)).
    apply EqRefl.
  -
    intros m _. unfold fundamental_branch.
    rewrite transition_break. simpl.
    apply minterm_prefix_complete_assignment_right.
  -
    intros m _. unfold fundamental_branch.
    rewrite transition_continue. simpl.
    apply minterm_prefix_complete_assignment_right.
  -
    intros m _. unfold fundamental_branch.
    rewrite transition_return. simpl.
    apply EqRefl.
  -
    intros m _. unfold fundamental_branch.
    rewrite transition_goto. simpl.
    apply minterm_prefix_complete_assignment_right.
  -
    intros m Hm.
    apply fundamental_branch_choice.
    + apply IH1. exact Hm.
    + apply IH2. exact Hm.
  -
    intros m Hm.
    apply fundamental_branch_sequence.
    + apply IH1. exact Hm.
    + exact IH2.
  -
    intros m Hm.
    apply fundamental_branch_loopseq.
    + apply IH1. exact Hm.
    + exact IH2.
  -
    intros m Hm.
    pose proof (L11lemmaFTloop_largest e b IH) as Htighten.
    eapply (loop_cplus_AtIY_induction e b
      (fun n =>
        test (AtIY_test n) ;; (while b do e) ==
          test (AtIY_test n) ;; fundamental_branch (while b do e) n)).
    + intros n _ Hb.
      apply fundamental_branch_loop_guard_false.
      exact Hb.
    + intros n _ Hb HCplus.
      apply fundamental_branch_loop_cplus_invariant; assumption.
    + intros n Hn Hb _ Haccept Hcontinue.
      apply fundamental_branch_loop_guard_true.
      * exact Hb.
      * apply fundamental_branch_loopseq_local.
        -- apply IH. exact Hn.
        -- exact Haccept.
        -- exact Hcontinue.
    + exact Hm.
Qed.

Lemma L11lemmaFTloop_unconditional
  (e : CFGKATExpression)
  (b : CFGKATTest)
  :
  (while b do e) ==
    (while b do (test (not largest_loop_invariant_test e b) ;; e)).
Proof.
  apply L11lemmaFTloop_largest.
  intros m _.
  cfgkat_rewrite (fundamental_theorem e) at 1.
  unfold fundamental_normal_form.
  apply branchsel_plus.
Qed.
