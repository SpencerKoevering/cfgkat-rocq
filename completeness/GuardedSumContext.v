From CFGKAT.Completeness Require Export FundamentalTheorem.
Require Import Stdlib.Logic.Classical.
From Stdlib Require Import Lists.List.
Import ListNotations.

Local Open Scope cfgkat_scope.
Local Open Scope cfgkat_setoid_scope.

Lemma filter_all_true
  {A : Type}
  (f : A -> bool)
  (xs : list A)
  :
  (forall x, In x xs -> f x = true) ->
  filter f xs = xs.
Proof.
  intro Hall.
  induction xs as [|x xs IH]; simpl; [reflexivity |].
  rewrite Hall by (left; reflexivity).
  rewrite IH by (intros y Hy; apply Hall; right; exact Hy).
  reflexivity.
Qed.

Lemma generic_guarded_sum_select_on
  {A : Type}
  (sum_on : list A -> CFGKATExpression)
  (guard : A -> CFGKATTest)
  (selected_guard : CFGKATTest)
  (branch_body : A -> CFGKATExpression)
  (selected_body : CFGKATExpression)
  (matches : A -> Prop)
  (xs : list A)
  :
  (forall x xs,
    sum_on (x :: xs) =
      (if guard x then branch_body x else sum_on xs)) ->
  (exists x, In x xs /\ matches x) ->
  (forall x,
    matches x ->
    guard x = selected_guard /\ branch_body x = selected_body) ->
  (forall x,
    In x xs ->
    ~ matches x ->
    (selected_guard and guard x) =BA 0) ->
  test selected_guard ;; sum_on xs ==
    test selected_guard ;; selected_body.
Proof.
  intros Hcons Hexists Hmatch Hskip.
  revert Hexists Hskip.
  induction xs as [|x xs IH]; intros Hexists Hskip.
  - destruct Hexists as [x [[] _]].
  - rewrite Hcons.
    destruct (classic (matches x)) as [Hx | Hx].
    + destruct (Hmatch x Hx) as [Hguard Hbody].
      rewrite Hguard, Hbody.
      apply branchsel.
    + cfgkat_rewrite (branchskip_disjoint
        selected_guard (guard x) (branch_body x) (sum_on xs)
        (Hskip x (or_introl eq_refl) Hx)).
      apply IH.
      * destruct Hexists as [y [[Hy | Hy] Hmatch_y]].
        -- subst y. contradiction.
        -- exists y. split; assumption.
      * intros y Hy Hmatch_y.
        apply Hskip.
        -- right. exact Hy.
        -- exact Hmatch_y.
Qed.

Lemma branchsel_assignment_on
  (assignments : list IndicatorAssignment)
  (body : IndicatorAssignment -> CFGKATExpression)
  (i : IndicatorAssignment)
  :
  In i assignments ->
  test (complete_test i) ;;
    guarded_assignment_sum_on assignments body ==
    test (complete_test i) ;; body i.
Proof.
  intro Hin.
  eapply (@generic_guarded_sum_select_on
    IndicatorAssignment
    (fun assignments => guarded_assignment_sum_on assignments body)
    complete_test
    (complete_test i)
    body
    (body i)
    (fun j => j = i)
    assignments).
  - reflexivity.
  - exists i. split; [exact Hin | reflexivity].
  - intros j Hji. subst j. split; reflexivity.
  - intros j _ Hji.
    apply complete_tests_disagree.
    intro Hij. apply Hji. exact (eq_sym Hij).
Qed.

Lemma branchsel_atom_on
  (atoms : list (Test -> bool))
  (body : Atom -> CFGKATExpression)
  (ba : Test -> bool)
  :
  In ba atoms ->
  test (atom_to_test (bool_to_atom ba)) ;;
    guarded_atom_sum_on atoms body ==
    test (atom_to_test (bool_to_atom ba)) ;; body (bool_to_atom ba).
Proof.
  intro Hin.
  eapply (@generic_guarded_sum_select_on
    (Test -> bool)
    (fun atoms => guarded_atom_sum_on atoms body)
    (fun ba' => atom_to_test (bool_to_atom ba'))
    (atom_to_test (bool_to_atom ba))
    (fun ba' => body (bool_to_atom ba'))
    (body (bool_to_atom ba))
    (fun ba' => bool_to_atom ba' = bool_to_atom ba)
    atoms).
  - reflexivity.
  - exists ba. split; [exact Hin | reflexivity].
  - intros ba' Heq. rewrite Heq. split; reflexivity.
  - intros ba' _ Hneq.
    apply atom_to_tests_disagree.
    intro Heq. apply Hneq. exact (eq_sym Heq).
Qed.

Lemma guarded_sum_on_cong_ctx
  (E F : label_environment CFGKATExpression)
  (ms : list (At x I^Y))
  (body body' : (At x I^Y) -> CFGKATExpression)
  :
  (forall m,
    In m ms ->
    E |- body m == body' m -| F) ->
  E |- guarded_sum_on ms body ==
    guarded_sum_on ms body' -| F.
Proof.
  intros Hbranches.
  induction ms as [|m ms IH]; simpl.
  - apply strong_equiv_no_goto.
    simpl. tauto.
  - apply EqChoiceCong.
    + apply Hbranches. left. reflexivity.
    + apply IH.
      intros n Hn.
      apply Hbranches. right. exact Hn.
Qed.

Lemma guarded_sum_all_cong_ctx
  (E F : label_environment CFGKATExpression)
  (body body' : (At x I^Y) -> CFGKATExpression)
  :
  (forall m,
    In m all_AtIY ->
    E |- body m == body' m -| F) ->
  E |- guarded_sum_all body ==
    guarded_sum_all body' -| F.
Proof.
  unfold guarded_sum_all.
  apply guarded_sum_on_cong_ctx.
Qed.

Lemma guarded_sum_on_jump_inv
  (ms : list (At x I^Y))
  (body : (At x I^Y) -> CFGKATExpression)
  (i j : IndicatorAssignment)
  (a : Atom)
  (l : Label)
  :
  CFGKATExpressionDynamics (guarded_sum_on ms body, i) a
    (CFGKATAutomatonJump l j) ->
  exists m,
    In m ms /\
    CFGKATExpressionDynamics (body m, i) a
      (CFGKATAutomatonJump l j).
Proof.
  intro Hdyn.
  pose proof
    (transition_output_unique
      (guarded_sum_on ms body) a i
      (CFGKATAutomatonJump l j) Hdyn) as Hout.
  revert Hdyn Hout.
  induction ms as [|m ms IH]; intros Hdyn Hout; simpl in Hout.
  - rewrite transition_assert in Hout.
    destruct (eval_test_dec (0 : CFGKATTest) a i); discriminate.
  - rewrite transition_choice in Hout.
    destruct (eval_test_dec (AtIY_test m) a i).
    + exists m.
      split; [left; reflexivity |].
      apply (proj2 (transition_output_exact (body m) a i _)).
      exact Hout.
    + destruct (IH
        (proj2 (transition_output_exact
          (guarded_sum_on ms body) a i _) Hout)
        Hout) as [selected [Hselected Hjump]].
      exists selected.
      split; [right; exact Hselected | exact Hjump].
Qed.
