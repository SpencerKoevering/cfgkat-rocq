From CFGKAT.Examples Require Export UsefulFacts.
Require Import Stdlib.Logic.FunctionalExtensionality.
From Stdlib Require Import Lists.List.
Import ListNotations.

Local Open Scope cfgkat_scope.
Local Open Scope cfgkat_setoid_scope.


Fixpoint expression_does_not_reference_indicator
  (x : IndicatorVariable)
  (e : CFGKATExpression)
  : Prop :=
  match e with
  | CFGKATAssert b => test_indicator_free x b
  | CFGKATAction _ => True
  | CFGKATAssign y _ => y <> x
  | CFGKATBreak => True
  | CFGKATContinue => True
  | CFGKATReturn => True
  | CFGKATGoto _ => True
  | CFGKATChoice b e1 e2 =>
      test_indicator_free x b /\
      expression_does_not_reference_indicator x e1 /\
      expression_does_not_reference_indicator x e2
  | CFGKATSequence e1 e2 =>
      expression_does_not_reference_indicator x e1 /\
      expression_does_not_reference_indicator x e2
  | CFGKATLoopSeq e1 e2 =>
      expression_does_not_reference_indicator x e1 /\
      expression_does_not_reference_indicator x e2
  | CFGKATLoop b body =>
      test_indicator_free x b /\
      expression_does_not_reference_indicator x body
  end.

Local Notation "e 'dnr' x" :=
  (expression_does_not_reference_indicator x e)
  (at level 70).

Local Lemma expression_does_not_reference_indicator_assign_free
  (x : IndicatorVariable)
  (e : CFGKATExpression)
  :
  e dnr x ->
  e dna x.
Proof.
  induction e as
    [b | p | y vy | | | | l | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b e IH];
    simpl; intro Hno; try exact I.
  - exact Hno.
  - destruct Hno as [_ [H1 H2]].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [H1 H2].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [H1 H2].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [_ Hbody].
    apply IH. exact Hbody.
Qed.

Local Lemma expression_does_not_reference_indicator_assigns_indicator_only_value
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e : CFGKATExpression)
  :
  e dnr x ->
  expression_assigns_indicator_only_value x v e.
Proof.
  induction e as
    [b | p | y vy | | | | l | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b e IH];
    simpl; intro Hno; try exact I.
  - left. exact Hno.
  - destruct Hno as [_ [H1 H2]].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [H1 H2].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [H1 H2].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [_ Hbody].
    apply IH. exact Hbody.
Qed.

Local Lemma expression_does_not_reference_indicator_not_test
  (x : IndicatorVariable)
  (e : CFGKATExpression)
  :
  e dnr x ->
  expression_does_not_test_indicator x e.
Proof.
  induction e as
    [b | p | y vy | | | | l | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b e IH];
    simpl; intro Hno; try exact I.
  - exact Hno.
  - destruct Hno as [Hb [H1 H2]].
    repeat split; [exact Hb | apply IH1 | apply IH2]; assumption.
  - destruct Hno as [H1 H2].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [H1 H2].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [Hb Hbody].
    split; [exact Hb | apply IH]; assumption.
Qed.

Fixpoint program_does_not_reference_indicator
  (x : IndicatorVariable)
  (e : CFGKATProgramSyntax)
  : Prop :=
  match e with
  | CFGKATProgramAssert b => test_indicator_free x b
  | CFGKATProgramAction _ => True
  | CFGKATProgramAssign y _ => y <> x
  | CFGKATProgramBreak => True
  | CFGKATProgramContinue => True
  | CFGKATProgramReturn => True
  | CFGKATProgramGoto _ => True
  | CFGKATProgramLabel _ => True
  | CFGKATProgramChoice b e1 e2 =>
      test_indicator_free x b /\
      program_does_not_reference_indicator x e1 /\
      program_does_not_reference_indicator x e2
  | CFGKATProgramSequence e1 e2 =>
      program_does_not_reference_indicator x e1 /\
      program_does_not_reference_indicator x e2
  | CFGKATProgramLoopSeq e1 e2 =>
      program_does_not_reference_indicator x e1 /\
      program_does_not_reference_indicator x e2
  | CFGKATProgramLoop b body =>
      test_indicator_free x b /\
      program_does_not_reference_indicator x body
  end.

Local Notation "e 'pdnr' x" :=
  (program_does_not_reference_indicator x e)
  (at level 70).

Local Lemma program_does_not_reference_indicator_erase
  (x : IndicatorVariable)
  (e : CFGKATProgramSyntax)
  :
  e pdnr x ->
  label_erase e dnr x.
Proof.
  induction e as
    [b | p | y vy | | | | l | l | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b e IH];
    simpl; intro Hno; try exact I.
  - exact Hno.
  - exact Hno.
  - destruct Hno as [Hb [H1 H2]].
    repeat split; [exact Hb | apply IH1 | apply IH2]; assumption.
  - destruct Hno as [H1 H2].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [H1 H2].
    split; [apply IH1 | apply IH2]; assumption.
  - destruct Hno as [Hb Hbody].
    split; [exact Hb | apply IH]; assumption.
Qed.

Local Lemma program_does_not_reference_indicator_extraction
  (x : IndicatorVariable)
  (e : CFGKATProgramSyntax)
  (l : Label)
  (body : CFGKATExpression)
  :
  e pdnr x ->
  label_extraction_syntax e l = Some body ->
  body dnr x.
Proof.
  revert l body.
  induction e as
    [b | p | y vy | | | | l0 | l0 | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b e IH];
    intros l body Hno Hbody; simpl in Hbody; try discriminate.
  - destruct (Label_eq_dec l0 l); inversion Hbody; subst.
    exact I.
  - destruct Hno as [_ [H1 H2]].
    destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody1.
    + inversion Hbody; subst.
      eapply IH1; eauto.
    + eapply IH2; eauto.
  - destruct Hno as [H1 H2].
    destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody1.
    + inversion Hbody; subst.
      split.
      * eapply IH1; eauto.
      * apply program_does_not_reference_indicator_erase. exact H2.
    + eapply IH2; eauto.
  - destruct Hno as [H1 H2].
    destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody1.
    + inversion Hbody; subst.
      split.
      * eapply IH1; eauto.
      * apply program_does_not_reference_indicator_erase. exact H2.
    + eapply IH2; eauto.
  - destruct Hno as [Hb Hbody_no].
    destruct (label_extraction_syntax e l) as [body_at_label |] eqn:Hlabel;
      inversion Hbody; subst.
    split.
    + eapply IH; eauto.
    + simpl. split.
      * exact Hb.
      * apply program_does_not_reference_indicator_erase.
        exact Hbody_no.
Qed.

Local Lemma program_does_not_reference_indicator_no_test_reduced
  (x : IndicatorVariable)
  (e : CFGKATProgramSyntax)
  :
  e pdnr x ->
  expression_does_not_test_indicator x (label_erase e) /\
  env_does_not_test_indicator x (label_extraction_syntax_environment e).
Proof.
  intro Hno.
  split.
  - apply expression_does_not_reference_indicator_not_test.
    apply program_does_not_reference_indicator_erase.
    exact Hno.
  - unfold env_does_not_test_indicator, env_all,
      label_extraction_syntax_environment.
    intros l body Hbody.
    apply expression_does_not_reference_indicator_not_test.
    eapply program_does_not_reference_indicator_extraction; eauto.
Qed.

Local Ltac solve_assign_free_from_dnr :=
  apply expression_does_not_reference_indicator_assign_free;
  apply program_does_not_reference_indicator_erase; assumption.

Local Ltac solve_assign_free_from_expr_dnr :=
  apply expression_does_not_reference_indicator_assign_free; assumption.

Local Ltac solve_no_test_from_dnr :=
  apply expression_does_not_reference_indicator_not_test;
  apply program_does_not_reference_indicator_erase; assumption.

Local Lemma ghost_erase_identity_dna
  (x : IndicatorVariable)
  (e : CFGKATExpression)
  :
  e dna x ->
  ghost_erase x e = e.
Proof.
  induction e as
    [b | p | y vy | | | | l | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b e IH];
    simpl; intro Hno; try reflexivity.
  - destruct (Var_eq_dec y x) as [Heq | _].
    + contradiction.
    + reflexivity.
  - destruct Hno as [H1 H2].
    rewrite IH1 by exact H1.
    rewrite IH2 by exact H2.
    reflexivity.
  - destruct Hno as [H1 H2].
    rewrite IH1 by exact H1.
    rewrite IH2 by exact H2.
    reflexivity.
  - destruct Hno as [H1 H2].
    rewrite IH1 by exact H1.
    rewrite IH2 by exact H2.
    reflexivity.
  - rewrite IH by exact Hno.
    reflexivity.
Qed.

Local Lemma program_ghost_erase_env_identity_dnr
  (x : IndicatorVariable)
  (e : CFGKATProgramSyntax)
  :
  e pdnr x ->
  ghost_erase_env x (label_extraction_syntax_environment e) =
    label_extraction_syntax_environment e.
Proof.
  intro Hno.
  apply environment_eq.
  intro l.
  unfold ghost_erase_env, label_extraction_syntax_environment,
    mk_environment.
  cbn.
  destruct (label_extraction_syntax e l) as [body |] eqn:Hbody.
  - rewrite ghost_erase_identity_dna.
    + reflexivity.
    + apply expression_does_not_reference_indicator_assign_free.
      eapply program_does_not_reference_indicator_extraction; eauto.
  - reflexivity.
Qed.

Local Lemma assign_prefixed_dnr_sequence_cong_from_assign
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e k1 k2 : CFGKATExpression)
  :
  e dnr x ->
  assign v to x ;; k1 == assign v to x ;; k2 ->
  assign v to x ;; (e ;; k1) ==
    assign v to x ;; (e ;; k2).
Proof.
  intros He Hk.
  apply assign_prefixed_dna_sequence_cong_from_assign.
  - apply expression_does_not_reference_indicator_assign_free.
    exact He.
  - exact Hk.
Qed.

Local Lemma assign_prefixed_dnr_loopseq_cong_from_assign
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e k1 k2 : CFGKATExpression)
  :
  e dnr x ->
  assign v to x ;; k1 == assign v to x ;; k2 ->
  assign v to x ;; (e |> k1) ==
    assign v to x ;; (e |> k2).
Proof.
  intros He Hk.
  apply assign_prefixed_dna_loopseq_cong_from_assign.
  - apply expression_does_not_reference_indicator_assign_free.
    exact He.
  - exact Hk.
Qed.

Definition eh_source_program
  (ell : Label)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  : CFGKATProgramSyntax :=
  (((if c then goto ell else 1) ;;
    (e ;;
      (while b do (f ;; (label ell ;; g))))) ;;
    return)%cfgkat_program.

Definition eh_transformed_loop_body
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (f g : CFGKATProgramSyntax)
  : CFGKATProgramSyntax :=
  ((if x is one then goto ell else 1) ;;
    (f ;; (label ell ;; (assign zero to x ;; g))))%cfgkat_program.

Definition eh_transformed_program
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  : CFGKATProgramSyntax :=
  (((if c then assign one to x else assign zero to x) ;;
    ((if x is zero then e else 1) ;;
      (while (b or x is one) do
        eh_transformed_loop_body ell x one zero f g))) ;;
    return)%cfgkat_program.

Local Lemma eh_source_program_ends_with_return
  (ell : Label)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  program_ends_with_return (eh_source_program ell c b e f g).
Proof.
  unfold program_ends_with_return, eh_source_program.
  eexists. reflexivity.
Qed.

Local Definition eh_program_labels
  (ell : Label)
  (e f g : CFGKATProgramSyntax)
  : list Label :=
  program_labels e ++ program_labels f ++ ell :: program_labels g.


Local Lemma eh_source_program_labels
  (ell : Label)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  program_labels (eh_source_program ell c b e f g) =
    eh_program_labels ell e f g.
Proof.
  unfold eh_source_program, eh_program_labels.
  simpl.
  repeat rewrite List.app_nil_r.
  reflexivity.
Qed.

Local Lemma eh_transformed_program_labels
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  program_labels (eh_transformed_program ell x one zero c b e f g) =
    eh_program_labels ell e f g.
Proof.
  unfold eh_transformed_program, eh_transformed_loop_body,
    eh_program_labels.
  simpl.
  repeat rewrite List.app_nil_r.
  reflexivity.
Qed.

Local Lemma eh_well_labeled_program_ell_not_in_generics
  (ell : Label)
  (e f g : CFGKATProgramSyntax)
  :
  NoDup (eh_program_labels ell e f g) ->
  ~ In ell (program_labels e ++ program_labels f ++ program_labels g).
Proof.
  unfold eh_program_labels.
  intro Hnodup.
  rewrite app_assoc in Hnodup.
  pose proof
    (NoDup_remove_2
      (program_labels e ++ program_labels f)
      (program_labels g)
      ell
      Hnodup) as Hnot.
  intro Hin.
  apply Hnot.
  rewrite <- app_assoc.
  exact Hin.
Qed.

Local Lemma eh_source_well_labeled_ell_not_in_generics
  (ell : Label)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  well_labeled_program (eh_source_program ell c b e f g) ->
  ~ In ell (program_labels e ++ program_labels f ++ program_labels g).
Proof.
  unfold well_labeled_program.
  rewrite eh_source_program_labels.
  apply eh_well_labeled_program_ell_not_in_generics.
Qed.

Local Lemma eh_target_well_labeled_ell_not_in_generics
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  well_labeled_program (eh_transformed_program ell x one zero c b e f g) ->
  ~ In ell (program_labels e ++ program_labels f ++ program_labels g).
Proof.
  unfold well_labeled_program.
  rewrite eh_transformed_program_labels.
  apply eh_well_labeled_program_ell_not_in_generics.
Qed.

Local Lemma NoDup_app_disjoint
  {A : Type}
  (xs ys : list A)
  :
  NoDup (xs ++ ys) ->
  forall a, In a xs -> ~ In a ys.
Proof.
  induction xs as [|x xs IH]; simpl.
  - intros _ a Hin. contradiction.
  - intros Hnodup a Hin Hiny.
    inversion Hnodup as [|? ? Hnotin Htail]; subst.
    destruct Hin as [Ha | Hin].
    + subst a.
      apply Hnotin.
      apply in_or_app. right. exact Hiny.
    + eapply IH; eauto.
Qed.

Local Lemma eh_well_labeled_from_f_not_in_e
  (ell l : Label)
  (e f g : CFGKATProgramSyntax)
  :
  NoDup (eh_program_labels ell e f g) ->
  program_label_occurs l f ->
  ~ program_label_occurs l e.
Proof.
  unfold eh_program_labels, program_label_occurs.
  intros Hnodup Hin_f Hin_e.
  eapply NoDup_app_disjoint with
    (xs := program_labels e)
    (ys := program_labels f ++ ell :: program_labels g)
    (a := l).
  - exact Hnodup.
  - exact Hin_e.
  - apply in_or_app. left. exact Hin_f.
Qed.

Local Lemma eh_well_labeled_from_g_not_in_e
  (ell l : Label)
  (e f g : CFGKATProgramSyntax)
  :
  NoDup (eh_program_labels ell e f g) ->
  program_label_occurs l g ->
  ~ program_label_occurs l e.
Proof.
  unfold eh_program_labels, program_label_occurs.
  intros Hnodup Hin_g Hin_e.
  eapply NoDup_app_disjoint with
    (xs := program_labels e)
    (ys := program_labels f ++ ell :: program_labels g)
    (a := l).
  - exact Hnodup.
  - exact Hin_e.
  - apply in_or_app. right. right. exact Hin_g.
Qed.

Local Lemma eh_well_labeled_from_g_not_in_f
  (ell l : Label)
  (e f g : CFGKATProgramSyntax)
  :
  NoDup (eh_program_labels ell e f g) ->
  program_label_occurs l g ->
  ~ program_label_occurs l f.
Proof.
  unfold eh_program_labels, program_label_occurs.
  intros Hnodup Hin_g Hin_f.
  pose proof
    (NoDup_app_remove_l
      (program_labels e)
      (program_labels f ++ ell :: program_labels g)
      Hnodup) as Htail.
  eapply NoDup_app_disjoint with
    (xs := program_labels f)
    (ys := ell :: program_labels g)
    (a := l).
  - exact Htail.
  - exact Hin_f.
  - right. exact Hin_g.
Qed.

Local Lemma eh_well_labeled_from_g_neq_ell
  (ell l : Label)
  (e f g : CFGKATProgramSyntax)
  :
  NoDup (eh_program_labels ell e f g) ->
  program_label_occurs l g ->
  l <> ell.
Proof.
  unfold eh_program_labels, program_label_occurs.
  intros Hnodup Hin_g Heq.
  subst l.
  pose proof
    (NoDup_app_remove_l
      (program_labels e)
      (program_labels f ++ ell :: program_labels g)
      Hnodup) as Htail.
  pose proof
    (NoDup_remove_2 (program_labels f) (program_labels g) ell Htail)
    as Hnot.
  apply Hnot.
  apply in_or_app. right. exact Hin_g.
Qed.

Local Definition eh_source_normal_form
  (ell : Label)
  (c b : CFGKATTest)
  (e f g : CFGKATExpression)
  : CFGKATExpression :=
  if c then goto ell else e ;; ((while b do (f ;; g)) ;; return).


Local Definition eh_target_loop_body_erased
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (f g : CFGKATExpression)
  : CFGKATExpression :=
  (if x is one then goto ell else 1) ;;
    (f ;; (1 ;; (assign zero to x ;; g))).

Local Definition eh_target_loop_guard
  (x : IndicatorVariable)
  (one : IndicatorValue)
  (b : CFGKATTest)
  : CFGKATTest :=
  b or x is one.

Local Definition eh_target_split_form
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATExpression)
  : CFGKATExpression :=
  if c then assign one to x ;; goto ell
  else assign zero to x ;;
    ((if x is zero then e else 1) ;;
      ((while eh_target_loop_guard x one b do
          eh_target_loop_body_erased ell x one zero f g) ;; return)).

Local Lemma test_prefix_test_sequence_cong_from_and_BA
  (p q r : CFGKATTest)
  (e : CFGKATExpression)
  :
  TAnd p q =BA TAnd p r ->
  test p ;; (test q ;; e) ==
    test p ;; (test r ;; e).
Proof.
  intro Hqr.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite (test_seq_ba p q (p and r) Hqr).
  cfgkat_rewrite <- EqS5.
  apply EqS1.
Qed.

Local Ltac eh_assignment_output_from_prefixed Hpref :=
  rewrite <- (assignment_prefix_transition_same _ _ _ _ _ ltac:(eassumption));
  exact Hpref.

Local Ltac eh_preserved_indicator_output x zero expr idx atom Hout Hfree Hvalue :=
  let Hkeep := fresh "Hkeep" in
  pose proof
    (expression_does_not_assign_indicator_transition_output
      x zero expr idx atom Hfree Hvalue) as Hkeep;
  rewrite Hout in Hkeep;
  exact Hkeep.

Local Lemma largest_loop_invariant_test_prefixed_assign_zero_guard_BA
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (b : CFGKATTest)
  (e : CFGKATExpression)
  :
  test_indicator_free x b ->
  e dna x ->
  TAnd (x is zero) (largest_loop_invariant_test (assign zero to x ;; e) b)
    =BA
  TAnd (x is zero) (largest_loop_invariant_test e b).
Proof.
  intros Hb_free He.
  apply Boolean_denotation_completeness.
  unfold CFGKATTestDenotationEquivalent.
  intros a i.
  split; intros [Hx HC].
  - split; [exact Hx |].
    apply largest_loop_invariant_test_complete.
    exists
      (TAnd
        (x is zero)
        (largest_loop_invariant_test (assign zero to x ;; e) b)).
    split.
    + apply BA_leq_left_weaken.
      apply largest_loop_invariant_test_leq_guard.
    + split.
      * unfold acc_cont_loop_invariant.
        intros a0 i0 [Hx0 HC0].
        pose proof
          (largest_loop_invariant_test_acc_cont_invariant
            (assign zero to x ;; e) b a0 i0 HC0)
          as [j [[Hacc | Hcont] HCj]].
        -- exists j.
           assert (Hacc_e :
             transition_output e a0 i0 = CFGKATAutomatonAccept j).
           { eh_assignment_output_from_prefixed Hacc. }
           split.
           ++ left.
              exact Hacc_e.
           ++ split.
              ** eh_preserved_indicator_output x zero e i0 a0 Hacc_e He Hx0.
              ** exact HCj.
        -- exists j.
           assert (Hcont_e :
             transition_output e a0 i0 = CFGKATAutomatonContinue j).
           { eh_assignment_output_from_prefixed Hcont. }
           split.
           ++ right.
              exact Hcont_e.
           ++ split.
              ** eh_preserved_indicator_output x zero e i0 a0 Hcont_e He Hx0.
              ** exact HCj.
      * split; assumption.
  - split; [exact Hx |].
    apply largest_loop_invariant_test_complete.
    exists
      (TAnd
        (x is zero)
        (largest_loop_invariant_test e b)).
    split.
    + apply BA_leq_left_weaken.
      apply largest_loop_invariant_test_leq_guard.
    + split.
      * unfold acc_cont_loop_invariant.
        intros a0 i0 [Hx0 HC0].
        pose proof
          (largest_loop_invariant_test_acc_cont_invariant e b a0 i0 HC0)
          as [j [[Hacc | Hcont] HCj]].
        -- exists j.
           split.
           ++ left.
              rewrite
                (assignment_prefix_transition_same x zero e i0 a0 Hx0).
              exact Hacc.
           ++ split.
              ** eh_preserved_indicator_output x zero e i0 a0 Hacc He Hx0.
              ** exact HCj.
        -- exists j.
           split.
           ++ right.
              rewrite
                (assignment_prefix_transition_same x zero e i0 a0 Hx0).
              exact Hcont.
           ++ split.
              ** eh_preserved_indicator_output x zero e i0 a0 Hcont He Hx0.
              ** exact HCj.
      * split; assumption.
Qed.

Local Lemma zero_guard_not_largest_loop_invariant_tests_BA
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (b : CFGKATTest)
  (e : CFGKATExpression)
  :
  test_indicator_free x b ->
  e dna x ->
  TAnd (x is zero) (not largest_loop_invariant_test e b) =BA
  TAnd
    (x is zero)
    (not largest_loop_invariant_test (assign zero to x ;; e) b).
Proof.
  intros Hb_free He.
  pose proof
    (largest_loop_invariant_test_prefixed_assign_zero_guard_BA
      x zero b e Hb_free He) as Hinv.
  pose proof (BooleanAlgebra_sound _ _ Hinv) as Hinv_sem.
  apply Boolean_denotation_completeness.
  unfold CFGKATTestDenotationEquivalent in *.
  intros a i.
  specialize (Hinv_sem a i).
  split; intros [Hx Hnot].
  - split; [exact Hx |].
    intro Hpref.
    apply Hnot.
    apply (proj1 Hinv_sem).
    split; assumption.
  - split; [exact Hx |].
    intro Hunpref.
    apply Hnot.
    apply (proj2 Hinv_sem).
    split; assumption.
Qed.

Local Lemma assign_zero_trimmed_loop_cong
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (b : CFGKATTest)
  (e : CFGKATExpression)
  :
  test_indicator_free x b ->
  e dna x ->
  let C := C+[assign zero to x ;; e, b] in
  assign zero to x ;;
    (while b do (test (not C+[e, b]) ;; e)) ==
  assign zero to x ;;
    (while b do (test (not C) ;; e)).
Proof.
  intros Hb_free He C.
  assert (Hbody_left_dna :
    (test (not largest_loop_invariant_test e b) ;; e) dna x).
  { simpl. split; [exact I | exact He]. }
  assert (Hbody_right_dna :
    (test (not C) ;; e) dna x).
  { simpl. split; [exact I | exact He]. }
  apply assign_prefixed_from_tested.
  cfgkat_rewrite (loop_zero_invariant_dna x zero b
    (test (not largest_loop_invariant_test e b) ;; e)
    Hbody_left_dna).
  cfgkat_rewrite (test_prefix_test_sequence_cong_from_and_BA
    (x is zero) (not C+[e, b]) (not C) e
    ltac:(unfold C;
      apply zero_guard_not_largest_loop_invariant_tests_BA;
      assumption)).
  cfgkat_rewrite <- (loop_zero_invariant_dna x zero b
    (test (not C) ;; e)
    Hbody_right_dna).
  apply EqRefl.
Qed.


Local Lemma eh_source_zero_entry_loop_largest_tightened
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  :
  test_indicator_free x b ->
  f dnr x ->
  g dnr x ->
  let C := C+[assign zero to x ;; (f ;; g), b] in
  assign zero to x ;; (while b do (f ;; g)) ==
    assign zero to x ;; (while b do (test (not C) ;; (f ;; g))).
Proof.
  intros Hb_free Hf Hg C.
  cfgkat_rewrite looptighten_largest.
  unfold C.
  apply assign_zero_trimmed_loop_cong.
  - exact Hb_free.
  - split; solve_assign_free_from_expr_dnr.
Qed.

Local Lemma eh_source_zero_entry_loop_largest_fixed
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  :
  test_indicator_free x b ->
  f dnr x ->
  g dnr x ->
  let C := C+[assign zero to x ;; (f ;; g), b] in
  (if b then
      (test (not C) ;; (assign zero to x ;; (f ;; g))) |>
        (assign zero to x ;; (while b do (f ;; g)))
   else assign zero to x) ==
    assign zero to x ;; (while b do (f ;; g)).
Proof.
  intros Hb_free Hf Hg C.
	  assert (Hh_dna : (f ;; g) dna x).
	  {
	    split; solve_assign_free_from_expr_dnr.
	  }
  assert (Htrim_dna : (test (not C) ;; (f ;; g)) dna x).
  {
    simpl. split; [exact I | exact Hh_dna].
  }
  set (tight_loop := while b do (test (not C) ;; (f ;; g))).
  unfold C.
  cfgkat_rewrite (trim_largest_prefixed_assign_comm x zero b (f ;; g)
    Hb_free).
  cfgkat_rewrite (ltac:(
    unfold C;
    apply (eh_source_zero_entry_loop_largest_tightened x zero b f g);
    [exact Hb_free | exact Hf | exact Hg])).
  fold C.
  fold tight_loop.
  cfgkat_rewrite <- (indpushloopseq x zero
    (test (not C) ;; (f ;; g)) tight_loop Htrim_dna).
  cfgkat_rewrite EqL8.
  cfgkat_rewrite <- (EqS4 (assign zero to x)) at 2.
  cfgkat_rewrite <- (inddistr x zero b
    ((test (not C) ;; (f ;; g)) |> tight_loop) 1 Hb_free).
  unfold tight_loop.
  cfgkat_rewrite <- EqL10.
  apply EqRefl.
Qed.


Local Lemma eh_target_loop_body_zero_branch
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (f g : CFGKATExpression)
  :
  one <> zero ->
  test x is zero ;;
    eh_target_loop_body_erased ell x one zero f g ==
  test x is zero ;; (f ;; (assign zero to x ;; g)).
Proof.
  intro Hone_zero.
  unfold eh_target_loop_body_erased.
  set (rest := f ;; (1 ;; (assign zero to x ;; g))).
  cfgkat_rewrite EqG5.
  cfgkat_rewrite (branchskip_disjoint
    (x is zero) (x is one) (goto ell ;; rest) (1 ;; rest)
    ltac:(apply indicator_distinct_and_false;
      intro Hzero_one; apply Hone_zero; symmetry; exact Hzero_one)).
  cfgkat_rewrite EqS3.
  unfold rest.
  cfgkat_rewrite EqS3.
  apply EqRefl.
Qed.

Local Lemma eh_target_loop_body_zero_guarded
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  :
  one <> zero ->
  f dnr x ->
  test ((x is zero) and b) ;;
    eh_target_loop_body_erased ell x one zero f g ==
  test ((x is zero) and b) ;; (f ;; g).
Proof.
  intros Hone_zero Hf.
  cfgkat_rewrite (EqBoolAssertCong
    ((x is zero) and b) (b and (x is zero))
    (BAAndComm (x is zero) b)).
  cfgkat_rewrite <- EqS5.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite (eh_target_loop_body_zero_branch ell x one zero f g Hone_zero).
  cfgkat_rewrite (test_prefixed_same_assignment_in_sequence
    x zero f g
    (expression_does_not_reference_indicator_assign_free x f Hf)).
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite EqS5.
  cfgkat_rewrite (EqBoolAssertCong
    (b and (x is zero)) ((x is zero) and b)
    (BAAndComm b (x is zero))).
  apply EqRefl.
Qed.

Local Lemma eh_assign_zero_target_tested_loop_body
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (q : CFGKATTest)
  (f g : CFGKATExpression)
  :
  one <> zero ->
  f dnr x ->
  assign zero to x ;;
    (test q ;;
      eh_target_loop_body_erased ell x one zero f g) ==
  assign zero to x ;; (test q ;; (f ;; g)).
Proof.
  intros Hone_zero Hf.
  apply assign_prefixed_from_tested.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite (test_seq_ba (x is zero) q ((x is zero) and q)
    (BARefl ((x is zero) and q))).
  cfgkat_rewrite (eh_target_loop_body_zero_guarded ell x one zero q f g
    Hone_zero Hf).
  cfgkat_rewrite <- (test_seq_ba (x is zero) q ((x is zero) and q)
    (BARefl ((x is zero) and q))).
  apply EqS1.
Qed.

Local Lemma eh_target_loop_body_zero
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (f g : CFGKATExpression)
  :
  one <> zero ->
  f dnr x ->
  test x is zero ;;
    eh_target_loop_body_erased ell x one zero f g ==
  test x is zero ;; (f ;; g).
Proof.
  intros Hone_zero Hf.
  cfgkat_rewrite (eh_target_loop_body_zero_branch ell x one zero f g Hone_zero).
  apply test_prefixed_same_assignment_in_sequence.
  apply expression_does_not_reference_indicator_assign_free.
  exact Hf.
Qed.

Local Lemma eh_eval_target_guard_zero_iff
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  one <> zero ->
  eval_test (x is zero) a i ->
  (eval_test (eh_target_loop_guard x one b) a i <->
   eval_test b a i).
Proof.
  intros Hone_zero Hx.
  unfold eh_target_loop_guard.
  simpl.
  split.
  - intros [Hb | Hx_one].
    + exact Hb.
    + exfalso.
      rewrite Hx in Hx_one.
      symmetry in Hx_one.
      exact (Hone_zero Hx_one).
  - intro Hb. left. exact Hb.
Qed.

Local Lemma eh_largest_loop_invariant_tests_zero_guard_BA
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  :
  one <> zero ->
  f dnr x ->
  g dnr x ->
  TAnd
    (x is zero)
    (largest_loop_invariant_test
      (eh_target_loop_body_erased ell x one zero f g)
      (eh_target_loop_guard x one b))
    =BA
  TAnd (x is zero) (largest_loop_invariant_test (f ;; g) b).
Proof.
  intros Hone_zero Hf Hg.
  set (h := f ;; g).
  set (target_body := eh_target_loop_body_erased ell x one zero f g).
  set (target_guard := eh_target_loop_guard x one b).
	  assert (Hh_dna : h dna x).
	  {
	    unfold h.
	    split; solve_assign_free_from_expr_dnr.
	  }
  assert (Hbody_eq :
    test x is zero ;; target_body == test x is zero ;; h).
  {
    unfold target_body, h.
    apply eh_target_loop_body_zero; assumption.
  }
  assert (Htarget_slice_leq_source_guard :
    BA_leq
      (TAnd
        (x is zero)
        (largest_loop_invariant_test target_body target_guard))
      b).
  {
    unfold BA_leq.
    apply Boolean_denotation_completeness.
    unfold CFGKATTestDenotationEquivalent.
    intros a i.
    split.
    - intros [Hb | [Hx HCt]].
      + exact Hb.
      + pose proof
          (BA_leq_eval
            (largest_loop_invariant_test target_body target_guard)
            target_guard a i
            (largest_loop_invariant_test_leq_guard
              target_body target_guard)
            HCt) as Htarget_guard.
        apply
          (proj1
            (eh_eval_target_guard_zero_iff
              x one zero b a i Hone_zero Hx)).
        exact Htarget_guard.
    - intro Hb.
      left. exact Hb.
  }
  assert (Htarget_slice_source_invariant :
    acc_cont_loop_invariant h
      (TAnd
        (x is zero)
        (largest_loop_invariant_test target_body target_guard))).
  {
    unfold acc_cont_loop_invariant.
    intros a i [Hx HCt].
    pose proof
      (largest_loop_invariant_test_acc_cont_invariant
        target_body target_guard a i HCt)
      as [j [[Htarget_accept | Htarget_continue] HCt_j]].
    - pose proof
        (proj1
          (test_prefixed_empty_equiv_accept_iff
            (x is zero) target_body h a i j Hbody_eq Hx)
          Htarget_accept) as Hsource_accept.
      exists j.
      split.
      + left. exact Hsource_accept.
      + split.
        * eh_preserved_indicator_output x zero h i a Hsource_accept Hh_dna Hx.
        * exact HCt_j.
    - pose proof
        (proj1
          (test_prefixed_empty_equiv_continue_iff
            (x is zero) target_body h a i j Hbody_eq Hx)
          Htarget_continue) as Hsource_continue.
      exists j.
      split.
      + right. exact Hsource_continue.
      + split.
        * eh_preserved_indicator_output x zero h i a Hsource_continue Hh_dna Hx.
        * exact HCt_j.
  }
  assert (Hsource_slice_leq_target_guard :
    BA_leq
      (TAnd (x is zero) (largest_loop_invariant_test h b))
      target_guard).
  {
    unfold BA_leq.
    apply Boolean_denotation_completeness.
    unfold CFGKATTestDenotationEquivalent.
    intros a i.
    split.
    - intros [Htarget_guard | [_ HCs]].
      + exact Htarget_guard.
      + left.
        eapply BA_leq_eval.
        * apply largest_loop_invariant_test_leq_guard.
        * exact HCs.
    - intro Htarget_guard.
      left. exact Htarget_guard.
  }
  assert (Hsource_slice_target_invariant :
    acc_cont_loop_invariant target_body
      (TAnd (x is zero) (largest_loop_invariant_test h b))).
  {
    unfold acc_cont_loop_invariant.
    intros a i [Hx HCs].
    pose proof
      (largest_loop_invariant_test_acc_cont_invariant h b a i HCs)
      as [j [[Hsource_accept | Hsource_continue] HCs_j]].
    - pose proof
        (proj2
          (test_prefixed_empty_equiv_accept_iff
            (x is zero) target_body h a i j Hbody_eq Hx)
          Hsource_accept) as Htarget_accept.
      exists j.
      split.
      + left. exact Htarget_accept.
      + split.
        * eh_preserved_indicator_output x zero h i a Hsource_accept Hh_dna Hx.
        * exact HCs_j.
    - pose proof
        (proj2
          (test_prefixed_empty_equiv_continue_iff
            (x is zero) target_body h a i j Hbody_eq Hx)
          Hsource_continue) as Htarget_continue.
      exists j.
      split.
      + right. exact Htarget_continue.
      + split.
        * eh_preserved_indicator_output x zero h i a Hsource_continue Hh_dna Hx.
        * exact HCs_j.
  }
  apply Boolean_denotation_completeness.
  unfold CFGKATTestDenotationEquivalent.
  intros a i.
  split; intros [Hx HC].
  - split; [exact Hx |].
    apply largest_loop_invariant_test_complete.
    exists
      (TAnd
        (x is zero)
        (largest_loop_invariant_test target_body target_guard)).
    split; [exact Htarget_slice_leq_source_guard |].
    split; [exact Htarget_slice_source_invariant |].
    split; assumption.
  - split; [exact Hx |].
    apply largest_loop_invariant_test_complete.
    exists (TAnd (x is zero) (largest_loop_invariant_test h b)).
    split; [exact Hsource_slice_leq_target_guard |].
    split; [exact Hsource_slice_target_invariant |].
    split; assumption.
Qed.

Local Lemma eh_loop_largest_invariants_zero_guard_BA
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  :
  one <> zero ->
  f dnr x ->
  g dnr x ->
  TAnd
    (x is zero)
    (not largest_loop_invariant_test
      (eh_target_loop_body_erased ell x one zero f g)
      (eh_target_loop_guard x one b))
    =BA
  TAnd (x is zero) (not largest_loop_invariant_test (f ;; g) b).
Proof.
  intros Hone_zero Hf Hg.
  pose proof
    (BooleanAlgebra_sound _ _
      (eh_largest_loop_invariant_tests_zero_guard_BA
        ell x one zero b f g Hone_zero Hf Hg))
    as Hreject.
  apply Boolean_denotation_completeness.
  unfold CFGKATTestDenotationEquivalent in *.
  intros a i.
  specialize (Hreject a i).
  split; intros [Hx Hnot].
  - split; [exact Hx |].
    intro Hsource.
    apply Hnot.
    apply (proj2 Hreject).
    split; assumption.
  - split; [exact Hx |].
    intro Htarget.
    apply Hnot.
    apply (proj1 Hreject).
    split; assumption.
Qed.

Local Lemma eh_assign_zero_largest_invariant_source_target_body
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  :
  one <> zero ->
  test_indicator_free x b ->
  f dnr x ->
  g dnr x ->
  let C := C+[assign zero to x ;; (f ;; g), b] in
  let target_body :=
    eh_target_loop_body_erased ell x one zero f g in
  let Ct := C+[target_body, eh_target_loop_guard x one b] in
  assign zero to x ;; (test (not C) ;; (f ;; g)) ==
    assign zero to x ;; (test (not Ct) ;; (f ;; g)).
Proof.
  intros Hone_zero Hb_free Hf Hg C target_body Ct.
	  assert (Hh_dna : (f ;; g) dna x).
	  {
	    split; solve_assign_free_from_expr_dnr.
	  }
  apply assign_prefixed_from_tested.
  apply test_prefix_test_sequence_cong_from_and_BA.
  unfold C, Ct, target_body.
  eapply BATrans.
  - apply BASym.
    apply zero_guard_not_largest_loop_invariant_tests_BA;
      assumption.
  - apply BASym.
    apply eh_loop_largest_invariants_zero_guard_BA;
      assumption.
Qed.


Local Lemma eh_target_zero_entry_tested_loop_unroll
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b q : CFGKATTest)
  (f g : CFGKATExpression)
  :
  one <> zero ->
  test_indicator_free x b ->
  f dnr x ->
  g dnr x ->
  let target_body :=
    eh_target_loop_body_erased ell x one zero f g in
  let target_loop :=
    while eh_target_loop_guard x one b do
      (test q ;; target_body) in
  (if b then
      (assign zero to x ;; (test q ;; (f ;; g))) |>
        (assign zero to x ;; target_loop)
   else assign zero to x) ==
    assign zero to x ;; target_loop.
Proof.
  intros Hone_zero Hfree Hf Hg target_body target_loop.
	  assert (Hh_dna : (f ;; g) dna x).
	  {
	    split; solve_assign_free_from_expr_dnr.
	  }
  assert (Htested_h_dna : (test q ;; (f ;; g)) dna x).
  {
    simpl. split; [exact I | exact Hh_dna].
  }
  cfgkat_rewrite <- (indpushloopseq x zero
    (test q ;; (f ;; g)) target_loop Htested_h_dna).
  cfgkat_rewrite <- (eh_assign_zero_target_tested_loop_body
    ell x one zero q f g Hone_zero Hf).
  cfgkat_rewrite EqL8.
  cfgkat_rewrite <- (EqS4 (assign zero to x)) at 2.
  cfgkat_rewrite <- (inddistr x zero b
    ((test q ;; eh_target_loop_body_erased ell x one zero f g) |> target_loop)
    1 Hfree).
  cfgkat_rewrite <- (assign_prefixed_from_tested x zero
    (if eh_target_loop_guard x one b then
       ((test q ;; eh_target_loop_body_erased ell x one zero f g) |> target_loop)
     else 1)
    (if b then
       ((test q ;; eh_target_loop_body_erased ell x one zero f g) |> target_loop)
     else 1)
    ltac:(apply partialselection;
      unfold eh_target_loop_guard;
      rewrite BAAndDistrib;
      rewrite (indicator_distinct_and_false x zero one);
      [apply BAOrIdentity |
        intro Hzero_one; apply Hone_zero; symmetry; exact Hzero_one])).
  unfold target_loop.
  apply EqSeqRightCong.
  - apply EqSym. apply EqL10.
  - apply EqRefl.
Qed.

Local Lemma eh_target_zero_entry_loop_largest_fixed
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  :
  one <> zero ->
  test_indicator_free x b ->
  f dnr x ->
  g dnr x ->
  let C := C+[assign zero to x ;; (f ;; g), b] in
  let target_body :=
    eh_target_loop_body_erased ell x one zero f g in
  let target_loop :=
    while eh_target_loop_guard x one b do target_body in
  (if b then
      (test (not C) ;; (assign zero to x ;; (f ;; g))) |>
        (assign zero to x ;; target_loop)
   else assign zero to x) ==
    assign zero to x ;; target_loop.
Proof.
  intros Hone_zero Hb_free Hf Hg C target_body target_loop.
  set (Ct := C+[target_body, eh_target_loop_guard x one b]).
  set (target_tight_loop :=
    while eh_target_loop_guard x one b do
      (test (not Ct) ;; target_body)).
  unfold C.
  cfgkat_rewrite (trim_largest_prefixed_assign_comm
    x zero b (f ;; g) Hb_free).
  cfgkat_rewrite (ltac:(
    unfold Ct, target_body;
    apply (eh_assign_zero_largest_invariant_source_target_body
      ell x one zero b f g);
    [exact Hone_zero | exact Hb_free | exact Hf | exact Hg])).
  cfgkat_rewrite (@EqSeqRightCong
    empty_label_context empty_label_context
    target_loop target_tight_loop (assign zero to x)
    ltac:(unfold target_loop, target_tight_loop, Ct, target_body;
      apply looptighten_largest)
    ltac:(apply EqRefl)).
  unfold target_tight_loop, Ct.
  unfold target_body.
  apply (eh_target_zero_entry_tested_loop_unroll
    ell x one zero b
    (not C+[eh_target_loop_body_erased ell x one zero f g,
      eh_target_loop_guard x one b])
    f g Hone_zero Hb_free Hf Hg).
Qed.

Local Lemma eh_target_loop_body_erased_to_expanded_body
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (f g : CFGKATExpression)
  :
  eh_target_loop_body_erased ell x one zero f g ==
    (if x is one then goto ell else 1) ;;
      (f ;; (assign zero to x ;; g)).
Proof.
  unfold eh_target_loop_body_erased.
  cfgkat_rewrite EqS3.
  apply EqRefl.
Qed.

Theorem ehzeroentryloopequiv
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  :
  one <> zero ->
  test_indicator_free x b ->
  f dnr x ->
  g dnr x ->
  assign zero to x ;; (while b do (f ;; g)) ==
    assign zero to x ;;
      (while b or x is one do
        ((if x is one then goto ell else 1) ;;
          (f ;; (assign zero to x ;; g)))).
Proof.
  intros Hone_zero Hb_free Hf Hg.
  cfgkat_rewrite (loop_unique_closed_after_largest_invariant_exit_pair
      b
      (assign zero to x ;; (f ;; g))
      (assign zero to x)
      (assign zero to x ;; (while b do (f ;; g)))
      (assign zero to x ;;
        (while eh_target_loop_guard x one b do
          eh_target_loop_body_erased ell x one zero f g))
      ltac:(apply eh_source_zero_entry_loop_largest_fixed;
        assumption)
      ltac:(apply eh_target_zero_entry_loop_largest_fixed;
        assumption)).
  cfgkat_rewrite eh_target_loop_body_erased_to_expanded_body.
  unfold eh_target_loop_guard.
  apply EqRefl.
Qed.


Local Definition erosa_hendren_loop_case_side_conditions
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  : Prop :=
  let source := eh_source_program ell c b e f g in
  let target := eh_transformed_program ell x one zero c b e f g in
  one <> zero /\
  test_indicator_free x c /\
  test_indicator_free x b /\
  e pdnr x /\
  f pdnr x /\
  g pdnr x /\
  program_no_free_goto source /\
  program_no_free_goto target /\
  well_labeled_program source /\
  well_labeled_program target /\
  program_well_nested source /\
  program_well_nested target.

Local Lemma eh_assign_one_enters_target_loop_as_goto
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  :
  assign one to x ;;
    (while eh_target_loop_guard x one b do
      eh_target_loop_body_erased ell x one zero f g) ==
  assign one to x ;; goto ell.
Proof.
  set (guard := eh_target_loop_guard x one b).
  set (body := eh_target_loop_body_erased ell x one zero f g).
  set (loop := while guard do body).
  unfold loop.
  cfgkat_rewrite EqL10.
  unfold guard, eh_target_loop_guard.
  cfgkat_rewrite (assign_selects_implied_branch x one (b or x is one)
    (body |> (while b or x is one do body)) 1
    (indicator_implies_or_right x one b)).
  cfgkat_rewrite <- EqA2.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite loopassoctest.
  unfold body, eh_target_loop_body_erased.
  set (rest := f ;; (1 ;; (assign zero to x ;; g))).
  cfgkat_rewrite EqG5.
  cfgkat_rewrite branchsel.
  cfgkat_rewrite EqS9.
  cfgkat_rewrite <- loopassoctest.
  cfgkat_rewrite EqL4.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite EqA2.
  apply EqRefl.
Qed.

Local Lemma eh_assign_one_target_entry_to_goto
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (e f g : CFGKATExpression)
  :
  one <> zero ->
  assign one to x ;;
    ((if x is zero then e else 1) ;;
      ((while eh_target_loop_guard x one b do
          eh_target_loop_body_erased ell x one zero f g) ;; return)) ==
  assign one to x ;; goto ell.
Proof.
  intro Hone_zero.
  set (loop :=
    while eh_target_loop_guard x one b do
      eh_target_loop_body_erased ell x one zero f g).
  set (rest := loop ;; return).
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite (assign_skips_disjoint_branch x one (x is zero) e 1
    ltac:(apply indicator_distinct_and_false; exact Hone_zero)).
  cfgkat_rewrite EqS4.
  unfold rest.
  cfgkat_rewrite <- EqS1.
  unfold loop.
  cfgkat_rewrite (eh_assign_one_enters_target_loop_as_goto
    ell x one zero b f g).
  cfgkat_rewrite EqS1.
  cfgkat_rewrite EqS9.
  apply EqRefl.
Qed.

Local Lemma eh_target_program_erase_split_form
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  one <> zero ->
  label_erase (eh_transformed_program ell x one zero c b e f g) ==
    eh_target_split_form ell x one zero c b
      (label_erase e) (label_erase f) (label_erase g).
Proof.
  intro Hone_zero.
  unfold eh_transformed_program, eh_target_split_form,
    eh_target_loop_guard, eh_target_loop_body_erased.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite EqG5.
  cfgkat_rewrite (eh_assign_one_target_entry_to_goto
    ell x one zero b (label_erase e) (label_erase f) (label_erase g)
    Hone_zero).
  apply EqRefl.
Qed.

Local Definition eh_source_loop_erased
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  : CFGKATExpression :=
  while b do (f ;; (1 ;; g)).

Local Definition eh_target_loop_erased
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  : CFGKATExpression :=
  while eh_target_loop_guard x one b do
    eh_target_loop_body_erased ell x one zero f g.

Local Lemma eh_source_label_extraction_ell
  (ell : Label)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  well_labeled_program (eh_source_program ell c b e f g) ->
  label_extraction_syntax (eh_source_program ell c b e f g) ell =
    Some
      (((1 ;; label_erase g)
        |> eh_source_loop_erased b (label_erase f) (label_erase g))
       ;; return).
Proof.
  intro Hwell.
  pose proof
    (eh_source_well_labeled_ell_not_in_generics ell c b e f g Hwell)
    as Hnot.
  assert (Hnot_e : ~ program_label_occurs ell e).
  {
    intro Hin.
    apply Hnot.
    apply in_or_app. left. exact Hin.
  }
  assert (Hnot_f : ~ program_label_occurs ell f).
  {
    intro Hin.
    apply Hnot.
    apply in_or_app. right.
    apply in_or_app. left. exact Hin.
  }
  unfold eh_source_program, eh_source_loop_erased.
  rewrite label_extraction_sequence_left.
  2:{
    unfold program_label_occurs. simpl.
    apply in_or_app. right.
    apply in_or_app. right.
    left. reflexivity.
  }
  rewrite label_extraction_sequence_right.
  2:{ unfold program_label_occurs. simpl. tauto. }
  rewrite label_extraction_sequence_right.
  2:{ exact Hnot_e. }
  rewrite label_extraction_loop_present.
  rewrite label_extraction_sequence_right.
  2:{ exact Hnot_f. }
  rewrite label_extraction_sequence_left.
  2:{ unfold program_label_occurs. simpl. left. reflexivity. }
  simpl.
  destruct (Label_eq_dec ell ell) as [_ | Hneq].
  - reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

Local Lemma eh_target_label_extraction_ell
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  well_labeled_program
    (eh_transformed_program ell x one zero c b e f g) ->
  label_extraction_syntax (eh_transformed_program ell x one zero c b e f g) ell =
    Some
      (((1 ;; (assign zero to x ;; label_erase g))
        |> eh_target_loop_erased ell x one zero b
             (label_erase f) (label_erase g))
       ;; return).
Proof.
  intro Hwell.
  pose proof
    (eh_target_well_labeled_ell_not_in_generics
      ell x one zero c b e f g Hwell) as Hnot.
  assert (Hnot_e : ~ program_label_occurs ell e).
  {
    intro Hin.
    apply Hnot.
    apply in_or_app. left. exact Hin.
  }
  assert (Hnot_f : ~ program_label_occurs ell f).
  {
    intro Hin.
    apply Hnot.
    apply in_or_app. right.
    apply in_or_app. left. exact Hin.
  }
  unfold eh_transformed_program, eh_transformed_loop_body,
    eh_target_loop_erased, eh_target_loop_body_erased,
    eh_target_loop_guard.
  rewrite label_extraction_sequence_left.
  2:{
    unfold program_label_occurs. simpl.
    apply in_or_app. right.
    apply in_or_app. right.
    left. reflexivity.
  }
  rewrite label_extraction_sequence_right.
  2:{ unfold program_label_occurs. simpl. tauto. }
  rewrite label_extraction_sequence_right.
  2:{
    unfold program_label_occurs. simpl.
    intro Hin.
    apply in_app_iff in Hin as [Hin_e | Hin_nil].
    - exact (Hnot_e Hin_e).
    - tauto.
  }
  rewrite label_extraction_loop_present.
  rewrite label_extraction_sequence_right.
  2:{ unfold program_label_occurs. simpl. tauto. }
  rewrite label_extraction_sequence_right.
  2:{ exact Hnot_f. }
  rewrite label_extraction_sequence_left.
  2:{ unfold program_label_occurs. simpl. left. reflexivity. }
  simpl.
  destruct (Label_eq_dec ell ell) as [_ | Hneq].
  - reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

Local Definition eh_zero_source_loop_form
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATExpression)
  : CFGKATExpression :=
  if c then
    (((assign zero to x ;; g) |> (while b do (f ;; g))) ;; return)
  else
    assign zero to x ;;
      (e ;; ((while b do (f ;; g)) ;; return)).


Local Lemma eh_not_c_branch_zero_loop_return
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (e f g : CFGKATExpression)
  :
  one <> zero ->
  test_indicator_free x b ->
  e dnr x ->
  f dnr x ->
  g dnr x ->
  assign zero to x ;;
    (e ;;
      ((while b or x is one do
        ((if x is one then goto ell else 1) ;;
          (f ;; (assign zero to x ;; g)))) ;; return)) ==
  assign zero to x ;;
    (e ;; ((while b do (f ;; g)) ;; return)).
Proof.
  intros Hone_zero Hb_free He Hf Hg.
  apply assign_prefixed_dnr_sequence_cong_from_assign.
  - exact He.
  - apply assign_prefix_sequence_right_cong_from_assign.
    apply EqSym.
    apply (ehzeroentryloopequiv ell x one zero b f g);
      assumption.
Qed.

Local Lemma eh_c_branch_target_context_to_source_loop
  (E : label_environment CFGKATExpression)
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  :
  E ell =
    Some
      (((1 ;; (assign zero to x ;; g)) |>
          (while eh_target_loop_guard x one b do
            eh_target_loop_body_erased ell x one zero f g)) ;; return) ->
  one <> zero ->
  test_indicator_free x b ->
  f dnr x ->
  g dnr x ->
  E |-
    assign one to x ;; goto ell ==
    ((assign zero to x ;; g) |> (while b do (f ;; g))) ;; return -| E.
Proof.
  intros Hlabel Hone_zero Hb_free Hf Hg.
  set (target_loop_with_erased_label :=
    while b or x is one do
      ((if x is one then goto ell else 1) ;;
        (f ;; (1 ;; (assign zero to x ;; g))))).
  set (target_loop :=
    while b or x is one do
      ((if x is one then goto ell else 1) ;;
        (f ;; (assign zero to x ;; g)))).
  set (source_loop := while b do (f ;; g)).
  cfgkat_rewrite (EqSeqRightCong E E
    (goto ell)
    (((1 ;; (assign zero to x ;; g)) |>
      target_loop_with_erased_label) ;; return)
    (assign one to x)
    ltac:(apply unfold_bound_goto; exact Hlabel)
    ltac:(apply EqRefl)).
  apply weaken_empty_to_env.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite EqS3.
  unfold target_loop_with_erased_label.
  cfgkat_rewrite (EqLoopBodyEmptyCong
    ((if x is one then goto ell else 1) ;;
      (f ;; (1 ;; (assign zero to x ;; g))))
    ((if x is one then goto ell else 1) ;;
      (f ;; (assign zero to x ;; g)))
    (b or x is one)
    ltac:(cfgkat_rewrite EqS3; apply EqRefl)).
  fold target_loop.
  cfgkat_rewrite EqL8.
  cfgkat_rewrite assign_prefix_overwrite.
  cfgkat_rewrite (assign_prefixed_dnr_loopseq_cong_from_assign
    x zero g target_loop source_loop Hg
    ltac:(unfold target_loop, source_loop;
      apply EqSym;
      apply (ehzeroentryloopequiv ell x one zero b f g);
      assumption)).
  cfgkat_rewrite <- EqL8.
  apply EqRefl.
Qed.

Local Lemma eh_not_c_branch_target_context_to_source_loop
  (E : label_environment CFGKATExpression)
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (e f g : CFGKATExpression)
  :
  one <> zero ->
  test_indicator_free x b ->
  e dnr x ->
  f dnr x ->
  g dnr x ->
  E |-
    assign zero to x ;;
      ((if x is zero then e else 1) ;;
        ((while eh_target_loop_guard x one b do
          eh_target_loop_body_erased ell x one zero f g) ;; return)) ==
    assign zero to x ;;
      (e ;; ((while b do (f ;; g)) ;; return)) -| E.
Proof.
  intros Hone_zero Hb_free He Hf Hg.
  apply weaken_empty_to_env.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite assign_selects_indicator_branch.
  cfgkat_rewrite EqS1.
  cfgkat_rewrite (assign_prefixed_dnr_sequence_cong_from_assign
    x zero e
    ((while eh_target_loop_guard x one b do
      eh_target_loop_body_erased ell x one zero f g) ;; return)
    ((while eh_target_loop_guard x one b do
      (if x is one then goto ell else 1) ;;
        (f ;; (assign zero to x ;; g))) ;; return)
    He
    ltac:(apply assign_prefix_sequence_right_cong_from_assign;
      cfgkat_rewrite eh_target_loop_body_erased_to_expanded_body;
      apply EqRefl)).
  unfold eh_target_loop_guard.
  apply (eh_not_c_branch_zero_loop_return
    ell x one zero b e f g);
    assumption.
Qed.

Local Lemma eh_target_split_form_to_zero_source_loop_ctx
  (E : label_environment CFGKATExpression)
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATExpression)
  :
  E ell =
    Some
      (((1 ;; (assign zero to x ;; g)) |>
        (while eh_target_loop_guard x one b do
          eh_target_loop_body_erased ell x one zero f g)) ;; return) ->
  one <> zero ->
  test_indicator_free x b ->
  e dnr x ->
  f dnr x ->
  g dnr x ->
  E |- eh_target_split_form ell x one zero c b e f g ==
    eh_zero_source_loop_form x zero c b e f g -| E.
Proof.
  intros Hlabel Hone_zero Hb_free He Hf Hg.
  unfold eh_target_split_form, eh_zero_source_loop_form.
  apply EqChoiceCong.
  - apply (eh_c_branch_target_context_to_source_loop
      E ell x one zero b f g);
      assumption.
  - apply (eh_not_c_branch_target_context_to_source_loop
      E ell x one zero b e f g);
      assumption.
Qed.

Local Lemma eh_transformed_program_erased_to_zero_source_loop_ctx
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  let target := eh_transformed_program ell x one zero c b e f g in
  well_labeled_program target ->
  one <> zero ->
  test_indicator_free x b ->
  label_erase e dnr x ->
  label_erase f dnr x ->
  label_erase g dnr x ->
  label_extraction_syntax_environment target |-
    label_erase target ==
    eh_zero_source_loop_form x zero c b
      (label_erase e) (label_erase f) (label_erase g) -|
    label_extraction_syntax_environment target.
Proof.
  intros target Hwell Hone_zero Hb_free He Hf Hg.
  set (K := label_extraction_syntax_environment target).
  pose proof
    (eh_target_label_extraction_ell
      ell x one zero c b e f g Hwell) as Hlabel.
  unfold label_extraction_syntax_environment, mk_environment in Hlabel.
  unfold eh_target_loop_erased, eh_target_loop_guard,
    eh_target_loop_body_erased in Hlabel.
  change (label_erase target) with
    (label_erase (eh_transformed_program ell x one zero c b e f g)).
  change (K |-
    label_erase (eh_transformed_program ell x one zero c b e f g) ==
    eh_zero_source_loop_form x zero c b
      (label_erase e) (label_erase f) (label_erase g) -| K).
  cfgkat_rewrite (weaken_empty_to_env K _ _
    (eh_target_program_erase_split_form
      ell x one zero c b e f g Hone_zero)).
  apply (eh_target_split_form_to_zero_source_loop_ctx
    K ell x one zero c b
    (label_erase e) (label_erase f) (label_erase g));
    assumption.
Qed.

Local Definition eh_meet_in_middle_tail
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATExpression)
  : CFGKATExpression :=
  (if c then
     g |> (while b do (f ;; g))
   else
     e ;; (while b do (f ;; g))) ;;
  return.

Local Lemma eh_meet_in_middle_tail_dna
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATExpression)
  :
  e dna x ->
  f dna x ->
  g dna x ->
  eh_meet_in_middle_tail x zero c b e f g dna x.
Proof.
  intros He Hf Hg.
  unfold eh_meet_in_middle_tail.
  simpl.
  repeat split; try exact I; try assumption.
Qed.

Local Lemma eh_meet_in_middle_factor
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATExpression)
  :
  test_indicator_free x c ->
  assign zero to x ;;
    eh_meet_in_middle_tail x zero c b e f g ==
  eh_zero_source_loop_form x zero c b e f g.
Proof.
  intro Hc.
  unfold eh_meet_in_middle_tail, eh_zero_source_loop_form,
    eh_zero_source_loop_form.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite (inddistr x zero c
    (g |> while b do (f ;; g))
    (e ;; while b do (f ;; g)) Hc).
  cfgkat_rewrite EqG5.
  apply EqChoiceCong.
  - apply EqSeqLeftEmptyCong.
    apply EqSym. apply EqL8.
  - eapply EqTrans.
    + apply EqS1.
    + apply (@EqSeqRightCong
        empty_label_context empty_label_context
        ((e ;; (while b do (f ;; g))) ;; return)
        (e ;; ((while b do (f ;; g)) ;; return))
        (assign zero to x)).
      * apply EqS1.
      * apply EqRefl.
Qed.

Local Lemma eh_source_program_erase_normal_form_ctx
  (E : label_environment CFGKATExpression)
  (ell : Label)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  E |- label_erase (eh_source_program ell c b e f g) ==
    eh_source_normal_form ell c b
      (label_erase e) (label_erase f) (label_erase g) -| E.
Proof.
  apply weaken_empty_to_env.
  unfold eh_source_program, eh_source_normal_form.
  simpl.
  set (body_with_label := label_erase f ;; (1 ;; label_erase g)).
  set (body_without_label := label_erase f ;; label_erase g).
  set (tail_with_label :=
    label_erase e ;; ((while b do body_with_label) ;; return)).
  set (tail_without_label :=
    label_erase e ;; ((while b do body_without_label) ;; return)).
  cfgkat_rewrite EqS1 at 1.
  cfgkat_rewrite EqS1 at 1.
  fold body_with_label.
  fold tail_with_label.
  fold tail_without_label.
  unfold tail_with_label, tail_without_label,
    body_with_label, body_without_label.
  cfgkat_rewrite EqS3.
  cfgkat_rewrite EqG5.
  cfgkat_rewrite EqS9.
  cfgkat_rewrite EqS3.
  apply EqRefl.
Qed.

Local Lemma eh_source_normal_form_to_meet_tail_ctx
  (ell : Label)
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  let source := eh_source_program ell c b e f g in
  well_labeled_program source ->
  label_extraction_syntax_environment source |-
    eh_source_normal_form ell c b
      (label_erase e) (label_erase f) (label_erase g) ==
    eh_meet_in_middle_tail x zero c b
      (label_erase e) (label_erase f) (label_erase g) -|
    label_extraction_syntax_environment source.
Proof.
  intros source Hsource_well.
  pose proof
    (eh_source_label_extraction_ell ell c b e f g Hsource_well)
    as Hlabel.
  unfold label_extraction_syntax_environment, mk_environment in Hlabel.
  unfold eh_source_normal_form, eh_meet_in_middle_tail.
  eapply EqTrans.
  - apply EqChoiceCong.
    + eapply EqTrans.
      * apply unfold_bound_goto. exact Hlabel.
      * apply weaken_empty_to_env.
        unfold eh_source_loop_erased.
        apply EqSeqLeftEmptyCong.
        eapply EqTrans.
        -- apply EqLoopSeqLeftEmptyCong.
           apply EqS3.
        -- apply EqLoopSeqRightCong.
           ++ apply EqLoopBodyEmptyCong.
              cfgkat_rewrite EqS3.
              apply EqRefl.
           ++ apply EqRefl.
    + apply EqSym.
      apply weaken_empty_to_env.
      apply EqS1.
  - apply EqSym.
    apply weaken_empty_to_env.
    apply EqG5.
Qed.

Local Lemma eh_source_program_does_not_reference_indicator
  (ell : Label)
  (x : IndicatorVariable)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  test_indicator_free x c ->
  test_indicator_free x b ->
  e pdnr x ->
  f pdnr x ->
  g pdnr x ->
  eh_source_program ell c b e f g pdnr x.
Proof.
  intros Hc Hb He Hf Hg.
  unfold eh_source_program.
  repeat split; try exact I; try assumption.
Qed.

Local Lemma eh_source_environment_binds_goto_from_component
  (ell l : Label)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  program_no_free_goto (eh_source_program ell c b e f g) ->
  contains_goto l (label_erase e) \/
  contains_goto l (label_erase f) \/
  contains_goto l (label_erase g) ->
  exists body,
    label_extraction_syntax_environment
      (eh_source_program ell c b e f g) l = Some body.
Proof.
  intros Hfree Hcontains.
  apply label_extraction_occurs_some.
  apply Hfree.
  unfold eh_source_program.
  simpl.
  destruct Hcontains as [He | [Hf | Hg]].
  - pose proof (program_contains_goto_erase e l He) as He'.
    tauto.
  - pose proof (program_contains_goto_erase f l Hf) as Hf'.
    tauto.
  - pose proof (program_contains_goto_erase g l Hg) as Hg'.
    tauto.
Qed.

Local Lemma eh_source_well_nested_e
  (ell : Label)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  program_well_nested (eh_source_program ell c b e f g) ->
  program_well_nested e.
Proof.
  intro Hwn.
  unfold eh_source_program in Hwn.
  pose proof (program_well_nested_sequence_left _ _ Hwn) as Hprefix.
  pose proof (program_well_nested_sequence_right _ _ Hprefix) as Htail.
  exact (program_well_nested_sequence_left _ _ Htail).
Qed.

Local Lemma eh_meet_in_middle_tail_indremoval_ctx
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  let source := eh_source_program ell c b e f g in
  erosa_hendren_loop_case_side_conditions ell x one zero c b e f g ->
  label_extraction_syntax_environment source |-
    eh_meet_in_middle_tail x zero c b
      (label_erase e) (label_erase f) (label_erase g) ==
    assign zero to x ;;
      eh_meet_in_middle_tail x zero c b
        (label_erase e) (label_erase f) (label_erase g) -|
    label_extraction_syntax_environment source.
Proof.
  intros source Hside.
  unfold erosa_hendren_loop_case_side_conditions in Hside.
  destruct Hside as
    (_Hone_zero & Hc & Hb & He & Hf & Hg &
     Hsource_free & _Htarget_free & _Hsource_well & _Htarget_well &
     Hsource_wn & _Htarget_wn).
  pose proof
    (eh_source_program_does_not_reference_indicator
      ell x c b e f g Hc Hb He Hf Hg) as Hsource_dnr.
  destruct (program_does_not_reference_indicator_no_test_reduced
    x source Hsource_dnr)
    as [_ Henv_no].
  destruct (program_well_nested_reduced source Hsource_wn)
    as [_ Henv_wn].
  destruct (program_ends_with_return_reduced source
    (eh_source_program_ends_with_return ell c b e f g))
    as [_ Henv_ret].
  destruct (program_no_free_goto_reduced source Hsource_free)
    as [_ Henv_free].
  set (tail :=
    eh_meet_in_middle_tail x zero c b
      (label_erase e) (label_erase f) (label_erase g)).
  assert (Htail_dna : tail dna x).
  {
    unfold tail.
    apply eh_meet_in_middle_tail_dna;
      apply expression_does_not_reference_indicator_assign_free;
      apply program_does_not_reference_indicator_erase; assumption.
  }
  set (inner :=
    if c then
      (label_erase g) |> (while b do (label_erase f ;; label_erase g))
    else
      label_erase e ;; (while b do (label_erase f ;; label_erase g))).
  assert (Hinner_dna : inner dna x).
  {
    unfold inner.
    repeat split; try exact I;
      apply expression_does_not_reference_indicator_assign_free;
      apply program_does_not_reference_indicator_erase; assumption.
  }
  set (top := (assign zero to x ;; inner) ;; return).
  assert (Htop_no_test :
    expression_does_not_test_indicator x top).
  {
    unfold top, inner.
    repeat split; try exact Hc; try exact Hb; try exact I;
      solve_no_test_from_dnr.
  }
  assert (Htop_wn : well_nested top).
  {
    unfold top, inner.
    apply WN_seq.
    - apply WN_seq.
      + apply WN_base. exact I.
      + apply WN_choice.
        * apply WN_loopseq. apply WN_loop.
        * apply WN_seq.
          -- apply program_well_nested_erase.
             eapply eh_source_well_nested_e. exact Hsource_wn.
          -- apply WN_loop.
    - apply WN_base. exact I.
  }
  assert (Htop_ret : ends_with_return top).
  {
    unfold top.
    eexists. reflexivity.
  }
  assert (Htop_free :
    no_free_goto_expr
      (label_extraction_syntax_environment source)
      top).
  {
    unfold no_free_goto_expr, top, inner.
    intros l Hcontains.
    simpl in Hcontains.
    eapply eh_source_environment_binds_goto_from_component.
    - exact Hsource_free.
    - intuition.
  }
  assert (Hghost_side :
    ghost_variable_elimination_side_conditions
      x (label_extraction_syntax_environment source)
      top).
  {
    unfold ghost_variable_elimination_side_conditions.
    split; [exact Htop_no_test|].
    split; [exact Henv_no|].
    split; [exact Htop_wn|].
    split; [exact Henv_wn|].
    split; [exact Htop_ret|].
    split; [exact Henv_ret|].
    split; [exact Htop_free|].
    exact Henv_free.
  }
  eapply (EqTrans _ _ _ _ (ghost_erase x top) _).
  - apply weaken_empty_to_env.
    unfold tail, top, eh_meet_in_middle_tail.
    fold inner.
    cbn [ghost_erase].
    destruct (Var_eq_dec x x) as [_ | Hneq].
    + change (inner ;; return == (1 ;; ghost_erase x inner) ;; return).
      rewrite ghost_erase_identity_dna by exact Hinner_dna.
      apply EqSeqLeftEmptyCong.
      apply EqSym. apply EqS3.
    + contradiction Hneq. reflexivity.
  - eapply EqTrans.
    + apply EqSym.
      pose proof
        (ghost_variable_elimination
          x (label_extraction_syntax_environment source)
          top Hghost_side) as Hghost.
      rewrite (program_ghost_erase_env_identity_dnr x source Hsource_dnr)
        in Hghost.
      exact Hghost.
    + apply weaken_empty_to_env.
      unfold tail, top, inner, eh_meet_in_middle_tail.
      apply EqS1.
Qed.


Theorem ehmeetinthemiddle
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  let source := eh_source_program ell c b e f g in
  let target := eh_transformed_program ell x one zero c b e f g in
  erosa_hendren_loop_case_side_conditions ell x one zero c b e f g ->
  label_extraction_syntax_environment source |-
    label_erase source ==
    eh_zero_source_loop_form x zero c b
      (label_erase e) (label_erase f) (label_erase g) -|
    label_extraction_syntax_environment source /\
  label_extraction_syntax_environment target |-
    label_erase target ==
    eh_zero_source_loop_form x zero c b
      (label_erase e) (label_erase f) (label_erase g) -|
    label_extraction_syntax_environment target.
Proof.
  intros source target Hside.
  pose proof Hside as Hside_full.
  unfold erosa_hendren_loop_case_side_conditions in Hside.
  destruct Hside as
    (Hone_zero & Hc & Hb & He & Hf & Hg &
     _Hsource_free & _Htarget_free & Hsource_well & Htarget_well &
     _Hsource_wn & _Htarget_wn).
  split.
  - eapply (EqTrans _ _ _ _
      (eh_source_normal_form ell c b
        (label_erase e) (label_erase f) (label_erase g)) _).
    + apply eh_source_program_erase_normal_form_ctx.
    + eapply (EqTrans _ _ _ _
        (eh_meet_in_middle_tail x zero c b
          (label_erase e) (label_erase f) (label_erase g)) _).
      * apply eh_source_normal_form_to_meet_tail_ctx.
        exact Hsource_well.
      * eapply (EqTrans _ _ _ _
          (assign zero to x ;;
            eh_meet_in_middle_tail x zero c b
              (label_erase e) (label_erase f) (label_erase g)) _).
        -- apply (eh_meet_in_middle_tail_indremoval_ctx
             ell x one zero c b e f g Hside_full).
        -- apply weaken_empty_to_env.
           apply eh_meet_in_middle_factor.
           exact Hc.
  - eapply eh_transformed_program_erased_to_zero_source_loop_ctx.
    + exact Htarget_well.
    + exact Hone_zero.
    + exact Hb.
    + apply program_does_not_reference_indicator_erase. exact He.
    + apply program_does_not_reference_indicator_erase. exact Hf.
    + apply program_does_not_reference_indicator_erase. exact Hg.
Qed.

Local Definition zero_prefixed_environment
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (E : label_environment CFGKATExpression)
  : label_environment CFGKATExpression :=
  assignment_prefixed_environment x zero E.

Local Lemma eh_meet_in_middle_prefix_environment
  (E : label_environment CFGKATExpression)
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATExpression)
  :
  test_indicator_free x c ->
  e dna x ->
  f dna x ->
  g dna x ->
  label_environment_assigns_indicator_only_value x zero E ->
  E |- eh_zero_source_loop_form x zero c b e f g ==
    eh_zero_source_loop_form x zero c b e f g -|
    zero_prefixed_environment x zero E.
Proof.
  intros Hc He Hf Hg Henv.
  unfold zero_prefixed_environment, assignment_prefixed_environment.
  cfgkat_rewrite <- (weaken_empty_to_env E _ _
    (eh_meet_in_middle_factor x zero c b e f g Hc)).
  cfgkat_rewrite (assignment_prefix_environment E x zero
    (eh_meet_in_middle_tail x zero c b e f g)
    (eh_meet_in_middle_tail_dna x zero c b e f g He Hf Hg)
    Henv).
  now cfgkat_rewrite (weaken_empty_to_env
    (assignment_prefixed_environment x zero E) _ _
    (eh_meet_in_middle_factor x zero c b e f g Hc)).
Qed.

Local Lemma eh_source_label_extraction_from_e
  (ell l : Label)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  (body : CFGKATExpression)
  :
  label_extraction_syntax e l = Some body ->
  label_extraction_syntax (eh_source_program ell c b e f g) l =
    Some
      ((body ;;
        eh_source_loop_erased b (label_erase f) (label_erase g)) ;;
        return).
Proof.
  intro Hbody.
  pose proof (label_extraction_some_occurs e l body Hbody) as Hin_e.
  unfold eh_source_program, eh_source_loop_erased.
  rewrite label_extraction_sequence_left.
  2:{
    unfold program_label_occurs. simpl.
    apply in_or_app. left. exact Hin_e.
  }
  rewrite label_extraction_sequence_right.
  2:{ unfold program_label_occurs. simpl. tauto. }
  rewrite label_extraction_sequence_left.
  2:{ exact Hin_e. }
  rewrite Hbody.
  reflexivity.
Qed.

Local Lemma eh_target_label_extraction_from_e
  (ell l : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  (body : CFGKATExpression)
  :
  label_extraction_syntax e l = Some body ->
  label_extraction_syntax (eh_transformed_program ell x one zero c b e f g) l =
    Some
      ((body ;;
        eh_target_loop_erased ell x one zero b
          (label_erase f) (label_erase g)) ;;
        return).
Proof.
  intro Hbody.
  pose proof (label_extraction_some_occurs e l body Hbody) as Hin_e.
  unfold eh_transformed_program, eh_transformed_loop_body,
    eh_target_loop_erased, eh_target_loop_body_erased,
    eh_target_loop_guard.
  rewrite label_extraction_sequence_left.
  2:{
    unfold program_label_occurs. simpl.
    apply in_or_app. left.
    apply in_or_app. left. exact Hin_e.
  }
  rewrite label_extraction_sequence_right.
  2:{ unfold program_label_occurs. simpl. tauto. }
  rewrite label_extraction_sequence_left.
  2:{
    unfold program_label_occurs. simpl.
    apply in_or_app. left. exact Hin_e.
  }
  rewrite label_extraction_choice_left.
  2:{ exact Hin_e. }
  rewrite Hbody.
  reflexivity.
Qed.

Local Lemma eh_source_label_extraction_from_f
  (ell l : Label)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  (body : CFGKATExpression)
  :
  well_labeled_program (eh_source_program ell c b e f g) ->
  label_extraction_syntax f l = Some body ->
  label_extraction_syntax (eh_source_program ell c b e f g) l =
    Some
      (((body ;; (1 ;; label_erase g))
        |> eh_source_loop_erased b (label_erase f) (label_erase g))
       ;; return).
Proof.
  intros Hwell Hbody.
  pose proof (label_extraction_some_occurs f l body Hbody) as Hin_f.
  assert (Hnodup : NoDup (eh_program_labels ell e f g)).
  {
    unfold well_labeled_program in Hwell.
    rewrite eh_source_program_labels in Hwell.
    exact Hwell.
  }
  assert (Hnot_e : ~ program_label_occurs l e).
  {
    eapply eh_well_labeled_from_f_not_in_e; eauto.
  }
  unfold eh_source_program, eh_source_loop_erased.
  rewrite label_extraction_sequence_left.
  2:{
    unfold program_label_occurs. simpl.
    apply in_or_app. right.
    apply in_or_app. left. exact Hin_f.
  }
  rewrite label_extraction_sequence_right.
  2:{ unfold program_label_occurs. simpl. tauto. }
  rewrite label_extraction_sequence_right.
  2:{ exact Hnot_e. }
  rewrite label_extraction_loop_present.
  rewrite label_extraction_sequence_left.
  2:{ exact Hin_f. }
  rewrite Hbody.
  reflexivity.
Qed.

Local Lemma eh_target_label_extraction_from_f
  (ell l : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  (body : CFGKATExpression)
  :
  well_labeled_program
    (eh_transformed_program ell x one zero c b e f g) ->
  label_extraction_syntax f l = Some body ->
  label_extraction_syntax (eh_transformed_program ell x one zero c b e f g) l =
    Some
      (((body ;; (1 ;; (assign zero to x ;; label_erase g)))
        |> eh_target_loop_erased ell x one zero b
             (label_erase f) (label_erase g))
       ;; return).
Proof.
  intros Hwell Hbody.
  pose proof (label_extraction_some_occurs f l body Hbody) as Hin_f.
  assert (Hnodup : NoDup (eh_program_labels ell e f g)).
  {
    unfold well_labeled_program in Hwell.
    rewrite eh_transformed_program_labels in Hwell.
    exact Hwell.
  }
  assert (Hnot_e : ~ program_label_occurs l e).
  {
    eapply eh_well_labeled_from_f_not_in_e; eauto.
  }
  unfold eh_transformed_program, eh_transformed_loop_body,
    eh_target_loop_erased, eh_target_loop_body_erased,
    eh_target_loop_guard.
  rewrite label_extraction_sequence_left.
  2:{
    unfold program_label_occurs. simpl.
    apply in_or_app. right.
    apply in_or_app. left. exact Hin_f.
  }
  rewrite label_extraction_sequence_right.
  2:{ unfold program_label_occurs. simpl. tauto. }
  rewrite label_extraction_sequence_right.
  2:{
    unfold program_label_occurs. simpl.
    intro Hin.
    apply in_app_iff in Hin as [Hin_e | Hin_nil].
    - exact (Hnot_e Hin_e).
    - tauto.
  }
  rewrite label_extraction_loop_present.
  rewrite label_extraction_sequence_right.
  2:{ unfold program_label_occurs. simpl. tauto. }
  rewrite label_extraction_sequence_left.
  2:{ exact Hin_f. }
  rewrite Hbody.
  reflexivity.
Qed.

Local Lemma eh_source_label_extraction_from_g
  (ell l : Label)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  (body : CFGKATExpression)
  :
  well_labeled_program (eh_source_program ell c b e f g) ->
  label_extraction_syntax g l = Some body ->
  label_extraction_syntax (eh_source_program ell c b e f g) l =
    Some
      ((body
        |> eh_source_loop_erased b (label_erase f) (label_erase g))
       ;; return).
Proof.
  intros Hwell Hbody.
  pose proof (label_extraction_some_occurs g l body Hbody) as Hin_g.
  assert (Hnodup : NoDup (eh_program_labels ell e f g)).
  {
    unfold well_labeled_program in Hwell.
    rewrite eh_source_program_labels in Hwell.
    exact Hwell.
  }
  assert (Hnot_e : ~ program_label_occurs l e).
  {
    eapply eh_well_labeled_from_g_not_in_e; eauto.
  }
  assert (Hnot_f : ~ program_label_occurs l f).
  {
    eapply eh_well_labeled_from_g_not_in_f; eauto.
  }
  assert (Hneq : ell <> l).
  {
    intro Heq.
    apply (eh_well_labeled_from_g_neq_ell ell l e f g Hnodup Hin_g).
    symmetry. exact Heq.
  }
  unfold eh_source_program, eh_source_loop_erased.
  rewrite label_extraction_sequence_left.
  2:{
    unfold program_label_occurs. simpl.
    apply in_or_app. right.
    apply in_or_app. right. right. exact Hin_g.
  }
  rewrite label_extraction_sequence_right.
  2:{ unfold program_label_occurs. simpl. tauto. }
  rewrite label_extraction_sequence_right.
  2:{ exact Hnot_e. }
  rewrite label_extraction_loop_present.
  rewrite label_extraction_sequence_right.
  2:{ exact Hnot_f. }
  rewrite label_extraction_sequence_right.
  2:{
    unfold program_label_occurs. simpl.
    intros [Heq | []].
    exact (Hneq Heq).
  }
  rewrite Hbody.
  reflexivity.
Qed.

Local Lemma eh_target_label_extraction_from_g
  (ell l : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  (body : CFGKATExpression)
  :
  well_labeled_program
    (eh_transformed_program ell x one zero c b e f g) ->
  label_extraction_syntax g l = Some body ->
  label_extraction_syntax (eh_transformed_program ell x one zero c b e f g) l =
    Some
      ((body
        |> eh_target_loop_erased ell x one zero b
             (label_erase f) (label_erase g))
       ;; return).
Proof.
  intros Hwell Hbody.
  pose proof (label_extraction_some_occurs g l body Hbody) as Hin_g.
  assert (Hnodup : NoDup (eh_program_labels ell e f g)).
  {
    unfold well_labeled_program in Hwell.
    rewrite eh_transformed_program_labels in Hwell.
    exact Hwell.
  }
  assert (Hnot_e : ~ program_label_occurs l e).
  {
    eapply eh_well_labeled_from_g_not_in_e; eauto.
  }
  assert (Hnot_f : ~ program_label_occurs l f).
  {
    eapply eh_well_labeled_from_g_not_in_f; eauto.
  }
  assert (Hneq : ell <> l).
  {
    intro Heq.
    apply (eh_well_labeled_from_g_neq_ell ell l e f g Hnodup Hin_g).
    symmetry. exact Heq.
  }
  unfold eh_transformed_program, eh_transformed_loop_body,
    eh_target_loop_erased, eh_target_loop_body_erased,
    eh_target_loop_guard.
  rewrite label_extraction_sequence_left.
  2:{
    unfold program_label_occurs. simpl.
    apply in_or_app. right.
    apply in_or_app. right. right. exact Hin_g.
  }
  rewrite label_extraction_sequence_right.
  2:{ unfold program_label_occurs. simpl. tauto. }
  rewrite label_extraction_sequence_right.
  2:{
    unfold program_label_occurs. simpl.
    intro Hin.
    apply in_app_iff in Hin as [Hin_e | Hin_nil].
    - exact (Hnot_e Hin_e).
    - tauto.
  }
  rewrite label_extraction_loop_present.
  rewrite label_extraction_sequence_right.
  2:{ unfold program_label_occurs. simpl. tauto. }
  rewrite label_extraction_sequence_right.
  2:{ exact Hnot_f. }
  rewrite label_extraction_sequence_right.
  2:{
    unfold program_label_occurs. simpl.
    intros [Heq | []].
    exact (Hneq Heq).
  }
  rewrite label_extraction_sequence_right.
  2:{ unfold program_label_occurs. simpl. tauto. }
  rewrite Hbody.
  reflexivity.
Qed.

Local Lemma eh_zero_prefixed_e_label_target_to_source_body
  (K : label_environment CFGKATExpression)
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (e' f g : CFGKATExpression)
  :
  one <> zero ->
  test_indicator_free x b ->
  e' dnr x ->
  f dnr x ->
  g dnr x ->
  K |-
    assign zero to x ;;
      ((e' ;;
        eh_target_loop_erased ell x one zero b f g) ;; return) ==
    assign zero to x ;;
      ((e' ;; eh_source_loop_erased b f g) ;; return) -|
    K.
Proof.
  intros Hone_zero Hb He Hf Hg.
  apply weaken_empty_to_env.
  apply assign_prefix_sequence_right_cong_from_assign.
  apply assign_prefixed_dnr_sequence_cong_from_assign.
  - exact He.
  - unfold eh_target_loop_erased, eh_source_loop_erased.
    cfgkat_rewrite eh_target_loop_body_erased_to_expanded_body.
    unfold eh_target_loop_guard.
    cfgkat_rewrite <-
      (ehzeroentryloopequiv ell x one zero b f g Hone_zero Hb Hf Hg).
    cfgkat_rewrite EqS3.
    apply EqRefl.
Qed.

Local Lemma eh_assign_prefixed_remove_erased_label_assign_in_tail
  (x : IndicatorVariable)
  (v : IndicatorValue)
  (e g : CFGKATExpression)
  :
  e dna x ->
  assign v to x ;; (e ;; (1 ;; (assign v to x ;; g))) ==
    assign v to x ;; (e ;; g).
Proof.
  intro He.
  cfgkat_rewrite (assign_prefixed_dna_sequence_cong_from_assign
    x v e (1 ;; (assign v to x ;; g)) (assign v to x ;; g) He
    ltac:(eapply EqSeqRightCong; [apply EqS3 | apply EqRefl])).
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite <- EqS1.
  cfgkat_rewrite (EqSeqLeftEmptyCong
    ((assign v to x ;; e) ;; assign v to x)
    (assign v to x ;; e) g
    ltac:(cfgkat_rewrite EqS1;
      cfgkat_rewrite <- (assignment_duplication x v e He);
      apply EqRefl)).
  apply EqS1.
Qed.

Local Lemma eh_zero_prefixed_f_label_target_to_source_body
  (K : label_environment CFGKATExpression)
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (f' f g : CFGKATExpression)
  :
  one <> zero ->
  test_indicator_free x b ->
  f' dnr x ->
  f dnr x ->
  g dnr x ->
  K |-
    assign zero to x ;;
      (((f' ;; (1 ;; (assign zero to x ;; g)))
        |> eh_target_loop_erased ell x one zero b f g) ;; return) ==
    assign zero to x ;;
      (((f' ;; (1 ;; g))
        |> eh_source_loop_erased b f g) ;; return) -|
    K.
Proof.
  intros Hone_zero Hb Hf' Hf Hg.
  apply weaken_empty_to_env.
  apply assign_prefix_sequence_right_cong_from_assign.
  cfgkat_rewrite <- EqL8.
  cfgkat_rewrite (eh_assign_prefixed_remove_erased_label_assign_in_tail
    x zero f' g
    ltac:(solve_assign_free_from_expr_dnr)).
  cfgkat_rewrite EqL8.
  cfgkat_rewrite (assign_prefixed_dnr_loopseq_cong_from_assign
    x zero (f' ;; g)
    (eh_target_loop_erased ell x one zero b f g)
    (eh_source_loop_erased b f g) (conj Hf' Hg)
    ltac:(unfold eh_target_loop_erased, eh_source_loop_erased;
      cfgkat_rewrite eh_target_loop_body_erased_to_expanded_body;
      unfold eh_target_loop_guard;
      cfgkat_rewrite <-
        (ehzeroentryloopequiv ell x one zero b f g Hone_zero Hb Hf Hg);
      cfgkat_rewrite EqS3;
      apply EqRefl)).
  apply EqSym.
  cfgkat_rewrite <- EqL8.
  cfgkat_rewrite (assign_prefixed_dna_sequence_cong_from_assign
    x zero f' (1 ;; g) g
    ltac:(solve_assign_free_from_expr_dnr)
    ltac:(eapply EqSeqRightCong; [apply EqS3 | apply EqRefl])).
  cfgkat_rewrite EqL8.
  unfold eh_source_loop_erased.
  cfgkat_rewrite EqS3.
  apply EqRefl.
Qed.

Local Lemma eh_zero_prefixed_g_label_target_to_source_body
  (K : label_environment CFGKATExpression)
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (g' f g : CFGKATExpression)
  :
  one <> zero ->
  test_indicator_free x b ->
  g' dnr x ->
  f dnr x ->
  g dnr x ->
  K |-
    assign zero to x ;;
      ((g' |> eh_target_loop_erased ell x one zero b f g) ;; return) ==
    assign zero to x ;;
      ((g' |> eh_source_loop_erased b f g) ;; return) -|
    K.
Proof.
  intros Hone_zero Hb Hg' Hf Hg.
  apply weaken_empty_to_env.
  apply assign_prefix_sequence_right_cong_from_assign.
  apply assign_prefixed_dnr_loopseq_cong_from_assign.
  - exact Hg'.
  - unfold eh_target_loop_erased, eh_source_loop_erased.
    cfgkat_rewrite eh_target_loop_body_erased_to_expanded_body.
    unfold eh_target_loop_guard.
    cfgkat_rewrite <-
      (ehzeroentryloopequiv ell x one zero b f g Hone_zero Hb Hf Hg).
    cfgkat_rewrite EqS3.
    apply EqRefl.
Qed.

Local Lemma eh_zero_prefixed_ell_label_target_to_source_body
  (K : label_environment CFGKATExpression)
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  :
  one <> zero ->
  test_indicator_free x b ->
  f dnr x ->
  g dnr x ->
  K |-
    assign zero to x ;;
      (((1 ;; (assign zero to x ;; g))
        |> eh_target_loop_erased ell x one zero b f g) ;; return) ==
    assign zero to x ;;
      (((1 ;; g) |> eh_source_loop_erased b f g) ;; return) -|
    K.
Proof.
  intros Hone_zero Hb Hf Hg.
  apply weaken_empty_to_env.
  apply assign_prefix_sequence_right_cong_from_assign.
  cfgkat_rewrite <- EqL8.
  cfgkat_rewrite EqS3.
  cfgkat_rewrite assign_prefix_overwrite.
  cfgkat_rewrite EqL8.
  cfgkat_rewrite (assign_prefixed_dnr_loopseq_cong_from_assign
    x zero g
    (eh_target_loop_erased ell x one zero b f g)
    (eh_source_loop_erased b f g) Hg
    ltac:(unfold eh_target_loop_erased, eh_source_loop_erased;
      cfgkat_rewrite eh_target_loop_body_erased_to_expanded_body;
      unfold eh_target_loop_guard;
      cfgkat_rewrite <-
        (ehzeroentryloopequiv ell x one zero b f g Hone_zero Hb Hf Hg);
      cfgkat_rewrite EqS3;
      apply EqRefl)).
  apply EqSym.
  cfgkat_rewrite <- EqL8.
  cfgkat_rewrite EqS3.
  cfgkat_rewrite EqL8.
  unfold eh_source_loop_erased.
  cfgkat_rewrite EqS3.
  apply EqRefl.
Qed.

Local Ltac collapse_label_extraction Hlookup Hshape :=
  unfold label_extraction_syntax_environment, mk_environment in Hlookup;
  match type of Hshape with
  | ?lhs = Some _ =>
      match type of Hlookup with
      | _ = Some ?body => change (lhs = Some body) in Hlookup
      end
  end;
  rewrite Hshape in Hlookup;
  inversion Hlookup; subst; clear Hlookup.

Local Ltac collapse_eh_label_pair source target Hsource Htarget Hsource_shape Htarget_shape :=
  unfold source in Hsource;
  collapse_label_extraction Hsource Hsource_shape;
  unfold target in Htarget;
  collapse_label_extraction Htarget Htarget_shape.

Local Lemma erosa_hendren_zero_prefixed_label_targets_agree
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  let source := eh_source_program ell c b e f g in
  let target := eh_transformed_program ell x one zero c b e f g in
  erosa_hendren_loop_case_side_conditions ell x one zero c b e f g ->
  forall K k target_body source_body,
    label_extraction_syntax_environment target k = Some target_body ->
    label_extraction_syntax_environment source k = Some source_body ->
    K |-
      assign zero to x ;; target_body ==
      assign zero to x ;; source_body -|
      K.
Proof.
  intros source target Hside K k target_body source_body Htarget Hsource.
  unfold erosa_hendren_loop_case_side_conditions in Hside.
  destruct Hside as
    (Hone_zero & _Hc & Hb & He & Hf & Hg &
     _Hsource_free & _Htarget_free & Hsource_well & Htarget_well &
     _Hsource_wn & _Htarget_wn).
  pose proof
    (label_extraction_some_occurs source k source_body Hsource)
    as Hocc.
  unfold source, program_label_occurs in Hocc.
  rewrite eh_source_program_labels in Hocc.
  unfold eh_program_labels in Hocc.
  apply in_app_iff in Hocc as [Hin_e | Htail].
  - destruct (label_extraction_occurs_some e k Hin_e) as [e' He'].
    collapse_eh_label_pair source target Hsource Htarget
      (eh_source_label_extraction_from_e ell k c b e f g e' He')
      (eh_target_label_extraction_from_e
        ell k x one zero c b e f g e' He').
    apply (eh_zero_prefixed_e_label_target_to_source_body
      K ell x one zero b e' (label_erase f) (label_erase g)).
    + exact Hone_zero.
    + exact Hb.
    + eapply program_does_not_reference_indicator_extraction;
        [exact He | exact He'].
    + apply program_does_not_reference_indicator_erase. exact Hf.
    + apply program_does_not_reference_indicator_erase. exact Hg.
  - apply in_app_iff in Htail as [Hin_f | Hell_g].
    + destruct (label_extraction_occurs_some f k Hin_f) as [f' Hf'].
      collapse_eh_label_pair source target Hsource Htarget
        (eh_source_label_extraction_from_f
          ell k c b e f g f' Hsource_well Hf')
        (eh_target_label_extraction_from_f
          ell k x one zero c b e f g f' Htarget_well Hf').
      apply (eh_zero_prefixed_f_label_target_to_source_body
        K ell x one zero b f' (label_erase f) (label_erase g)).
      * exact Hone_zero.
      * exact Hb.
      * eapply program_does_not_reference_indicator_extraction;
          [exact Hf | exact Hf'].
      * apply program_does_not_reference_indicator_erase. exact Hf.
      * apply program_does_not_reference_indicator_erase. exact Hg.
    + destruct Hell_g as [Hk_ell | Hin_g].
      * subst k.
        collapse_eh_label_pair source target Hsource Htarget
          (eh_source_label_extraction_ell ell c b e f g Hsource_well)
          (eh_target_label_extraction_ell
            ell x one zero c b e f g Htarget_well).
        apply (eh_zero_prefixed_ell_label_target_to_source_body
          K ell x one zero b (label_erase f) (label_erase g)).
        -- exact Hone_zero.
        -- exact Hb.
        -- apply program_does_not_reference_indicator_erase. exact Hf.
        -- apply program_does_not_reference_indicator_erase. exact Hg.
      * destruct (label_extraction_occurs_some g k Hin_g) as [g' Hg'].
        collapse_eh_label_pair source target Hsource Htarget
          (eh_source_label_extraction_from_g
            ell k c b e f g g' Hsource_well Hg')
          (eh_target_label_extraction_from_g
            ell k x one zero c b e f g g' Htarget_well Hg').
        apply (eh_zero_prefixed_g_label_target_to_source_body
          K ell x one zero b g' (label_erase f) (label_erase g)).
        -- exact Hone_zero.
        -- exact Hb.
        -- eapply program_does_not_reference_indicator_extraction;
            [exact Hg | exact Hg'].
        -- apply program_does_not_reference_indicator_erase. exact Hf.
        -- apply program_does_not_reference_indicator_erase. exact Hg.
Qed.

Local Lemma label_extraction_environment_domain_iff
  (p : CFGKATProgramSyntax)
  (l : Label)
  :
  label_in_dom (label_extraction_syntax_environment p) l <->
  program_label_occurs l p.
Proof.
  unfold label_in_dom, label_extraction_syntax_environment.
  apply label_extraction_some_iff_occurs.
Qed.

Local Lemma label_extraction_environment_none_of_not_occurs
  (program : CFGKATProgramSyntax)
  (k : Label)
  :
  ~ program_label_occurs k program ->
  label_extraction_syntax_environment program k = None.
Proof.
  intro Hnot_occurs.
  destruct (label_extraction_syntax_environment program k) as [body |]
    eqn:Hbody.
  - exfalso.
    apply Hnot_occurs.
    apply label_extraction_environment_domain_iff.
    exists body. exact Hbody.
  - reflexivity.
Qed.

Local Lemma erosa_hendren_zero_prefixed_environment_switch
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  let source := eh_source_program ell c b e f g in
  let target := eh_transformed_program ell x one zero c b e f g in
  erosa_hendren_loop_case_side_conditions ell x one zero c b e f g ->
  forall h,
    zero_prefixed_environment x zero (label_extraction_syntax_environment target) |-
      h == h -|
    zero_prefixed_environment x zero (label_extraction_syntax_environment source).
Proof.
  intros source target Hside h.
  pose proof Hside as Hside_full.
  unfold erosa_hendren_loop_case_side_conditions in Hside.
  destruct Hside as
    (_Hone_zero & _Hc & _Hb & _He & _Hf & _Hg &
     _Hsource_free & _Htarget_free & _Hsource_well & _Htarget_well &
     _Hsource_wn & _Htarget_wn).
  set (labels := eh_program_labels ell e f g).
  set (Etarget :=
    zero_prefixed_environment x zero (label_extraction_syntax_environment target)).
  set (Esource :=
    zero_prefixed_environment x zero (label_extraction_syntax_environment source)).
  apply iterated_environment_replacement.
  intro k.
  unfold Etarget, Esource, zero_prefixed_environment,
    assignment_prefixed_environment, mk_environment.
  change (label_binding_equiv
    (match label_extraction_syntax_environment target k with
     | Some body => Some (assign zero to x ;; body)
     | None => None
     end)
    (match label_extraction_syntax_environment source k with
     | Some body => Some (assign zero to x ;; body)
     | None => None
     end)).
  destruct (in_dec Label_eq_dec k labels) as [Hin | Hnotin].
  - assert (Htarget_dom :
      label_in_dom (label_extraction_syntax_environment target) k).
    {
      apply label_extraction_environment_domain_iff.
      unfold program_label_occurs.
      unfold target.
      rewrite eh_transformed_program_labels.
      unfold labels in Hin.
      exact Hin.
    }
    assert (Hsource_dom :
      label_in_dom (label_extraction_syntax_environment source) k).
    {
      apply label_extraction_environment_domain_iff.
      unfold program_label_occurs.
      unfold source.
      rewrite eh_source_program_labels.
      unfold labels in Hin.
      exact Hin.
    }
    destruct Htarget_dom as [target_body Htarget_body].
    destruct Hsource_dom as [source_body Hsource_body].
    rewrite Htarget_body, Hsource_body.
    exact (erosa_hendren_zero_prefixed_label_targets_agree
      ell x one zero c b e f g Hside_full
      empty_label_context k target_body source_body
      Htarget_body Hsource_body).
  - rewrite (label_extraction_environment_none_of_not_occurs target k
      ltac:(intro Hocc; apply Hnotin;
        unfold labels, target, program_label_occurs in Hocc;
        rewrite eh_transformed_program_labels in Hocc; exact Hocc)).
    rewrite (label_extraction_environment_none_of_not_occurs source k
      ltac:(intro Hocc; apply Hnotin;
        unfold labels, source, program_label_occurs in Hocc;
        rewrite eh_source_program_labels in Hocc; exact Hocc)).
    exact I.
Qed.

Local Lemma eh_target_loop_erased_assigns_only_zero
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (b : CFGKATTest)
  (f g : CFGKATExpression)
  :
  f dnr x ->
  g dnr x ->
  expression_assigns_indicator_only_value x zero
    (eh_target_loop_erased ell x one zero b f g).
Proof.
  intros Hf Hg.
  unfold eh_target_loop_erased, eh_target_loop_body_erased,
    eh_target_loop_guard.
  repeat split; try exact I.
  - apply expression_does_not_reference_indicator_assigns_indicator_only_value.
    exact Hf.
  - right. reflexivity.
  - apply expression_does_not_reference_indicator_assigns_indicator_only_value.
    exact Hg.
Qed.

Local Ltac solve_assigns_only_zero_base :=
  first
    [ exact I
    | right; reflexivity
    | apply eh_target_loop_erased_assigns_only_zero;
      apply program_does_not_reference_indicator_erase; assumption
    | match goal with
      | |- expression_assigns_indicator_only_value _ _ (label_erase _) =>
          apply expression_does_not_reference_indicator_assigns_indicator_only_value;
          apply program_does_not_reference_indicator_erase; assumption
      end
    ].

Local Ltac solve_assigns_only_zero_from_dnr Hno Hlookup :=
  simpl;
  repeat split;
    first
      [ solve_assigns_only_zero_base
      | apply expression_does_not_reference_indicator_assigns_indicator_only_value;
        eapply program_does_not_reference_indicator_extraction;
          [ exact Hno | exact Hlookup ] ].

Local Ltac solve_assigns_only_zero_from_erased :=
  simpl; repeat split; solve_assigns_only_zero_base.

Local Lemma erosa_hendren_target_environment_assigns_only_zero
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  let target := eh_transformed_program ell x one zero c b e f g in
  erosa_hendren_loop_case_side_conditions ell x one zero c b e f g ->
  label_environment_assigns_indicator_only_value x zero
    (label_extraction_syntax_environment target).
Proof.
  intros target Hside.
  unfold label_environment_assigns_indicator_only_value.
  intros k body Hbody.
  unfold erosa_hendren_loop_case_side_conditions in Hside.
  destruct Hside as
    (_Hone_zero & _Hc & _Hb & He & Hf & Hg &
     _Hsource_free & _Htarget_free & _Hsource_well & Htarget_well &
     _Hsource_wn & _Htarget_wn).
  pose proof
    (label_extraction_some_occurs target k body Hbody)
    as Hocc.
  unfold target, program_label_occurs in Hocc.
  rewrite eh_transformed_program_labels in Hocc.
  unfold eh_program_labels in Hocc.
  apply in_app_iff in Hocc as [Hin_e | Htail].
  - destruct (label_extraction_occurs_some e k Hin_e) as [e' He'].
    pose proof
      (eh_target_label_extraction_from_e
        ell k x one zero c b e f g e' He') as Hshape.
    unfold target in Hbody.
    collapse_label_extraction Hbody Hshape.
    solve_assigns_only_zero_from_dnr He He'.
  - apply in_app_iff in Htail as [Hin_f | Hell_g].
    + destruct (label_extraction_occurs_some f k Hin_f) as [f' Hf'].
      pose proof
        (eh_target_label_extraction_from_f
          ell k x one zero c b e f g f' Htarget_well Hf')
      as Hshape.
      unfold target in Hbody.
      collapse_label_extraction Hbody Hshape.
      solve_assigns_only_zero_from_dnr Hf Hf'.
    + destruct Hell_g as [Hk_ell | Hin_g].
      * subst k.
        pose proof
          (eh_target_label_extraction_ell
            ell x one zero c b e f g Htarget_well) as Hshape.
        unfold target in Hbody.
        collapse_label_extraction Hbody Hshape.
        solve_assigns_only_zero_from_erased.
      * destruct (label_extraction_occurs_some g k Hin_g) as [g' Hg'].
        pose proof
          (eh_target_label_extraction_from_g
            ell k x one zero c b e f g g' Htarget_well Hg')
        as Hshape.
        unfold target in Hbody.
        collapse_label_extraction Hbody Hshape.
        solve_assigns_only_zero_from_dnr Hg Hg'.
Qed.

Local Lemma erosa_hendren_source_environment_assigns_only_zero
  (ell : Label)
  (x : IndicatorVariable)
  (zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  let source := eh_source_program ell c b e f g in
  test_indicator_free x c ->
  test_indicator_free x b ->
  e pdnr x ->
  f pdnr x ->
  g pdnr x ->
  label_environment_assigns_indicator_only_value x zero
    (label_extraction_syntax_environment source).
Proof.
  intros source Hc Hb He Hf Hg.
  unfold label_environment_assigns_indicator_only_value.
  intros k body Hbody.
  apply expression_does_not_reference_indicator_assigns_indicator_only_value.
  unfold source in Hbody.
  eapply program_does_not_reference_indicator_extraction.
  - apply (eh_source_program_does_not_reference_indicator
      ell x c b e f g); assumption.
  - exact Hbody.
Qed.

Theorem erosa_hendren_loop_case
  (ell : Label)
  (x : IndicatorVariable)
  (one zero : IndicatorValue)
  (c b : CFGKATTest)
  (e f g : CFGKATProgramSyntax)
  :
  one <> zero ->
  test_indicator_free x c ->
  test_indicator_free x b ->
  program_does_not_reference_indicator x e ->
  program_does_not_reference_indicator x f ->
  program_does_not_reference_indicator x g ->
  program_no_free_goto (eh_source_program ell c b e f g) ->
  program_no_free_goto (eh_transformed_program ell x one zero c b e f g) ->
  well_labeled_program (eh_source_program ell c b e f g) ->
  well_labeled_program (eh_transformed_program ell x one zero c b e f g) ->
  program_well_nested (eh_source_program ell c b e f g) ->
  program_well_nested (eh_transformed_program ell x one zero c b e f g) ->
  label_extraction_syntax_environment (eh_source_program ell c b e f g) |-
    label_erase (eh_source_program ell c b e f g) ==
    label_erase (eh_transformed_program ell x one zero c b e f g) -|
	    label_extraction_syntax_environment
	      (eh_transformed_program ell x one zero c b e f g).
	Proof.
	  intros Hone_zero Hc Hb He Hf Hg
	    Hsource_free Htarget_free Hsource_well Htarget_well
	    Hsource_wn Htarget_wn.
	  set (source := eh_source_program ell c b e f g).
	  set (target := eh_transformed_program ell x one zero c b e f g).
	  set (middle :=
	    eh_zero_source_loop_form x zero c b
	      (label_erase e) (label_erase f) (label_erase g)).
	  assert (Hside :
	    erosa_hendren_loop_case_side_conditions
	      ell x one zero c b e f g).
	  {
	    unfold erosa_hendren_loop_case_side_conditions.
	    repeat split; assumption.
	  }
	  pose proof
	    (ehmeetinthemiddle ell x one zero c b e f g Hside)
	    as [Hsource_meet Htarget_meet].
	  eapply (EqTrans _ _ _ _ middle _).
	  - exact Hsource_meet.
	  - eapply (EqTrans _ _ _ _ middle _).
	    + unfold middle.
	      apply (eh_meet_in_middle_prefix_environment
	        (label_extraction_syntax_environment source)
	        x zero c b
	        (label_erase e) (label_erase f) (label_erase g)).
	      * exact Hc.
	      * apply expression_does_not_reference_indicator_assign_free.
	        apply program_does_not_reference_indicator_erase. exact He.
	      * apply expression_does_not_reference_indicator_assign_free.
	        apply program_does_not_reference_indicator_erase. exact Hf.
	      * apply expression_does_not_reference_indicator_assign_free.
	        apply program_does_not_reference_indicator_erase. exact Hg.
	      * apply (erosa_hendren_source_environment_assigns_only_zero
	          ell x zero c b e f g Hc Hb He Hf Hg).
	    + eapply (EqTrans _ _ _ _ middle _).
	      * apply EqSym.
	        unfold middle.
	        apply (erosa_hendren_zero_prefixed_environment_switch
	          ell x one zero c b e f g Hside).
	      * eapply (EqTrans _ _ _ _ middle _).
	        -- apply EqSym.
	           unfold middle.
	           apply (eh_meet_in_middle_prefix_environment
	             (label_extraction_syntax_environment target)
	             x zero c b
	             (label_erase e) (label_erase f) (label_erase g)).
	           ++ exact Hc.
	           ++ apply expression_does_not_reference_indicator_assign_free.
	              apply program_does_not_reference_indicator_erase. exact He.
	           ++ apply expression_does_not_reference_indicator_assign_free.
	              apply program_does_not_reference_indicator_erase. exact Hf.
	           ++ apply expression_does_not_reference_indicator_assign_free.
	              apply program_does_not_reference_indicator_erase. exact Hg.
	           ++ apply (erosa_hendren_target_environment_assigns_only_zero
	                ell x one zero c b e f g Hside).
	        -- unfold middle.
	           apply EqSym.
	           exact Htarget_meet.
	Qed.
