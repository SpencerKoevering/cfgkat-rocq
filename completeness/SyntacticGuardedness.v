From Stdlib Require Import Bool.Bool Lists.List.

From CFGKAT.Completeness Require Import GuardedSumContext.

Local Open Scope cfgkat_scope.

Definition is_jump_to
  (target : Label)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : bool :=
  match r with
  | CFGKATAutomatonJump l _ =>
      match Label_eq_dec l target with
      | left _ => true
      | right _ => false
      end
  | _ => false
  end.

Definition guarded_fundamental_normal_form
  (target : Label)
  (e : CFGKATExpression)
  : CFGKATExpression :=
  guarded_sum_on
    (filter
      (fun m =>
        negb (is_jump_to target
          (transition_output e (AtIY_atom m) (AtIY_assignment m))))
      all_AtIY)
    (fundamental_branch e).

Definition syntactically_guarded
  (l : Label)
  (e : CFGKATExpression)
  : Prop :=
  e == guarded_fundamental_normal_form l e.

Local Ltac simplify_transition_output_in H :=
  repeat progress
    (simpl in H;
     repeat
      (rewrite transition_sequence in H ||
       rewrite transition_complete_assignment in H ||
       rewrite transition_break in H ||
       rewrite transition_continue in H ||
       rewrite transition_return in H ||
       rewrite transition_goto in H ||
       rewrite transition_action in H ||
       rewrite transition_assert in H)).

Local Lemma guarded_branch_kept
  (l : Label)
  (e : CFGKATExpression)
  (m : At x I^Y)
  :
  guarded l e ->
  negb
    (is_jump_to l
      (transition_output e (AtIY_atom m) (AtIY_assignment m))) = true.
Proof.
  intro Hguarded.
  destruct (transition_output e (AtIY_atom m) (AtIY_assignment m))
    as [|i_accept|i_break|i_continue| |l_jump i_jump|p next]
    eqn:Hout; try reflexivity.
  simpl.
  destruct (Label_eq_dec l_jump l) as [-> | Hneq]; [|reflexivity].
  exfalso.
  apply (Hguarded (AtIY_atom m) (AtIY_assignment m) i_jump).
  apply (proj2 (transition_output_exact e _ _ _)).
  exact Hout.
Qed.

Local Lemma sys_not_jump_to_guarded
  (l : Label)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  is_jump_to l r = false ->
  guarded l (sys r).
Proof.
  intros Hnot a i j Hdyn.
  pose proof (transition_output_unique (sys r) a i _ Hdyn) as Hout.
  destruct r as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p [f i_next]];
    simpl in Hnot; simplify_transition_output_in Hout; try discriminate.
  destruct (Label_eq_dec l_jump l) as [_ | Hneq]; [discriminate |].
  injection Hout as Hlabel _.
  apply Hneq. exact Hlabel.
Qed.

Local Lemma guarded_fundamental_normal_form_guarded
  (l : Label)
  (e : CFGKATExpression)
  :
  guarded l (guarded_fundamental_normal_form l e).
Proof.
  unfold guarded_fundamental_normal_form, guarded.
  intros a i j Hjump.
  destruct (guarded_sum_on_jump_inv _ _ _ _ _ _ Hjump)
    as [m [Hm Hbranch]].
  apply filter_In in Hm as [_ Hkept].
  apply negb_true_iff in Hkept.
  unfold fundamental_branch in Hbranch.
  exact
    (sys_not_jump_to_guarded
      l
      (transition_output e (AtIY_atom m) (AtIY_assignment m))
      Hkept
      a i j Hbranch).
Qed.

Corollary guardedsyndef
  (l : Label)
  (e : CFGKATExpression)
  :
  guarded l e <-> syntactically_guarded l e.
Proof.
  split.
  - intro Hguarded.
    unfold syntactically_guarded, guarded_fundamental_normal_form.
    rewrite filter_all_true.
    + apply fundamental_theorem.
    + intros m _. apply guarded_branch_kept. exact Hguarded.
  - intros Hsyn a i j Hjump.
    destruct (CFGKATEquiv_sound _ _ _ _ Hsyn i) as [R HR].
    pose proof
      (proj2 (resolve_syntactic_empty_identity (e, i) a _) Hjump)
      as Hleft.
    destruct
      (CFGKATExpressionDynamics_total
        (guarded_fundamental_normal_form l e, i) a)
      as [r Hright_raw].
    pose proof
      (proj2
        (resolve_syntactic_empty_identity
          (guarded_fundamental_normal_form l e, i) a r)
        Hright_raw)
      as Hright.
    pose proof
      (cfgkat_bisimulation_step
        R
        (e, i)
        (guarded_fundamental_normal_form l e, i)
        a
        (CFGKATAutomatonJump l j)
        r
        HR Hleft Hright)
      as Hlift.
    inversion Hlift; subst.
    exact (guarded_fundamental_normal_form_guarded l e a i j Hright_raw).
Qed.
