Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Logic.ClassicalEpsilon.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Program.Equality.
From Stdlib Require Import Lists.List.
Import ListNotations.

From CFGKAT.Completeness Require Export gtnflem1.

Local Open Scope cfgkat_scope.
Local Open Scope cfgkat_setoid_scope.


Fixpoint lookup_gtnf_expr
  (expr_label : CFGKATExpression -> Label)
  (states : list CFGKATSyntConfiguration)
  (target : Label)
  : option CFGKATExpression :=
  match states with
  | [] => None
  | (f, _) :: states' =>
      match Label_eq_dec target (expr_label f) with
      | left _ => Some f
      | right _ => lookup_gtnf_expr expr_label states' target
      end
  end.

Record gtnf_label_supply
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  : Type :=
{
  gtnf_supply_states : list CFGKATSyntConfiguration;
  gtnf_supply_label : CFGKATSyntConfiguration -> Label;
  gtnf_supply_expr_label : CFGKATExpression -> Label;

  gtnf_supply_label_injective :
    forall s t,
      In s gtnf_supply_states ->
      In t gtnf_supply_states ->
      gtnf_supply_label s = gtnf_supply_label t ->
      s = t;

  gtnf_supply_expr_label_injective :
    forall f g i j,
      In (f, i) gtnf_supply_states ->
      In (g, j) gtnf_supply_states ->
      gtnf_supply_expr_label f = gtnf_supply_expr_label g ->
      f = g;

  gtnf_supply_label_fresh_original :
    forall s k body,
      In s gtnf_supply_states ->
      E k = Some body ->
      gtnf_supply_label s <> k;

  gtnf_supply_expr_label_fresh_original :
    forall f k body,
      (exists i, In (f, i) gtnf_supply_states) ->
      E k = Some body ->
      gtnf_supply_expr_label f <> k;

  gtnf_supply_expr_label_not_in_supply_expr :
    forall target f,
      (exists i, In (target, i) gtnf_supply_states) ->
      (exists i, In (f, i) gtnf_supply_states) ->
      ~ contains_goto (gtnf_supply_expr_label target) f;

  gtnf_supply_label_expr_disjoint :
    forall s f,
      In s gtnf_supply_states ->
      (exists i, In (f, i) gtnf_supply_states) ->
      gtnf_supply_label s <> gtnf_supply_expr_label f;

  gtnf_supply_initial :
    forall i, In (e, i) gtnf_supply_states;

  gtnf_supply_original :
    forall k body i,
      E k = Some body ->
      In (body, i) gtnf_supply_states;

  gtnf_supply_assignment_closed :
    forall f i j,
      In (f, i) gtnf_supply_states ->
      In (f, j) gtnf_supply_states;

  gtnf_supply_next_closed :
    forall f i a p next,
      In (f, i) gtnf_supply_states ->
      resolved_transition_output E f a i =
        CFGKATAutomatonNext p next ->
      In next gtnf_supply_states;

  supply_state_label_no_raw_jump :
    forall target_state source a j,
      In target_state gtnf_supply_states ->
      In source gtnf_supply_states ->
      CFGKATExpressionDynamics source a
        (CFGKATAutomatonJump (gtnf_supply_label target_state) j) ->
      False
}.

Arguments gtnf_supply_label {E e} _ _.

Definition gtnf_ell_source
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (k : Label)
  : option CFGKATExpression :=
  lookup_gtnf_expr
    (gtnf_supply_expr_label E e supply)
    (gtnf_supply_states E e supply)
    k.

Arguments gtnf_ell_source {E e} _ _.

Lemma gtnf_supply_expr_label_not_in_original_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  forall f k body,
    (exists i, In (f, i) (gtnf_supply_states E e supply)) ->
    E k = Some body ->
    ~ contains_goto (gtnf_supply_expr_label E e supply f) body.
Proof.
  intros f k body Hf HE.
  eapply gtnf_supply_expr_label_not_in_supply_expr.
  - exact Hf.
  - exists indicator_assignment_witness.
    eapply gtnf_supply_original. exact HE.
Qed.

Lemma gtnf_supply_expr_label_not_in_original_expr
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  forall f,
    (exists i, In (f, i) (gtnf_supply_states E e supply)) ->
    ~ contains_goto (gtnf_supply_expr_label E e supply f) e.
Proof.
  intros f Hf.
  eapply gtnf_supply_expr_label_not_in_supply_expr.
  - exact Hf.
  - exists indicator_assignment_witness.
    apply gtnf_supply_initial.
Qed.

Lemma supply_expr_label_no_raw_jump
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  forall f source a j,
    (exists u, In (f, u) (gtnf_supply_states E e supply)) ->
    In source (gtnf_supply_states E e supply) ->
    CFGKATExpressionDynamics source a
      (CFGKATAutomatonJump (gtnf_supply_expr_label E e supply f) j) ->
    False.
Proof.
  intros f [source_f source_i] a j Hf Hsource Hjump.
  eapply contains_goto_jump_back in Hjump as Hcontains; eauto.
  eapply gtnf_supply_expr_label_not_in_supply_expr.
  - exact Hf.
  - exists source_i. exact Hsource.
  - exact Hcontains.
Qed.


Fixpoint expr_raw_nexts (f : CFGKATExpression) : list CFGKATExpression :=
  match f with
  | CFGKATAction _ => [1]
  | CFGKATChoice _ e1 e2 =>
      expr_raw_nexts e1 ++ expr_raw_nexts e2
  | CFGKATSequence e1 e2 =>
      expr_raw_nexts e2 ++
      map (fun e1' => CFGKATSequence e1' e2) (expr_raw_nexts e1)
  | CFGKATLoopSeq e1 e2 =>
      expr_raw_nexts e2 ++
      map (fun e1' => CFGKATLoopSeq e1' e2) (expr_raw_nexts e1)
  | CFGKATLoop b e =>
      map (fun e' => CFGKATLoopSeq e' (CFGKATLoop b e))
          (e :: expr_raw_nexts e)
  | _ => []
  end.

Lemma expr_raw_nexts_loopseq_loop_subset :
  forall b e,
    incl (expr_raw_nexts (CFGKATLoopSeq e (CFGKATLoop b e)))
         (expr_raw_nexts (CFGKATLoop b e)).
Proof.
  intros b e f Hf.
  destruct Hf as [<- | Hf].
  - left. reflexivity.
  - apply in_app_or in Hf as [Hf | Hf].
    + right. exact Hf.
    + apply in_map_iff in Hf as [e' [<- He']].
      right.
      apply in_map_iff. exists e'. split. reflexivity.
      exact He'.
Qed.

Lemma expr_raw_nexts_correct :
  forall f i a p f' i',
    CFGKATExpressionFiniteDynamics (f, i) a (CFGKATAutomatonNext p (f', i')) ->
    In f' (expr_raw_nexts f).
Proof.
  intros f i a p f' i' H.
  dependent induction H; simpl in *; try discriminate.
  -
    change (1 = 1 \/ False).
    left. reflexivity.
  -
    apply in_app_iff. left.
    exact (IHCFGKATExpressionFiniteDynamics _ _ _ _ _ eq_refl eq_refl).
  -
    apply in_app_iff. right.
    exact (IHCFGKATExpressionFiniteDynamics _ _ _ _ _ eq_refl eq_refl).
  -
    apply in_app_iff. left.
    exact (IHCFGKATExpressionFiniteDynamics2 _ _ _ _ _ eq_refl eq_refl).
  -
    apply in_app_iff. right.
    apply in_map_iff. exists e1'. split. reflexivity.
    exact (IHCFGKATExpressionFiniteDynamics _ _ _ _ _ eq_refl eq_refl).
  -
    apply in_app_iff. left.
    exact (IHCFGKATExpressionFiniteDynamics2 _ _ _ _ _ eq_refl eq_refl).
  -
    apply in_app_iff. left.
    exact (IHCFGKATExpressionFiniteDynamics2 _ _ _ _ _ eq_refl eq_refl).
  -
    apply in_app_iff. right.
    apply in_map_iff. exists e1'. split. reflexivity.
    exact (IHCFGKATExpressionFiniteDynamics _ _ _ _ _ eq_refl eq_refl).
  -
    apply expr_raw_nexts_loopseq_loop_subset.
    exact (IHCFGKATExpressionFiniteDynamics _ _ _ _ _ eq_refl eq_refl).
Qed.

Lemma expr_raw_nexts_incl_self :
  forall f f',
    In f' (expr_raw_nexts f) ->
    incl (expr_raw_nexts f') (expr_raw_nexts f).
Proof.
  induction f; intros f' Hf' g Hg; simpl in *.
  - contradiction.
  -
    destruct Hf' as [<- | []]. simpl in Hg. contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  -
    apply in_app_or in Hf' as [H1 | H2].
    + apply in_app_iff. left. apply IHf1 with f'; assumption.
    + apply in_app_iff. right. apply IHf2 with f'; assumption.
  -
    apply in_app_or in Hf' as [H2 | Hmap].
    +
      apply in_app_iff. left. apply IHf2 with f'; assumption.
    +
      apply in_map_iff in Hmap as [e1' [<- He1']].
      apply in_app_or in Hg as [Hg2 | Hgmap].
      *
        apply in_app_iff. left. exact Hg2.
      *
        apply in_map_iff in Hgmap as [e1'' [<- He1'']].
        apply in_app_iff. right. apply in_map_iff.
        exists e1''. split. reflexivity.
        apply IHf1 with e1'; assumption.
  -
    apply in_app_or in Hf' as [H2 | Hmap].
    + apply in_app_iff. left. apply IHf2 with f'; assumption.
    + apply in_map_iff in Hmap as [e1' [<- He1']].
      apply in_app_or in Hg as [Hg2 | Hgmap].
      * apply in_app_iff. left. exact Hg2.
      * apply in_map_iff in Hgmap as [e1'' [<- He1'']].
        apply in_app_iff. right. apply in_map_iff.
        exists e1''. split. reflexivity.
        apply IHf1 with e1'; assumption.
  -
    destruct Hf' as [<- | Hf'].
    + apply expr_raw_nexts_loopseq_loop_subset.
      exact Hg.
    + apply in_map_iff in Hf' as [e' [<- He']].
      destruct Hg as [<- | Hg].
      * left. reflexivity.
      * apply in_app_or in Hg as [Hloop | Hgmap].
        --
           right. exact Hloop.
        --
        apply in_map_iff in Hgmap as [e'' [<- He'']].
        right. apply in_map_iff.
        exists e''. split. reflexivity.
        apply IHf with e'. exact He'. exact He''.
Qed.

Lemma lookup_gtnf_expr_in_some
  (expr_label : CFGKATExpression -> Label)
  (states : list CFGKATSyntConfiguration)
  (f : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  (forall g h j k,
    In (g, j) states ->
    In (h, k) states ->
    expr_label g = expr_label h ->
    g = h) ->
  In (f, i) states ->
  lookup_gtnf_expr expr_label states (expr_label f) = Some f.
Proof.
  intros Hinj Hin.
  induction states as [|[g j] states IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Hhead | Htail].
    + injection Hhead as <- <-.
      destruct (Label_eq_dec (expr_label g) (expr_label g)) as [_ | Hneq].
      * reflexivity.
      * contradiction Hneq. reflexivity.
    + destruct (Label_eq_dec (expr_label f) (expr_label g)) as [Heq | _].
      * assert (Hg : g = f).
        { eapply Hinj.
          - left. reflexivity.
          - right. exact Htail.
          - symmetry. exact Heq. }
        subst g. reflexivity.
      * apply IH.
        -- intros g0 h0 j0 k0 Hg Hh Heq.
           eapply Hinj; try (right; eassumption); exact Heq.
        -- exact Htail.
Qed.

Lemma lookup_gtnf_expr_some_in
  (expr_label : CFGKATExpression -> Label)
  (states : list CFGKATSyntConfiguration)
  (target : Label)
  (f : CFGKATExpression)
  :
  lookup_gtnf_expr expr_label states target = Some f ->
  exists i, In (f, i) states /\ target = expr_label f.
Proof.
  induction states as [|[g i] states IH]; simpl.
  - discriminate.
  - destruct (Label_eq_dec target (expr_label g)) as [Heq | Hneq].
    + intro H. injection H as <-.
      exists i. split; [left; reflexivity | exact Heq].
    + intro H.
      destruct (IH H) as [j [Hin Htarget]].
      exists j. split; [right; exact Hin | exact Htarget].
Qed.

Inductive gtnflem2_reachable_state
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  : CFGKATSyntConfiguration -> Prop :=
| gtnflem2_reachable_initial :
    forall i, gtnflem2_reachable_state (e, i)
| gtnflem2_reachable_original :
    forall k body i,
      E k = Some body ->
      gtnflem2_reachable_state (body, i)
| gtnflem2_reachable_assignment :
    forall f i j,
      gtnflem2_reachable_state (f, i) ->
      gtnflem2_reachable_state (f, j)
| gtnflem2_reachable_next :
    forall f i a p next,
      gtnflem2_reachable_state (f, i) ->
      resolved_transition_output E f a i =
        CFGKATAutomatonNext p next ->
      gtnflem2_reachable_state next.

Lemma gtnflem2_reachable_state_in_supply
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  :
  gtnflem2_reachable_state (E := E) (e := e) s ->
  In s (gtnf_supply_states E e supply).
Proof.
  intro Hreach.
  induction Hreach.
  - apply gtnf_supply_initial.
  - eapply gtnf_supply_original. exact H.
  - eapply gtnf_supply_assignment_closed. exact IHHreach.
  - eapply gtnf_supply_next_closed; eauto.
Qed.

Definition gtnflem2_reachable_states
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  : list CFGKATSyntConfiguration :=
  filter
    (fun s =>
      match excluded_middle_informative
        (gtnflem2_reachable_state (E := E) (e := e) s) with
      | left _ => true
      | right _ => false
      end)
    (gtnf_supply_states E e supply).

Lemma gtnflem2_reachable_states_in_supply
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  :
  In s (gtnflem2_reachable_states supply) ->
  In s (gtnf_supply_states E e supply).
Proof.
  unfold gtnflem2_reachable_states.
  intro Hin.
  apply filter_In in Hin.
  exact (proj1 Hin).
Qed.

Lemma gtnflem2_reachable_states_in_reachable
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  :
  In s (gtnflem2_reachable_states supply) ->
  gtnflem2_reachable_state (E := E) (e := e) s.
Proof.
  unfold gtnflem2_reachable_states.
  intro Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Hselected].
  destruct (excluded_middle_informative
    (gtnflem2_reachable_state (E := E) (e := e) s))
    as [Hreach | Hnot]; [exact Hreach | discriminate Hselected].
Qed.

Lemma gtnflem2_reachable_states_contains
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (s : CFGKATSyntConfiguration)
  :
  gtnflem2_reachable_state (E := E) (e := e) s ->
  In s (gtnflem2_reachable_states supply).
Proof.
  intro Hreach.
  unfold gtnflem2_reachable_states.
  apply filter_In.
  split.
  - exact (gtnflem2_reachable_state_in_supply supply s Hreach).
  - destruct (excluded_middle_informative
      (gtnflem2_reachable_state (E := E) (e := e) s))
      as [_ | Hnot]; [reflexivity | contradiction].
Qed.

Lemma gtnflem2_reachable_states_expr_label_injective
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  forall f g i j,
    In (f, i) (gtnflem2_reachable_states supply) ->
    In (g, j) (gtnflem2_reachable_states supply) ->
    gtnf_supply_expr_label E e supply f =
      gtnf_supply_expr_label E e supply g ->
    f = g.
Proof.
  intros f g i j Hf Hg Hlabel.
  eapply gtnf_supply_expr_label_injective.
  - eapply gtnflem2_reachable_states_in_supply. exact Hf.
  - eapply gtnflem2_reachable_states_in_supply. exact Hg.
  - exact Hlabel.
Qed.

Definition gtnflem2_reachable_ell_source
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (k : Label)
  : option CFGKATExpression :=
  lookup_gtnf_expr
    (gtnf_supply_expr_label E e supply)
    (gtnflem2_reachable_states supply)
    k.

Arguments gtnflem2_reachable_ell_source {E e} _ _.

Lemma gtnflem2_reachable_ell_source_in_some
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (f : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  In (f, i) (gtnflem2_reachable_states supply) ->
  gtnflem2_reachable_ell_source supply
    (gtnf_supply_expr_label E e supply f) = Some f.
Proof.
  intro Hin.
  unfold gtnflem2_reachable_ell_source.
  eapply lookup_gtnf_expr_in_some.
  - exact (gtnflem2_reachable_states_expr_label_injective supply).
  - exact Hin.
Qed.

Lemma gtnflem2_reachable_ell_source_some_in
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (k : Label)
  (f : CFGKATExpression)
  :
  gtnflem2_reachable_ell_source supply k = Some f ->
  exists i,
    In (f, i) (gtnflem2_reachable_states supply) /\
    k = gtnf_supply_expr_label E e supply f.
Proof.
  unfold gtnflem2_reachable_ell_source.
  apply lookup_gtnf_expr_some_in.
Qed.

Definition sysc
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  : CFGKATExpression :=
  match r with
  | CFGKATAutomatonNext p (f, i) =>
      complete_assignment i ;;
      do p ;;
      goto (gtnf_supply_expr_label E e supply f)
  | _ => sys r
  end.

Definition gtnf_supply_exprs
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  : list CFGKATExpression :=
  (e :: expr_raw_nexts e) ++
  flat_map
      (fun k =>
        match E k with
        | Some body => body :: expr_raw_nexts body
        | None => []
        end)
      (env_support E).

Definition gtnf_supply_state_list
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  : list CFGKATSyntConfiguration :=
  flat_map
    (fun f => map (fun i => (f, i)) all_assignments)
    (gtnf_supply_exprs E e).

Lemma gtnf_supply_state_expr_in
  (E : label_environment CFGKATExpression)
  (e f : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  In f (gtnf_supply_exprs E e) ->
  In (f, i) (gtnf_supply_state_list E e).
Proof.
  intro Hf.
  unfold gtnf_supply_state_list.
  apply in_flat_map.
  exists f.
  split; [exact Hf |].
  apply in_map_iff.
  exists i.
  split; [reflexivity | apply all_assignments_complete].
Qed.

Lemma gtnf_supply_state_expr
  (E : label_environment CFGKATExpression)
  (e f : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  In (f, i) (gtnf_supply_state_list E e) ->
  In f (gtnf_supply_exprs E e).
Proof.
  unfold gtnf_supply_state_list.
  intro Hstate.
  apply in_flat_map in Hstate.
  destruct Hstate as [g [Hg Hmap]].
  apply in_map_iff in Hmap.
  destruct Hmap as [j [Hpair _]].
  injection Hpair as <- <-.
  exact Hg.
Qed.

Lemma gtnf_supply_initial_expr
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  :
  In e (gtnf_supply_exprs E e).
Proof.
  unfold gtnf_supply_exprs.
  apply in_or_app.
  left. left. reflexivity.
Qed.

Lemma gtnf_supply_original_expr
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  (k : Label)
  (body : CFGKATExpression)
  :
  E k = Some body ->
  In body (gtnf_supply_exprs E e).
Proof.
  intro HE.
  unfold gtnf_supply_exprs.
  apply in_or_app.
  right.
  apply in_flat_map.
    exists k.
    split.
    - eapply env_supported. exact HE.
    - rewrite HE. left. reflexivity.
Qed.

Lemma gtnf_supply_exprs_raw_next_closed
  (E : label_environment CFGKATExpression)
  (e f f' : CFGKATExpression)
  :
  In f (gtnf_supply_exprs E e) ->
  In f' (expr_raw_nexts f) ->
  In f' (gtnf_supply_exprs E e).
Proof.
  intros Hf Hnext.
  unfold gtnf_supply_exprs in *.
  apply in_app_or in Hf as [Hinit | Henv].
  - destruct Hinit as [<- | Hinit_next].
    + apply in_or_app. left. right. exact Hnext.
    + apply in_or_app. left. right.
      eapply expr_raw_nexts_incl_self; eauto.
  - apply in_flat_map in Henv.
    destruct Henv as [k [Hk Hbody]].
    destruct (E k) as [body |] eqn:HE; [| contradiction].
    destruct Hbody as [<- | Hbody_next].
    + apply in_or_app. right.
      apply in_flat_map.
      exists k.
      split; [exact Hk |].
      rewrite HE. right. exact Hnext.
    + apply in_or_app. right.
      apply in_flat_map.
      exists k.
      split; [exact Hk |].
      rewrite HE. right.
      eapply expr_raw_nexts_incl_self; eauto.
Qed.

Lemma gtnf_supply_raw_next_expr_closed
  (E : label_environment CFGKATExpression)
  (e f f' : CFGKATExpression)
  (i i' : IndicatorAssignment)
  (a : Atom)
  (p : Action)
  :
  In f (gtnf_supply_exprs E e) ->
  CFGKATExpressionFiniteDynamics (f, i) a
    (CFGKATAutomatonNext p (f', i')) ->
  In f' (gtnf_supply_exprs E e).
Proof.
  intros Hf Hdyn.
  eapply gtnf_supply_exprs_raw_next_closed.
  - exact Hf.
  - eapply expr_raw_nexts_correct.
    exact Hdyn.
Qed.

Lemma gtnf_supply_resolved_finite_next_expr_closed
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  (source next : CFGKATSyntConfiguration)
  (a : Atom)
  (p : Action)
  :
  In (fst source) (gtnf_supply_exprs E e) ->
  ResolveCFGKATAutomatonFiniteDynamics
    CFGKATExpressionAutomaton
    (CFGKATExpressionDynamics source)
    (lift E) a
    (CFGKATAutomatonNext p next) ->
  In (fst next) (gtnf_supply_exprs E e).
Proof.
  intros Hsource Hfin.
  revert Hsource.
  dependent induction Hfin; intro Hsource.
  - destruct source as [f i].
    destruct next as [f' i'].
    eapply gtnf_supply_raw_next_expr_closed.
    + exact Hsource.
    + eapply cfgkat_expression_dynamics_next_finite.
      exact H.
    - rewrite lift_lookup in H0.
      destruct (E l) as [body |] eqn:HE; [| discriminate H0].
    injection H0 as <-.
    eapply IHHfin.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + apply gtnf_supply_original_expr with (k := l).
      exact HE.
Qed.

Lemma gtnf_supply_resolved_next_closed
  (E : label_environment CFGKATExpression)
  (e f : CFGKATExpression)
  (i : IndicatorAssignment)
  (a : Atom)
  (p : Action)
  (next : CFGKATSyntConfiguration)
  :
  In f (gtnf_supply_exprs E e) ->
  resolved_transition_output E f a i =
    CFGKATAutomatonNext p next ->
  In (fst next) (gtnf_supply_exprs E e).
Proof.
  intros Hf Hout.
  pose proof (resolved_transition_output_spec E f a i) as Hres.
  rewrite Hout in Hres.
  inversion Hres as [a0 zeta Hfin | a0 Hnone]; subst.
  eapply (gtnf_supply_resolved_finite_next_expr_closed E e (f, i) next a p).
  - simpl. exact Hf.
  - exact Hfin.
Qed.

Fixpoint goto_labels
  (e : CFGKATExpression)
  : list Label :=
  match e with
  | CFGKATAssert _
  | CFGKATAction _
  | CFGKATAssign _ _
  | CFGKATBreak
  | CFGKATContinue
  | CFGKATReturn => []
  | CFGKATGoto l => [l]
  | CFGKATChoice _ e1 e2
  | CFGKATSequence e1 e2
  | CFGKATLoopSeq e1 e2 =>
      goto_labels e1 ++ goto_labels e2
  | CFGKATLoop _ body => goto_labels body
  end.

Lemma contains_goto_in_goto_labels
  (target : Label)
  (e : CFGKATExpression)
  :
  contains_goto target e ->
  In target (goto_labels e).
Proof.
  induction e; simpl; intro H; try contradiction.
  - subst. left. reflexivity.
  - destruct H as [H | H].
    + apply in_or_app. left. apply IHe1. exact H.
    + apply in_or_app. right. apply IHe2. exact H.
  - destruct H as [H | H].
    + apply in_or_app. left. apply IHe1. exact H.
    + apply in_or_app. right. apply IHe2. exact H.
  - destruct H as [H | H].
    + apply in_or_app. left. apply IHe1. exact H.
    + apply in_or_app. right. apply IHe2. exact H.
  - apply IHe. exact H.
Qed.

Definition gtnf_expr_label_avoid
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  (exprs : list CFGKATExpression)
  : list Label :=
  env_support E ++ goto_labels e ++ flat_map goto_labels exprs.

Definition gtnf_state_label_avoid
  (E : label_environment CFGKATExpression)
  (exprs : list CFGKATExpression)
  (expr_label : CFGKATExpression -> Label)
  : list Label :=
  env_support E ++ map expr_label exprs ++ flat_map goto_labels exprs.

Lemma gtnf_expr_label_avoid_env
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  (exprs : list CFGKATExpression)
  (k : Label)
  (body : CFGKATExpression)
  :
  E k = Some body ->
  In k (gtnf_expr_label_avoid E e exprs).
Proof.
  intro HE.
  unfold gtnf_expr_label_avoid.
  apply in_or_app. left.
  eapply env_supported. exact HE.
Qed.

Lemma gtnf_expr_label_avoid_member
  (E : label_environment CFGKATExpression)
  (e f : CFGKATExpression)
  (exprs : list CFGKATExpression)
  (l : Label)
  :
  In f exprs ->
  contains_goto l f ->
  In l (gtnf_expr_label_avoid E e exprs).
Proof.
  intros Hf Hcontains.
  unfold gtnf_expr_label_avoid.
  apply in_or_app. right.
  apply in_or_app. right.
  apply in_flat_map.
  exists f. split.
  - exact Hf.
  - apply contains_goto_in_goto_labels. exact Hcontains.
Qed.

Lemma gtnf_state_label_avoid_env
  (E : label_environment CFGKATExpression)
  (exprs : list CFGKATExpression)
  (expr_label : CFGKATExpression -> Label)
  (k : Label)
  (body : CFGKATExpression)
  :
  E k = Some body ->
  In k (gtnf_state_label_avoid E exprs expr_label).
Proof.
  intro HE.
  unfold gtnf_state_label_avoid.
  apply in_or_app. left.
  eapply env_supported. exact HE.
Qed.

Lemma gtnf_state_label_avoid_expr_label
  (E : label_environment CFGKATExpression)
  (exprs : list CFGKATExpression)
  (expr_label : CFGKATExpression -> Label)
  (f : CFGKATExpression)
  (l : Label)
  :
  In f exprs ->
  l = expr_label f ->
  In l (gtnf_state_label_avoid E exprs expr_label).
Proof.
  intros Hf ->.
  unfold gtnf_state_label_avoid.
  apply in_or_app. right.
  apply in_or_app. left.
  apply in_map.
  exact Hf.
Qed.

Lemma gtnf_state_label_avoid_member
  (E : label_environment CFGKATExpression)
  (exprs : list CFGKATExpression)
  (expr_label : CFGKATExpression -> Label)
  (f : CFGKATExpression)
  (l : Label)
  :
  In f exprs ->
  contains_goto l f ->
  In l (gtnf_state_label_avoid E exprs expr_label).
Proof.
  intros Hf Hcontains.
  unfold gtnf_state_label_avoid.
  apply in_or_app. right.
  apply in_or_app. right.
  apply in_flat_map.
  exists f. split.
  - exact Hf.
  - apply contains_goto_in_goto_labels. exact Hcontains.
Qed.

Lemma gtnf_label_supply_exists
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  :
  gtnf_label_supply E e.
Proof.
  set (exprs := gtnf_supply_exprs E e).
  set (states := gtnf_supply_state_list E e).
  destruct (fresh_label_family exprs (gtnf_expr_label_avoid E e exprs))
    as [expr_label [Hexpr_fresh Hexpr_inj]].
  destruct (fresh_label_family states
    (gtnf_state_label_avoid E exprs expr_label))
    as [state_label [Hstate_fresh Hstate_inj]].
  refine {|
    gtnf_supply_states := states;
    gtnf_supply_label := state_label;
    gtnf_supply_expr_label := expr_label
  |}.
  - exact Hstate_inj.
  - intros f g i j Hf Hg Hlabel.
    apply Hexpr_inj.
    + subst states exprs.
      eapply gtnf_supply_state_expr. exact Hf.
    + subst states exprs.
      eapply gtnf_supply_state_expr. exact Hg.
    + exact Hlabel.
  - intros s k body Hs HE Hbad.
    apply (Hstate_fresh s Hs).
    rewrite Hbad.
    eapply gtnf_state_label_avoid_env. exact HE.
  - intros f k body [i Hf] HE Hbad.
    apply (Hexpr_fresh f).
    + subst states exprs.
      eapply gtnf_supply_state_expr. exact Hf.
    + rewrite Hbad.
      eapply gtnf_expr_label_avoid_env. exact HE.
  - intros target f [target_i Htarget] [f_i Hf] Hcontains.
    apply (Hexpr_fresh target).
    + subst states exprs.
      eapply gtnf_supply_state_expr. exact Htarget.
    + eapply gtnf_expr_label_avoid_member.
      * subst states exprs.
        eapply gtnf_supply_state_expr. exact Hf.
      * exact Hcontains.
  - intros s f Hs [i Hf] Hbad.
    apply (Hstate_fresh s Hs).
    eapply gtnf_state_label_avoid_expr_label.
    + subst states exprs.
      eapply gtnf_supply_state_expr. exact Hf.
    + exact Hbad.
  - intro i.
    apply gtnf_supply_state_expr_in.
    apply gtnf_supply_initial_expr.
  - intros k body i HE.
    apply gtnf_supply_state_expr_in.
    eapply gtnf_supply_original_expr. exact HE.
  - intros f i j Hf.
    apply gtnf_supply_state_expr_in.
    eapply gtnf_supply_state_expr. exact Hf.
  - intros f i a p next Hf Hnext.
    destruct next as [next_f next_i].
    apply gtnf_supply_state_expr_in.
    eapply (gtnf_supply_resolved_next_closed
      E e f i a p (next_f, next_i)).
    + eapply gtnf_supply_state_expr. exact Hf.
    + exact Hnext.
  - intros target_state source a j Htarget Hsource Hjump.
    destruct source as [source_f source_i].
    eapply contains_goto_jump_back in Hjump as Hcontains.
    apply (Hstate_fresh target_state Htarget).
    eapply gtnf_state_label_avoid_member.
    + subst states exprs.
      eapply gtnf_supply_state_expr. exact Hsource.
    + exact Hcontains.
Defined.

Lemma finite_resolution_no_supply_expr_label_jump
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (target : CFGKATExpression)
  (source : CFGKATSyntConfiguration)
  (a : Atom)
  (j : IndicatorAssignment)
  :
  (exists u, In (target, u) (gtnf_supply_states E e supply)) ->
  In source (gtnf_supply_states E e supply) ->
  ~ ResolveCFGKATAutomatonFiniteDynamics
      CFGKATExpressionAutomaton
      (CFGKATExpressionDynamics source)
      (lift E) a
      (CFGKATAutomatonJump (gtnf_supply_expr_label E e supply target) j).
Proof.
  intros Htarget Hsource Hfin.
  revert Hsource.
  dependent induction Hfin generalizing source;
    intro Hsource.
  - destruct source as [g source_i].
    eapply supply_expr_label_no_raw_jump.
    + exact Htarget.
    + exact Hsource.
    + exact H.
  - rewrite lift_lookup in H0.
    destruct (E l) as [body |] eqn:HE; [| discriminate H0].
    injection H0 as <-.
    eapply IHHfin.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply gtnf_supply_original.
      exact HE.
Qed.

Lemma resolved_transition_output_no_supply_expr_label_jump
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (target source : CFGKATExpression)
  (source_i j : IndicatorAssignment)
  (a : Atom)
  :
  (exists u, In (target, u) (gtnf_supply_states E e supply)) ->
  In (source, source_i) (gtnf_supply_states E e supply) ->
  resolved_transition_output E source a source_i <>
    CFGKATAutomatonJump (gtnf_supply_expr_label E e supply target) j.
Proof.
  intros Htarget Hsource Hjump.
  pose proof (resolved_transition_output_spec E source a source_i) as Hres.
  rewrite Hjump in Hres.
  inversion Hres as [a0 zeta Hfin | a0 Hnone]; subst.
  - eapply (finite_resolution_no_supply_expr_label_jump
      supply target (source, source_i) a j).
    + exact Htarget.
    + exact Hsource.
    + exact Hfin.
Qed.

Fixpoint lookup_gtnf_state
  {state : Type}
  (state_label : state -> Label)
  (states : list state)
  (target : Label)
  : option state :=
  match states with
  | [] => None
  | s :: states' =>
      match Label_eq_dec target (state_label s) with
      | left _ => Some s
      | right _ => lookup_gtnf_state state_label states' target
      end
  end.

Lemma lookup_gtnf_state_in_some
  {state : Type}
  (state_label : state -> Label)
  (states : list state)
  (s : state)
  :
  (forall x y,
    In x states ->
    In y states ->
    state_label x = state_label y ->
    x = y) ->
  In s states ->
  lookup_gtnf_state state_label states (state_label s) = Some s.
Proof.
  intros Hinj Hin.
  induction states as [|t states IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Hhead | Htail].
    + subst t.
      destruct (Label_eq_dec (state_label s) (state_label s)) as [_ | Hneq].
      * reflexivity.
      * contradiction Hneq. reflexivity.
    + destruct (Label_eq_dec (state_label s) (state_label t)) as [Heq | _].
      * assert (Ht : t = s).
        { eapply Hinj.
          - left. reflexivity.
          - right. exact Htail.
          - symmetry. exact Heq. }
        subst t. reflexivity.
      * apply IH.
        -- intros x y Hx Hy Heq.
           eapply Hinj; try (right; eassumption); exact Heq.
        -- exact Htail.
Qed.

Lemma lookup_gtnf_state_some_in
  {state : Type}
  (state_label : state -> Label)
  (states : list state)
  (target : Label)
  (s : state)
  :
  lookup_gtnf_state state_label states target = Some s ->
  In s states /\ target = state_label s.
Proof.
  induction states as [|t states IH]; simpl.
  - discriminate.
  - destruct (Label_eq_dec target (state_label t)) as [Heq | Hneq].
    + intro H. injection H as <-.
      split; [left; reflexivity | exact Heq].
    + intro H.
      destruct (IH H) as [Hin Htarget].
      split; [right; exact Hin | exact Htarget].
Qed.

Definition gtnflem2_state_body
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (source : CFGKATExpression)
  : CFGKATExpression :=
  guarded_sum_all
    (fun m =>
      sysc supply
        (resolved_transition_output
          E source (AtIY_atom m) (AtIY_assignment m))).

Definition canonical_gtnf_supply
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  : gtnf_label_supply E e :=
  gtnf_label_supply_exists E e.

Lemma sysc_jump_label_inv
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  (i j : IndicatorAssignment)
  (a : Atom)
  (l : Label)
  :
  CFGKATExpressionDynamics (sysc supply r, i) a
    (CFGKATAutomatonJump l j) ->
  exists j0, r = CFGKATAutomatonJump l j0.
Proof.
  intro Hdyn.
  pose proof
    (transition_output_unique
      (sysc supply r) a i
      (CFGKATAutomatonJump l j) Hdyn) as Hout.
  destruct r as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p [f i_next]];
    simplify_sysc_transition_in Hout;
    try discriminate.
  injection Hout as Hlabel _.
  exists i_jump.
  rewrite Hlabel.
  reflexivity.
Qed.

Lemma gtnflem2_state_body_jump_inv
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (source : CFGKATExpression)
  (i j : IndicatorAssignment)
  (a : Atom)
  (l : Label)
  :
  CFGKATExpressionDynamics
    (gtnflem2_state_body supply source, i) a
    (CFGKATAutomatonJump l j) ->
  exists m j0,
    In m all_AtIY /\
    resolved_transition_output E source
      (AtIY_atom m) (AtIY_assignment m) =
      CFGKATAutomatonJump l j0.
Proof.
  intro Hdyn.
  unfold gtnflem2_state_body, guarded_sum_all in Hdyn.
  destruct (guarded_sum_on_jump_inv all_AtIY _ _ _ _ _ Hdyn)
    as [m [Hin Hbranch]].
  destruct (sysc_jump_label_inv supply _ _ _ _ _ Hbranch)
    as [j0 Hj].
  exists m, j0.
  split; [exact Hin | exact Hj].
Qed.

Lemma gtnflem2_state_body_no_original_jump
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (target : Label)
  (target_body source : CFGKATExpression)
  (i j : IndicatorAssignment)
  (a : Atom)
  :
  E target = Some target_body ->
  ~ CFGKATExpressionDynamics
      (gtnflem2_state_body supply source, i) a
      (CFGKATAutomatonJump target j).
Proof.
  intros Htarget Hdyn.
  destruct (gtnflem2_state_body_jump_inv
    supply source i j a target Hdyn)
    as [m [j0 [_ Hout]]].
  eapply resolved_transition_output_no_original_bound_jump.
  - exact Htarget.
  - exact Hout.
Qed.

Lemma finite_resolution_no_supply_state_label_jump
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (target_state : CFGKATSyntConfiguration)
  (source : CFGKATSyntConfiguration)
  (a : Atom)
  (i j : IndicatorAssignment)
  :
  In target_state (gtnf_supply_states E e supply) ->
  In source (gtnf_supply_states E e supply) ->
  ~ ResolveCFGKATAutomatonFiniteDynamics
      CFGKATExpressionAutomaton
      (CFGKATExpressionDynamics source)
      (lift E) a
      (CFGKATAutomatonJump (gtnf_supply_label supply target_state) j).
Proof.
  intros Htarget Hsource Hfin.
  revert Hsource.
  dependent induction Hfin generalizing source;
    intro Hsource.
  - destruct source as [g source_i].
    eapply supply_state_label_no_raw_jump.
    + exact Htarget.
    + exact Hsource.
    + exact H.
  - rewrite lift_lookup in H0.
    destruct (E l) as [body |] eqn:HE; [| discriminate H0].
    injection H0 as <-.
    eapply IHHfin.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply gtnf_supply_original.
      exact HE.
Qed.

Lemma resolved_transition_output_no_supply_state_label_jump
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (target_state : CFGKATSyntConfiguration)
  (source : CFGKATExpression)
  (source_i j : IndicatorAssignment)
  (a : Atom)
  :
  In target_state (gtnf_supply_states E e supply) ->
  In (source, source_i) (gtnf_supply_states E e supply) ->
  resolved_transition_output E source a source_i <>
    CFGKATAutomatonJump (gtnf_supply_label supply target_state) j.
Proof.
  intros Htarget Hsource Hjump.
  pose proof (resolved_transition_output_spec E source a source_i) as Hres.
  rewrite Hjump in Hres.
  inversion Hres as [a0 zeta Hfin | a0 Hnone]; subst.
  - eapply (finite_resolution_no_supply_state_label_jump
      supply target_state (source, source_i) a source_i j).
    + exact Htarget.
    + exact Hsource.
    + exact Hfin.
Qed.

Lemma gtnflem2_state_body_no_supply_expr_label_jump
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (target source : CFGKATExpression)
  (i j : IndicatorAssignment)
  (a : Atom)
  :
  (exists u, In (target, u) (gtnf_supply_states E e supply)) ->
  (exists u, In (source, u) (gtnf_supply_states E e supply)) ->
  ~ CFGKATExpressionDynamics
      (gtnflem2_state_body supply source, i) a
      (CFGKATAutomatonJump (gtnf_supply_expr_label E e supply target) j).
Proof.
  intros Htarget [source_i Hsource] Hdyn.
  destruct (gtnflem2_state_body_jump_inv
    supply source i j a
    (gtnf_supply_expr_label E e supply target) Hdyn)
    as [m [j0 [_ Hout]]].
  eapply resolved_transition_output_no_supply_expr_label_jump.
  - exact Htarget.
  - eapply gtnf_supply_assignment_closed.
    exact Hsource.
  - exact Hout.
Qed.

Lemma gtnflem2_env_supported
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  label_environment_supports
    (fun k =>
      match E k with
      | Some body =>
          Some
            (guarded_sum_all
              (fun alpha_pi =>
                sysc supply
                  (resolved_transition_output
                    E body
                    (AtIY_atom alpha_pi)
                    (AtIY_assignment alpha_pi))))
      | None =>
          match gtnflem2_reachable_ell_source supply k with
          | Some f =>
              Some
                (guarded_sum_all
                  (fun alpha_pi =>
                    sysc supply
                      (resolved_transition_output
                        E f
                        (AtIY_atom alpha_pi)
                        (AtIY_assignment alpha_pi))))
          | None => None
          end
      end)
    (env_support E
     ++
     map
       (fun state => gtnf_supply_expr_label E e supply (fst state))
       (gtnflem2_reachable_states supply)).
Proof.
  intros k value Hlookup.
  destruct (E k) as [body |] eqn:HE.
  - apply in_or_app. left.
    eapply env_supported. exact HE.
  - destruct (gtnflem2_reachable_ell_source supply k) as [source |] eqn:Hexpr;
      [| discriminate Hlookup].
    destruct (gtnflem2_reachable_ell_source_some_in supply k source Hexpr)
      as [i [Hin Hlabel]].
    apply in_or_app. right.
    subst k.
    apply in_map_iff.
    exists (source, i).
    split; [reflexivity | exact Hin].
Qed.

Definition gtnflem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  : label_environment CFGKATExpression :=
  mk_environment
    (fun k =>
      match E k with
      | Some body =>
          Some
            (guarded_sum_all
              (fun alpha_pi =>
                sysc supply
                  (resolved_transition_output
                    E body
                    (AtIY_atom alpha_pi)
                    (AtIY_assignment alpha_pi))))
      | None =>
          match gtnflem2_reachable_ell_source supply k with
          | Some f =>
              Some
                (guarded_sum_all
                  (fun alpha_pi =>
                    sysc supply
                      (resolved_transition_output
                        E f
                        (AtIY_atom alpha_pi)
                        (AtIY_assignment alpha_pi))))
          | None => None
          end
      end)
	    (env_support E
	     ++
	     map
	       (fun state => gtnf_supply_expr_label E e supply (fst state))
	       (gtnflem2_reachable_states supply))
	    (gtnflem2_env_supported supply).

Lemma gtnf_reachable_expr_label_source_env_supported
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  label_environment_supports
    (fun k => gtnflem2_reachable_ell_source supply k)
    (map
      (fun state => gtnf_supply_expr_label E e supply (fst state))
      (gtnflem2_reachable_states supply)).
Proof.
  intros k source Hlookup.
  destruct (gtnflem2_reachable_ell_source_some_in
    supply k source Hlookup) as [i [Hin Hlabel]].
  subst k.
  apply in_map_iff.
  exists (source, i).
  split; [reflexivity | exact Hin].
Qed.

Definition gtnf_reachable_expr_label_source_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  : label_environment CFGKATExpression :=
  mk_environment
    (fun k => gtnflem2_reachable_ell_source supply k)
    (map
      (fun state => gtnf_supply_expr_label E e supply (fst state))
      (gtnflem2_reachable_states supply))
    (gtnf_reachable_expr_label_source_env_supported supply).

Lemma gtnf_reachable_expr_label_source_env_disjoint
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  label_disjoint E (gtnf_reachable_expr_label_source_env supply).
Proof.
  unfold label_disjoint, label_in_dom,
    gtnf_reachable_expr_label_source_env, mk_environment.
  intros k [body HE] [f Hlookup].
  destruct (gtnflem2_reachable_ell_source_some_in
    supply k f Hlookup) as [i [Hin Hlabel]].
  pose proof
    (gtnf_supply_expr_label_fresh_original E e supply f k body
      (ex_intro _
        i
        (gtnflem2_reachable_states_in_supply supply (f, i) Hin))
      HE) as Hfresh.
  apply Hfresh.
  symmetry.
  exact Hlabel.
Qed.
#[local] Existing Instance gtnf_reachable_expr_label_source_env_disjoint.

Definition gtnf_source_with_reachable_expr_labels_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  : label_environment CFGKATExpression :=
  E + gtnf_reachable_expr_label_source_env supply.

Lemma gtnf_source_with_reachable_expr_labels_env_lookup_expr
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (f : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  In (f, i) (gtnflem2_reachable_states supply) ->
  gtnf_source_with_reachable_expr_labels_env supply
    (gtnf_supply_expr_label E e supply f) = Some f.
Proof.
  intro Hin.
  unfold gtnf_source_with_reachable_expr_labels_env, label_env_cup,
    gtnf_reachable_expr_label_source_env, mk_environment.
  simpl.
  destruct (E (gtnf_supply_expr_label E e supply f))
    as [body |] eqn:HE.
  - exfalso.
    pose proof
      (gtnf_supply_expr_label_fresh_original E e supply f
        (gtnf_supply_expr_label E e supply f) body
        (ex_intro _
          i
          (gtnflem2_reachable_states_in_supply supply (f, i) Hin))
        HE) as Hfresh.
    apply Hfresh.
    reflexivity.
  - rewrite gtnflem2_reachable_ell_source_in_some with (i := i).
    + reflexivity.
    + exact Hin.
Qed.

Lemma gtnf_original_no_goto_reachable_expr_label_source_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  no_goto_env E (gtnf_reachable_expr_label_source_env supply).
Proof.
  unfold no_goto_env, no_goto_expr, label_in_dom,
    gtnf_reachable_expr_label_source_env, mk_environment.
  intros k body HE target [f Hlookup].
  destruct (gtnflem2_reachable_ell_source_some_in
    supply target f Hlookup) as [i [Hin Hlabel]].
  rewrite Hlabel.
  eapply gtnf_supply_expr_label_not_in_original_env.
  - exists i.
    eapply gtnflem2_reachable_states_in_supply.
    exact Hin.
  - exact HE.
Qed.

Lemma gtnf_initial_no_goto_reachable_expr_label_source_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  no_goto_expr e (gtnf_reachable_expr_label_source_env supply).
Proof.
  unfold no_goto_expr, label_in_dom,
    gtnf_reachable_expr_label_source_env, mk_environment.
  intros target [f Hlookup].
  destruct (gtnflem2_reachable_ell_source_some_in
    supply target f Hlookup) as [i [Hin Hlabel]].
  rewrite Hlabel.
  eapply gtnf_supply_expr_label_not_in_original_expr.
  exists i.
  eapply gtnflem2_reachable_states_in_supply.
  exact Hin.
Qed.

Lemma original_initial_to_gtnf_source_with_reachable_expr_labels_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  E |- e == e -| gtnf_source_with_reachable_expr_labels_env supply.
Proof.
  unfold gtnf_source_with_reachable_expr_labels_env.
  apply EqSym.
  apply EqC3.
  intros l Hl.
  split.
  - intros k body Hbody.
    eapply gtnf_original_no_goto_reachable_expr_label_source_env; eauto.
  - eapply gtnf_initial_no_goto_reachable_expr_label_source_env.
    exact Hl.
Qed.

Lemma gtnf_source_with_reachable_expr_labels_env_bound_original_or_expr
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (l : Label)
  (body : CFGKATExpression)
  :
  gtnf_source_with_reachable_expr_labels_env supply l = Some body ->
  (E l = Some body) \/
  (E l = None /\
    exists i,
      In (body, i) (gtnflem2_reachable_states supply) /\
      gtnf_supply_expr_label E e supply body = l).
Proof.
  intro Hsource.
  unfold gtnf_source_with_reachable_expr_labels_env, label_env_cup,
    gtnf_reachable_expr_label_source_env, mk_environment in Hsource.
  simpl in Hsource.
  destruct (E l) as [original |] eqn:HE.
  - injection Hsource as <-.
    left. reflexivity.
  - right.
    split; [reflexivity |].
    destruct (gtnflem2_reachable_ell_source supply l)
      as [source |] eqn:Hlookup;
      [| discriminate Hsource].
    injection Hsource as <-.
    destruct (gtnflem2_reachable_ell_source_some_in
      supply l source Hlookup) as [i [Hin Hlabel]].
    exists i.
    split.
    + exact Hin.
    + symmetry. exact Hlabel.
Qed.

Lemma gtnf_source_with_reachable_expr_labels_env_finite_to_original
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (source : CFGKATSyntConfiguration)
  (a : Atom)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  gtnflem2_reachable_state (E := E) (e := e) source ->
  ResolveCFGKATAutomatonFiniteDynamics
    CFGKATExpressionAutomaton
    (CFGKATExpressionDynamics source)
    (lift (gtnf_source_with_reachable_expr_labels_env supply)) a r ->
  ResolveCFGKATAutomatonFiniteDynamics
    CFGKATExpressionAutomaton
    (CFGKATExpressionDynamics source)
    (lift E) a r.
Proof.
  intros Hsource Hfin.
  revert Hsource.
  dependent induction Hfin generalizing source; intro Hsource.
  - apply ResolveCFGKATAutomatonFiniteDynamicsDirect.
    + exact H.
    + destruct r as [|i_accept|i_break|i_continue| |l_jump i_jump|p s];
        simpl in *; try exact I.
      destruct (E l_jump) as [body |] eqn:HE; [| reflexivity].
      unfold gtnf_source_with_reachable_expr_labels_env, label_env_cup,
        mk_environment in H0.
      discriminate H0.
  - rewrite lift_lookup in H0.
    destruct (gtnf_source_with_reachable_expr_labels_env supply l)
      as [body |] eqn:Hsource_l;
      simpl in H0; [| discriminate H0].
    injection H0 as <-.
    destruct (gtnf_source_with_reachable_expr_labels_env_bound_original_or_expr
      supply l body Hsource_l)
      as [HEbody | [HEnone [body_i [Hbody_in Hlabel]]]].
    + eapply ResolveCFGKATAutomatonFiniteDynamicsBoundJump.
      * exact H.
      * apply lift_label_some. exact HEbody.
      * eapply IHHfin.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- eapply gtnflem2_reachable_original.
           exact HEbody.
    + exfalso.
      destruct source as [g source_i].
      rewrite <- Hlabel in H.
      eapply supply_expr_label_no_raw_jump.
      * exists body_i.
        eapply gtnflem2_reachable_states_in_supply.
        exact Hbody_in.
      * eapply gtnflem2_reachable_state_in_supply.
        exact Hsource.
      * exact H.
Qed.

Lemma gtnf_original_finite_to_source_with_reachable_expr_labels_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (source : CFGKATSyntConfiguration)
  (a : Atom)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  gtnflem2_reachable_state (E := E) (e := e) source ->
  ResolveCFGKATAutomatonFiniteDynamics
    CFGKATExpressionAutomaton
    (CFGKATExpressionDynamics source)
    (lift E) a r ->
  ResolveCFGKATAutomatonFiniteDynamics
    CFGKATExpressionAutomaton
    (CFGKATExpressionDynamics source)
    (lift (gtnf_source_with_reachable_expr_labels_env supply)) a r.
Proof.
  intros Hsource Hfin.
  revert Hsource.
  dependent induction Hfin generalizing source; intro Hsource.
  - apply ResolveCFGKATAutomatonFiniteDynamicsDirect.
    + exact H.
    + destruct r as [|i_accept|i_break|i_continue| |l_jump i_jump|p s];
        simpl in *; try exact I.
      unfold gtnf_source_with_reachable_expr_labels_env, label_env_cup,
        gtnf_reachable_expr_label_source_env, mk_environment in *.
      destruct (E l_jump) as [body |] eqn:HE; [discriminate H0 |].
      destruct (gtnflem2_reachable_ell_source supply l_jump)
        as [f |] eqn:Hlookup; [| reflexivity].
      destruct (gtnflem2_reachable_ell_source_some_in
        supply l_jump f Hlookup) as [f_i [Hf_in Hlabel]].
      destruct source as [g source_i].
      rewrite Hlabel in H.
      exfalso.
      eapply supply_expr_label_no_raw_jump.
      * exists f_i.
        eapply gtnflem2_reachable_states_in_supply.
        exact Hf_in.
      * eapply gtnflem2_reachable_state_in_supply.
        exact Hsource.
      * exact H.
  - eapply ResolveCFGKATAutomatonFiniteDynamicsBoundJump.
    + exact H.
    + rewrite lift_lookup.
      rewrite lift_lookup in H0.
      unfold gtnf_source_with_reachable_expr_labels_env,
        label_env_cup, mk_environment in *.
      simpl in *.
      destruct (E l) as [body |] eqn:HE; [| discriminate H0].
      injection H0 as <-.
      reflexivity.
    + rewrite lift_lookup in H0.
      destruct (E l) as [body |] eqn:HE; [| discriminate H0].
      injection H0 as <-.
      eapply IHHfin.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * eapply gtnflem2_reachable_original.
        exact HE.
Qed.

Lemma gtnf_source_with_reachable_expr_labels_env_resolution_dynamics_iff
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (source : CFGKATSyntConfiguration)
  (a : Atom)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  gtnflem2_reachable_state (E := E) (e := e) source ->
  ResolveCFGKATAutomatonDynamics
    CFGKATExpressionAutomaton
    (CFGKATExpressionDynamics source)
    (lift (gtnf_source_with_reachable_expr_labels_env supply)) a r <->
  ResolveCFGKATAutomatonDynamics
    CFGKATExpressionAutomaton
    (CFGKATExpressionDynamics source)
    (lift E) a r.
Proof.
  intro Hsource.
  split.
  - intro Hres.
    inversion Hres as [a0 zeta Hfin | a0 Hnone]; subst.
    + apply ResolveCFGKATAutomatonDynamicsFinite.
      eapply gtnf_source_with_reachable_expr_labels_env_finite_to_original; eauto.
    + apply ResolveCFGKATAutomatonDynamicsDefaultReject.
      intros r0 Hfin_E.
      apply (Hnone r0).
      eapply gtnf_original_finite_to_source_with_reachable_expr_labels_env; eauto.
  - intro Hres.
    inversion Hres as [a0 zeta Hfin | a0 Hnone]; subst.
    + apply ResolveCFGKATAutomatonDynamicsFinite.
      eapply gtnf_original_finite_to_source_with_reachable_expr_labels_env; eauto.
    + apply ResolveCFGKATAutomatonDynamicsDefaultReject.
      intros r0 Hfin_source.
      apply (Hnone r0).
      eapply gtnf_source_with_reachable_expr_labels_env_finite_to_original; eauto.
Qed.

Lemma gtnf_source_with_reachable_expr_labels_env_resolved_transition_output
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (f : CFGKATExpression)
  (i : IndicatorAssignment)
  (a : Atom)
  :
  gtnflem2_reachable_state (E := E) (e := e) (f, i) ->
  resolved_transition_output (gtnf_source_with_reachable_expr_labels_env supply) f a i =
  resolved_transition_output E f a i.
Proof.
  intro Hreach.
  apply resolved_transition_output_unique.
  apply (proj2
    (gtnf_source_with_reachable_expr_labels_env_resolution_dynamics_iff
      supply (f, i) a
      (resolved_transition_output E f a i) Hreach)).
  exact (resolved_transition_output_spec E f a i).
Qed.

Definition gtnf_resolved_source_with_reachable_expr_labels_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  : label_environment CFGKATExpression :=
  resolved_env (gtnf_source_with_reachable_expr_labels_env supply).

Lemma gtnf_resolved_source_with_reachable_expr_labels_expr_to_goto
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (f : CFGKATExpression)
  (i : IndicatorAssignment)
  :
  In (f, i) (gtnflem2_reachable_states supply) ->
  gtnf_resolved_source_with_reachable_expr_labels_env supply |- f ==
    goto (gtnf_supply_expr_label E e supply f) -|
    gtnf_resolved_source_with_reachable_expr_labels_env supply.
Proof.
  intro Hin.
  set (S := gtnf_source_with_reachable_expr_labels_env supply).
  set (R := gtnf_resolved_source_with_reachable_expr_labels_env supply).
  change R with (resolved_env S).
  cfgkat_rewrite <- (gtnflem1 S f).
  cfgkat_rewrite <- (unfold_bound_goto S
    (gtnf_supply_expr_label E e supply f) f
    (gtnf_source_with_reachable_expr_labels_env_lookup_expr
      supply f i Hin)) at 1.
  apply gtnflem1.
Qed.

Lemma sys_to_sysc_in_resolved_source_with_reachable_expr_labels
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (r : CFGKATAutomatonOutputs CFGKATSyntConfiguration)
  :
  (forall p f i,
    r = CFGKATAutomatonNext p (f, i) ->
    In (f, i) (gtnflem2_reachable_states supply)) ->
  gtnf_resolved_source_with_reachable_expr_labels_env supply |- sys r == sysc supply r -|
    gtnf_resolved_source_with_reachable_expr_labels_env supply.
Proof.
  intro Hnext.
  destruct r as
    [|i_accept|i_break|i_continue| |l_jump i_jump|p [f i_next]];
    simpl; try apply EqRefl.
  assert (Hin : In (f, i_next) (gtnflem2_reachable_states supply)).
  { apply Hnext with (p := p). reflexivity. }
  eapply EqSeqRightCong.
  - apply gtnf_resolved_source_with_reachable_expr_labels_expr_to_goto with (i := i_next).
    exact Hin.
  - apply EqRefl.
Qed.

Lemma resolved_source_with_reachable_expr_labels_body_to_gtnflem2_body
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (f : CFGKATExpression)
  :
  (exists i,
    gtnflem2_reachable_state (E := E) (e := e) (f, i)) ->
  gtnf_resolved_source_with_reachable_expr_labels_env supply |-
    resolved_body (gtnf_source_with_reachable_expr_labels_env supply) f ==
    gtnflem2_state_body supply f -|
    gtnf_resolved_source_with_reachable_expr_labels_env supply.
Proof.
  intros [i0 Hreach0].
  unfold resolved_body, resolved_branch, gtnflem2_state_body.
  apply guarded_sum_all_cong_ctx.
  intros m _.
  rewrite gtnf_source_with_reachable_expr_labels_env_resolved_transition_output.
  - apply sys_to_sysc_in_resolved_source_with_reachable_expr_labels.
    intros p g j Hnext.
    apply gtnflem2_reachable_states_contains.
    eapply gtnflem2_reachable_next.
    + eapply gtnflem2_reachable_assignment.
      exact Hreach0.
    + exact Hnext.
  - eapply gtnflem2_reachable_assignment.
    exact Hreach0.
Qed.

Lemma gtnflem2_env_same_domain_as_resolved_source_with_reachable_expr_labels
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  C7_same_domain (gtnflem2_env supply)
    (gtnf_resolved_source_with_reachable_expr_labels_env supply).
Proof.
  unfold C7_same_domain, label_in_dom.
  intro l.
  split.
  - intros [body Hbody].
    unfold gtnflem2_env, mk_environment in Hbody.
    simpl in Hbody.
    destruct (E l) as [source |] eqn:HE.
    + injection Hbody as <-.
      exists (resolved_body (gtnf_source_with_reachable_expr_labels_env supply) source).
      unfold gtnf_resolved_source_with_reachable_expr_labels_env, resolved_env,
        environment_map_values, gtnf_source_with_reachable_expr_labels_env,
        label_env_cup, mk_environment.
      simpl.
      rewrite HE.
      reflexivity.
    + destruct (gtnflem2_reachable_ell_source supply l)
        as [source |] eqn:Hexpr;
        [| discriminate Hbody].
      injection Hbody as <-.
      exists (resolved_body (gtnf_source_with_reachable_expr_labels_env supply) source).
      unfold gtnf_resolved_source_with_reachable_expr_labels_env, resolved_env,
        environment_map_values, gtnf_source_with_reachable_expr_labels_env,
        label_env_cup, gtnf_reachable_expr_label_source_env,
        mk_environment.
      simpl.
      rewrite HE.
      rewrite Hexpr.
      reflexivity.
  - intros [body Hbody].
    unfold gtnf_resolved_source_with_reachable_expr_labels_env, resolved_env,
      environment_map_values, gtnf_source_with_reachable_expr_labels_env,
      label_env_cup, gtnf_reachable_expr_label_source_env,
      mk_environment in Hbody.
    simpl in Hbody.
    destruct (E l) as [source |] eqn:HE.
    + exists (gtnflem2_state_body supply source).
      unfold gtnflem2_env, mk_environment.
      simpl.
      rewrite HE.
      reflexivity.
    + destruct (gtnflem2_reachable_ell_source supply l)
        as [source |] eqn:Hexpr.
      * exists (gtnflem2_state_body supply source).
        unfold gtnflem2_env, mk_environment.
        simpl.
        rewrite HE.
        rewrite Hexpr.
        reflexivity.
      * discriminate Hbody.
Qed.

Lemma gtnflem2_env_guarded_direct
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  C7_guarded (gtnflem2_env supply).
Proof.
  unfold C7_guarded.
  intros l target body target_body Hbody Htarget_body.
  unfold guarded.
  intros a i j.
  unfold gtnflem2_env, mk_environment in Hbody, Htarget_body.
  simpl in Hbody, Htarget_body.
  destruct (E target) as [original_target |] eqn:HEtarget.
  - destruct (E l) as [original |] eqn:HEl.
    + injection Hbody as <-.
      eapply gtnflem2_state_body_no_original_jump.
      exact HEtarget.
    + destruct (gtnflem2_reachable_ell_source supply l)
        as [source |] eqn:Hsource;
        [| discriminate Hbody].
      injection Hbody as <-.
      eapply gtnflem2_state_body_no_original_jump.
      exact HEtarget.
  - destruct (gtnflem2_reachable_ell_source supply target)
      as [target_expr |] eqn:Htarget;
      [| discriminate Htarget_body].
    destruct (gtnflem2_reachable_ell_source_some_in
      supply target target_expr Htarget) as [target_i [Htarget_in Htarget_label]].
    rewrite Htarget_label.
    destruct (E l) as [original |] eqn:HEl.
    + injection Hbody as <-.
      eapply gtnflem2_state_body_no_supply_expr_label_jump.
      * exists target_i.
        eapply gtnflem2_reachable_states_in_supply.
        exact Htarget_in.
      * exists i.
        eapply gtnf_supply_original.
        exact HEl.
    + destruct (gtnflem2_reachable_ell_source supply l)
        as [source |] eqn:Hsource;
        [| discriminate Hbody].
      injection Hbody as <-.
      destruct (gtnflem2_reachable_ell_source_some_in
        supply l source Hsource) as [source_i [Hsource_in _]].
      eapply gtnflem2_state_body_no_supply_expr_label_jump.
      * exists target_i.
        eapply gtnflem2_reachable_states_in_supply.
        exact Htarget_in.
      * exists source_i.
        eapply gtnflem2_reachable_states_in_supply.
        exact Hsource_in.
Qed.

Lemma gtnflem2_env_solution_in_resolved_source_with_reachable_expr_labels
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  :
  C7_solution (gtnflem2_env supply)
    (gtnf_resolved_source_with_reachable_expr_labels_env supply).
Proof.
  unfold C7_solution.
  intros l body Hbody.
  unfold gtnflem2_env, mk_environment in Hbody.
  simpl in Hbody.
  destruct (E l) as [source |] eqn:HE.
  - injection Hbody as <-.
    cfgkat_rewrite (unfold_bound_goto
      (gtnf_resolved_source_with_reachable_expr_labels_env supply) l
      (resolved_body (gtnf_source_with_reachable_expr_labels_env supply) source)
      ltac:(unfold gtnf_resolved_source_with_reachable_expr_labels_env,
        resolved_env, environment_map_values,
        gtnf_source_with_reachable_expr_labels_env, label_env_cup,
        mk_environment;
        simpl;
        rewrite HE;
        reflexivity)).
    apply resolved_source_with_reachable_expr_labels_body_to_gtnflem2_body.
    exists indicator_assignment_witness.
    eapply gtnflem2_reachable_original.
    exact HE.
  - destruct (gtnflem2_reachable_ell_source supply l)
      as [source |] eqn:Hexpr;
      [| discriminate Hbody].
    injection Hbody as <-.
    cfgkat_rewrite (unfold_bound_goto
      (gtnf_resolved_source_with_reachable_expr_labels_env supply) l
      (resolved_body (gtnf_source_with_reachable_expr_labels_env supply) source)
      ltac:(unfold gtnf_resolved_source_with_reachable_expr_labels_env,
        resolved_env, environment_map_values,
        gtnf_source_with_reachable_expr_labels_env, label_env_cup,
        gtnf_reachable_expr_label_source_env, mk_environment;
        simpl;
        rewrite HE;
        rewrite Hexpr;
        reflexivity)).
    apply resolved_source_with_reachable_expr_labels_body_to_gtnflem2_body.
    destruct (gtnflem2_reachable_ell_source_some_in
      supply l source Hexpr) as [i [Hin _]].
    exists i.
    eapply gtnflem2_reachable_states_in_reachable.
    exact Hin.
Qed.

Lemma gtnf_resolved_source_with_reachable_expr_labels_to_gtnflem2_env
  {E : label_environment CFGKATExpression}
  {e : CFGKATExpression}
  (supply : gtnf_label_supply E e)
  (x : CFGKATExpression)
  :
  gtnf_resolved_source_with_reachable_expr_labels_env supply |- x == x -|
    gtnflem2_env supply.
Proof.
  apply EqC7_from_side_condition.
  split.
  - apply gtnflem2_env_same_domain_as_resolved_source_with_reachable_expr_labels.
  - split.
    + apply gtnflem2_env_solution_in_resolved_source_with_reachable_expr_labels.
    + apply gtnflem2_env_guarded_direct.
Qed.

Definition canonical_gtnflem2_env
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  : label_environment CFGKATExpression :=
  gtnflem2_env
    (canonical_gtnf_supply (E := E) (e := e)).

Definition gtnflem2_ell
  (E : label_environment CFGKATExpression)
  (e f : CFGKATExpression)
  : Label :=
  gtnf_supply_expr_label E e
    (canonical_gtnf_supply (E := E) (e := e)) f.

Theorem gtnflem2
  (E : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  :
  let E' := canonical_gtnflem2_env E e in
  (E |- e == e -| E') /\
  (E' |- e == goto (gtnflem2_ell E e e) -| E').
Proof.
  unfold canonical_gtnflem2_env, gtnflem2_ell.
  set (supply := canonical_gtnf_supply (E := E) (e := e)).
  split.
  - cfgkat_rewrite (original_initial_to_gtnf_source_with_reachable_expr_labels_env supply).
    cfgkat_rewrite
      (gtnflem1 (gtnf_source_with_reachable_expr_labels_env supply) e).
    apply gtnf_resolved_source_with_reachable_expr_labels_to_gtnflem2_env.
  - set (i0 := indicator_assignment_witness).
    assert (Hin0 : In (e, i0) (gtnflem2_reachable_states supply)).
    {
      apply gtnflem2_reachable_states_contains.
      apply gtnflem2_reachable_initial.
    }
    cfgkat_rewrite <-
      (gtnf_resolved_source_with_reachable_expr_labels_to_gtnflem2_env supply e).
    cfgkat_rewrite
      (gtnf_resolved_source_with_reachable_expr_labels_expr_to_goto supply e i0 Hin0)
      at 1.
    apply gtnf_resolved_source_with_reachable_expr_labels_to_gtnflem2_env.
Qed.
