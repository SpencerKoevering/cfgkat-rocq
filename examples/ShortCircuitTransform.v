From CFGKAT.Examples Require Export UsefulFacts.
From Stdlib Require Import Lists.List.
Import ListNotations.

Local Open Scope cfgkat_scope.
Local Open Scope cfgkat_setoid_scope.

Local Ltac cfgkat_reflexivity :=
  try cfgkat_change_preferred_equiv;
  try cfgkat_change_contextual_equiv;
  reflexivity.

Local Ltac label_cases :=
  cbn in *;
  repeat match goal with
  | H : context[Label_eq_dec ?x ?y] |- _ =>
      destruct (Label_eq_dec x y); subst; cbn in *; try congruence
  | |- context[Label_eq_dec ?x ?y] =>
      destruct (Label_eq_dec x y); subst; cbn in *; try congruence
  end;
  try reflexivity; try congruence; simpl in *; intuition congruence.


Definition short_circuit_algorithm1
  (a b c : CFGKATTest) (e f : CFGKATProgramSyntax) :=
  (if (a and b) or c then e else f)%cfgkat_program.

Definition short_circuit_algorithm2
  (ell k : Label) (a b c : CFGKATTest) (e f : CFGKATProgramSyntax) :=
  (if a then
    (if b then plabel ell ;; e
     else plabel k ;; (if c then pgoto ell else f))
   else pgoto k)%cfgkat_program.

Definition short_circuit_source
  (a b c : CFGKATTest) (e f : CFGKATExpression) :=
  if (a and b) or c then e else f.

Definition short_circuit_bound_tail
  (ell : Label) (c : CFGKATTest) (f : CFGKATExpression) :=
  if c then goto ell else f.

Definition short_circuit_target
  (ell k : Label) (a b c : CFGKATTest) (e f : CFGKATExpression) :=
  if a then
    (if b then 1 ;; e else 1 ;; short_circuit_bound_tail ell c f)
  else goto k.

Definition short_circuit_extracted_context
  (e f : CFGKATProgramSyntax)
  (Hdisj :
    label_disjoint
      (label_extraction_syntax_environment e)
      (label_extraction_syntax_environment f))
  : label_environment CFGKATExpression :=
  @label_env_cup
    (label_extraction_syntax_environment e)
    (label_extraction_syntax_environment f)
    Hdisj.

Definition short_circuit_generated_context
  (ell k : Label) (c : CFGKATTest) (e f : CFGKATExpression)
  : label_environment CFGKATExpression.
Proof.
  refine
    (mk_environment
      (fun l =>
        match Label_eq_dec l ell with
        | left _ => Some (1 ;; e)
        | right _ =>
            match Label_eq_dec l k with
            | left _ => Some (1 ;; short_circuit_bound_tail ell c f)
            | right _ => None
            end
        end)
      [ell; k]
      _).
  intros l body Hlookup.
  label_cases.
Defined.

Definition short_circuit_fresh_label (l : Label) (p : CFGKATProgramSyntax) :=
  ~ program_label_occurs l p /\ ~ program_contains_goto l p.

Local Lemma short_circuit_generated_dom
  (ell k l : Label) (c : CFGKATTest) (e f : CFGKATExpression) :
  ell <> k ->
  label_in_dom (short_circuit_generated_context ell k c e f) l ->
  l = ell \/ l = k.
Proof.
  intros Hneq [body Hbody].
  unfold short_circuit_generated_context, mk_environment in Hbody.
  label_cases.
Qed.

Local Lemma short_circuit_extracted_lookup_no_goto (e f : CFGKATProgramSyntax)
  (Hdisj :
    label_disjoint
      (label_extraction_syntax_environment e)
      (label_extraction_syntax_environment f))
  (l k : Label) (body : CFGKATExpression) :
  ~ program_contains_goto l e ->
  ~ program_contains_goto l f ->
  short_circuit_extracted_context e f Hdisj k = Some body ->
  ~ contains_goto l body.
Proof.
  intros Hno_e Hno_f Hlookup Hcontains.
  unfold short_circuit_extracted_context, label_env_cup,
    label_extraction_syntax_environment, mk_environment in Hlookup.
  cbn in Hlookup.
  destruct (label_extraction_syntax e k) eqn:He.
  - cbn in Hlookup.
    inversion Hlookup; subst.
    apply Hno_e; eapply label_extraction_contains_goto; eauto.
  - apply Hno_f; eapply label_extraction_contains_goto; eauto.
Qed.

Local Lemma short_circuit_context_disjoint
  (ell k : Label) (c : CFGKATTest) (e f : CFGKATProgramSyntax)
  (Hef_disj :
    label_disjoint
      (label_extraction_syntax_environment e)
      (label_extraction_syntax_environment f))
  :
  ell <> k ->
  short_circuit_fresh_label ell e ->
  short_circuit_fresh_label ell f ->
  short_circuit_fresh_label k e ->
  short_circuit_fresh_label k f ->
  label_disjoint
    (short_circuit_extracted_context e f Hef_disj)
    (short_circuit_generated_context ell k c (label_erase e) (label_erase f)).
Proof.
  intros Hneq [Hell_e _] [Hell_f _] [Hk_e _] [Hk_f _].
  intros l [body Hambient] Hgenerated.
  apply (short_circuit_generated_dom
    ell k l c (label_erase e) (label_erase f) Hneq) in Hgenerated.
  unfold short_circuit_extracted_context, label_env_cup,
    mk_environment in Hambient.
  cbn in Hambient.
  destruct Hgenerated as [-> | ->];
    repeat rewrite label_extraction_not_occurs_none in Hambient by assumption;
    discriminate.
Qed.

Local Lemma short_circuit_algorithm1_context
  (a b c : CFGKATTest) (e f : CFGKATProgramSyntax)
  (Hef_disj :
    label_disjoint
      (label_extraction_syntax_environment e)
      (label_extraction_syntax_environment f))
  :
  label_extraction_syntax_environment
    (short_circuit_algorithm1 a b c e f) =
  short_circuit_extracted_context e f Hef_disj.
Proof.
  apply environment_eq.
  intro l.
  unfold short_circuit_algorithm1, short_circuit_extracted_context,
    label_extraction_syntax_environment, label_env_cup, mk_environment.
  cbn.
  destruct (label_extraction_syntax e l); reflexivity.
Qed.

Local Lemma short_circuit_algorithm2_context
  (ell k : Label) (a b c : CFGKATTest) (e f : CFGKATProgramSyntax)
  (Hef_disj :
    label_disjoint
      (label_extraction_syntax_environment e)
      (label_extraction_syntax_environment f))
  (Hneq : ell <> k)
  (Hell_e : short_circuit_fresh_label ell e)
  (Hell_f : short_circuit_fresh_label ell f)
  (Hk_e : short_circuit_fresh_label k e)
  (Hk_f : short_circuit_fresh_label k f)
  :
  label_extraction_syntax_environment
    (short_circuit_algorithm2 ell k a b c e f) =
  @label_env_cup
    (short_circuit_extracted_context e f Hef_disj)
    (short_circuit_generated_context ell k c (label_erase e) (label_erase f))
    (short_circuit_context_disjoint
      ell k c e f Hef_disj Hneq Hell_e Hell_f Hk_e Hk_f).
Proof.
  apply environment_eq.
  intro l.
  unfold short_circuit_algorithm2, short_circuit_extracted_context,
    short_circuit_generated_context, short_circuit_bound_tail,
    label_extraction_syntax_environment, label_env_cup, mk_environment.
  destruct Hell_e as [Hell_e _].
  destruct Hell_f as [Hell_f _].
  destruct Hk_e as [Hk_e _].
  destruct Hk_f as [Hk_f _].
  cbn.
  destruct (Label_eq_dec ell l) as [Hell_l | Hnell_l].
  - subst l.
    rewrite (label_extraction_not_occurs_none e ell Hell_e).
    rewrite (label_extraction_not_occurs_none f ell Hell_f).
    label_cases.
  - destruct (label_extraction_syntax e l).
    + label_cases.
    + destruct (Label_eq_dec k l) as [Hk_l | Hnk_l].
      * subst l.
        rewrite (label_extraction_not_occurs_none f k Hk_f).
        label_cases.
      * destruct (label_extraction_syntax f l); label_cases.
Qed.

Local Lemma short_circuit_tail_to_prefixed_bound
  (E : label_environment CFGKATExpression)
  (ell : Label) (c : CFGKATTest) (e f : CFGKATExpression) :
  E ell = Some (1 ;; e) ->
  E |- (if c then e else f) ==
    1 ;; short_circuit_bound_tail ell c f -| E.
Proof.
  intro Hell.
  unfold short_circuit_bound_tail.
  cfgkat_rewrite <- (weaken_empty_to_env E (1 ;; e) e (EqS3 e)).
  cfgkat_rewrite <- (unfold_bound_goto E ell (1 ;; e) Hell).
  cfgkat_rewrite (weaken_empty_to_env E
    (1 ;; (if c then goto ell else f))
    (if c then goto ell else f)
    (EqS3 (if c then goto ell else f))).
  cfgkat_reflexivity.
Qed.

Local Lemma short_circuit_normal_to_target
  (E : label_environment CFGKATExpression)
  (ell k : Label) (a b c : CFGKATTest) (e f : CFGKATExpression) :
  E ell = Some (1 ;; e) ->
  E k = Some (1 ;; short_circuit_bound_tail ell c f) ->
  E |-
    (if a then (if b then e else (if c then e else f))
     else (if c then e else f)) ==
    short_circuit_target ell k a b c e f -| E.
Proof.
  intros Hell Hk.
  unfold short_circuit_target.
  apply EqChoiceCong.
  - apply EqChoiceCong.
    + try cfgkat_change_preferred_equiv.
      cfgkat_rewrite (weaken_empty_to_env E (1 ;; e) e (EqS3 e)).
      cfgkat_reflexivity.
    + apply short_circuit_tail_to_prefixed_bound.
      exact Hell.
  - cfgkat_rewrite (short_circuit_tail_to_prefixed_bound
      E ell c e f Hell).
    cfgkat_rewrite <- (unfold_bound_goto
      E k (1 ;; short_circuit_bound_tail ell c f) Hk).
    cfgkat_reflexivity.
Qed.

Local Lemma short_circuit_source_redundant
  (ell k : Label) (a b c : CFGKATTest) (e f : CFGKATProgramSyntax)
  (Hef_disj :
    label_disjoint
      (label_extraction_syntax_environment e)
      (label_extraction_syntax_environment f))
  (Hgenerated_disj :
    label_disjoint
      (short_circuit_extracted_context e f Hef_disj)
      (short_circuit_generated_context ell k c (label_erase e) (label_erase f)))
  :
  ell <> k ->
  short_circuit_fresh_label ell e ->
  short_circuit_fresh_label ell f ->
  short_circuit_fresh_label k e ->
  short_circuit_fresh_label k f ->
  short_circuit_extracted_context e f Hef_disj |-
    short_circuit_source a b c (label_erase e) (label_erase f) ==
    short_circuit_source a b c (label_erase e) (label_erase f) -|
      @label_env_cup
        (short_circuit_extracted_context e f Hef_disj)
        (short_circuit_generated_context ell k c (label_erase e) (label_erase f))
        Hgenerated_disj.
Proof.
  intros Hneq Hell_e Hell_f Hk_e Hk_f.
  apply EqSym.
  apply EqC3.
  intros l Hdom.
  apply (short_circuit_generated_dom
    ell k l c (label_erase e) (label_erase f) Hneq) in Hdom.
  destruct Hell_e as [_ Hell_e], Hell_f as [_ Hell_f],
    Hk_e as [_ Hk_e], Hk_f as [_ Hk_f].
  destruct Hdom as [-> | ->]; split; eauto using
    short_circuit_extracted_lookup_no_goto;
    unfold short_circuit_source; simpl;
    firstorder eauto using program_contains_goto_erase.
Qed.

Theorem short_circuit_transform
  (ell k : Label)
  (a b c : CFGKATTest)
  (e f : CFGKATProgramSyntax)
  (Hef_disj :
    label_disjoint
      (label_extraction_syntax_environment e)
      (label_extraction_syntax_environment f))
  :
  forall
    (Hneq : ell <> k)
    (Hell_e : short_circuit_fresh_label ell e)
    (Hell_f : short_circuit_fresh_label ell f)
    (Hk_e : short_circuit_fresh_label k e)
    (Hk_f : short_circuit_fresh_label k f),
  let P := short_circuit_algorithm1 a b c e f in
  let Q := short_circuit_algorithm2 ell k a b c e f in
  label_extraction_syntax_environment P |-
    label_erase P == label_erase Q -|
    label_extraction_syntax_environment Q.
Proof.
  intros Hneq Hell_e Hell_f Hk_e Hk_f.
  change (label_extraction_syntax_environment
      (short_circuit_algorithm1 a b c e f) |-
    label_erase (short_circuit_algorithm1 a b c e f) ==
    label_erase (short_circuit_algorithm2 ell k a b c e f) -|
    label_extraction_syntax_environment
      (short_circuit_algorithm2 ell k a b c e f)).
  rewrite (short_circuit_algorithm1_context a b c e f Hef_disj).
  rewrite (short_circuit_algorithm2_context
    ell k a b c e f Hef_disj Hneq Hell_e Hell_f Hk_e Hk_f).
  pose proof (short_circuit_context_disjoint
    ell k c e f Hef_disj Hneq Hell_e Hell_f Hk_e Hk_f)
    as Hgenerated_disj.
  set (Target :=
    @label_env_cup
      (short_circuit_extracted_context e f Hef_disj)
      (short_circuit_generated_context ell k c (label_erase e) (label_erase f))
      Hgenerated_disj).
  change (short_circuit_extracted_context e f Hef_disj |-
    short_circuit_source a b c (label_erase e) (label_erase f) ==
    short_circuit_target ell k a b c (label_erase e) (label_erase f) -| Target).
  cfgkat_rewrite (short_circuit_source_redundant
    ell k a b c e f Hef_disj Hgenerated_disj
    Hneq Hell_e Hell_f Hk_e Hk_f).
  assert (Hsplit :
    short_circuit_source a b c (label_erase e) (label_erase f) ==
    if a then (if b then label_erase e else
      (if c then label_erase e else label_erase f))
    else (if c then label_erase e else label_erase f)).
  {
    unfold short_circuit_source.
    cfgkat_rewrite <- (EqG1 (label_erase e) (a and b)) at 1.
    cfgkat_rewrite <- (antiskewcom
      (TAnd a b) c (label_erase e) (label_erase e) (label_erase f)).
    cfgkat_rewrite EqG3.
    cfgkat_rewrite EqG1.
    cfgkat_reflexivity.
  }
  cfgkat_rewrite (weaken_empty_to_env Target
    _ _ Hsplit).
  apply short_circuit_normal_to_target; apply label_env_cup_right.
  - unfold short_circuit_generated_context, mk_environment; label_cases.
  - unfold short_circuit_generated_context, mk_environment; label_cases.
Qed.
