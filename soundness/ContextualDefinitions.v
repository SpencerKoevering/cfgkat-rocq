From CFGKAT.Soundness Require Export CongruenceLaws.
From Stdlib Require Import Lists.List.
Import ListNotations.

Local Open Scope type_scope.
Local Open Scope cfgkat_scope.

Definition label_in_dom
  (E : label_environment CFGKATExpression)
  (l : Label)
  : Prop :=
  exists e, E l = Some e.

Definition label_disjoint
  (E F : label_environment CFGKATExpression)
  : Prop :=
  forall l,
    label_in_dom E l ->
    label_in_dom F l ->
    False.

Existing Class label_disjoint.

Local Unset Program Cases.

Program Definition label_env_cup
  (E F : label_environment CFGKATExpression)
  `{label_disjoint E F}
  : label_environment CFGKATExpression
:= {| env_lookup l :=  match E l with
                       | Some e => Some e
                       | None => F l
                       end |}.
Next Obligation.
  simpl. intros E1 E2 Hdisjoint.
  exists (env_support E1 ++ env_support E2).
  intros l v. destruct (E1 l) eqn:?; intros.
  - apply in_or_app. left.
    eapply env_supported; eauto.
  - apply in_or_app. right.
    eapply env_supported; eauto.
Qed.

Notation "E '+' F" :=
  (label_env_cup E F)
  (at level 50, left associativity) : cfgkat_scope.

#[export] Instance label_disjoint_empty_l
  (E : label_environment CFGKATExpression)
  : label_disjoint empty_label_context E.
Proof.
  intros l [body Hbody].
  discriminate.
Qed.

Lemma label_env_cup_right
  (E F : label_environment CFGKATExpression)
  `{label_disjoint E F}
  (l : Label)
  (body : CFGKATExpression)
  :
  F l = Some body ->
  (E + F) l = Some body.
Proof.
  intro HF. simpl.
  destruct (E l) as [left_body |] eqn:HE; auto.
  exfalso. eapply H.
  - exists left_body; eauto.
  - exists body; eauto.
Qed.

Lemma label_env_cup_empty_l
  (E : label_environment CFGKATExpression)
  :
  empty_label_context + E = E.
Proof.
  apply environment_eq.
  reflexivity.
Qed.

Fixpoint contains_goto
  (target : Label)
  (e : CFGKATExpression)
  : Prop :=
  match e with
  | CFGKATGoto l =>
      l = target
  | CFGKATChoice _ e1 e2 =>
      contains_goto target e1 \/ contains_goto target e2
  | CFGKATSequence e1 e2 =>
      contains_goto target e1 \/ contains_goto target e2
  | CFGKATLoop _ e =>
      contains_goto target e
  | CFGKATLoopSeq e1 e2 =>
      contains_goto target e1 \/ contains_goto target e2
  | _ => False
  end.

Definition no_goto_expr
  (e : CFGKATExpression)
  (E : label_environment CFGKATExpression)
  : Prop :=
  forall l,
    label_in_dom E l ->
    ~ contains_goto l e.

Definition no_goto_env
  (E F : label_environment CFGKATExpression)
  : Prop :=
  forall l e,
    E l = Some e ->
    no_goto_expr e F.

Fixpoint subst_goto
  (target : Label)
  (replacement : CFGKATExpression)
  (e : CFGKATExpression)
  : CFGKATExpression :=
  match e with
  | CFGKATAssert b =>
      test b
  | CFGKATAction p =>
      do p
  | CFGKATAssign x v =>
      assign v to x
  | CFGKATBreak =>
      break
  | CFGKATContinue =>
      continue
  | CFGKATReturn =>
      return
  | CFGKATGoto l =>
      match Label_eq_dec l target with
      | left _ => replacement
      | right _ => goto l
      end
  | CFGKATChoice b e1 e2 =>
      if b then
        subst_goto target replacement e1
      else
        subst_goto target replacement e2
  | CFGKATSequence e1 e2 =>
      subst_goto target replacement e1 ;;
      subst_goto target replacement e2
  | CFGKATLoop b e1 =>
      while b do subst_goto target replacement e1
  | CFGKATLoopSeq e1 e2 =>
      subst_goto target replacement e1 |>
      subst_goto target replacement e2
  end.

Definition Expm_r
  (l : Label)
  (e : CFGKATExpression)
  : Prop :=
  ~ contains_goto l e.

Inductive RHS
  (l : Label)
  : CFGKATExpression -> Prop :=
| RHS_goto :
    RHS l (goto l)
| RHS_no_goto :
    forall f,
      Expm_r l f ->
      RHS l f
| RHS_choice :
    forall b h f,
      RHS l h ->
      RHS l f ->
      RHS l (if b then h else f)
| RHS_sequence :
    forall g h,
      Expm_r l g ->
      RHS l h ->
      RHS l (g ;; h)
| RHS_loopseq :
    forall g h,
      Expm_r l g ->
      RHS l h ->
      RHS l (g |> h)
.

Notation "e '<[' l '<-' e1 ']>'" :=
  (subst_goto l e1 e)
  (at level 20,
   l at level 200,
   e1 at level 200).

Definition rename_goto
  (old new : Label)
  (e : CFGKATExpression)
  : CFGKATExpression :=
  subst_goto old (goto new) e.

Program Definition label_env_rename
  (E : label_environment CFGKATExpression)
  (old new : Label)
  : label_environment CFGKATExpression := {|
  env_lookup k := match Label_eq_dec k new with
                  | left _ =>
                      match E old with
                      | Some e => Some (rename_goto old new e)
                      | None => None
                      end
                  | right _ =>
                      match Label_eq_dec k old with
                      | left _ => None
                      | right _ =>
                          match E k with
                          | Some e => Some (rename_goto old new e)
                          | None => None
                          end
                      end
                  end;
|}.
Next Obligation.
  intros E old new. simpl.
  exists (new :: env_support E).
  intros k body Hlookup.
  destruct (Label_eq_dec k new) as [Hnew | Hnot_new].
  - subst. now left.
  - destruct (Label_eq_dec k old) as [Hold | Hnot_old]; try discriminate.
    destruct (E k) as [source |] eqn:HE; try discriminate.
    right. eapply env_supported; eauto.
Defined.

Notation "e '<e[' old '~>' new ']>'" :=
  (rename_goto old new e)
  (at level 20,
   old at level 200,
   new at level 200).

Notation "E '<E[' old '~>' new ']>'" :=
  (label_env_rename E old new)
  (at level 20,
   old at level 200,
   new at level 200).

Lemma label_env_rename_new
  (E : label_environment CFGKATExpression)
  (old new : Label)
  (body : CFGKATExpression)
  :
  E old = Some body ->
  (E <E[ old ~> new ]>) new = Some (rename_goto old new body).
Proof.
  intro HE. simpl.
  destruct (Label_eq_dec new new) as [_ | Hneq].
  - now rewrite HE.
  - now contradiction Hneq.
Qed.

Lemma label_env_rename_other_some
  (E : label_environment CFGKATExpression)
  (old new k : Label)
  (body : CFGKATExpression)
  :
  k <> old ->
  k <> new ->
  E k = Some body ->
  (E <E[ old ~> new ]>) k = Some (rename_goto old new body).
Proof.
  intros Hkold Hknew HE. simpl.
  destruct (Label_eq_dec k new) as [Heqnew | _].
  - contradiction.
  - destruct (Label_eq_dec k old) as [Heqold | _].
    + contradiction.
    + now rewrite HE.
Qed.

Lemma label_env_rename_other_none
  (E : label_environment CFGKATExpression)
  (old new k : Label)
  :
  k <> old ->
  k <> new ->
  E k = None ->
  (E <E[ old ~> new ]>) k = None.
Proof.
  intros Hkold Hknew HE. simpl.
  destruct (Label_eq_dec k new) as [Heqnew | _].
  - contradiction.
  - destruct (Label_eq_dec k old) as [Heqold | _].
    + contradiction.
    + now rewrite HE.
Qed.

Definition label_rename_fresh
  (E : label_environment CFGKATExpression)
  (new : Label)
  : Prop :=
  E new = None /\
  forall k e,
    E k = Some e ->
    ~ contains_goto new e.

Definition guarded
  (l : Label)
  (e : CFGKATExpression)
  : Prop :=
  forall a i j,
    ~ CFGKATExpressionDynamics (e, i) a (CFGKATAutomatonJump l j).
