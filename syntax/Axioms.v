Require Import Stdlib.Classes.RelationClasses.
Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Relations.Relation_Definitions.

From CFGKAT.Soundness Require Export ContextualDefinitions.

Local Open Scope cfgkat_scope.

Reserved Notation "E '|-' e '==' f '-|' F"
  (at level 70, e at next level, f at next level).
Reserved Notation "E '|-' e '==' f"
  (at level 70, e at next level, f at next level).
Reserved Notation "e '==' f" (at level 70).

Inductive CFGKATEquiv :
  (label_environment CFGKATExpression) ->
  CFGKATExpression ->
  CFGKATExpression ->
  (label_environment CFGKATExpression) ->
  Prop :=
| EqRefl :
    forall E e,
      E |- e == e -| E
| EqSym :
    forall E F e f,
      E |- e == f -| F ->
      F |- f == e -| E
| EqTrans :
    forall E F G e f g,
      E |- e == f -| F ->
      F |- f == g -| G ->
      E |- e == g -| G

| EqG1 :
    forall e b,
      (if b then e else e) == e
| EqG2 :
    forall e b f,
      (if b then e else f) == (if not b then f else e)
| EqG3 :
    forall e f g b c,
      (if c then (if b then e else f) else g) ==
        (if c and b then e else (if c then f else g))
| EqG4 :
    forall e f b,
      (if b then e else f) == (if b then test b ;; e else f)
| EqG5 :
    forall e f g b,
      (if b then e else f) ;; g == if b then e ;; g else f ;; g

| EqS1 :
    forall e f g,
      (e ;; f) ;; g == e ;; (f ;; g)
| EqS2 :
    forall e,
      0 ;; e == 0
| EqS3 :
    forall e,
      1 ;; e == e
| EqS4 :
    forall e,
      e ;; 1 == e
| EqS5 :
    forall b c,
      test b ;; test c == test (b and c)
| EqS6 :
    forall e,
      return ;; e == return
| EqS7 :
    forall e,
      continue ;; e == continue
| EqS8 :
    forall e,
      break ;; e == break
| EqS9 :
    forall e l,
      goto l ;; e == goto l

| EqL1 :
    forall e,
      1 |> e == e
| EqL2 :
    forall e,
      0 |> e == 0
| EqL3 :
    forall e,
      return |> e == return
| EqL4 :
    forall e l,
      goto l |> e == goto l
| EqL5 :
    forall e,
      break |> e == 1
| EqL6 :
    forall e,
      continue |> e == e
| EqL7 :
    forall p f g,
      (do p ;; f) |> g == do p ;; (f |> g)
| EqL8 :
    forall x j f g,
      (assign j to x ;; f) |> g == assign j to x ;; (f |> g)
| EqL9 :
    forall b e f g,
      (if b then e else f) |> g == if b then e |> g else f |> g
| EqL10 :
    forall e b,
      (while b do e) == (if b then e |> while b do e else 1)
| EqL11 :
    forall e b c,
      ((test (c and b) ;; e) |> test (not (c and b))) == 0 ->
      (while b do e) == (while b do (test (not c) ;; e))

| EqA1 :
    forall p x v,
      assign v to x ;; do p == do p ;; assign v to x
| EqA2 :
    forall x v,
      assign v to x ;; test x is v == assign v to x
| EqA3 :
    forall x v,
      test x is v ;; assign v to x == test x is v
| EqA4 :
    forall x v v',
      assign v' to x ;; assign v to x == assign v to x
| EqA5 :
    forall x v,
      assign v to x ;; return == return
| EqA6 :
    forall x v t e f,
      assign v to x ;; (if TPrim t then e else f) ==
        if TPrim t then assign v to x ;; e else assign v to x ;; f
| EqA7 :
    forall x v,
      assign v to x ;; 0 == 0
| EqA8 :
    forall x x' v v',
      x <> x' ->
      assign v' to x' ;; assign v to x == assign v to x ;; assign v' to x'
| EqA9 :
    forall x x' v v' e f,
      x <> x' ->
      assign v to x ;; (if x' is v' then e else f) ==
        if x' is v' then assign v to x ;; e else assign v to x ;; f

| EqC1 :
    forall E e f x l `{label_fresh E l},
      E |- e == f -| E ->
      (E ## l # x) |- e == f -| (E ## l # x)
| EqC2 :
    forall E e e1 e2 l `{label_fresh E l},
      E |- e1 == e2 -| E ->
      (E ## l # e1) |- e == e -| (E ## l # e2)
| EqC3 :
    forall E F e `{label_disjoint E F},
      (forall l,
        label_in_dom F l ->
        (forall k body, E k = Some body -> ~ contains_goto l body) /\
        ~ contains_goto l e) ->
      E + F |- e == e -| E
| EqC4 :
    forall E l l',
      label_rename_fresh E l' ->
      (exists e, E l = Some e) ->
      E |- goto l == goto l' -| E <E[ l ~> l' ]>
| EqC5 :
    forall E e e1 l `{label_fresh E l},
      RHS l e ->
      (E ## l # e1) |- subst_goto l e1 e == e -| (E ## l # e1)
| EqC6 :
    forall E l b f g e `{label_fresh E l},
      E |- test (not b) ;; (f ;; test b) == 0 -| E ->
      (E ## l # if b then g else f ;; goto l) |- e == e -|
        (E ## l # test b ;; g)
| EqC7 :
    forall E F e,
      (forall l, label_in_dom E l <-> label_in_dom F l) ->
      (forall l l' body target,
        E l = Some body ->
        E l' = Some target ->
        guarded l' body) ->
      (forall l body,
        E l = Some body ->
        F |- goto l == body -| F) ->
      F |- e == e -| E

| EqChoiceCong :
    forall E F e f e' f' b,
      E |- e == e' -| F ->
      E |- f == f' -| F ->
      E |- (if b then e else f) == (if b then e' else f') -| F
| EqBoolChoiceCong :
    forall e f b c,
      b =BA c ->
      (if b then e else f) == (if c then e else f)
| EqBoolAssertCong :
    forall b c,
      b =BA c ->
      test b == test c
| EqBoolLoopCong :
    forall e b c,
      b =BA c ->
      (while b do e) == (while c do e)
| EqSeqRightCong :
    forall E F e f g,
      E |- e == f -| F ->
      E |- g == g -| F ->
      E |- (g ;; e) == (g ;; f) -| F
| EqLoopSeqRightCong :
    forall E F e f g,
      E |- e == f -| F ->
      E |- g == g -| F ->
      E |- (g |> e) == (g |> f) -| F
| EqSeqLeftEmptyCong :
    forall e f g,
      e == f ->
      e ;; g == f ;; g
| EqLoopSeqLeftEmptyCong :
    forall e f g,
      e == f ->
      e |> g == f |> g
| EqLoopBodyEmptyCong :
    forall e f b,
      e == f ->
      (while b do e) == (while b do f)
| EqLoopBodyCong :
    forall E F e b,
      E |- e == e -| F ->
      E |- (while b do e) == (while b do e) -| F
where "E '|-' e '==' f '-|' F" := (CFGKATEquiv E e f F)
and "e '==' f" :=
  (CFGKATEquiv empty_label_context e f empty_label_context).

Definition cfgkat_contextual_expression : Type :=
  ((label_environment CFGKATExpression) * CFGKATExpression)%type.

Definition cfgkat_equiv
  : relation cfgkat_contextual_expression :=
  fun '(E, e) '(F, f) => E |- e == f -| F.

Definition cfgkat_non_ctx_equiv
  : relation CFGKATExpression :=
  fun e f =>
    empty_label_context |- e == f -| empty_label_context.

Definition cfgkat_equiv_in
  (E : label_environment CFGKATExpression)
  : relation CFGKATExpression :=
  fun e f => E |- e == f -| E.

Declare Scope cfgkat_setoid_scope.
Delimit Scope cfgkat_setoid_scope with cfgkat_setoid.

Notation "E '|~' e '=~=' f '~|' F" :=
  (cfgkat_equiv (E, e) (F, f))
  (at level 70, e at next level, f at next level)
  : cfgkat_setoid_scope.

Notation "E '|~' e '=~=' f" :=
  (cfgkat_equiv_in E e f)
  (at level 70, e at next level, f at next level)
  : cfgkat_setoid_scope.

Notation "e '=~=' f" :=
  (cfgkat_non_ctx_equiv e f)
  (at level 70)
  : cfgkat_setoid_scope.


Section FullContextualRewrite.

Lemma cfgkat_equiv_refl :
  Reflexive cfgkat_equiv.
Proof.
  intros [E e].
  apply EqRefl.
Qed.

Lemma cfgkat_equiv_sym :
  Symmetric cfgkat_equiv.
Proof.
  intros [E e] [F f] H.
  apply EqSym.
  exact H.
Qed.

Lemma cfgkat_equiv_trans :
  Transitive cfgkat_equiv.
Proof.
  intros [E e] [F f] [G g] Hef Hfg.
  eapply EqTrans; eauto.
Qed.

#[export] Instance cfgkat_equiv_equivalence :
  Equivalence cfgkat_equiv.
Proof.
  split.
  - apply cfgkat_equiv_refl.
  - apply cfgkat_equiv_sym.
  - apply cfgkat_equiv_trans.
Qed.

#[export] Instance cfgkat_equiv_proper :
  Proper (cfgkat_equiv ==> cfgkat_equiv ==> iff) cfgkat_equiv.
Proof.
  intros x x' Hx y y' Hy.
  split; intro H.
  - eapply cfgkat_equiv_trans.
    + apply cfgkat_equiv_sym. exact Hx.
    + eapply cfgkat_equiv_trans; eauto.
  - eapply cfgkat_equiv_trans.
    + exact Hx.
    + eapply cfgkat_equiv_trans.
      * exact H.
      * apply cfgkat_equiv_sym. exact Hy.
Qed.

Add Parametric Relation : cfgkat_contextual_expression cfgkat_equiv
  reflexivity proved by cfgkat_equiv_refl
  symmetry proved by cfgkat_equiv_sym
  transitivity proved by cfgkat_equiv_trans
  as cfgkat_equiv_relation.

Lemma cfgkat_choice_congruence
  (E F : label_environment CFGKATExpression)
  (b : CFGKATTest)
  (e e' f f' : CFGKATExpression)
  :
  cfgkat_equiv (E, e) (F, e') ->
  cfgkat_equiv (E, f) (F, f') ->
  cfgkat_equiv
    (E, if b then e else f)
    (F, if b then e' else f').
Proof.
  intros He Hf.
  exact (EqChoiceCong E F e f e' f' b He Hf).
Qed.

Lemma cfgkat_sequence_right_congruence
  (E F : label_environment CFGKATExpression)
  (e f g : CFGKATExpression)
  :
  cfgkat_equiv (E, e) (F, f) ->
  cfgkat_equiv (E, g) (F, g) ->
  cfgkat_equiv (E, g ;; e) (F, g ;; f).
Proof.
  intros Hef Hg.
  exact (EqSeqRightCong E F e f g Hef Hg).
Qed.

Lemma cfgkat_loopseq_right_congruence
  (E F : label_environment CFGKATExpression)
  (e f g : CFGKATExpression)
  :
  cfgkat_equiv (E, e) (F, f) ->
  cfgkat_equiv (E, g) (F, g) ->
  cfgkat_equiv (E, g |> e) (F, g |> f).
Proof.
  intros Hef Hg.
  exact (EqLoopSeqRightCong E F e f g Hef Hg).
Qed.

Lemma cfgkat_loop_body_congruence
  (E F : label_environment CFGKATExpression)
  (e : CFGKATExpression)
  (b : CFGKATTest)
  :
  cfgkat_equiv (E, e) (F, e) ->
  cfgkat_equiv (E, while b do e) (F, while b do e).
Proof.
  intro He.
  exact (EqLoopBodyCong E F e b He).
Qed.

End FullContextualRewrite.


Section FixedEnvironmentRewrite.

Context (E : label_environment CFGKATExpression).

Lemma cfgkat_equiv_in_refl :
  Reflexive (cfgkat_equiv_in E).
Proof.
  intro x.
  apply EqRefl.
Qed.

Lemma cfgkat_equiv_in_sym :
  Symmetric (cfgkat_equiv_in E).
Proof.
  intros x y Hxy.
  apply EqSym.
  exact Hxy.
Qed.

Lemma cfgkat_equiv_in_trans :
  Transitive (cfgkat_equiv_in E).
Proof.
  intros x y z Hxy Hyz.
  eapply EqTrans; eauto.
Qed.

#[export] Instance cfgkat_equiv_in_equivalence :
  Equivalence (cfgkat_equiv_in E).
Proof.
  split.
  - apply cfgkat_equiv_in_refl.
  - apply cfgkat_equiv_in_sym.
  - apply cfgkat_equiv_in_trans.
Qed.

#[export] Instance cfgkat_equiv_in_proper :
  Proper
    (cfgkat_equiv_in E ==> cfgkat_equiv_in E ==> iff)
    (cfgkat_equiv_in E).
Proof.
  intros x x' Hx y y' Hy.
  split; intro H.
  - eapply cfgkat_equiv_in_trans.
    + apply cfgkat_equiv_in_sym. exact Hx.
    + eapply cfgkat_equiv_in_trans; eauto.
  - eapply cfgkat_equiv_in_trans.
    + exact Hx.
    + eapply cfgkat_equiv_in_trans.
      * exact H.
      * apply cfgkat_equiv_in_sym. exact Hy.
Qed.

#[export] Instance fixed_context_pair_proper :
  Proper (cfgkat_equiv_in E ==> cfgkat_equiv) (pair E).
Proof.
  intros e f H.
  exact H.
Qed.

Add Parametric Relation : CFGKATExpression (cfgkat_equiv_in E)
  reflexivity proved by cfgkat_equiv_in_refl
  symmetry proved by cfgkat_equiv_in_sym
  transitivity proved by cfgkat_equiv_in_trans
  as cfgkat_equiv_in_relation.

Lemma cfgkat_choice_congruence_in
  (b : CFGKATTest)
  (e e' f f' : CFGKATExpression)
  :
  cfgkat_equiv_in E e e' ->
  cfgkat_equiv_in E f f' ->
  cfgkat_equiv_in E (if b then e else f) (if b then e' else f').
Proof.
  intros He Hf.
  apply cfgkat_choice_congruence; assumption.
Qed.

Lemma cfgkat_sequence_right_congruence_in
  (e f g : CFGKATExpression)
  :
  cfgkat_equiv_in E e f ->
  cfgkat_equiv_in E (g ;; e) (g ;; f).
Proof.
  intro Hef.
  apply cfgkat_sequence_right_congruence.
  - exact Hef.
  - apply EqRefl.
Qed.

Lemma cfgkat_loopseq_right_congruence_in
  (e f g : CFGKATExpression)
  :
  cfgkat_equiv_in E e f ->
  cfgkat_equiv_in E (g |> e) (g |> f).
Proof.
  intro Hef.
  apply cfgkat_loopseq_right_congruence.
  - exact Hef.
  - apply EqRefl.
Qed.

#[export] Instance CFGKATChoice_cfgkat_equiv_in_proper
  (b : CFGKATTest)
  : Proper
      (cfgkat_equiv_in E ==>
       cfgkat_equiv_in E ==>
       cfgkat_equiv_in E)
      (CFGKATChoice b).
Proof.
  intros e e' He f f' Hf.
  apply cfgkat_choice_congruence_in; assumption.
Qed.

#[export] Instance CFGKATSequence_right_cfgkat_equiv_in_proper
  (g : CFGKATExpression)
  : Proper (cfgkat_equiv_in E ==> cfgkat_equiv_in E)
      (CFGKATSequence g).
Proof.
  intros x y Hxy.
  apply cfgkat_sequence_right_congruence_in.
  exact Hxy.
Qed.

#[export] Instance CFGKATLoopSeq_right_cfgkat_equiv_in_proper
  (g : CFGKATExpression)
  : Proper (cfgkat_equiv_in E ==> cfgkat_equiv_in E)
      (CFGKATLoopSeq g).
Proof.
  intros x y Hxy.
  apply cfgkat_loopseq_right_congruence_in.
  exact Hxy.
Qed.

End FixedEnvironmentRewrite.


Section EmptyContextRewrite.

Lemma cfgkat_non_ctx_equiv_refl :
  Reflexive cfgkat_non_ctx_equiv.
Proof.
  intro e.
  apply EqRefl.
Qed.

Lemma cfgkat_non_ctx_equiv_sym :
  Symmetric cfgkat_non_ctx_equiv.
Proof.
  intros e f H.
  apply EqSym.
  exact H.
Qed.

Lemma cfgkat_non_ctx_equiv_trans :
  Transitive cfgkat_non_ctx_equiv.
Proof.
  intros e f g Hef Hfg.
  eapply EqTrans; eauto.
Qed.

#[export] Instance cfgkat_non_ctx_equiv_equivalence :
  Equivalence cfgkat_non_ctx_equiv.
Proof.
  split.
  - apply cfgkat_non_ctx_equiv_refl.
  - apply cfgkat_non_ctx_equiv_sym.
  - apply cfgkat_non_ctx_equiv_trans.
Qed.

#[export] Instance cfgkat_non_ctx_equiv_proper :
  Proper
    (cfgkat_non_ctx_equiv ==> cfgkat_non_ctx_equiv ==> iff)
    cfgkat_non_ctx_equiv.
Proof.
  intros e e' He f f' Hf.
  split; intro H.
  - eapply cfgkat_non_ctx_equiv_trans.
    + apply cfgkat_non_ctx_equiv_sym. exact He.
    + eapply cfgkat_non_ctx_equiv_trans; eauto.
  - eapply cfgkat_non_ctx_equiv_trans.
    + exact He.
    + eapply cfgkat_non_ctx_equiv_trans.
      * exact H.
      * apply cfgkat_non_ctx_equiv_sym. exact Hf.
Qed.

#[export] Instance empty_context_pair_proper :
  Proper (cfgkat_non_ctx_equiv ==> cfgkat_equiv)
    (pair empty_label_context).
Proof.
  intros e f H.
  exact H.
Qed.

Add Parametric Relation : CFGKATExpression cfgkat_non_ctx_equiv
  reflexivity proved by cfgkat_non_ctx_equiv_refl
  symmetry proved by cfgkat_non_ctx_equiv_sym
  transitivity proved by cfgkat_non_ctx_equiv_trans
  as cfgkat_non_ctx_equiv_relation.

Lemma cfgkat_boolean_choice_congruence
  (b c : CFGKATTest)
  (e f : CFGKATExpression)
  :
  b =BA c ->
  cfgkat_non_ctx_equiv
    (if b then e else f)
    (if c then e else f).
Proof.
  intro Hbc.
  exact (EqBoolChoiceCong e f b c Hbc).
Qed.

Lemma cfgkat_boolean_assert_congruence
  (b c : CFGKATTest)
  :
  b =BA c ->
  cfgkat_non_ctx_equiv (test b) (test c).
Proof.
  intro Hbc.
  exact (EqBoolAssertCong b c Hbc).
Qed.

Lemma cfgkat_boolean_loop_congruence
  (b c : CFGKATTest)
  (e : CFGKATExpression)
  :
  b =BA c ->
  cfgkat_non_ctx_equiv
    (while b do e)
    (while c do e).
Proof.
  intro Hbc.
  exact (EqBoolLoopCong e b c Hbc).
Qed.

Lemma cfgkat_choice_non_ctx_congruence
  (b : CFGKATTest)
  (e e' f f' : CFGKATExpression)
  :
  cfgkat_non_ctx_equiv e e' ->
  cfgkat_non_ctx_equiv f f' ->
  cfgkat_non_ctx_equiv
    (if b then e else f)
    (if b then e' else f').
Proof.
  intros He Hf.
  apply cfgkat_choice_congruence; assumption.
Qed.

Lemma cfgkat_sequence_right_non_ctx_congruence
  (e f g : CFGKATExpression)
  :
  cfgkat_non_ctx_equiv e f ->
  cfgkat_non_ctx_equiv (g ;; e) (g ;; f).
Proof.
  intro Hef.
  apply cfgkat_sequence_right_congruence.
  - exact Hef.
  - apply EqRefl.
Qed.

Lemma cfgkat_loopseq_right_non_ctx_congruence
  (e f g : CFGKATExpression)
  :
  cfgkat_non_ctx_equiv e f ->
  cfgkat_non_ctx_equiv (g |> e) (g |> f).
Proof.
  intro Hef.
  apply cfgkat_loopseq_right_congruence.
  - exact Hef.
  - apply EqRefl.
Qed.

Lemma cfgkat_sequence_left_non_ctx_congruence
  (e f g : CFGKATExpression)
  :
  cfgkat_non_ctx_equiv e f ->
  cfgkat_non_ctx_equiv (e ;; g) (f ;; g).
Proof.
  intro Hef.
  exact (EqSeqLeftEmptyCong e f g Hef).
Qed.

Lemma cfgkat_loopseq_left_non_ctx_congruence
  (e f g : CFGKATExpression)
  :
  cfgkat_non_ctx_equiv e f ->
  cfgkat_non_ctx_equiv (e |> g) (f |> g).
Proof.
  intro Hef.
  exact (EqLoopSeqLeftEmptyCong e f g Hef).
Qed.

Lemma cfgkat_loop_body_non_ctx_congruence
  (e f : CFGKATExpression)
  (b : CFGKATTest)
  :
  cfgkat_non_ctx_equiv e f ->
  cfgkat_non_ctx_equiv
    (while b do e)
    (while b do f).
Proof.
  intro Hef.
  exact (EqLoopBodyEmptyCong e f b Hef).
Qed.

#[export] Instance CFGKATAssert_non_ctx_proper :
  Proper (CFGKATBooleanAlgebraEquivalent ==> cfgkat_non_ctx_equiv)
    CFGKATAssert.
Proof.
  intros b c Hbc.
  apply cfgkat_boolean_assert_congruence.
  exact Hbc.
Qed.

#[export] Instance CFGKATChoice_non_ctx_proper :
  Proper
    (CFGKATBooleanAlgebraEquivalent ==>
     cfgkat_non_ctx_equiv ==>
     cfgkat_non_ctx_equiv ==>
     cfgkat_non_ctx_equiv)
    CFGKATChoice.
Proof.
  intros b c Hbc e e' He f f' Hf.
  eapply cfgkat_non_ctx_equiv_trans with
    (y := if b then e' else f').
  - apply cfgkat_choice_non_ctx_congruence; [exact He | exact Hf].
  - apply cfgkat_boolean_choice_congruence.
    exact Hbc.
Qed.

#[export] Instance CFGKATSequence_non_ctx_proper :
  Proper
    (cfgkat_non_ctx_equiv ==>
     cfgkat_non_ctx_equiv ==>
     cfgkat_non_ctx_equiv)
    CFGKATSequence.
Proof.
  intros e e' He f f' Hf.
  eapply cfgkat_non_ctx_equiv_trans.
  - apply cfgkat_sequence_left_non_ctx_congruence.
    exact He.
  - apply cfgkat_sequence_right_non_ctx_congruence.
    exact Hf.
Qed.

#[export] Instance CFGKATLoopSeq_non_ctx_proper :
  Proper
    (cfgkat_non_ctx_equiv ==>
     cfgkat_non_ctx_equiv ==>
     cfgkat_non_ctx_equiv)
    CFGKATLoopSeq.
Proof.
  intros e e' He f f' Hf.
  eapply cfgkat_non_ctx_equiv_trans.
  - apply cfgkat_loopseq_left_non_ctx_congruence.
    exact He.
  - apply cfgkat_loopseq_right_non_ctx_congruence.
    exact Hf.
Qed.

#[export] Instance CFGKATLoop_non_ctx_proper :
  Proper
    (CFGKATBooleanAlgebraEquivalent ==>
     cfgkat_non_ctx_equiv ==>
     cfgkat_non_ctx_equiv)
    CFGKATLoop.
Proof.
  intros b c Hbc e e' He.
  eapply cfgkat_non_ctx_equiv_trans.
  - apply cfgkat_loop_body_non_ctx_congruence.
    exact He.
  - apply cfgkat_boolean_loop_congruence.
    exact Hbc.
Qed.

End EmptyContextRewrite.


Create HintDb cfgkat_congruence.

#[export] Hint Resolve
  cfgkat_equiv_refl
  cfgkat_choice_congruence
  cfgkat_sequence_right_congruence
  cfgkat_loopseq_right_congruence
  cfgkat_loop_body_congruence
  : cfgkat_congruence.

#[export] Hint Resolve
  cfgkat_equiv_in_refl
  cfgkat_choice_congruence_in
  cfgkat_sequence_right_congruence_in
  cfgkat_loopseq_right_congruence_in
  : cfgkat_congruence.

#[export] Hint Resolve
  cfgkat_non_ctx_equiv_refl
  cfgkat_boolean_choice_congruence
  cfgkat_boolean_assert_congruence
  cfgkat_boolean_loop_congruence
  cfgkat_choice_non_ctx_congruence
  cfgkat_sequence_right_non_ctx_congruence
  cfgkat_loopseq_right_non_ctx_congruence
  cfgkat_sequence_left_non_ctx_congruence
  cfgkat_loopseq_left_non_ctx_congruence
  cfgkat_loop_body_non_ctx_congruence
  : cfgkat_congruence.


Ltac cfgkat_change_preferred_equiv :=
  match goal with
  | |- @CFGKATEquiv empty_label_context ?e ?f empty_label_context =>
      change (cfgkat_non_ctx_equiv e f)
  | |- @CFGKATEquiv ?E ?e ?f ?E =>
      change (cfgkat_equiv_in E e f)
  | |- @CFGKATEquiv ?E ?e ?f ?F =>
      change (cfgkat_equiv (E, e) (F, f))
  | |- cfgkat_equiv (empty_label_context, ?e) (empty_label_context, ?f) =>
      change (cfgkat_non_ctx_equiv e f)
  | |- cfgkat_equiv (?E, ?e) (?E, ?f) =>
      change (cfgkat_equiv_in E e f)
  | |- cfgkat_equiv_in empty_label_context ?e ?f =>
      change (cfgkat_non_ctx_equiv e f)
  end.

Ltac cfgkat_change_contextual_equiv :=
  match goal with
  | |- @CFGKATEquiv ?E ?e ?f ?F =>
      change (cfgkat_equiv (E, e) (F, f))
  end.

Ltac cfgkat_prepare_preferred_goal :=
  try cfgkat_change_preferred_equiv.

Ltac cfgkat_prepare_contextual_goal :=
  try cfgkat_change_contextual_equiv.

Ltac cfgkat_instantiate_rewrite H :=
  repeat lazymatch type of H with
  | forall _ : ?T, _ =>
      lazymatch type of T with
      | Prop => fail
      | _ =>
          let x := fresh "rwarg" in
          evar (x : T);
          specialize (H x);
          subst x
      end
  end.

Ltac cfgkat_change_preferred_rewrite H :=
  lazymatch type of H with
  | @CFGKATEquiv empty_label_context ?e ?f empty_label_context =>
      change (cfgkat_non_ctx_equiv e f) in H
  | @CFGKATEquiv ?E ?e ?f ?E =>
      change (cfgkat_equiv_in E e f) in H
  | @CFGKATEquiv ?E ?e ?f ?F =>
      change (cfgkat_equiv (E, e) (F, f)) in H
  | cfgkat_equiv (empty_label_context, ?e) (empty_label_context, ?f) =>
      change (cfgkat_non_ctx_equiv e f) in H
  | cfgkat_equiv (?E, ?e) (?E, ?f) =>
      change (cfgkat_equiv_in E e f) in H
  | cfgkat_equiv_in empty_label_context ?e ?f =>
      change (cfgkat_non_ctx_equiv e f) in H
  | cfgkat_non_ctx_equiv _ _ =>
      idtac
  | cfgkat_equiv_in _ _ _ =>
      idtac
  | cfgkat_equiv _ _ =>
      idtac
  end.

Ltac cfgkat_change_contextual_rewrite H :=
  lazymatch type of H with
  | @CFGKATEquiv ?E ?e ?f ?F =>
      change (cfgkat_equiv (E, e) (F, f)) in H
  | cfgkat_non_ctx_equiv ?e ?f =>
      change (cfgkat_equiv (empty_label_context, e) (empty_label_context, f)) in H
  | cfgkat_equiv_in ?E ?e ?f =>
      change (cfgkat_equiv (E, e) (E, f)) in H
  | cfgkat_equiv _ _ =>
      idtac
  end.

Ltac cfgkat_prepare_goal_for_rewrite H :=
  lazymatch type of H with
  | cfgkat_equiv _ _ =>
      cfgkat_prepare_contextual_goal
  | _ =>
      cfgkat_prepare_preferred_goal
  end.

Ltac cfgkat_rewrite_forward H :=
  first
    [ let Hrewrite := fresh "Hrewrite" in
      pose proof H as Hrewrite;
      cfgkat_instantiate_rewrite Hrewrite;
      cfgkat_change_preferred_rewrite Hrewrite;
      cfgkat_prepare_goal_for_rewrite Hrewrite;
      setoid_rewrite Hrewrite;
      clear Hrewrite
    | let Hrewrite := fresh "Hrewrite" in
      pose proof H as Hrewrite;
      cfgkat_instantiate_rewrite Hrewrite;
      cfgkat_change_contextual_rewrite Hrewrite;
      cfgkat_prepare_contextual_goal;
      setoid_rewrite Hrewrite;
      clear Hrewrite ].

Tactic Notation "cfgkat_rewrite" constr(H) :=
  cfgkat_rewrite_forward H.

Ltac cfgkat_rewrite_reverse H :=
  first
    [ let Hrewrite := fresh "Hrewrite" in
      pose proof H as Hrewrite;
      cfgkat_instantiate_rewrite Hrewrite;
      cfgkat_change_preferred_rewrite Hrewrite;
      cfgkat_prepare_goal_for_rewrite Hrewrite;
      setoid_rewrite <- Hrewrite;
      clear Hrewrite
    | let Hrewrite := fresh "Hrewrite" in
      pose proof H as Hrewrite;
      cfgkat_instantiate_rewrite Hrewrite;
      cfgkat_change_contextual_rewrite Hrewrite;
      cfgkat_prepare_contextual_goal;
      setoid_rewrite <- Hrewrite;
      clear Hrewrite ].

Tactic Notation "cfgkat_rewrite" "<-" constr(H) :=
  cfgkat_rewrite_reverse H.

Ltac cfgkat_rewrite_at H n :=
  first
    [ let Hrewrite := fresh "Hrewrite" in
      pose proof H as Hrewrite;
      cfgkat_instantiate_rewrite Hrewrite;
      cfgkat_change_preferred_rewrite Hrewrite;
      cfgkat_prepare_goal_for_rewrite Hrewrite;
      setoid_rewrite Hrewrite at n;
      clear Hrewrite
    | let Hrewrite := fresh "Hrewrite" in
      pose proof H as Hrewrite;
      cfgkat_instantiate_rewrite Hrewrite;
      cfgkat_change_contextual_rewrite Hrewrite;
      cfgkat_prepare_contextual_goal;
      setoid_rewrite Hrewrite at n;
      clear Hrewrite ].

Ltac cfgkat_rewrite_reverse_at H n :=
  first
    [ let Hrewrite := fresh "Hrewrite" in
      pose proof H as Hrewrite;
      cfgkat_instantiate_rewrite Hrewrite;
      cfgkat_change_preferred_rewrite Hrewrite;
      cfgkat_prepare_goal_for_rewrite Hrewrite;
      setoid_rewrite <- Hrewrite at n;
      clear Hrewrite
    | let Hrewrite := fresh "Hrewrite" in
      pose proof H as Hrewrite;
      cfgkat_instantiate_rewrite Hrewrite;
      cfgkat_change_contextual_rewrite Hrewrite;
      cfgkat_prepare_contextual_goal;
      setoid_rewrite <- Hrewrite at n;
      clear Hrewrite ].

Tactic Notation "cfgkat_rewrite" constr(H) "at" integer(n) :=
  cfgkat_rewrite_at H n.

Tactic Notation "cfgkat_rewrite" "<-" constr(H) "at" integer(n) :=
  cfgkat_rewrite_reverse_at H n.
