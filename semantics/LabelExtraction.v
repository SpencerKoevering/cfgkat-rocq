From CFGKAT.Semantics Require Export ExpressionSemantics.
From Stdlib Require Import Lists.List.
Import ListNotations.

Local Open Scope cfgkat_scope.

Inductive CFGKATProgramSyntax :=
| CFGKATProgramAssert :
    CFGKATTest ->
    CFGKATProgramSyntax
| CFGKATProgramAction :
    Action ->
    CFGKATProgramSyntax
| CFGKATProgramAssign :
    IndicatorVariable ->
    IndicatorValue ->
    CFGKATProgramSyntax
| CFGKATProgramBreak :
    CFGKATProgramSyntax
| CFGKATProgramContinue :
    CFGKATProgramSyntax
| CFGKATProgramReturn :
    CFGKATProgramSyntax
| CFGKATProgramGoto :
    Label ->
    CFGKATProgramSyntax
| CFGKATProgramLabel :
    Label ->
    CFGKATProgramSyntax
| CFGKATProgramChoice :
    CFGKATTest ->
    CFGKATProgramSyntax ->
    CFGKATProgramSyntax ->
    CFGKATProgramSyntax
| CFGKATProgramSequence :
    CFGKATProgramSyntax ->
    CFGKATProgramSyntax ->
    CFGKATProgramSyntax
| CFGKATProgramLoopSeq :
    CFGKATProgramSyntax ->
    CFGKATProgramSyntax ->
    CFGKATProgramSyntax
| CFGKATProgramLoop :
    CFGKATTest ->
    CFGKATProgramSyntax ->
    CFGKATProgramSyntax.

Declare Scope cfgkat_program_scope.
Delimit Scope cfgkat_program_scope with cfgkat_program.
Bind Scope cfgkat_program_scope with CFGKATProgramSyntax.

Notation "'test' b" :=
  (CFGKATProgramAssert b)
  (at level 40) : cfgkat_program_scope.
Notation "'0'" :=
  (CFGKATProgramAssert (0 : CFGKATTest)) : cfgkat_program_scope.
Notation "'1'" :=
  (CFGKATProgramAssert (1 : CFGKATTest)) : cfgkat_program_scope.
Notation "'assign' v 'to' x" :=
  (CFGKATProgramAssign x v)
  (at level 40) : cfgkat_program_scope.
Notation "'do' p" :=
  (CFGKATProgramAction p)
  (at level 40) : cfgkat_program_scope.
Notation "'break'" :=
  CFGKATProgramBreak : cfgkat_program_scope.
Notation "'return'" :=
  CFGKATProgramReturn : cfgkat_program_scope.
Notation "'continue'" :=
  CFGKATProgramContinue : cfgkat_program_scope.
Notation "'goto' l" :=
  (CFGKATProgramGoto l)
  (at level 40) : cfgkat_program_scope.
Notation "'label' l" :=
  (CFGKATProgramLabel l)
  (at level 40) : cfgkat_program_scope.
Notation "'plabel' l" :=
  (CFGKATProgramLabel l)
  (at level 40) : cfgkat_program_scope.
Notation "'pgoto' l" :=
  (CFGKATProgramGoto l)
  (at level 40) : cfgkat_program_scope.
Notation "e ';;' f" :=
  (CFGKATProgramSequence e f)
  (at level 50) : cfgkat_program_scope.
Notation "e '|>' f" :=
  (CFGKATProgramLoopSeq e f)
  (at level 45) : cfgkat_program_scope.
Notation "'if' b 'then' e 'else' f" :=
  (CFGKATProgramChoice b e f)
  (at level 200, b at level 200, e at level 200, f at level 200,
   right associativity) : cfgkat_program_scope.
Notation "'while' b 'do' e" :=
  (CFGKATProgramLoop b e)
  (at level 80) : cfgkat_program_scope.

Fixpoint label_erase
  (e : CFGKATProgramSyntax)
  : CFGKATExpression :=
  match e with
  | CFGKATProgramAssert b => test b
  | CFGKATProgramAction p => do p
  | CFGKATProgramAssign x v => assign v to x
  | CFGKATProgramBreak => break
  | CFGKATProgramContinue => continue
  | CFGKATProgramReturn => return
  | CFGKATProgramGoto l => goto l
  | CFGKATProgramLabel _ => 1
  | CFGKATProgramChoice b e1 e2 =>
      if b then label_erase e1 else label_erase e2
  | CFGKATProgramSequence e1 e2 =>
      label_erase e1 ;; label_erase e2
  | CFGKATProgramLoopSeq e1 e2 =>
      label_erase e1 |> label_erase e2
  | CFGKATProgramLoop b body =>
      while b do label_erase body
  end.

Fixpoint program_labels
  (e : CFGKATProgramSyntax)
  : list Label :=
  match e with
  | CFGKATProgramAssert _
  | CFGKATProgramAction _
  | CFGKATProgramAssign _ _
  | CFGKATProgramBreak
  | CFGKATProgramContinue
  | CFGKATProgramReturn
  | CFGKATProgramGoto _ => []
  | CFGKATProgramLabel l => [l]
  | CFGKATProgramChoice _ e1 e2
  | CFGKATProgramSequence e1 e2
  | CFGKATProgramLoopSeq e1 e2 =>
      program_labels e1 ++ program_labels e2
  | CFGKATProgramLoop _ body =>
      program_labels body
  end.

Definition program_label_occurs
  (l : Label)
  (e : CFGKATProgramSyntax)
  : Prop :=
  In l (program_labels e).

Definition well_labeled_program
  (e : CFGKATProgramSyntax)
  : Prop :=
  NoDup (program_labels e).

Record CFGKATProgram := {
  cfgkat_program_syntax :> CFGKATProgramSyntax;
  cfgkat_program_well_labeled :
    well_labeled_program cfgkat_program_syntax;
}.

Bind Scope cfgkat_program_scope with CFGKATProgram.

Fixpoint label_extraction_syntax
  (e : CFGKATProgramSyntax)
  (target : Label)
  : option CFGKATExpression :=
  match e with
  | CFGKATProgramAssert _
  | CFGKATProgramAction _
  | CFGKATProgramAssign _ _
  | CFGKATProgramBreak
  | CFGKATProgramContinue
  | CFGKATProgramReturn
  | CFGKATProgramGoto _ => None
  | CFGKATProgramLabel l =>
      match Label_eq_dec l target with
      | left _ => Some 1
      | right _ => None
	      end
  | CFGKATProgramChoice _ e1 e2 =>
      match label_extraction_syntax e1 target with
      | Some body => Some body
      | None => label_extraction_syntax e2 target
      end
  | CFGKATProgramSequence e1 e2 =>
      match label_extraction_syntax e1 target with
      | Some body => Some (body ;; label_erase e2)
      | None => label_extraction_syntax e2 target
      end
  | CFGKATProgramLoopSeq e1 e2 =>
      match label_extraction_syntax e1 target with
      | Some body => Some (body |> label_erase e2)
      | None => label_extraction_syntax e2 target
      end
  | CFGKATProgramLoop b body =>
      match label_extraction_syntax body target with
      | Some body_at_label =>
          Some (body_at_label |> label_erase (CFGKATProgramLoop b body))
      | None => None
      end
  end.

Definition label_extraction
  (e : CFGKATProgram)
  (target : Label)
  : option CFGKATExpression :=
  label_extraction_syntax e target.

Notation "e '_-'" := (label_erase e)
  (at level 40) : cfgkat_program_scope.

Lemma label_extraction_some_occurs
  (e : CFGKATProgramSyntax)
  (l : Label)
  (body : CFGKATExpression)
  :
  label_extraction_syntax e l = Some body ->
  program_label_occurs l e.
Proof.
  revert l body.
  induction e as
    [b | p | x v | | | | k | k | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b body IH];
    intros l body0 Hextract; simpl in *; try discriminate.
	  - destruct (Label_eq_dec k l) as [Heq | Hneq].
	    + left. exact Heq.
	    + discriminate.
	  - destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody.
	    + apply in_or_app. left.
	      eapply IH1. exact Hbody.
	    + apply in_or_app. right.
	      eapply IH2. exact Hextract.
	  - destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody.
	    + apply in_or_app. left.
	      eapply IH1. exact Hbody.
	    + apply in_or_app. right.
	      eapply IH2. exact Hextract.
	  - destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody.
	    + apply in_or_app. left.
	      eapply IH1. exact Hbody.
	    + apply in_or_app. right.
	      eapply IH2. exact Hextract.
	  - destruct (label_extraction_syntax body l) as [body_at_label |] eqn:Hbody;
	      try discriminate.
	    eapply IH. exact Hbody.
Qed.

Definition label_extraction_syntax_environment
  (e : CFGKATProgramSyntax)
  : label_environment CFGKATExpression :=
  mk_environment
    (fun l => label_extraction_syntax e l)
    (program_labels e)
    (fun l body Hbody => label_extraction_some_occurs e l body Hbody).

Definition label_extraction_environment
  (e : CFGKATProgram)
  : label_environment CFGKATExpression :=
  mk_environment
    (fun l => label_extraction e l)
    (program_labels e)
    (fun l body Hbody => label_extraction_some_occurs e l body Hbody).

Notation "'sigma' '(' e ')'" := (label_extraction_environment e)
  (at level 40) : cfgkat_program_scope.

Lemma label_extraction_not_occurs_none
  (e : CFGKATProgramSyntax)
  (l : Label)
  :
  ~ program_label_occurs l e ->
  label_extraction_syntax e l = None.
Proof.
  revert l.
  induction e as
    [b | p | x v | | | | k | k | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b body IH];
    intros l Hnot; simpl in *; try reflexivity.
  - destruct (Label_eq_dec k l) as [Heq | Hneq].
    + subst. exfalso. apply Hnot. left. reflexivity.
    + reflexivity.
		  - destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody.
		    + exfalso. apply Hnot. apply in_or_app. left.
		      eapply label_extraction_some_occurs. exact Hbody.
		    + apply IH2.
		      intro Hin.
		      apply Hnot.
		      apply in_or_app. right. exact Hin.
		  - destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody.
		    + exfalso. apply Hnot. apply in_or_app. left.
		      eapply label_extraction_some_occurs. exact Hbody.
		    + apply IH2.
		      intro Hin.
		      apply Hnot.
		      apply in_or_app. right. exact Hin.
		  - destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody.
		    + exfalso. apply Hnot. apply in_or_app. left.
		      eapply label_extraction_some_occurs. exact Hbody.
		    + apply IH2.
		      intro Hin.
		      apply Hnot.
		      apply in_or_app. right. exact Hin.
		  - destruct (label_extraction_syntax body l) as [body_at_label |] eqn:Hbody.
		    + exfalso. apply Hnot.
		      unfold program_label_occurs. simpl.
		      eapply label_extraction_some_occurs. exact Hbody.
		    + reflexivity.
Qed.

Lemma label_extraction_occurs_some
  (e : CFGKATProgramSyntax)
  (l : Label)
  :
  program_label_occurs l e ->
  exists body,
    label_extraction_syntax e l = Some body.
Proof.
  revert l.
  induction e as
    [b | p | x v | | | | k | k | b e1 IH1 e2 IH2
     | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b body IH];
    intros l Hoccurs; simpl in *; try contradiction.
  - destruct Hoccurs as [Heq | []].
    subst l.
    destruct (Label_eq_dec k k) as [_ | Hneq].
    + exists 1. reflexivity.
    + contradiction Hneq. reflexivity.
	  - apply in_app_iff in Hoccurs as [Hleft | Hright].
	    + destruct (IH1 l Hleft) as [body0 Hbody].
	      rewrite Hbody. exists body0. reflexivity.
	    + destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody1.
	      * exists body1. reflexivity.
	      * apply IH2. exact Hright.
		  - apply in_app_iff in Hoccurs as [Hleft | Hright].
		    + destruct (IH1 l Hleft) as [body0 Hbody].
		      rewrite Hbody.
		      exists (body0 ;; label_erase e2). reflexivity.
		    + destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody1.
		      * exists (body1 ;; label_erase e2). reflexivity.
		      * apply IH2. exact Hright.
		  - apply in_app_iff in Hoccurs as [Hleft | Hright].
		    + destruct (IH1 l Hleft) as [body0 Hbody].
		      rewrite Hbody.
		      exists (body0 |> label_erase e2). reflexivity.
		    + destruct (label_extraction_syntax e1 l) as [body1 |] eqn:Hbody1.
		      * exists (body1 |> label_erase e2). reflexivity.
		      * apply IH2. exact Hright.
		  - destruct (IH l Hoccurs) as [body_at_label Hbody].
		    rewrite Hbody.
		    exists (body_at_label |> label_erase (CFGKATProgramLoop b body)).
		    reflexivity.
Qed.

Lemma label_extraction_some_iff_occurs
  (e : CFGKATProgramSyntax)
  (l : Label)
  :
  (exists body, label_extraction_syntax e l = Some body) <->
  program_label_occurs l e.
Proof.
  split.
  - intros [body Hbody].
    eapply label_extraction_some_occurs.
    exact Hbody.
	  - apply label_extraction_occurs_some.
Qed.

Lemma label_extraction_choice_left
  (b : CFGKATTest)
  (e1 e2 : CFGKATProgramSyntax)
  (l : Label)
  :
  program_label_occurs l e1 ->
  label_extraction_syntax (CFGKATProgramChoice b e1 e2) l =
    label_extraction_syntax e1 l.
Proof.
  intro Hoccurs.
  simpl.
  destruct (label_extraction_syntax e1 l) as [body |] eqn:Hbody.
  - reflexivity.
  - destruct (label_extraction_occurs_some e1 l Hoccurs) as [body Hsome].
    rewrite Hsome in Hbody. discriminate.
Qed.

Lemma label_extraction_sequence_left
  (e1 e2 : CFGKATProgramSyntax)
  (l : Label)
  :
  program_label_occurs l e1 ->
  label_extraction_syntax (CFGKATProgramSequence e1 e2) l =
    match label_extraction_syntax e1 l with
    | Some body => Some (body ;; label_erase e2)
    | None => None
    end.
Proof.
  intro Hoccurs.
  simpl.
  destruct (label_extraction_syntax e1 l) as [body |] eqn:Hbody.
  - reflexivity.
  - destruct (label_extraction_occurs_some e1 l Hoccurs) as [body Hsome].
    rewrite Hsome in Hbody. discriminate.
Qed.

Lemma label_extraction_sequence_right
  (e1 e2 : CFGKATProgramSyntax)
  (l : Label)
  :
  ~ program_label_occurs l e1 ->
  label_extraction_syntax (CFGKATProgramSequence e1 e2) l =
    label_extraction_syntax e2 l.
Proof.
  intro Hnot.
  simpl.
  rewrite (label_extraction_not_occurs_none e1 l Hnot).
  reflexivity.
Qed.

Lemma label_extraction_loop_present
  (b : CFGKATTest)
  (body : CFGKATProgramSyntax)
  (l : Label)
  :
  label_extraction_syntax (CFGKATProgramLoop b body) l =
    match label_extraction_syntax body l with
    | Some body_at_label =>
        Some (body_at_label |> label_erase (CFGKATProgramLoop b body))
    | None => None
    end.
Proof.
  reflexivity.
Qed.
