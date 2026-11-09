Require Import Stdlib.Logic.FunctionalExtensionality.
From Stdlib Require Import Lists.List.
Import ListNotations.

From CFGKAT.Completeness Require Export gtnfthm.

Local Open Scope cfgkat_scope.

Definition canonical_control_output
  {state : Type}
  (r : CFGKATAutomatonOutputs state)
  : option (CFGKATAutomatonOutputs CFGKATSyntConfiguration) :=
  match r with
  | CFGKATAutomatonReject => Some CFGKATAutomatonReject
  | CFGKATAutomatonAccept i => Some (CFGKATAutomatonAccept i)
  | CFGKATAutomatonBreak i => Some (CFGKATAutomatonBreak i)
  | CFGKATAutomatonContinue i => Some (CFGKATAutomatonContinue i)
  | CFGKATAutomatonReturn => Some CFGKATAutomatonReturn
  | CFGKATAutomatonJump l i => Some (CFGKATAutomatonJump l i)
  | CFGKATAutomatonNext _ _ => None
  end.

Definition canonical_control_sys
  {state : Type}
  (r : CFGKATAutomatonOutputs state)
  : CFGKATExpression :=
  match canonical_control_output r with
  | Some c => sys c
  | None => 0
  end.

Definition canonical_sysc_Y
  {state : Type}
  (state_label : state -> Label)
  (r : CFGKATAutomatonOutputs state)
  : CFGKATExpression :=
  match r with
  | CFGKATAutomatonNext p s =>
      do p ;; goto (state_label s)
  | _ => canonical_control_sys r
  end.

Definition canonical_body_Y
  {state : Type}
  (state_label : state -> Label)
  (step : state -> Atom -> CFGKATAutomatonOutputs state)
  (s : state)
  : CFGKATExpression :=
  guarded_atom_sum_all (fun a => canonical_sysc_Y state_label (step s a)).

Definition canonical_env_Y
  {state : Type}
  (states : list state)
  (state_label : state -> Label)
  (step : state -> Atom -> CFGKATAutomatonOutputs state)
  : label_environment CFGKATExpression.
Proof.
  refine
    (mk_environment
      (fun k =>
        match lookup_gtnf_state state_label states k with
        | Some s => Some (canonical_body_Y state_label step s)
        | None => None
        end)
      (map state_label states)
      _).
  intros k body Hlookup.
  destruct (lookup_gtnf_state state_label states k) as [s |] eqn:Hstate;
    [| discriminate Hlookup].
  destruct (lookup_gtnf_state_some_in _ _ _ _ Hstate)
    as [Hin Hlabel].
  subst k.
  apply in_map. exact Hin.
Defined.

Definition CFGKATCoalgebra (X : Type) : Type :=
  X -> Atom -> CFGKATAutomatonOutputs X.

Definition CFGKATCoalgebraHomomorphism
  {X Z : Type}
  (chi : CFGKATCoalgebra X)
  (zeta : CFGKATCoalgebra Z)
  (h : X -> Z)
  : Prop :=
  forall x a,
    lifted_relation (fun x' z' => h x' = z')
      (chi x a) (zeta (h x) a).

Definition canonical_sysc
  {X : Type}
  (state_label : X -> Label)
  (r : CFGKATAutomatonOutputs X)
  : CFGKATExpression :=
  canonical_sysc_Y state_label r.

Definition canonical_body
  {X : Type}
  (state_label : X -> Label)
  (step : CFGKATCoalgebra X)
  (x : X)
  : CFGKATExpression :=
  canonical_body_Y state_label step x.

Definition lookup_canonical_state
  {X : Type}
  (state_label : X -> Label)
  (states : list X)
  (target : Label)
  : option X :=
  lookup_gtnf_state state_label states target.

Definition canonical_env
  {X : Type}
  (states : list X)
  (state_label : X -> Label)
  (step : CFGKATCoalgebra X)
  : label_environment CFGKATExpression.
Proof.
  refine
    (mk_environment
      (fun k =>
        match lookup_canonical_state state_label states k with
        | Some x => Some (canonical_body state_label step x)
        | None => None
        end)
      (map state_label states)
      _).
  intros k body Hlookup.
  destruct (lookup_canonical_state state_label states k) as [x |] eqn:Hstate;
    [| discriminate Hlookup].
  destruct (lookup_gtnf_state_some_in _ _ _ _ Hstate)
    as [Hin Hlabel].
  subst k.
  apply in_map. exact Hin.
Defined.

Lemma lookup_canonical_state_in_some
  {X : Type}
  (state_label : X -> Label)
  (states : list X)
  (x : X)
  :
  (forall u v,
    In u states ->
    In v states ->
    state_label u = state_label v ->
    u = v) ->
  In x states ->
  lookup_canonical_state state_label states (state_label x) = Some x.
Proof.
  apply lookup_gtnf_state_in_some.
Qed.

Lemma lookup_canonical_state_some_in
  {X : Type}
  (state_label : X -> Label)
  (states : list X)
  (target : Label)
  (x : X)
  :
  lookup_canonical_state state_label states target = Some x ->
  In x states /\ target = state_label x.
Proof.
  apply lookup_gtnf_state_some_in.
Qed.

Record canonical_environment_witness
  {X : Type}
  (chi : CFGKATCoalgebra X)
  : Type :=
{
  canonical_environment_states : list X;
  canonical_environment_label : X -> Label;
  canonical_environment_contains :
    forall x, In x canonical_environment_states;
  canonical_environment_next_closed :
    forall x a p x',
      In x canonical_environment_states ->
      chi x a = CFGKATAutomatonNext p x' ->
      In x' canonical_environment_states;
  canonical_environment_label_injective :
    forall x y,
      In x canonical_environment_states ->
      In y canonical_environment_states ->
      canonical_environment_label x = canonical_environment_label y ->
      x = y
}.

Arguments canonical_environment_states {X chi} _.
Arguments canonical_environment_label {X chi} _ _.
Arguments canonical_environment_contains {X chi} _ _.
Arguments canonical_environment_next_closed {X chi} _ _ _ _ _ _ _.
Arguments canonical_environment_label_injective {X chi} _ _ _ _ _ _.
