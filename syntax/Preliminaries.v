Require Import Stdlib.Program.Equality.
Require Import Stdlib.Setoids.Setoid.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.Logic.ProofIrrelevance.
Require Import Stdlib.Logic.ClassicalEpsilon.
Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.Arith.Arith.

From Stdlib Require Import Lists.List.
Import ListNotations.

Local Open Scope type_scope.

Record FinType := {
  carrier :> Type;
  elements : list carrier;
  all_in : forall x : carrier, In x elements;
  eq_dec : forall x y : carrier, {x = y} + {x <> y};
  nodup : NoDup elements
}.

Record NonEmptyFinType := {
  nonempty_fintype :> FinType;
  nonempty_elements : elements nonempty_fintype <> []
}.

Record InfiniteType := {
  infinite_carrier :> Type;
  infinite_eq_dec :
    forall x y : infinite_carrier, {x = y} + {x <> y};
  infinite_not_all_in :
    forall elements : list infinite_carrier,
      exists x, ~ In x elements
}.

Definition infinite_fresh
  (A : InfiniteType)
  (avoid : list A)
  : {x : A | ~ In x avoid}.
Proof.
  apply constructive_indefinite_description.
  apply infinite_not_all_in.
Defined.

Theorem infinite_no_finite_enumeration
  (A : InfiniteType)
  :
  ~ exists xs : list A, forall x : A, In x xs.
Proof.
  intros [xs Hall].
  destruct (infinite_not_all_in A xs) as [x Hfresh].
  apply Hfresh.
  apply Hall.
Qed.

Definition nonempty_fin_witness
  (A : NonEmptyFinType)
  : A.
Proof.
  destruct (elements A) as [|x xs] eqn:HA.
  - exfalso.
    apply (nonempty_elements A).
    exact HA.
  - exact x.
Defined.

Parameter Action : FinType.
Parameter Test : FinType.
Parameter Label : InfiniteType.
Parameter IndicatorVariable : FinType.
Parameter IndicatorValue : NonEmptyFinType.

Lemma fresh_label_family :
  forall {A : Type} (xs : list A) (avoid : list Label),
    { label_of : A -> Label |
      (forall x, In x xs -> ~ In (label_of x) avoid) /\
      (forall x y,
        In x xs ->
        In y xs ->
        label_of x = label_of y ->
        x = y) }.
Proof.
  intros A xs.
  induction xs as [|x xs IH]; intro avoid.
  - destruct (infinite_fresh Label []) as [default _].
    exists (fun _ => default).
    split; intros; contradiction.
  - destruct (IH avoid) as [tail_of [Htail_fresh Htail_inj]].
    destruct (infinite_fresh Label (avoid ++ map tail_of xs))
      as [head_label Hhead_fresh].
    exists (fun y =>
      match excluded_middle_informative (y = x) with
      | left _ => head_label
      | right _ => tail_of y
      end).
    split.
    + intros y Hy.
      destruct (excluded_middle_informative (y = x)) as [Hyx | Hynx].
      * intro Havoid.
        apply Hhead_fresh.
        apply in_or_app. left. exact Havoid.
      * destruct Hy as [Hyx' | Hy_tail].
        -- subst. contradiction.
        -- apply Htail_fresh. exact Hy_tail.
    + intros y z Hy Hz Hlabel.
      destruct (excluded_middle_informative (y = x)) as [Hyx | Hynx].
      * destruct (excluded_middle_informative (z = x)) as [Hzx | Hznx].
        -- subst. reflexivity.
        -- exfalso.
           destruct Hz as [Hzx' | Hz_tail]; [subst; contradiction |].
           apply Hhead_fresh.
           apply in_or_app. right.
           apply in_map_iff.
           exists z. split.
           ++ symmetry. exact Hlabel.
           ++ exact Hz_tail.
      * destruct (excluded_middle_informative (z = x)) as [Hzx | Hznx].
        -- exfalso.
           destruct Hy as [Hyx' | Hy_tail]; [subst; contradiction |].
           apply Hhead_fresh.
           apply in_or_app. right.
           apply in_map_iff.
           exists y. split.
           ++ exact Hlabel.
           ++ exact Hy_tail.
        -- destruct Hy as [Hyx' | Hy_tail]; [subst; contradiction |].
           destruct Hz as [Hzx' | Hz_tail]; [subst; contradiction |].
           eapply Htail_inj; eauto.
Qed.

Definition Label_eq_dec := infinite_eq_dec Label.
Definition Test_eq_dec  := eq_dec Test.
Definition Var_eq_dec   := eq_dec IndicatorVariable.
Definition Val_eq_dec   := eq_dec IndicatorValue.

Definition label_environment_supports
  {A : Type}
  (lookup : Label -> option A)
  (support : list Label)
  : Prop :=
  forall l value,
    lookup l = Some value ->
    In l support.

Record label_environment (A : Type) := {
  env_lookup :> Label -> option A;
  env_finite : exists support : list Label,
    label_environment_supports env_lookup support
}.

Arguments env_lookup {A} _ _.
Arguments env_finite {A} _.

Definition env_support
  {A : Type}
  (E : label_environment A)
  : list Label :=
  epsilon (inhabits []) (fun support =>
    label_environment_supports (env_lookup E) support).

Lemma env_supported
  {A : Type}
  (E : label_environment A)
  :
  label_environment_supports (env_lookup E) (env_support E).
Proof.
  unfold env_support.
  apply epsilon_spec.
  exact (env_finite E).
Qed.

Definition mk_environment
  {A : Type}
  (lookup : Label -> option A)
  (support : list Label)
  (supported : label_environment_supports lookup support)
  : label_environment A :=
  {|
    env_lookup := lookup;
    env_finite := ex_intro _ support supported
  |}.

Definition empty_environment
  {A : Type}
  : label_environment A :=
  mk_environment (fun _ => None) [] (fun _ _ H => match H with end).

Lemma environment_eq
  {A : Type}
  (E F : label_environment A)
  :
  (forall l, E l = F l) ->
  E = F.
Proof.
  destruct E as [El Efin].
  destruct F as [Fl Ffin].
  intro Hlookup.
  assert (El = Fl) as Hfun.
  {
    apply functional_extensionality.
    exact Hlookup.
  }
  subst Fl.
  f_equal.
  apply proof_irrelevance.
Qed.

Definition environment_map_values
  {A B : Type}
  (E : label_environment A)
  (f : Label -> A -> B)
  : label_environment B.
Proof.
  refine
    (mk_environment
      (fun l =>
        match E l with
        | Some value => Some (f l value)
        | None => None
        end)
      (env_support E)
      _).
  intros l value Hlookup.
  destruct (E l) as [source |] eqn:HE; inversion Hlookup; subst.
  eapply env_supported.
  exact HE.
Defined.

Definition IndicatorAssignment := IndicatorVariable -> IndicatorValue.

Definition environment_supports
  {A : Type}
  (lookup : Label -> IndicatorAssignment -> option A)
  (support : list Label)
  : Prop :=
  forall l i value,
    lookup l i = Some value ->
    In l support.

Record environment (A : Type) := {
  environment_lookup :> Label -> IndicatorAssignment -> option A;
  environment_finite : exists support : list Label,
    environment_supports environment_lookup support
}.

Arguments environment_lookup {A} _ _ _.
Arguments environment_finite {A} _.

Definition environment_support
  {A : Type}
  (E : environment A)
  : list Label :=
  epsilon (inhabits []) (fun support =>
    environment_supports (environment_lookup E) support).

Lemma environment_supported
  {A : Type}
  (E : environment A)
  :
  environment_supports (environment_lookup E) (environment_support E).
Proof.
  unfold environment_support.
  apply epsilon_spec.
  exact (environment_finite E).
Qed.

Definition mk_resolution_environment
  {A : Type}
  (lookup : Label -> IndicatorAssignment -> option A)
  (support : list Label)
  (supported : environment_supports lookup support)
  : environment A :=
  {|
    environment_lookup := lookup;
    environment_finite := ex_intro _ support supported
  |}.

Definition indicator_assignment_witness : IndicatorAssignment :=
  fun _ => nonempty_fin_witness IndicatorValue
.

Lemma indicator_assignment_inhabited : inhabited IndicatorAssignment.
Proof.
  exact (inhabits indicator_assignment_witness).
Qed.

Definition Atom := Test -> Prop.

Definition atom_dec (a : Atom) (t : Test) : {a t} + {~ a t} :=
  excluded_middle_informative (a t).

Inductive CFGKATTest :=
  | TPrim : Test -> CFGKATTest
  | TInd : IndicatorVariable -> IndicatorValue -> CFGKATTest
  | TTrue : CFGKATTest
  | TFalse : CFGKATTest
  | TAnd : CFGKATTest -> CFGKATTest -> CFGKATTest
  | TOr : CFGKATTest -> CFGKATTest -> CFGKATTest
  | TNot : CFGKATTest -> CFGKATTest.

Declare Scope test_scope.
Declare Scope cfgkat_scope.
Delimit Scope test_scope with test.
Bind Scope test_scope with CFGKATTest.
Notation "'prim' t" := (TPrim t) (at level 15) : test_scope.
Notation "'0'" := TFalse : test_scope.
Notation "'1'" := TTrue : test_scope.
Notation "'not' b" := (TNot b) (at level 30) : test_scope.
Notation "b 'and' c" := (TAnd b c) (at level 35) : test_scope.
Notation "b 'or' c" := (TOr b c) (at level 35) : test_scope.
Notation "x 'is' v" := (TInd x v) (at level 15) : test_scope.

Definition fold_TAnd := fold_right TAnd (1 : CFGKATTest).
Definition fold_TOr := fold_right TOr (0 : CFGKATTest).

Definition big_TAnd {A : FinType} (f : A -> CFGKATTest) : CFGKATTest :=
  fold_TAnd (map f (elements A)).

Definition big_TOr {A : FinType} (f : A -> CFGKATTest) : CFGKATTest :=
  fold_TOr (map f (elements A)).

Definition atom_to_test (a : Atom) : CFGKATTest :=
  big_TAnd (fun t => if atom_dec a t then TPrim t else TNot (TPrim t)).

Definition complete_test (i : IndicatorAssignment) : CFGKATTest :=
  big_TAnd (fun x => TInd x (i x)).

Fixpoint eval_test
  (e : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
:
  Prop
:=
  match e with
  | TPrim t => a t
  | TInd x v => i x = v
  | TTrue   => True
  | TFalse  => False
  | TAnd x y => eval_test x a i /\ eval_test y a i
  | TOr  x y => eval_test x a i \/ eval_test y a i
  | TNot x   => ~ eval_test x a i
  end.

Fixpoint test_indicator_free
  (x : IndicatorVariable)
  (b : CFGKATTest)
  : Prop :=
  match b with
  | TPrim _ => True
  | TInd y _ => y <> x
  | TTrue => True
  | TFalse => True
  | TAnd b1 b2 => test_indicator_free x b1 /\ test_indicator_free x b2
  | TOr b1 b2 => test_indicator_free x b1 /\ test_indicator_free x b2
  | TNot b' => test_indicator_free x b'
  end.

Lemma eval_fold_TAnd
  (l : list CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
:
  eval_test (fold_TAnd l) a i <-> (forall t, In t l -> eval_test t a i).
Proof.
  induction l as [|x xs IH];
  simpl; firstorder; now subst.
Qed.

Lemma eval_test_big_TAnd
  {J: FinType}
  (f: J -> CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
:
  eval_test (big_TAnd f) a i <-> forall j, eval_test (f j) a i
.
Proof.
  unfold big_TAnd. rewrite eval_fold_TAnd. firstorder.
  - apply H. apply in_map_iff.
    exists j; intuition.
    apply all_in.
  - apply in_map_iff in H0 as [j [? _]]; now subst.
Qed.

Lemma eval_fold_TOr
  (l : list CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
:
  eval_test (fold_TOr l) a i <-> (exists t, In t l /\ eval_test t a i).
Proof.
  induction l as [|x xs IH]; simpl; firstorder.
  subst; now left.
Qed.

Lemma eval_test_big_TOr
  {J: FinType}
  (f: J -> CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
:
  eval_test (big_TOr f) a i <-> exists j, eval_test (f j) a i
.
Proof.
  unfold big_TOr. rewrite eval_fold_TOr. firstorder.
  - apply in_map_iff in H as [j [? _]]; subst.
    eexists; eauto.
  - exists (f x); intuition.
    apply in_map_iff. eexists x; intuition.
    apply all_in.
Qed.

Lemma eval_atom_to_test (a' a'' : Atom) (i : IndicatorAssignment) :
  eval_test (atom_to_test a') a'' i <-> forall t, a' t <-> a'' t.
Proof.
  unfold atom_to_test.
  rewrite eval_test_big_TAnd.
  split.
  - intros H t. specialize (H t).
    destruct (atom_dec a' t); simpl in *; intuition.
  - intros H t. specialize (H t).
    destruct (atom_dec a' t); simpl; intuition.
Qed.

Lemma eval_complete_test (i' i'' : IndicatorAssignment) (a : Atom) :
  eval_test (complete_test i') a i'' <-> forall x, i' x = i'' x.
Proof.
  unfold complete_test.
  rewrite eval_test_big_TAnd. simpl.
  firstorder.
Qed.
