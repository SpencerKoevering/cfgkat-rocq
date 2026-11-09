Require Import Stdlib.Program.Equality.
Require Import Stdlib.Setoids.Setoid.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.Logic.ClassicalEpsilon.
Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.Arith.Arith.
From Stdlib Require Import Lists.List.
Import ListNotations.

From CFGKAT.Semantics Require Export ExpressionSemantics.

Local Open Scope type_scope.

Fixpoint all_bool_atoms_aux (ts : list Test) : list (Test -> bool) :=
  match ts with
  | [] => [fun _ => true]
  | t :: rest =>
    flat_map (fun f =>
      (fun t' => match Test_eq_dec t t' with
                 | left _ => true
                 | right _ => f t' end) ::
      (fun t' => match Test_eq_dec t t' with
                 | left _ => false
                 | right _ => f t' end) ::
      nil)
    (all_bool_atoms_aux rest)
  end.

Fixpoint all_assignments_aux
  (vs : list IndicatorVariable)
: list IndicatorAssignment :=
  match vs with
  | [] => [indicator_assignment_witness]
  | v :: rest =>
    flat_map (fun f =>
      map (fun val => update f v val) (elements IndicatorValue))
    (all_assignments_aux rest)
  end.

Definition all_assignments :=
  all_assignments_aux (elements IndicatorVariable).
Definition all_bool_atoms :=
  all_bool_atoms_aux (elements Test).

Definition bool_to_atom (ba : Test -> bool) : Atom :=
  fun t => ba t = true.

Definition predicate_to_test
  (P : Atom -> IndicatorAssignment -> Prop)
  (P_dec : forall a i, {P a i} + {~ P a i}) : CFGKATTest :=
  fold_TOr (flat_map (fun ba =>
    let a := bool_to_atom ba in
    map (fun i => TAnd (atom_to_test a) (complete_test i))
        (filter (fun i => match P_dec a i with
                          | left _ => true
                          | right _ => false
                          end)
                all_assignments))
  all_bool_atoms).

Local Lemma all_bool_atoms_aux_complete (ts : list Test) (a : Atom) :
  NoDup ts ->
  exists ba, In ba (all_bool_atoms_aux ts) /\
             forall t, In t ts -> (ba t = true <-> a t).
Proof.
  intro Hnd.
  induction ts as [|t rest IH].
  - exists (fun _ => true). firstorder.
  - inversion Hnd as [|? ? Hnotin Hnd_rest]. subst.
    destruct (IH Hnd_rest) as [f [Hf_in Hf_char]].
    exists (fun t' => match Test_eq_dec t t' with
                      | left _ => match atom_dec a t with
                                  | left _ => true
                                  | right _ => false
                                  end
                      | right _ => f t'
                      end); split.
    * destruct (atom_dec a t);
      apply in_flat_map;
      eauto with *.
    * intros t' [<- | Hin].
      -- destruct (Test_eq_dec t t), (atom_dec a t);
           simpl in *; intuition; discriminate.
      -- destruct (Test_eq_dec t t') as [<- | _]; firstorder.
Qed.

Lemma bool_to_atom_eq (a : Atom) :
  exists ba, In ba all_bool_atoms /\ bool_to_atom ba = a.
Proof.
  unfold all_bool_atoms.
  destruct (all_bool_atoms_aux_complete (elements Test) a (nodup Test))
    as [ba [Hba_in Hba_char]]; eauto using all_in.
  exists ba; intuition; auto.
  extensionality t.
  apply propositional_extensionality.
  exact (Hba_char t (all_in Test t)).
Qed.

Lemma all_assignments_complete (i : IndicatorAssignment) :
  In i all_assignments.
Proof.
  unfold all_assignments.
  assert (Hcomplete :
    exists f, In f (all_assignments_aux (elements IndicatorVariable)) /\
              forall v, In v (elements IndicatorVariable) -> f v = i v).
  {
    induction (elements IndicatorVariable) as [|v rest IH].
    - exists indicator_assignment_witness; firstorder.
    - destruct IH as [f [Hf_in Hf_char]].
      exists (update f v (i v)). split.
      + apply in_flat_map; exists f.
        intuition; auto.
        apply in_map, all_in.
      + intros v' [<- | Hin].
        * apply update_same.
        * unfold update.
          destruct (Var_eq_dec v v'); auto.
          congruence.
  }
  destruct Hcomplete as [f [Hf_in Hf_char]].
  replace i with f. exact Hf_in.
  apply functional_extensionality. intro v.
  apply Hf_char. apply all_in.
Qed.


Lemma predicate_to_test_complete (P : Atom -> IndicatorAssignment -> Prop)
  (P_dec : forall a i, {P a i} + {~ P a i})
  (a : Atom) (i : IndicatorAssignment)
:
  P a i -> eval_test (predicate_to_test P P_dec) a i.
Proof.
  intro HP.
  unfold predicate_to_test.
  rewrite eval_fold_TOr.
  destruct (bool_to_atom_eq a) as [ba [Hba_in Hba_eq]].
  exists (TAnd (atom_to_test (bool_to_atom ba)) (complete_test i));
  simpl; intuition.
  - apply in_flat_map. exists ba. split. exact Hba_in.
    apply in_map_iff. exists i. intuition.
    apply filter_In; split.
    * apply all_assignments_complete.
    * destruct (P_dec (bool_to_atom ba) i) as [_ | HnP]; auto.
      exfalso. apply HnP. rewrite Hba_eq. exact HP.
  - apply eval_atom_to_test. intro t.
    rewrite Hba_eq. tauto.
  - apply eval_complete_test. intro x. reflexivity.
Qed.

Lemma predicate_to_test_sound (P : Atom -> IndicatorAssignment -> Prop)
  (P_dec : forall a i, {P a i} + {~ P a i})
  (a : Atom) (i : IndicatorAssignment)
:
  eval_test (predicate_to_test P P_dec) a i -> P a i.
Proof.
  unfold predicate_to_test.
  rewrite eval_fold_TOr.
  intros [t [Hin Ht]].
  apply in_flat_map in Hin as [ba [_ Hin]].
  apply in_map_iff in Hin as [i' [<- Hi'_in]].
  apply filter_In in Hi'_in as [_ Hfilter].
  destruct (P_dec (bool_to_atom ba) i') as [HP | HnP];
    try discriminate.
  destruct Ht as [Hat Hai].
  rewrite eval_atom_to_test in Hat.
  rewrite eval_complete_test in Hai.
  erewrite functional_extensionality with (f := a);
  erewrite functional_extensionality with (f := i); eauto.
  firstorder. now apply propositional_extensionality.
Qed.
