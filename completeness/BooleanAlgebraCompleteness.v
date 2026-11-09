Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.Classes.RelationClasses.
Require Import Stdlib.Classes.Morphisms.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.Permutation.
Import ListNotations.

From CFGKAT.Soundness Require Export BooleanAlgebraSoundness.
From CFGKAT.Semantics Require Export FiniteModels.

Local Open Scope type_scope.
Local Open Scope test_scope.

Lemma BAOrIdentity (b : CFGKATTest) :
  (b or 0) =BA b.
Proof.
  rewrite <- BAAndComplement with (b := b).
  apply BAOrAbsorption.
Qed.

Lemma BAAndIdentity (b : CFGKATTest) :
  (b and 1) =BA b.
Proof.
  rewrite <- BAOrComplement with (b := b).
  apply BAAndAbsorption.
Qed.

Local Lemma BAOrIdentityLeft (b : CFGKATTest) :
  (0 or b) =BA b.
Proof.
  now rewrite BAOrComm, BAOrIdentity.
Qed.

Local Lemma BAAndIdentityLeft (b : CFGKATTest) :
  (1 and b) =BA b.
Proof.
  now rewrite BAAndComm, BAAndIdentity.
Qed.

Local Lemma BAAndFalseRight (b : CFGKATTest) :
  (b and 0) =BA 0.
Proof.
  rewrite <- BAAndComplement with (b := b) at 1.
  now rewrite BAAndAssoc, BAAndIdem, BAAndComplement.
Qed.

Local Lemma BAAndFalseLeft (b : CFGKATTest) :
  (0 and b) =BA 0.
Proof.
  now rewrite BAAndComm, BAAndFalseRight.
Qed.

Local Lemma BAOrTrueRight (b : CFGKATTest) :
  (b or 1) =BA 1.
Proof.
  rewrite <- BAOrComplement with (b := b).
  now rewrite BAOrAssoc, BAOrIdem.
Qed.

Local Lemma BAOrTrueLeft (b : CFGKATTest) :
  (1 or b) =BA 1.
Proof.
  now rewrite BAOrComm, BAOrTrueRight.
Qed.

Lemma BAAndComplementLeft
  (b : CFGKATTest)
  :
  (not b) and b =BA 0.
Proof.
  rewrite BAAndComm.
  apply BAAndComplement.
Qed.

Lemma BAOrComplementLeft
  (b : CFGKATTest)
  :
  (not b) or b =BA 1.
Proof.
  rewrite BAOrComm.
  apply BAOrComplement.
Qed.

Lemma BANotFalse :
  (not 0) =BA 1.
Proof.
  now rewrite <- BAOrIdentityLeft, BAOrComplement.
Qed.

Lemma BANotTrue :
  (not 1) =BA 0.
Proof.
  now rewrite <- BAAndIdentityLeft, BAAndComplement.
Qed.

Local Lemma BAAndDistribRight (b c d : CFGKATTest) :
  ((b or c) and d) =BA ((b and d) or (c and d)).
Proof.
  rewrite BAAndComm, BAAndDistrib.
  now repeat rewrite BAAndComm with (c := d).
Qed.

Local Lemma BAOrDistribRight (a b c: CFGKATTest) :
  (a and b) or c =BA (a or c) and (b or c).
Proof.
  rewrite BAOrComm, BAOrDistrib.
  now repeat rewrite BAOrComm with (b := c).
Qed.

Local Lemma BA_complement_unique
  (a c : CFGKATTest)
  :
  (a or c) =BA 1 ->
  (a and c) =BA 0 ->
  c =BA not a.
Proof.
  intros Hor Hand.
  rewrite <- BAAndIdentity at 1.
  rewrite <- BAOrComplement with (b := a).
  rewrite BAAndDistrib, BAAndComm, Hand.
  rewrite BAOrIdentityLeft.
  rewrite <- BAAndIdentityLeft with (b := not a) at 2.
  rewrite <- Hor.
  rewrite BAAndDistribRight.
  rewrite BAAndComplement.
  now rewrite BAOrIdentityLeft.
Qed.

Lemma BANotNot
  (b : CFGKATTest)
  :
  not (not b) =BA b.
Proof.
  symmetry; apply BA_complement_unique.
  - apply BAOrComplementLeft.
  - apply BAAndComplementLeft.
Qed.

Local Lemma BANotOr
  (b c : CFGKATTest)
  :
  not (b or c) =BA ((not b) and (not c)).
Proof.
  symmetry.
  apply BA_complement_unique.
  - rewrite BAOrDistrib.
    rewrite <- BAOrAssoc with (d := not c).
    rewrite BAOrComplement.
    rewrite BAOrTrueRight.
    rewrite BAAndIdentity.
    rewrite BAOrComm with (b := b).
    rewrite <- BAOrAssoc.
    rewrite BAOrComplement.
    now rewrite BAOrTrueRight.
  - rewrite BAAndDistribRight.
    rewrite BAAndAssoc.
    rewrite BAAndComplement.
    rewrite BAAndFalseLeft.
    rewrite BAOrIdentityLeft.
    rewrite BAAndComm with (b := not b).
    rewrite BAAndAssoc.
    rewrite BAAndComplement.
    now rewrite BAAndFalseLeft.
Qed.

Lemma BANotAndNot
  (b c : CFGKATTest)
  :
  (not ((not b) and (not c))) =BA (b or c).
Proof.
  rewrite <- BANotOr.
  apply BANotNot.
Qed.

Definition BA_leq (b c : CFGKATTest) : Prop := (c or b) =BA c.

Definition BA_atom (b : CFGKATTest) : Prop :=
  ~ (b =BA 0) /\
  forall c, BA_leq c b -> (c =BA 0) \/ (c =BA b).

#[export] Program Instance BA_preorder :
  PreOrder BA_leq
.
Next Obligation.
  constructor.
  now rewrite BAOrIdem.
Qed.
Next Obligation.
  constructor.
  unfold BA_leq in *.
  rewrite <- H0.
  rewrite <- H at 1.
  now rewrite BAOrAssoc.
Qed.

#[export] Program Instance BA_partial_order :
  PartialOrder CFGKATBooleanAlgebraEquivalent BA_leq
.
Next Obligation.
  constructor; intros.
  - constructor.
    + unfold BA_leq.
      now rewrite H, BAOrIdem.
    + unfold Basics.flip, BA_leq.
      now rewrite H, BAOrIdem.
  - unfold BA_leq, Basics.flip in H. destruct H.
    rewrite <- H.
    rewrite <- H0 at 1.
    now rewrite BAOrComm.
Qed.

#[export] Program Instance TAnd_proper_leq :
  Proper (BA_leq ==>
          BA_leq ==>
          BA_leq) TAnd.
Next Obligation.
  constructor.
  unfold BA_leq in *.
  rewrite BAOrDistrib.
  repeat rewrite BAOrDistribRight.
  repeat rewrite BAAndAssoc.
  rewrite BAAndComm with (b := y or x).
  rewrite BAAndComm with (c := y0 or x0).
  repeat rewrite BAAndAssoc.
  rewrite H0, H.
  rewrite BAAndAbsorption.
  rewrite <- BAAndAssoc.
  rewrite BAAndAbsorption.
  apply BAAndComm.
Qed.

#[export] Program Instance TOr_proper_leq :
  Proper (BA_leq ==>
          BA_leq ==>
          BA_leq) TOr.
Next Obligation.
  constructor.
  unfold BA_leq in *.
  rewrite BAOrAssoc.
  rewrite BAOrComm with (c := x).
  rewrite BAOrAssoc.
  rewrite BAOrComm with (b := x).
  rewrite H.
  rewrite <- BAOrAssoc.
  now rewrite H0.
Qed.

Lemma BA_leq_and_right (b c : CFGKATTest) :
  BA_leq (b and c) b.
Proof.
  unfold BA_leq.
  apply BAOrAbsorption.
Qed.

Local Lemma BA_leq_and_left (b c : CFGKATTest) :
  BA_leq (b and c) c.
Proof.
  rewrite BAAndComm.
  apply BA_leq_and_right.
Qed.

Lemma BA_leq_left_weaken
  (p c b : CFGKATTest)
  :
  BA_leq c b ->
  BA_leq (p and c) b.
Proof.
  intro Hle.
  rewrite <- Hle.
  apply BA_leq_and_left.
Qed.

Local Lemma BA_leq_or_left (b c : CFGKATTest) :
  BA_leq b (b or c).
Proof.
  unfold BA_leq.
  rewrite BAOrComm.
  rewrite BAOrAssoc.
  now rewrite BAOrIdem.
Qed.

Lemma BA_leq_or_right (b c : CFGKATTest) :
  BA_leq c (b or c).
Proof.
  rewrite BAOrComm.
  apply BA_leq_or_left.
Qed.

Lemma BA_leq_to_and_right
  (a b : CFGKATTest)
  :
  BA_leq a b ->
  (a and b) =BA a.
Proof.
  unfold BA_leq.
  intro H.
  rewrite <- H.
  rewrite BAOrComm.
  apply BAAndAbsorption.
Qed.

Local Lemma BA_leq_from_and_right
  (a b : CFGKATTest)
  :
  (a and b) =BA a ->
  BA_leq a b.
Proof.
  intro H.
  rewrite <- H.
  rewrite BAAndComm.
  apply BAOrAbsorption.
Qed.

Local Lemma BA_leq_and_intro
  (a b c : CFGKATTest)
  :
  BA_leq a b ->
  BA_leq a c ->
  BA_leq a (b and c).
Proof.
  intros Hab Hac.
  rewrite <- Hac.
  rewrite <- Hab.
  now rewrite BAAndIdem.
Qed.

Lemma BA_leq_and_annihilate_right
  (a b c : CFGKATTest)
  :
  BA_leq a b ->
  (b and c) =BA 0 ->
  (a and c) =BA 0.
Proof.
  intros Hab Hbc.
  rewrite <- BA_leq_to_and_right with (a := a) (b := b); auto.
  rewrite <- BAAndAssoc.
  rewrite Hbc.
  apply BAAndFalseRight.
Qed.

Local Lemma BA_leq_and_complement_annihilate_right
  (a b : CFGKATTest)
  :
  BA_leq a b ->
  (a and (not b)) =BA 0.
Proof.
  intro Hab.
  eapply BA_leq_and_annihilate_right; eauto.
  apply BAAndComplement.
Qed.

Lemma BA_disjoint_to_leq_complement
  (a b : CFGKATTest)
  :
  (a and b) =BA 0 ->
  BA_leq a (not b).
Proof.
  intro Hab.
  apply BA_leq_from_and_right.
  rewrite <- BAOrIdentityLeft.
  rewrite <- Hab.
  rewrite <- BAAndDistrib.
  rewrite BAOrComplement.
  apply BAAndIdentity.
Qed.

Local Lemma fold_TAnd_member_leq
  (p : CFGKATTest)
  (xs : list CFGKATTest)
  :
  In p xs ->
  BA_leq (fold_TAnd xs) p.
Proof.
  induction xs as [|x xs IH]; simpl in *; try now intuition.
  intros [Hp | Hp].
  - subst. apply BA_leq_and_right.
  - simpl. rewrite BA_leq_and_left. intuition.
Qed.

Local Lemma fold_TOr_map_congr
  {A : Type}
  (f g : A -> CFGKATTest)
  (xs : list A)
  :
  (forall x, In x xs -> f x =BA g x) ->
  fold_TOr (map f xs) =BA fold_TOr (map g xs).
Proof.
  intro H.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite H by intuition (auto with *).
    rewrite IH; intuition (auto with *).
Qed.

Local Lemma fold_TAnd_map_congr
  {A : Type}
  (f g : A -> CFGKATTest)
  (xs : list A)
  :
  (forall x, In x xs -> f x =BA g x) ->
  fold_TAnd (map f xs) =BA fold_TAnd (map g xs).
Proof.
  intro H.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite H by intuition (auto with *).
    rewrite IH; try reflexivity.
    intros. apply H. intuition (auto with *).
Qed.

Local Lemma BAAnd_fold_TOr_distr_left
  (b : CFGKATTest)
  (xs : list CFGKATTest)
  :
  (b and (fold_TOr xs)) =BA
  fold_TOr (map (fun x => (b and x)) xs).
Proof.
  induction xs as [|x xs IH]; simpl.
  - apply BAAndFalseRight.
  - rewrite BAAndDistrib.
    now rewrite IH.
Qed.

Local Lemma BAAnd_fold_TOr_distr_right
  (b : CFGKATTest)
  (xs : list CFGKATTest)
  :
  ((fold_TOr xs) and b) =BA
  fold_TOr (map (fun x => (x and b)) xs).
Proof.
  rewrite BAAndComm.
  rewrite BAAnd_fold_TOr_distr_left.
  apply fold_TOr_map_congr.
  intros. apply BAAndComm.
Qed.

Local Lemma fold_TOr_app
  (xs ys : list CFGKATTest)
  :
  fold_TOr (xs ++ ys) =BA ((fold_TOr xs) or (fold_TOr ys)).
Proof.
  induction xs as [|x xs IH]; simpl.
  - now rewrite BAOrIdentityLeft.
  - now rewrite IH, BAOrAssoc.
Qed.

Fixpoint eval_test_dec
  (b : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
  : {eval_test b a i} + {~ eval_test b a i}.
Proof.
  induction b; simpl; try intuition.
  - exact (atom_dec a c).
  - destruct (Val_eq_dec (i c) c0) as [Heq | Hneq].
    + now left.
    + now right.
Defined.

Lemma BA_leq_eval
  (c b : CFGKATTest)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  BA_leq c b ->
  eval_test c a i ->
  eval_test b a i.
Proof.
  intros Hle Hc.
  apply (BooleanAlgebra_sound (b or c) b Hle a i).
  simpl. intuition.
Qed.

Definition test_literal (t : Test) (value : bool) : CFGKATTest :=
  match value with
  | true => (prim t)
  | false => (not (prim t))
  end.

Definition atom_term_on (ts : list Test) (ba : Test -> bool) : CFGKATTest :=
  fold_TAnd (map (fun t => test_literal t (ba t)) ts).

Definition complete_test_on
  (vs : list IndicatorVariable)
  (i : IndicatorAssignment)
  : CFGKATTest :=
  fold_TAnd (map (fun x => (x is (i x))) vs).

Lemma eval_complete_test_on
  (xs : list IndicatorVariable)
  (i' i : IndicatorAssignment)
  (a : Atom)
  :
  eval_test (complete_test_on xs i') a i <->
  forall x, In x xs -> i' x = i x.
Proof.
  unfold complete_test_on.
  rewrite eval_fold_TAnd; split.
  - intros H x Hx.
    erewrite (H (TInd x (i' x))); eauto.
    apply in_map_iff.
    firstorder.
  - intros H t Ht.
    apply in_map_iff in Ht as [x [<- Hx]].
    rewrite H; now eauto.
Qed.

Lemma complete_test_on_permutation
  (xs ys : list IndicatorVariable)
  (i : IndicatorAssignment)
  :
  Permutation xs ys ->
  complete_test_on xs i =BA complete_test_on ys i.
Proof.
  intro Hperm.
  induction Hperm.
  - reflexivity.
  - unfold complete_test_on in *. simpl in *.
    now rewrite IHHperm.
  - unfold complete_test_on. simpl.
    eapply BATrans.
    + apply BAAndAssoc.
    + eapply BATrans.
      * apply BAAndCong.
        -- apply BAAndComm.
        -- reflexivity.
      * apply BASym. apply BAAndAssoc.
  - etransitivity; eauto.
Qed.

Definition atom_term (ba : Test -> bool) : CFGKATTest :=
  atom_term_on (elements Test) ba.

Definition minterm (ba : Test -> bool) (i : IndicatorAssignment) : CFGKATTest :=
  ((atom_term ba) and (complete_test i)).

Definition set_bool_atom
  (t : Test)
  (value : bool)
  (ba : Test -> bool)
  : Test -> bool :=
  fun t' =>
    match Test_eq_dec t t' with
    | left _ => value
    | right _ => ba t'
    end.

Local Lemma atom_term_on_set_bool_atom_notin
  (ts : list Test)
  (t : Test)
  (value : bool)
  (ba : Test -> bool)
  :
  ~ In t ts ->
  atom_term_on ts (set_bool_atom t value ba) =BA
  atom_term_on ts ba.
Proof.
  intro Hnotin.
  apply fold_TAnd_map_congr.
  intros t' Ht'. unfold set_bool_atom.
  destruct (Test_eq_dec t t') as [Heq | _].
  - subst. contradiction.
  - reflexivity.
Qed.

Local Lemma complete_test_on_update_notin
  (vs : list IndicatorVariable)
  (x : IndicatorVariable)
  (value : IndicatorValue)
  (i : IndicatorAssignment)
  :
  ~ In x vs ->
  complete_test_on vs (update i x value) =BA complete_test_on vs i.
Proof.
  intro Hnotin.
  apply fold_TAnd_map_congr.
  intros x' Hx'. unfold update.
  destruct (Var_eq_dec x x') as [Heq | _].
  - subst. contradiction.
  - reflexivity.
Qed.

Local Lemma atom_term_on_cons_set_true
  (t : Test)
  (ts : list Test)
  (ba : Test -> bool)
  :
  ~ In t ts ->
  atom_term_on (t :: ts) (set_bool_atom t true ba)
    =BA ((prim t) and (atom_term_on ts ba)).
Proof.
  intro Hnotin.
  unfold atom_term_on at 1. simpl.
  unfold test_literal, set_bool_atom.
  destruct (Test_eq_dec t t) as [_ | Hneq].
  - now rewrite <- atom_term_on_set_bool_atom_notin
      with (t := t) (value := true) by intuition.
  - contradiction.
Qed.

Local Lemma atom_term_on_cons_set_false
  (t : Test)
  (ts : list Test)
  (ba : Test -> bool)
  :
  ~ In t ts ->
  atom_term_on (t :: ts) (set_bool_atom t false ba)
    =BA ((not (prim t)) and (atom_term_on ts ba)).
Proof.
  intro Hnotin.
  unfold atom_term_on at 1. simpl.
  unfold test_literal, set_bool_atom.
  destruct (Test_eq_dec t t) as [_ | Hneq].
  - now rewrite <- atom_term_on_set_bool_atom_notin
      with (t := t) (value := false) by intuition.
  - contradiction.
Qed.

Local Lemma complete_test_on_cons_update
  (x : IndicatorVariable)
  (vs : list IndicatorVariable)
  (value : IndicatorValue)
  (i : IndicatorAssignment)
  :
  ~ In x vs ->
  complete_test_on (x :: vs) (update i x value)
    =BA ((x is value) and (complete_test_on vs i)).
Proof.
  intro Hnotin.
  unfold complete_test_on at 1. simpl.
  unfold update.
  destruct (Var_eq_dec x x) as [_ | Hneq].
  - now rewrite <- complete_test_on_update_notin
      with (value := value) (x := x).
  - contradiction.
Qed.

Local Lemma fold_TOr_map_flat_map_pair
  {A B : Type}
  (h : B -> CFGKATTest)
  (f g : A -> B)
  (xs : list A)
  :
  fold_TOr (map h (flat_map (fun x => [f x; g x]) xs))
    =BA
  fold_TOr (map (fun x => ((h (f x)) or (h (g x)))) xs).
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - now rewrite IH, BAOrAssoc.
Qed.

Local Lemma atom_partition_aux
  (ts : list Test)
  :
  NoDup ts ->
  fold_TOr (map (atom_term_on ts) (all_bool_atoms_aux ts)) =BA 1.
Proof.
  induction ts as [|t ts IH]; intro Hnodup.
  - simpl. apply BAOrIdentity.
  - inversion Hnodup as [|? ? Hnotin Hnodup_tail]. subst.
    simpl all_bool_atoms_aux.
    rewrite fold_TOr_map_flat_map_pair, fold_TOr_map_congr.
    + now apply IH.
    + intros ba Hba.
      rewrite atom_term_on_cons_set_true with (t := t) (ba := ba) by auto.
      rewrite atom_term_on_cons_set_false with (t := t) (ba := ba) by auto.
      rewrite <- BAAndDistribRight.
      rewrite BAOrComplement.
      apply BAAndIdentityLeft.
Qed.

Local Lemma atom_partition :
  fold_TOr (map atom_term all_bool_atoms) =BA 1.
Proof.
  unfold atom_term, all_bool_atoms.
  apply atom_partition_aux.
  apply nodup.
Qed.

Local Lemma complete_test_values_partition
  (x : IndicatorVariable)
  (tail : CFGKATTest)
  :
  fold_TOr (map (fun value => ((x is value) and tail))
                 (elements IndicatorValue))
    =BA tail.
Proof.
  rewrite <- map_map with (g := fun y => y and tail)
                          (f := fun v => x is v).
  rewrite <- BAAnd_fold_TOr_distr_right.
  rewrite (BAIndicatorSum x).
  apply BAAndIdentityLeft.
Qed.

Local Lemma fold_TOr_map_flat_map_values
  {A B : Type}
  (h : B -> CFGKATTest)
  (f : A -> IndicatorValue -> B)
  (xs : list A)
  :
  fold_TOr (map h (flat_map (fun x =>
      map (fun value => f x value) (elements IndicatorValue)) xs)) =BA
  fold_TOr (map (fun x => fold_TOr (map (fun value =>
      h (f x value)) (elements IndicatorValue))) xs).
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite map_app, map_map.
    now rewrite fold_TOr_app, IH.
Qed.

Local Lemma complete_test_partition_aux
  (vs : list IndicatorVariable)
  :
  NoDup vs ->
  fold_TOr (map (complete_test_on vs) (all_assignments_aux vs)) =BA 1.
Proof.
  induction vs as [|x vs IH]; intro Hnodup.
  - simpl. apply BAOrIdentity.
  - inversion Hnodup as [|? ? Hnotin Hnodup_tail]. subst.
    simpl all_assignments_aux.
    rewrite fold_TOr_map_flat_map_values.
    rewrite fold_TOr_map_congr; eauto.
    intros i Hi.
    rewrite fold_TOr_map_congr.
    + apply complete_test_values_partition.
    + intros value _.
      now apply complete_test_on_cons_update.
Qed.

Lemma complete_test_partition :
  fold_TOr (map complete_test all_assignments) =BA 1.
Proof.
  unfold complete_test, all_assignments.
  apply complete_test_partition_aux.
  apply nodup.
Qed.

Definition AtIY := (Atom * IndicatorAssignment)%type.

Notation "'At' 'x' 'I^Y'" := AtIY (at level 0).

Definition all_AtIY : list (At x I^Y) :=
  flat_map
    (fun ba => map (fun i => (bool_to_atom ba, i)) all_assignments)
    all_bool_atoms.

Definition AtIY_test (m : At x I^Y) : CFGKATTest :=
  ((atom_to_test (fst m)) and (complete_test (snd m))).

Definition AtIY_atom (m : At x I^Y) : Atom :=
  fst m.

Definition AtIY_assignment (m : At x I^Y) : IndicatorAssignment :=
  snd m.

Lemma eval_AtIY_test_refl
  (a : Atom)
  (i : IndicatorAssignment)
  :
  eval_test (AtIY_test (a, i)) a i.
Proof.
  unfold AtIY_test. simpl. split.
  - apply eval_atom_to_test.
    intro t. tauto.
  - apply eval_complete_test.
    intro x. reflexivity.
Qed.

Lemma eval_AtIY_test_inv
  (a b : Atom)
  (i j : IndicatorAssignment)
  :
  eval_test (AtIY_test (a, i)) b j ->
  b = a /\ j = i.
Proof.
  unfold AtIY_test. simpl. intuition.
  - symmetry. extensionality t.
    apply propositional_extensionality.
    eapply eval_atom_to_test; eauto.
  - symmetry. extensionality x.
    eapply eval_complete_test; eauto.
Qed.

Lemma eval_AtIY_test_eq
  (m : At x I^Y)
  (a : Atom)
  (i : IndicatorAssignment)
  :
  eval_test (AtIY_test m) a i ->
  a = AtIY_atom m /\ i = AtIY_assignment m.
Proof.
  destruct m as [am im].
  apply eval_AtIY_test_inv.
Qed.

Lemma AtIY_test_nonzero
  (m : At x I^Y)
  :
  ~ (AtIY_test m =BA 0).
Proof.
  destruct m as [a i].
  intro Hzero.
  destruct (BooleanAlgebra_sound _ _ Hzero a i) as [Hsound _].
  simpl in Hsound.
  exact (Hsound (eval_AtIY_test_refl a i)).
Qed.

Lemma AtIY_in_all
  (a : Atom)
  (i : IndicatorAssignment)
  :
  In (a, i) all_AtIY.
Proof.
  destruct (bool_to_atom_eq a) as [ba [Hba Hatom]].
  unfold all_AtIY. apply in_flat_map.
  exists ba. split.
  - exact Hba.
  - apply in_map_iff.
    exists i. split.
    + now rewrite Hatom.
    + apply all_assignments_complete.
Qed.

Lemma AtIY_same_atom_assignment_in
  (m : (At x I^Y))
  (i : IndicatorAssignment)
  :
  In (AtIY_atom m, i) all_AtIY.
Proof.
  apply AtIY_in_all.
Qed.

Local Lemma atom_to_test_bool_to_atom
  (ba : Test -> bool)
  :
  atom_to_test (bool_to_atom ba) =BA atom_term ba.
Proof.
  unfold atom_to_test, big_TAnd, atom_term, atom_term_on.
  apply fold_TAnd_map_congr.
  intros t _.
  unfold bool_to_atom, test_literal.
  destruct (atom_dec (fun t0 : Test => ba t0 = true) t)
    as [Ht | Ht];
    destruct (ba t) eqn:Hba; try reflexivity.
  - discriminate.
  - exfalso. apply Ht. reflexivity.
Qed.

Local Lemma AtIY_test_bool_to_atom
  (ba : Test -> bool)
  (i : IndicatorAssignment)
  :
  AtIY_test (bool_to_atom ba, i) =BA minterm ba i.
Proof.
  unfold AtIY_test, minterm; simpl.
  now rewrite atom_to_test_bool_to_atom.
Qed.

Local Lemma fold_TOr_map_flat_map_const
  {A B C : Type}
  (h : C -> CFGKATTest)
  (f : A -> B -> C)
  (ys : list B)
  (xs : list A)
  :
  fold_TOr (map h (flat_map (fun x => map (f x) ys) xs)) =BA
  fold_TOr (map (fun x => fold_TOr (map (fun y => h (f x y)) ys)) xs).
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite map_app, map_map.
    now rewrite fold_TOr_app, IH.
Qed.

Local Lemma minterms_for_atom_partition
  (ba : Test -> bool)
  :
  fold_TOr (map (fun i => minterm ba i) all_assignments)
    =BA atom_term ba.
Proof.
  unfold minterm.
  rewrite <- map_map with (g := fun t => (atom_term ba) and t)
                          (f := complete_test).
  rewrite <- BAAnd_fold_TOr_distr_left.
  rewrite complete_test_partition.
  apply BAAndIdentity.
Qed.

Lemma minterm_partition :
  fold_TOr (map AtIY_test all_AtIY) =BA 1.
Proof.
  unfold all_AtIY.
  rewrite fold_TOr_map_flat_map_const.
  rewrite fold_TOr_map_congr.
  + apply atom_partition.
  + intros ba Hba.
    rewrite fold_TOr_map_congr.
    * apply minterms_for_atom_partition.
    * intros i _.
      apply AtIY_test_bool_to_atom.
Qed.

Local Lemma atom_term_leq_true_literal
  (ba : Test -> bool)
  (t : Test)
  :
  ba t = true ->
  BA_leq (atom_term ba) (prim t).
Proof.
  intro Htrue.
  unfold atom_term, atom_term_on.
  apply fold_TAnd_member_leq.
  apply in_map_iff.
  exists t. split.
  - unfold test_literal. now rewrite Htrue.
  - apply all_in.
Qed.

Local Lemma atom_term_leq_false_literal
  (ba : Test -> bool)
  (t : Test)
  :
  ba t = false ->
  BA_leq (atom_term ba) (not (prim t)).
Proof.
  intro Hfalse.
  unfold atom_term, atom_term_on.
  apply fold_TAnd_member_leq.
  apply in_map_iff.
  exists t. split.
  - unfold test_literal. rewrite Hfalse. reflexivity.
  - apply all_in.
Qed.

Local Lemma complete_test_leq_indicator
  (i : IndicatorAssignment)
  (x : IndicatorVariable)
  :
  BA_leq (complete_test i) ((x is (i x))).
Proof.
  unfold complete_test, complete_test_on.
  apply fold_TAnd_member_leq, in_map_iff.
  exists x. intuition.
  apply all_in.
Qed.

Lemma minterm_leq_atom_term
  (ba : Test -> bool)
  (i : IndicatorAssignment)
  :
  BA_leq (minterm ba i) (atom_term ba).
Proof.
  unfold minterm.
  apply BA_leq_and_right.
Qed.

Local Lemma minterm_leq_complete_test
  (ba : Test -> bool)
  (i : IndicatorAssignment)
  :
  BA_leq (minterm ba i) (complete_test i).
Proof.
  unfold minterm.
  apply BA_leq_and_left.
Qed.

Local Lemma minterm_leq_prim_true
  (ba : Test -> bool)
  (i : IndicatorAssignment)
  (t : Test)
  :
  ba t = true ->
  BA_leq (minterm ba i) (prim t).
Proof.
  intro Htrue.
  rewrite minterm_leq_atom_term.
  now apply atom_term_leq_true_literal.
Qed.

Local Lemma minterm_annihilates_prim_false
  (ba : Test -> bool)
  (i : IndicatorAssignment)
  (t : Test)
  :
  ba t = false ->
  ((minterm ba i) and (prim t)) =BA 0.
Proof.
  intro Hfalse.
  eapply BA_leq_and_annihilate_right.
  - rewrite minterm_leq_atom_term.
    apply atom_term_leq_false_literal; eauto.
  - now rewrite BAAndComm, BAAndComplement.
Qed.

Local Lemma minterm_leq_indicator_true
  (ba : Test -> bool)
  (i : IndicatorAssignment)
  (x : IndicatorVariable)
  (v : IndicatorValue)
  :
  i x = v ->
  BA_leq (minterm ba i) (x is v).
Proof.
  intro Hv; subst.
  rewrite minterm_leq_complete_test.
  apply complete_test_leq_indicator.
Qed.

Local Lemma minterm_annihilates_indicator_false
  (ba : Test -> bool)
  (i : IndicatorAssignment)
  (x : IndicatorVariable)
  (v : IndicatorValue)
  :
  i x <> v ->
  ((minterm ba i) and (x is v)) =BA 0.
Proof.
  intro Hneq.
  eapply BA_leq_and_annihilate_right.
  - rewrite minterm_leq_complete_test.
    apply complete_test_leq_indicator.
  - apply BAIndicatorExclusivity; eauto.
Qed.

Local Lemma BA_annihilate_leq_both
  (a a' b b' : CFGKATTest)
  :
  BA_leq a b ->
  BA_leq a' b' ->
  (b and b') =BA 0 ->
  (a and a') =BA 0.
Proof.
  intros Hab Ha'b' Hbb'.
  eapply BA_leq_and_annihilate_right; eauto.
  rewrite BAAndComm.
  eapply BA_leq_and_annihilate_right; eauto.
  now rewrite BAAndComm.
Qed.

Local Lemma assignment_neq_point
  (i j : IndicatorAssignment)
  :
  i <> j ->
  exists x, i x <> j x.
Proof.
  intro Hneq.
  apply not_all_ex_not.
  contradict Hneq.
  now extensionality n.
Qed.

Lemma complete_tests_disagree
  (i j : IndicatorAssignment)
  :
  i <> j ->
  ((complete_test i) and (complete_test j)) =BA 0.
Proof.
  intro Hneq.
  destruct (assignment_neq_point i j Hneq) as [x Hx].
  eapply BA_annihilate_leq_both.
  - apply complete_test_leq_indicator.
  - apply complete_test_leq_indicator.
  - apply BAIndicatorExclusivity. exact Hx.
Qed.

Local Lemma atom_to_test_leq_true_literal
  (a : Atom)
  (t : Test)
  :
  a t ->
  BA_leq (atom_to_test a) (prim t).
Proof.
  intro Htrue.
  apply fold_TAnd_member_leq.
  apply in_map_iff.
  exists t. split.
  - destruct (atom_dec a t) as [_ | Hfalse]; eauto.
    contradiction.
  - apply all_in.
Qed.

Local Lemma atom_to_test_leq_false_literal
  (a : Atom)
  (t : Test)
  :
  ~ a t ->
  BA_leq (atom_to_test a) (not (prim t)).
Proof.
  intro Hfalse.
  apply fold_TAnd_member_leq.
  apply in_map_iff.
  exists t. split.
  - destruct (atom_dec a t) as [Htrue | _]; eauto.
    contradiction.
  - apply all_in.
Qed.

Lemma AtIY_test_leq_atom_to_test
  (a : Atom)
  (i : IndicatorAssignment)
  :
  BA_leq (AtIY_test (a, i)) (atom_to_test a).
Proof.
  unfold AtIY_test. simpl.
  apply BA_leq_and_right.
Qed.

Lemma AtIY_test_leq_complete_test
  (a : Atom)
  (i : IndicatorAssignment)
  :
  BA_leq (AtIY_test (a, i)) (complete_test i).
Proof.
  unfold AtIY_test. simpl.
  apply BA_leq_and_left.
Qed.

Lemma AtIY_test_complete_test_same
  (a : Atom)
  (i : IndicatorAssignment)
  :
  ((AtIY_test (a, i)) and (complete_test i)) =BA AtIY_test (a, i).
Proof.
  apply BA_leq_to_and_right.
  apply AtIY_test_leq_complete_test.
Qed.

Lemma AtIY_test_complete_test_disagree
  (a : Atom)
  (i j : IndicatorAssignment)
  :
  j <> i ->
  ((AtIY_test (a, j)) and (complete_test i)) =BA 0.
Proof.
  intro Hneq.
  eapply BA_leq_and_annihilate_right.
  - apply AtIY_test_leq_complete_test.
  - now apply complete_tests_disagree.
Qed.

Local Lemma atom_neq_point
  (a a' : Atom)
  :
  a <> a' ->
  exists t, (a t /\ ~ a' t) \/ (~ a t /\ a' t).
Proof.
  intro Hneq. apply not_all_not_ex.
  contradict Hneq. extensionality t.
  apply propositional_extensionality.
  destruct (classic (a t)) as [Hat | Hnat];
  destruct (classic (a' t)) as [Hat' | Hnat'];
  firstorder.
Qed.

Lemma atom_to_tests_disagree
  (a a' : Atom)
  :
  a <> a' ->
  ((atom_to_test a) and (atom_to_test a')) =BA 0.
Proof.
  intro Hneq.
  destruct (atom_neq_point a a' Hneq) as [t [[Ha Hna'] | [Hna Ha']]].
  - eapply BA_annihilate_leq_both.
    + apply atom_to_test_leq_true_literal; eauto.
    + apply atom_to_test_leq_false_literal; eauto.
    + apply BAAndComplement.
  - eapply BA_annihilate_leq_both.
    + apply atom_to_test_leq_false_literal; eauto.
    + apply atom_to_test_leq_true_literal; eauto.
    + now rewrite BAAndComm, BAAndComplement.
Qed.

Lemma minterms_disagree
  (m n : (At x I^Y))
  :
  m <> n ->
  ((AtIY_test m) and (AtIY_test n)) =BA 0.
Proof.
  destruct m as [a i].
  destruct n as [a' j].
  intro Hneq.
  destruct (classic (a = a')) as [Ha | Ha].
  - subst a'.
    destruct (classic (i = j)) as [Hi | Hi].
    + subst j. contradiction Hneq. reflexivity.
    + eapply BA_annihilate_leq_both.
      * apply AtIY_test_leq_complete_test.
      * apply AtIY_test_leq_complete_test.
      * now apply complete_tests_disagree.
  - eapply BA_annihilate_leq_both.
    + apply AtIY_test_leq_atom_to_test.
    + apply AtIY_test_leq_atom_to_test.
    + now apply atom_to_tests_disagree.
Qed.

Local Lemma minterm_test_facts
  (b : CFGKATTest)
  (ba : Test -> bool)
  (i : IndicatorAssignment)
  :
  (eval_test b (bool_to_atom ba) i -> BA_leq (minterm ba i) b) /\
  (~ eval_test b (bool_to_atom ba) i ->
     ((minterm ba i) and b) =BA 0).
Proof.
  induction b as [t | x v | | | b IHb c IHc | b IHb c IHc | b IHb]; simpl.
  - split.
    + intro Htrue.
      now apply minterm_leq_prim_true.
    + intro Hfalse.
      apply minterm_annihilates_prim_false.
      destruct (ba t) eqn:Hbt; intuition.
  - split.
    + intro Hv. now apply minterm_leq_indicator_true.
    + intro Hneq. now apply minterm_annihilates_indicator_false.
  - intuition. apply BAOrTrueLeft.
  - intuition. apply BAAndFalseRight.
  - destruct IHb as [IHb_true IHb_false].
    destruct IHc as [IHc_true IHc_false].
    split.
    + intros [Hb Hc].
      apply BA_leq_and_intro; eauto.
    + intro Hnot.
      destruct (classic (eval_test b (bool_to_atom ba) i)) as [Hb | Hnb].
      * rewrite BAAndAssoc.
        rewrite BA_leq_to_and_right with (a := minterm ba i); auto.
      * rewrite BAAndAssoc.
        rewrite IHb_false; auto.
        apply BAAndFalseLeft.
  - destruct IHb as [IHb_true IHb_false].
    destruct IHc as [IHc_true IHc_false].
    split.
    + intros [Hb | Hc].
      * rewrite IHb_true; eauto.
        apply BA_leq_or_left.
      * rewrite IHc_true; eauto.
        apply BA_leq_or_right.
    + intro Hnot.
      rewrite BAAndDistrib.
      rewrite IHb_false by auto.
      rewrite IHc_false by auto.
      apply BAOrIdentity.
  - destruct IHb as [IHb_true IHb_false].
    split.
    + intro Hnot_b.
      apply BA_disjoint_to_leq_complement.
      now apply IHb_false.
    + intro Hnot_not_b.
      apply BA_leq_and_complement_annihilate_right.
      apply IHb_true.
      now apply NNPP.
Qed.

Definition in_test (m : At x I^Y) (b : CFGKATTest) : bool :=
  match eval_test_dec b (AtIY_atom m) (AtIY_assignment m) with
  | left _ => true
  | right _ => false
  end.

Notation "m '\in' b" := (in_test m b) (at level 70).

Lemma in_test_true
  (b : CFGKATTest)
  (m : At x I^Y)
  :
  m \in b = true ->
  eval_test b (AtIY_atom m) (AtIY_assignment m).
Proof.
  unfold in_test.
  destruct (eval_test_dec b (AtIY_atom m) (AtIY_assignment m)) as [Hb | Hnb].
  - intros _. exact Hb.
  - intro H. discriminate H.
Qed.

Lemma in_test_false
  (b : CFGKATTest)
  (m : At x I^Y)
  :
  m \in b = false ->
  ~ eval_test b (AtIY_atom m) (AtIY_assignment m).
Proof.
  unfold in_test.
  destruct (eval_test_dec b (AtIY_atom m) (AtIY_assignment m))
    as [Hb | Hnb]; simpl in *; intuition; discriminate.
Qed.

Lemma in_test_of_eval
  (b : CFGKATTest)
  (m : (At x I^Y))
  :
  eval_test b (AtIY_atom m) (AtIY_assignment m) ->
  (m \in b) = true.
Proof.
  unfold in_test.
  destruct (eval_test_dec b (AtIY_atom m) (AtIY_assignment m))
    as [_ | Hnb]; intuition.
Qed.

Lemma in_test_false_of_not_eval
  (b : CFGKATTest)
  (m : At x I^Y)
  :
  eval_test (not b) (AtIY_atom m) (AtIY_assignment m) ->
  (m \in b) = false.
Proof.
  unfold in_test.
  destruct (eval_test_dec b (AtIY_atom m) (AtIY_assignment m))
    as [Hb | _]; simpl in *; intuition.
Qed.

Lemma in_test_false_of_not_eval'
  (b : CFGKATTest)
  (m : At x I^Y)
  :
  ~ eval_test b (AtIY_atom m) (AtIY_assignment m) ->
  (m \in b) = false.
Proof.
  unfold in_test.
  destruct (eval_test_dec b (AtIY_atom m) (AtIY_assignment m))
    as [Hb | _]; intuition.
Qed.

Lemma in_test_not_true
  (b : CFGKATTest)
  (m : (At x I^Y))
  :
  (m \in b) = true ->
  (m \in (not b)) = false.
Proof.
  unfold in_test.
  destruct (eval_test_dec (not b) (AtIY_atom m) (AtIY_assignment m))
    as [Hnot | _]; intuition.
  exfalso. apply Hnot. now apply in_test_true.
Qed.

Lemma in_test_not_false
  (b : CFGKATTest)
  (m : (At x I^Y))
  :
  (m \in b) = false ->
  (m \in (not b)) = true.
Proof.
  unfold in_test.
  destruct (eval_test_dec (not b) (AtIY_atom m) (AtIY_assignment m))
    as [_ | Hnot]; intuition.
  exfalso. apply Hnot. now apply in_test_false.
Qed.

Definition boolean_dnf (b : CFGKATTest) : CFGKATTest :=
  fold_TOr (map AtIY_test (filter (fun m => m \in b) all_AtIY)).

Lemma minterm_test_reduce
  (b : CFGKATTest)
  (m : (At x I^Y))
  :
  ((AtIY_test m) and b)
    =BA
  match m \in b with
  | true => AtIY_test m
  | false => 0
  end.
Proof.
  destruct m as [a i].
  unfold in_test, AtIY_atom, AtIY_assignment. simpl.
  destruct (eval_test_dec b a i) as [Hb | Hnb].
  - destruct (bool_to_atom_eq a) as [ba [_ Hba]]; subst.
    rewrite AtIY_test_bool_to_atom.
    apply BA_leq_to_and_right.
    now apply minterm_test_facts.
  - destruct (bool_to_atom_eq a) as [ba [_ Hba]]; subst.
    rewrite AtIY_test_bool_to_atom.
    now apply minterm_test_facts.
Qed.

Lemma minterm_test_true_right
  (b : CFGKATTest)
  (m : (At x I^Y))
  :
  (m \in b) = true ->
  ((AtIY_test m) and b) =BA AtIY_test m.
Proof.
  intro Hsat.
  now rewrite minterm_test_reduce, Hsat.
Qed.

Lemma minterm_test_true_left
  (b : CFGKATTest)
  (m : (At x I^Y))
  :
  (m \in b) = true ->
  (b and (AtIY_test m)) =BA AtIY_test m.
Proof.
  rewrite BAAndComm.
  now apply minterm_test_true_right.
Qed.

Lemma minterm_test_false_right
  (b : CFGKATTest)
  (m : (At x I^Y))
  :
  (m \in b) = false ->
  ((AtIY_test m) and b) =BA 0.
Proof.
  intro Hsat.
  now rewrite minterm_test_reduce, Hsat.
Qed.

Lemma minterm_test_false_left
  (b : CFGKATTest)
  (m : (At x I^Y))
  :
  (m \in b) = false ->
  (b and (AtIY_test m)) =BA 0.
Proof.
  rewrite BAAndComm.
  now apply minterm_test_false_right.
Qed.

Lemma AtIY_test_atom
  (m : At x I^Y)
  :
  BA_atom (AtIY_test m).
Proof.
  split.
  - apply AtIY_test_nonzero.
  - intros b Hle.
    destruct (m \in b) eqn:Hsat.
    + right.
      eapply (BATrans b (b and AtIY_test m) (AtIY_test m)).
      * apply BASym. exact (BA_leq_to_and_right b (AtIY_test m) Hle).
      * now apply minterm_test_true_left.
    + left.
      eapply (BATrans b (b and AtIY_test m) 0).
      * apply BASym. exact (BA_leq_to_and_right b (AtIY_test m) Hle).
      * now apply minterm_test_false_left.
Qed.

Local Lemma fold_TOr_filter_false
  {A : Type}
  (p : A -> bool)
  (f : A -> CFGKATTest)
  (xs : list A)
  :
  fold_TOr (map (fun x => match p x with
                          | true => f x
                          | false => 0
                          end) xs) =BA
  fold_TOr (map f (filter p xs)).
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - destruct (p x) eqn:Hp.
    + now rewrite IH.
    + now rewrite BAOrIdentityLeft.
Qed.

Theorem boolean_dnf_BA
  (b : CFGKATTest)
  :
  b =BA boolean_dnf b.
Proof.
  unfold boolean_dnf.
  rewrite <- BAAndIdentityLeft.
  rewrite <- minterm_partition.
  rewrite BAAnd_fold_TOr_distr_right.
  rewrite map_map with (f := AtIY_test)
                       (g := fun x => x and b).
  rewrite fold_TOr_map_congr.
  - apply fold_TOr_filter_false.
  - intros m Hm.
    apply minterm_test_reduce.
Qed.

Theorem BA_atom_iff_AtIY_test
  (b : CFGKATTest)
  :
  BA_atom b <-> exists m, b =BA AtIY_test m.
Proof.
  split.
  - intros [Hnonzero Hminimal].
    destruct (filter (fun m => m \in b) all_AtIY) as [|m ms] eqn:Hfilter.
    + exfalso. apply Hnonzero.
      eapply BATrans.
      * apply boolean_dnf_BA.
      * unfold boolean_dnf. rewrite Hfilter. reflexivity.
    + assert (Hin : In m (filter (fun m => m \in b) all_AtIY)).
      { rewrite Hfilter. now left. }
      apply filter_In in Hin as [_ Hsat].
      assert (Hle : BA_leq (AtIY_test m) b).
      { apply BA_leq_from_and_right.
        now apply minterm_test_true_right. }
      destruct (Hminimal (AtIY_test m) Hle) as [Hzero | Hsame].
      * exfalso. exact (AtIY_test_nonzero m Hzero).
      * exists m. now apply BASym.
  - intros [m Hbm].
    split.
    + intro Hzero.
      apply (AtIY_test_nonzero m).
      eapply BATrans.
      * apply BASym. exact Hbm.
      * exact Hzero.
    + intros c Hle.
      destruct (AtIY_test_atom m) as [_ Hminimal].
      assert (Hle' : BA_leq c (AtIY_test m)).
      { unfold BA_leq in *.
        eapply BATrans.
        - apply BAOrCong.
          + apply BASym. exact Hbm.
          + reflexivity.
        - eapply BATrans.
          + exact Hle.
          + exact Hbm. }
      destruct (Hminimal c Hle') as [Hzero | Hsame].
      * now left.
      * right.
        eapply BATrans.
        -- exact Hsame.
        -- apply BASym. exact Hbm.
Qed.

Local Lemma boolean_dnf_ext
  (b c : CFGKATTest)
  :
  (forall m, (m \in b) = (m \in c)) ->
  boolean_dnf b =BA boolean_dnf c.
Proof.
  intro Hext. unfold boolean_dnf.
  now rewrite (filter_ext _ _ Hext all_AtIY).
Qed.

Theorem Boolean_denotation_completeness
  (b c : CFGKATTest)
  :
  CFGKATTestDenotationEquivalent b c ->
  b =BA c.
Proof.
  intro Hbc.
  rewrite boolean_dnf_BA with (b := b).
  rewrite boolean_dnf_BA with (b := c).
  apply boolean_dnf_ext.
  intros [a i].
  destruct ((a, i) \in b) eqn:Hb_sat;
  destruct ((a, i) \in c) eqn:Hc_sat;
  try reflexivity; exfalso.
  - eapply in_test_false; eauto.
    now apply Hbc, in_test_true.
  - eapply in_test_false; eauto.
    now apply Hbc, in_test_true.
Qed.
