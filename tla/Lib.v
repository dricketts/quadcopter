Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.RIneq.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ExtLib.Tactics.
Require Charge.Logics.ILInsts.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.BasicProofRules.
Require Import TLA.Automation.

(* A library of useful TLA formulas, built
   from TLA primitives. *)

Local Open Scope HP_scope.
Local Open Scope string_scope.

(* Action formula expressing that all variables
   in xs are unchanged. *)
Fixpoint Unchanged (xs:list Var) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (x! = x) //\\ (Unchanged xs)
  end.

Fixpoint UnchangedT (xs:list Term) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (next_term x = x) //\\ (UnchangedT xs)
  end.

(* Formula taking the maximum of two terms. *)
Definition Max (a b : Term)
           (c : Term -> Formula) : Formula :=
  (a >= b -->> (c a)) //\\ (a <= b -->> c b).

(* State formula expressing that the values of all
   variables in xs in the current state are equal
   to their value in st. *)
Fixpoint VarsAgree (xs:list Var) (st:state) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (x = st x) //\\ (VarsAgree xs st)
  end.

(* Action formula expressing that the values of all
   variables in xs in the next state are equal to
   their value in st. *)
Fixpoint AVarsAgree (xs:list Var) (st:state) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (x! = st x) //\\ (AVarsAgree xs st)
  end.

(* Our shallow encoding of continuous evolutions. *)
Definition DerivMap := (Var->Term).
Definition Evolution : Type := state -> Formula.

Global Instance ILogicOps_Evolution : ILogicOps Evolution :=
  @Charge.Logics.ILInsts.ILFun_Ops _ _ _.
Global Instance ILogic_Evolution : ILogic Evolution :=
  @Charge.Logics.ILInsts.ILFun_ILogic _ _ _ _.

Transparent Charge.Logics.ILInsts.ILFun_Ops.

Lemma Evolution_lequiv_lequiv : forall (a b : Evolution),
    (a -|- b) <-> (forall x, a x -|- b x).
Proof.
  unfold lequiv. simpl. intros. intuition.
  apply H. apply H.
Qed.

Lemma Evolution_lentails_lentails : forall (a b : Evolution),
    (a |-- b) <-> (forall x, a x |-- b x).
Proof. intros. exact (conj (fun x => x) (fun x => x)). Qed.

Opaque Charge.Logics.ILInsts.ILFun_Ops.

Definition deriv_stateF
           (f : R -> state)
           (is_derivable : forall x, derivable (fun t => f t x))
  :=
  fun x => derive (fun t => f t x) (is_derivable x).

(* Expresses the property that a differentiable formula
   is a solution to a list of differential equations
   in the range 0 to r. *)
Definition solves_diffeqs (f : R -> state)
           (cp : Evolution) (r : R)
           (is_derivable : forall x, derivable (fun t => f t x)) :=
    forall z, (R0 <= z <= r)%R ->
              eval_formula (cp (fun x =>
                                  deriv_stateF f is_derivable x z))
                           (Stream.forever (f z)).

(* Prop expressing that f is a solution to diffeqs in
   [0,r]. *)
Definition is_solution (f : R -> state)
           (cp:Evolution) (r : R) :=
  exists is_derivable,
    (* f is a solution to diffeqs *)
    solves_diffeqs f cp r is_derivable.

(* Action formula expressing that a transition
   is consistent with the system of differential
   equations represented by cp. *)
Definition Continuous (cp:Evolution) : Formula :=
  Exists r : R,
  Exists f : R -> state,
         (r > 0)
    //\\ (PropF (is_solution f cp r))
    //\\ (Embed (fun st st' => f R0 = st /\ f r = st')).

Global Instance Proper_is_solution_lequiv
: Proper (eq ==> pointwise_relation _ lequiv ==> eq ==> iff)
         is_solution.
Proof.
  morphism_intro.
  subst. unfold is_solution.
  eapply exists_iff. intros.
  unfold solves_diffeqs.
  eapply forall_iff; intros.
  eapply impl_iff; try reflexivity. intros.
  red in H0.
  match goal with
  |- context [eval_formula (_ ?c) _]
    => specialize (H0 c)
  end.
  destruct H0; intuition.
Qed.

Global Instance Proper_is_solution_lequiv2
: Proper (eq ==> (pointwise_relation _ term_equiv ==> lequiv) ==> eq ==> iff)
         is_solution.
Proof.
  morphism_intro.
  subst. unfold is_solution.
  eapply exists_iff. intros.
  unfold solves_diffeqs.
  eapply forall_iff; intros.
  eapply impl_iff; try reflexivity. intros.
  red in H0.
  match goal with
  |- context [eval_formula (_ ?c) _]
    => specialize (H0 c)
  end.
  specialize (H0 (fun x2 : Var => derive (fun t : R => y t x2) (x x2) x1)).
  rewrite lequiv_to_iff in H0.
  eapply H0.
  reflexivity.
Qed.

Instance Proper_is_solution_lentails
  : Proper (eq ==> lentails ==> Rge ==> Basics.impl) is_solution.
Proof.
  morphism_intro. red. unfold is_solution.
  subst.
  intros. destruct H. exists x.
  unfold solves_diffeqs in *.
  intros.
  assert (0 <= z <= x1)%R.
  { destruct H2. split. assumption.
    eapply Rle_trans. eassumption.
    eapply Rge_le. assumption. }
  eapply H in H3.
  specialize (H0 (fun x2 : Var => deriv_stateF y x x2 z)
                 (Stream.forever (y z))).
  eauto.
Qed.

(** TODO: These should probably be done with subrelations **)
Global Instance Proper_Continuous_entails
  : Proper ((pointwise_relation _ lentails) ==> lentails) Continuous.
Proof.
  do 5 red.
  simpl. destruct tr; simpl.
  destruct 1. destruct H0.
  exists x0. intuition.
  eexists; split; eauto.
  split; eauto.
  unfold is_solution in *. destruct H0. exists x2.
  unfold solves_diffeqs in *.
  intros.
  specialize (H0 _ H3).
  eapply H. assumption.
Qed.

Global Instance Proper_Continuous_equiv
  : Proper ((pointwise_relation _ lequiv) ==> lequiv) Continuous.
Proof.
  morphism_intro.
  eapply lequiv_to_iff.
  intros. simpl.
  apply exists_iff; intros.
  apply exists_iff; intros.
  eapply and_iff; try tauto; intros.
  eapply and_iff; try tauto; intros.
  unfold is_solution.
  apply exists_iff; intros.
  unfold solves_diffeqs.
  apply forall_iff; intros.
  apply impl_iff; try tauto; intros.
  red in H.
  rewrite H.
  eapply Proper_eval_formula; reflexivity.
Qed.

Instance Proper_Continuous_lentails:
  Proper (lentails ==> lentails) Continuous.
Proof. exact Proper_Continuous_entails. Qed.

Instance Proper_Continuous_lequiv:
  Proper (lequiv ==> lequiv) Continuous.
Proof.
  morphism_intro.
  eapply Proper_Continuous_equiv.
  red. eapply Evolution_lequiv_lequiv. assumption.
Qed.


(*
Lemma VarRenameMap_derivable : forall f m,
    (forall x, Ranalysis1.derivable (fun t => f t x)) ->
    forall x,
      Ranalysis1.derivable
        (fun t => subst_state (VarRenameMap m) (f t) x).
Proof.
  intros.
  induction m.
  - simpl. auto.
  - simpl. destruct a. simpl.
    destruct (String.string_dec x v).
    + subst. apply H.
    + auto.
Qed.*)

(*
Lemma subst_VarRenameMap_derive_distr :
  forall m f z pf1 pf2,
    subst_state (VarRenameMap m)
          (fun x =>
             Ranalysis1.derive (fun t : R => f t x) (pf1 x) z) =
    fun x =>
      Ranalysis1.derive (fun t : R =>
                           subst_state (VarRenameMap m) (f t) x) (pf2 x)
                        z.
Proof.
  intros. apply functional_extensionality.
  intros. generalize (pf2 x). clear pf2.
  induction m; intros.
  - simpl. apply Ranalysis4.pr_nu_var. auto.
  - destruct a. simpl in *.
    destruct (String.string_dec x v).
    + subst. apply Ranalysis4.pr_nu_var.
      auto.
    + erewrite IHm. auto.
Qed.
*)

(*
Lemma subst_VarRenameMap_derive_distr :
  forall m f z pf1 pf2,
    subst_derivmap (VarRenameMap m)
          (fun x =>
             Ranalysis1.derive (fun t : R => f t x) (pf1 x) z) =
    fun x =>
      Ranalysis1.derive
        (fun t : R =>
           subst_derivmap (VarRenameMap m) (f t) x) (pf2 x)
        z.
Proof.
  intros. apply functional_extensionality.
  intros. generalize (pf2 x). clear pf2.
  induction m; intros.
  - simpl. apply Ranalysis4.pr_nu_var. auto.
  - destruct a. simpl in *.
    destruct (String.string_dec x v).
    + subst. apply Ranalysis4.pr_nu_var.
      auto.
    + erewrite IHm. auto.
Qed.
*)

Lemma lequiv_eq : forall {T} (lo : ILogicOps T) (IL : ILogic T) (a b : T),
    a = b -> a -|- b.
Proof. intros; subst; reflexivity. Qed.


Import Stream.

Definition RenameDerivOk (r : RenameMap) (r' : state->Var->Term) : Prop :=
  forall f (pf2:forall x : Var, derivable (fun t : R => f t x)),
  exists (pf1:forall v,
             derivable (fun t : R =>
                          eval_term (r v) (f t) (f t))),
  forall v,
    let e := r v in
    let e' t := r' (fun x => deriv_stateF f pf2 x t) v in
    forall z,
      (0 <= z)%R ->
      eq
        (Ranalysis1.derive
           (fun t => eval_term e (f t) (f t)) (pf1 v) z)
        (eval_term (e' z) (f z) (f z)).


Theorem Rename_Continuous :
  forall (r : RenameMap) (r' : state->Var->Term)
         (c:Evolution),
  RenameDerivOk r r' ->
      Continuous (fun st' => (Forall x : Var, st' x = r' st' x) //\\ Rename r (c st'))
  |-- Rename r (Continuous c).
Proof.
  breakAbstraction. intros.
  forward_reason.
  rewrite (Stream.trace_eta tr).
  rewrite (Stream.trace_eta (Stream.tl tr)). simpl.
  exists x. exists (fun t => subst_state r (x0 t)).
  split; auto.
  rewrite H2; clear H2; rewrite H3; clear H3.
  split; auto.

  unfold is_solution in *.
  destruct H1 as [pf1 H1].
  specialize (H x0 pf1).
  destruct H as [pf2 H]. exists pf2.
  unfold solves_diffeqs in *.
  intros. specialize (H1 _ H2).
  simpl in H1.
  rewrite Stream.stream_map_forever in H1;
    eauto with typeclass_instances.
  unfold deriv_stateF, subst_state in *.
  destruct H1.
  specialize (fun v => H v z (proj1 H2)).
  setoid_rewrite <- H1 in H; clear H1.
  eapply Proper_eval_formula; [ | reflexivity | eassumption ].
  eapply lequiv_eq; eauto with typeclass_instances.
  f_equal.
  eapply functional_extensionality. intros.
  rewrite H. reflexivity.
Qed.

Theorem Rename_Continuous' :
  forall (r : RenameMap) (r' : state->Var->Term)
         (c:Evolution),
  RenameDerivOk r r' ->
  Continuous (fun st' => Forall st'' : state,
                            (Forall x : Var, st'' x = r' st' x) -->> Rename r (c st''))
 |-- Rename r (Continuous c).
Proof.
  breakAbstraction. intros.
  forward_reason.
  rewrite (Stream.trace_eta tr).
  rewrite (Stream.trace_eta (Stream.tl tr)). simpl.
  exists x. exists (fun t => subst_state r (x0 t)).
  split; auto.
  rewrite H2; clear H2; rewrite H3; clear H3.
  split; auto.

  unfold is_solution in *.
  destruct H1 as [pf1 H1].
  specialize (H x0 pf1).
  destruct H as [pf2 H]. exists pf2.
  unfold solves_diffeqs in *.
  intros. specialize (H1 _ H2).
  simpl in H1.
  specialize (H1 (fun x1 : Var =>
         deriv_stateF (fun t : R => subst_state r (x0 t)) pf2 x1 z)).
  rewrite Stream.stream_map_forever in H1;
    eauto with typeclass_instances.
  unfold deriv_stateF, subst_state in *.
  match type of H1 with
  | ?H -> _ => assert H
  end.
  { intros; apply H; tauto. }
  forward_reason.
  eapply Proper_eval_formula; [ | reflexivity | eassumption ].
  eapply lequiv_eq; eauto with typeclass_instances.
Qed.

Lemma UnchangedT_app :
  forall l1 l2,
    UnchangedT (l1 ++ l2) -|-
    UnchangedT l1 //\\ UnchangedT l2.
Proof.
  induction l1.
  - simpl. restoreAbstraction. split; charge_tauto.
  - simpl. restoreAbstraction. intros. rewrite IHl1.
    split; charge_tauto.
Qed.
