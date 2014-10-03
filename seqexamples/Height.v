Require Import SeqLang.Syntax.
Require Import SeqLang.Semantics.
Require Import Rbase.
Require Import String.

Open Scope HP_scope.
Open Scope string_scope.

Section HeightCtrl.

  (* The delays for evaluating the condition,
     running the first assignment, and
     running the second assignment. *)
  Variable d : time.

  (* Reading in the current height. *)
  Definition read :=
    "H" ::= `"h"; "T" ::= `"t".

  (* The controller. *)
  Definition ctrl :=
    IFF `"H" < #0
    THEN "v" ::= #1
    ELSE "v" ::= --#1.

  (* The continuous dynamics. *)
  Definition world :=
    ["h"' ::= `"v", "t"' ::= #1].

  (* The entire system. The controller reads in the
     current height, runs the continuous program
     for d time, then outputs a new velocity. *)
  Definition sys :=
    (read; world @ d; ctrl)**.

  Definition init : Formula string :=
    (--#1 = `"v" \/ `"v" = #1) /\
    --#d <=`"h" /\ `"h" <= #d /\
    `"t" = #0 /\ `"T" = #0.

  Definition safe : Formula string :=
    --#2*#d <=`"h" /\ `"h" <= #2*#d.

  Definition ind_inv : Formula string :=
    (`"v"=#1 --> #d-(`"t"-`"T") <= #2*#d-`"h") /\
    (`"v"=--#1 --> #d-(`"t"-`"T") <= #2*#d+`"h") /\
    `"t"-`"T" <= #d /\
    (--#1 = `"v" \/ `"v" = #1).

  Lemma weaken_hyp : forall F1 F1' F2,
    (|- F1 --> F1') ->
    (|- F1' --> F2) ->
    (|- F1 --> F2).
  Proof. firstorder. Qed.

  Lemma strengthen_concl : forall F1 F2 F2',
    (|- F2' --> F2) ->
    (|- F1 --> F2') ->
    (|- F1 --> F2).
  Proof. firstorder. Qed.

  Lemma always_imp : forall F1 F2,
    (|- F1 --> F2) ->
    (|- []F1 --> []F2).
  Proof. firstorder. Qed.

  Lemma and_right : forall F1 F2 F3,
    (|- F1 --> F2) ->
    (|- F1 --> F3) ->
    (|- F1 --> (F2 /\ F3)).
  Proof. firstorder. Qed.

  Lemma and_left1 : forall F1 F2 F3,
    (|- F1 --> F3) ->
    (|- (F1 /\ F2) --> F3).
  Proof. firstorder. Qed.

  Lemma and_left2 : forall F1 F2 F3,
    (|- F2 --> F3) ->
    (|- (F1 /\ F2) --> F3).
  Proof. firstorder. Qed.

  Lemma imp_id : forall F,
    |- F --> F.
  Proof. firstorder. Qed.

Fixpoint is_st_formula {Var} (F:Formula Var) : bool :=
  match F with
    | CompF _ _ _ => true
    | AndF F1 F2 => andb (is_st_formula F1)
                         (is_st_formula F2)
    | OrF F1 F2 => andb (is_st_formula F1)
                        (is_st_formula F2)
    | Imp F1 F2 => andb (is_st_formula F1)
                        (is_st_formula F2)
    | _ => false
  end.

Lemma st_formula : forall Var (F:Formula Var)
                          beh1 beh2,
  is_st_formula F = true ->
  eval_formula _ F beh1 ->
  beh1 time_0 = beh2 time_0 ->
  eval_formula _ F beh2.
Proof.
  induction F; simpl in *; intros; auto;
  try discriminate.
  - rewrite <- H1. auto.
  - apply Bool.andb_true_iff in H.
    split; try apply (IHF1 beh1);
    try apply (IHF2 beh1); tauto.
  - apply Bool.andb_true_iff in H.
    destruct H0; [left; apply (IHF1 beh1) |
    right; apply (IHF2 beh1)]; tauto.
  - apply Bool.andb_true_iff in H. firstorder.
Qed.

  Lemma discr_ind : forall I p,
   (* is_st_formula I = true ->*)
    (|- I /\ (|p| --> []I)) ->
    (|- (*I /\ |p**| -->*) []I).
  Proof.
    simpl. intros.
    destruct t. destruct cond_nonneg.
    - admit.
    - Show Proof. firstorder. Show Proof.


 firstorder.
Show Proof.
Variable tr : trace string.
Variable p : HybridProg string.
Variable t : time.
Variable I : Formula string.
Eval simpl in eval_formula string (I /\ (|p | --> []I))
                      (fun r : nonnegreal => tr (add_time r t)).
Print and_ind.
Definition test :=

(fun
               H5 : eval_formula string (I /\ (|p | --> []I))
                      (fun r : nonnegreal => tr (add_time r t)) =>
             and_ind
               (fun
                  (H6 : eval_formula string I
                          (fun r : nonnegreal => tr (add_time r t)))
                  (_ : eval_formula string (|p | --> []I)
                         (fun r : nonnegreal => tr (add_time r t))) => H6) H5).
    simpl. intros.
    split.
    - apply H.
    - intros.
      firstorder.
      Show Proof.

  Lemma seq_rule : forall I p1 p2,
    (|- (I /\ |p1|) --> []I) ->
    (|- (I /\ |p2|) --> []I) ->
    (|- (I /\ |p1; p2|) --> []I).
  Admitted.

  Lemma ind_inv_init : |- init --> ind_inv.
  Proof.
    simpl. intros. decompose [and or] H;
    unfold eval_comp in *; simpl in *;
    rewrite H3; rewrite H5; repeat split; intros.
    - rewrite <- H2 in H4. contradict H4.
      (* -1 <> 1 *) admit.
    - (* -d <= h <= d -> d <= 2d + h *) admit.
    - destruct d. simpl. rewrite Rminus_0_r. auto.
    - left; auto.
    - (* -d <= h <= d -> d <= 2d + h *) admit.
    - rewrite H2 in H4. contradict H4.
      (* 1 <> -1 *) admit.
    - destruct d. simpl. rewrite Rminus_0_r. auto.
    - right; auto.
  Qed.

  Lemma ind_inv_safe : |- ind_inv --> safe.
  Proof.
    simpl. intros. decompose [and] H; clear H.
    destruct H4; unfold eval_comp in *;
    simpl in *; split.
    - symmetry in H. apply H2 in H.
      admit.
    - symmetry in H. apply H2 in H.
      admit.
    - apply H0 in H.
      admit.
    - apply H0 in H.
      admit.
  Qed.

  (* The safety property. Any behavior produced by
     the system has the invariant -2d <= h <= 2d. *)
  (* We'll need to add some initial conditions here.
     It remains to be seen what those are. *)
  Lemma safety :
    |- (init /\ |sys|) --> []safe.
  Proof.
    apply weaken_hyp with (F1':=ind_inv /\ |sys|).
    - apply and_right. apply and_left1.
      apply ind_inv_init.
      apply and_left2. apply imp_id.
    - apply strengthen_concl with (F2':=[]ind_inv).
      + apply always_imp. apply ind_inv_safe.
      + apply discr_ind; try reflexivity.
        repeat apply seq_rule.
        *

  (* The liveness property. Any behavior produced by
     the system has some point in time in which h = c. *)
  Lemma liveness :
    |- |sys| --> <>`"h" = #c.
  Admitted.

End HeightCtrl.