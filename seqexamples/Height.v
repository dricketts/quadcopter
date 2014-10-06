Require Import SeqLang.Syntax.
Require Import SeqLang.Semantics.
Require Import Rbase.
Require Import String.
Require Import Equality.

Open Scope HP_scope.
Open Scope string_scope.

Section HeightCtrl.

  (* The delays for evaluating the condition,
     running the first assignment, and
     running the second assignment. *)
  Variable d : time.

  (* Reading in the current height. *)
  Definition read :=
    "H" ::= "h"; "T" ::= "t".

  (* The controller. *)
  Definition ctrl :=
    IFF "H" < 0
    THEN "v" ::= 1
    ELSE "v" ::= --1.

  (* The continuous dynamics. *)
  Definition world :=
    ["h"' ::= "v", "t"' ::= 1].

  (* The entire system. The controller reads in the
     current height, runs the continuous program
     for d time, then outputs a new velocity. *)
  Definition sys :=
    (read; world @ d; ctrl)**.

  Definition init : Formula :=
    (--1 = "v" \/ "v" = 1) /\
    --d <= "h" /\ "h" <= d /\
    "t" = 0 /\ "T" = 0.

  Definition safe : Formula :=
    --2*d <="h" /\ "h" <= 2*d.

  Definition ind_inv : Formula :=
    ("v"=1 --> d-("t"-"T") <= 2*d-"h") /\
    ("v"=--1 --> d-("t"-"T") <= 2*d+"h") /\
    "t"-"T" <= d /\
    (--1 = "v" \/ "v" = 1).

  Lemma weaken_hyp : forall F1 F1' F2,
    (|- F1 --> F1') ->
    (|- F1' --> F2) ->
    (|- F1 --> F2).
  Proof. firstorder. Qed.

(*  Lemma strengthen_concl : forall F1 F2 F2',
    (|- F2' --> F2) ->
    (|- F1 --> F2') ->
    (|- F1 --> F2).
  Proof. firstorder. Qed.*)

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

Fixpoint is_st_formula (F:Formula) : bool :=
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

Lemma st_formula : forall F beh1 beh2,
  is_st_formula F = true ->
  eval_formula F beh1 ->
  beh1 time_0 = beh2 time_0 ->
  eval_formula F beh2.
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

Lemma bad :
  |- ("x" = 0 /\ |"x" ::= 1|) --> (2 = 0).
Proof.
  simpl. intros. destruct H as [Hinit [e [s [Hbeh] ] ] ].
  inversion Hbeh.
  inversion H4.
  subst e. simpl in *.
  subst tr.
  unfold eval_comp in *. simpl in *.
  rewrite H5 in Hinit. contradict Hinit.
  eapply F_1_neq_0.
  apply Rfield.
Qed.

Lemma assign_rule : forall x t I,
  is_st_formula I = true ->
  (|- (
  (|- (I /\ |x ::= t|) --> []I).

Lemma Rle_add_time1 : forall (t1 t2:time),
  (t1 <= add_time t1 t2)%R.
Admitted.

Fixpoint max_time (e:Event) : time :=
  match e with
    | Finish _ => time_0
    | Evolve f t e' => max_time e'
  end.

Require Import FunctionalExtensionality.      
  Lemma event_app_tr : forall e1 e2,
      toFunction (Event_app e1 e2) =
      fun t:time =>
        match time_left t (max_time e1) with
          | Some rem => toFunction e2 rem
          | None => toFunction e1 t
        end.
  Proof.
    induction e1; intros e2; simpl in *.
    - unfold time_left.
      apply functional_extensionality.
      intro t. destruct (Rlt_dec t time_0).
      + destruct t. unfold time_0. simpl in *.
        contradict r. apply Rle_not_lt; auto.
      + simpl. 
    - exists (toFunction e2). exists (toFunction e2).
      exists time_0. apply functional_extensionality. intro t.
      destruct (Rlt_dec t time_0); reflexivity.
    - destruct (IHe1 e2) as [tr1 [tr2 [b Heq] ] ].
      exists (fun r:time =>
                match time_left r t with
                  | Some rem => tr1 rem
                  | None => s r
                end).
      exists (fun r:time =>
                match time_left r t with
                  | Some rem => tr2 rem
                  | None => s r
                end).
      rewrite Heq.
      exists (add_time t b).
      apply functional_extensionality.
      intro x. unfold time_left. simpl.
      destruct (Rlt_dec x t).
      + destruct (Rlt_dec x (t + b)); auto.
      + simpl. destruct (Rlt_dec (x - t) b);
        destruct (Rlt_dec x (t + b)); auto.
        apply Rplus_lt_le_compat with (r3:=t) (r4:=t) in r.
        rewrite Rplus_comm in r. rewrite Rplus_minus in r.
        rewrite Rplus_comm in r. intuition.
        apply Rle_refl.
        contradict n0.
        apply Rlt_minus in r. apply Rminus_lt.
        admit.
  Qed.

Open Scope HP_scope.
  Lemma discr_ind : forall I p,
    is_st_formula I = true ->
    (|- (I /\ |p|) --> []I) ->
    (|- (I /\ |p**|) --> []I).
  Proof.
    simpl. intros I p Hst HI tr H t.
    destruct H as [Heval [e [s [Hbeh Hfun] ] ] ].
    generalize dependent tr.
    dependent induction Hbeh; intros.
    - simpl in *. rewrite <- Hfun.
      rewrite Hfun. auto.
    - subst tr0. pose proof (event_app_tr.


  Lemma seq_rule : forall I p1 p2,
    is_st_formula I = true ->
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