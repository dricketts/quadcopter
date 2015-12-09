Require Import Logic.Logic.
Require Import Logic.BasicProofRules.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import ChargeTactics.Lemmas.
Require Import Examples.ParLang.ParLang.
Require Import Examples.Velocity.

Open Scope HP_scope.
Open Scope string_scope.

Goal exists ins outs, exists prog : Parallel ins outs,
      Abstracts ("x"! = 2 //\\ "y"! = 3) prog.
Proof.
  do 3 eexists.
  Synth_Term.
  Grab Existential Variables.
  unfold sets_disjoint. intros. intro. red in H. destruct H.
  Focus 2. assumption.
  destruct H0. congruence.
  assumption.
Qed.

Goal
  exists ins outs, exists prog : Parallel ins outs,
      (* Abstracts ("x"! = "x" //\\ "x" = 3) prog. *)
      Abstracts (("x"=3 //\\ "x"!="x") \\// ("x"!=7)) prog.
Proof.
  do 3 eexists.
  Synth_Term.
Qed.

(* Velocity Shim *)
Module MyParams <: VelocityShimParams.
                    Local Open Scope R_scope.
                    Definition ub : R := 100.
                    Definition d : R := 10.
                    Parameter d_gt_0 : (d > 0).
End MyParams.

Module MyVelShim := VelocityShim MyParams.

(*

Abstracts (("a") ! * MyParams.d + "v" <= MyParams.ub \\// ("a") ! <= 0) ?271

if ("a") * MyParams.d + "v" <= MyParams.u
then ("a") ! = "a"
else synth ("a") ! <= 0

 *)

Definition copy_next (vs : list Var) : Formula :=
  List.fold_right (fun v f => v! = v //\\ f) ltrue vs.

Lemma copy_next_app : forall ys xs,
    copy_next (xs ++ ys) -|- copy_next xs //\\ copy_next ys.
Proof.
  induction xs.
  { simpl copy_next. restoreAbstraction. split; charge_tauto. }
  { simpl. restoreAbstraction.
    rewrite IHxs. rewrite landA. reflexivity. }
Qed.

Require Import Coq.Classes.Morphisms.
Instance Proper_Abstracts_lequiv {ins outs}
  : Proper (lequiv ==> eq ==> iff) (@Abstracts ins outs).
Proof.
  red. red. red. intros.
  subst. unfold Abstracts.
  setoid_rewrite H.
  reflexivity.
Qed.

Lemma copy_next_abstracts_concat :
  forall {ins outs}
         (xs ys : list Var)
         (N : Parallel ins outs),
    Abstracts (copy_next (xs ++ ys)) N ->
    Abstracts (copy_next xs) N /\
    Abstracts (copy_next ys) N.
Proof.
  intros. rewrite copy_next_app in H.
  unfold Abstracts in *; split.
  { intuition. eapply H; eauto. }
  { intuition. eapply H; eauto. }
Qed.

Lemma copy_next_undup : forall xs,
    copy_next xs -|- copy_next (remove_dup xs).
Proof.
  induction xs.
  { simpl. reflexivity. }
  { simpl. admit.  }
Admitted.

Lemma Abstracts_copy_next_same
  : forall {ins outs1} st1 st3 vs (N : Parallel ins outs1),
    Abstracts (copy_next vs) N ->
    (forall x, In x vs -> In x outs1) ->
    (forall x, In x outs1 -> eval_Parallel N st1 x = st3 x) ->
    (forall x, In x vs -> st1 x = st3 x).
Proof.
  induction vs; simpl in *; intros.
  { contradiction. }
  { destruct H2; subst.
    { specialize (H st1 _ st3 (Stream.forever st1) eq_refl H1).
      specialize (H1 _ (H0 _ (or_introl eq_refl))).
      simpl in H. destruct H.
      auto. }
    { eapply IHvs; eauto.
      clear - H.
      unfold Abstracts in *; intros.
      simpl in H.
      eapply H in H0.
      destruct H0; eassumption.
      auto. } }
Qed.

Lemma unnext_term_eq_next :
  forall st1 st3 t,
    (forall x, In x (get_next_vars_term t) -> st1 x = st3 x) ->
    eval_term t st1 st3 = eval_term (unnext_term t) st1 st3.
Proof.
  induction t; simpl; auto; intros;
  try solve [ symmetry; apply H; auto
            | rewrite IHt; auto
            | rewrite IHt1, IHt2; auto;
              intros; apply H; apply in_app_iff; auto ].
Qed.

Definition lift2 {A B C} (f : A -> B -> C) (a : option A) (b : option B) : option C :=
  match a , b with
  | Some a , Some b => Some (f a b)
  | _ , _ => None
  end.

Fixpoint unnext_o (F : Formula) : option Formula :=
  match F with
  | TRUE | FALSE  => Some F
  | Comp t1 t2 op => Some (Comp (unnext_term t1) (unnext_term t2) op)
  | And f1 f2     => lift2 And (unnext_o f1) (unnext_o f2)
  | Or f1 f2      => lift2 Or (unnext_o f1) (unnext_o f2)
  | Imp f1 f2     => lift2 Imp (unnext_o f1) (unnext_o f2)
  | PropF _       => Some F
  | Enabled _     => Some F
  | _             => None
  end.


Lemma unnext_eq_next :
  forall st1 st3 sts A A',
    unnext_o A = Some A' ->
    (forall x : Var, In x (get_next_vars_formula A) -> st1 x = st3 x) ->
    (eval_formula A' (Stream.Cons st1 (Stream.Cons st3 sts)) <->
     eval_formula A (Stream.Cons st1 (Stream.Cons st3 sts))).
Proof.
  induction A; simpl;
  try solve [ inversion 1; tauto
            | intros
              ; destruct (unnext_o A1); simpl in *; try congruence
              ; destruct (unnext_o A2); simpl in *; try congruence
              ; inversion H
              ; clear H; subst
              ; simpl
              ; setoid_rewrite in_app_iff in H0
              ; rewrite <- IHA1 by (clear - H0; firstorder)
              ; rewrite <- IHA2 by (clear - H0; firstorder)
              ; tauto ].
  { inversion 1; subst; clear H.
    simpl; unfold eval_comp.
    intros.
    setoid_rewrite in_app_iff in H.
    do 2 rewrite <- unnext_term_eq_next by firstorder.
    tauto. }
Qed.

Theorem synth_monitor
  : forall {insc ins1 outs1 ins2 outs2}
           A A' (Pred : Cond insc) (N : Parallel ins1 outs1)
           B (B' : Parallel ins2 outs2)
           (vars : list Var),
    unnext_o A = Some A' ->
    Abstracts_cond A' Pred ->
    get_next_vars_formula A = vars ->
    (forall x, In x vars -> In x outs1) ->
    Abstracts (copy_next vars) N ->
    Abstracts B B' ->
    Abstracts (A \\// B) (Ite Pred N B').
Proof.
  do 12 intro.
  intro Hunnext.
  do 2 intro.
  intro Hsub. intros.
  unfold Abstracts; intros.
  breakAbstraction.
  subst.
  destruct (eval_Cond Pred st1) eqn:?.
  { left.
    red in H. specialize (H st1 (Stream.Cons st3 sts)).
    rewrite Heqb in H. simpl in H.
    destruct H. clear H. specialize (H0 I). rename H0 into H.
    clear - H H4 H1 Hsub Hunnext.
    assert (forall x : Var, In x outs1 -> eval_Parallel N st1 x = st3 x).
    { intros. apply H4. apply in_app_iff. auto. }
    specialize (Abstracts_copy_next_same _ _ _ _ H1 Hsub H0).
    clear - H Hunnext. intros.
    eapply unnext_eq_next with (A' := A'); eauto. }
  { right.
    clear - H2 H4.
    red in H2. eapply H2.
    reflexivity.
    intros. apply H4.
    apply in_app_iff. tauto. }
Qed.

Definition ParVelShim :
  ParResult MyVelShim.Ctrl.
Proof.
  econstructor.
  unfold MyVelShim.Ctrl.
  unfold MyVelShim.SafeAcc.
  unfold MyVelShim.Default.
  eapply synth_monitor; try solve [ reflexivity | Synth_Term ].
  eapply Le_choice; Synth_Term.
  Grab Existential Variables.
  compute. auto.
Defined.