Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import ChargeTactics.Lemmas.
Require Import Examples.ParLang.
Require Import Examples.FirstDerivShimCtrl.

Open Scope HP_scope.
Open Scope string_scope.

(* TODO:
examples:
 velocity, height shims and stability ctrl. Box?
small examples in TLA
 *)
Goal exists ins outs, exists prog : Parallel ins outs,
      Abstracts ("x"! = 2 //\\ "y"! = 3) prog.
Proof.
  do 3 eexists.
  Synth_Term.
    (* eapply And_synth_Par; apply Next_assign_synth_real. *)
  Grab Existential Variables.
  unfold sets_disjoint. intros. intro. red in H. destruct H.
  Focus 2. assumption.
  destruct H0. congruence.
  assumption.
Qed.

(*
Ltac Synth_Term :=
  repeat first [ eapply And_synth_Par
               | eapply Next_assign_synth
               | eapply Ite_synth
               | eapply Ite_default_synth
               | eapply Var_term_synth
               | eapply Real_term_synth
               | eapply Nat_term_synth
               | eapply Plus_term_synth
               | eapply Sub_term_synth
               | eapply Mult_term_synth
               | eapply Inv_term_synth
               | eapply Sin_term_synth
               | eapply Cos_term_synth
               | eapply Arctan_term_synth
               | eapply Sqrt_term_synth
               | eapply Exp_term_synth
               | eapply Max_term_synth
               ].

Hint Extern 0 (Abstracts_cond _ _) => solve [ apply Formula_to_Cond_sound; reflexivity ] : synth_lemmas.
*)
Goal
  exists ins outs, exists prog : Parallel ins outs,
      (* Abstracts ("x"! = "x" //\\ "x" = 3) prog. *)
      Abstracts (("x"=3 //\\ "x"!="x") \\// ("x"!=7)) prog.
Proof.
  do 3 eexists.
  Synth_Term.
Qed.

(* Velocity Shim *)
Module MyParams <: FirstDerivShimParams.
  Local Open Scope R_scope.
  Definition ub : R := 100.
  Definition d : R := 10.
  Parameter d_gt_0 : (d > 0).
End MyParams.

Module MyVelShim := FirstDerivShim MyParams.

(*

Abstracts (("a") ! * MyParams.d + "v" <= MyParams.ub \\// ("a") ! <= 0) ?271

if ("a") * MyParams.d + "v" <= MyParams.u
then ("a") ! = "a"
else synth ("a") ! <= 0

*)

Definition copy_next (vs : list Var) : Formula :=
  List.fold_left (fun f v => v! = v //\\ f) vs TRUE.
SearchAbout Formula Eq.

Lemma copy_next_concat :
  forall (xs ys : list Var),
  |-- copy_next (xs ++ ys) -->> copy_next ys //\\ copy_next xs.
Proof.
  intros. charge_intros. unfold copy_next.
  rewrite fold_left_app.
  charge_split.
  {



Theorem synth_monitor
: forall {insc ins1 outs1 ins2 outs2}
    A (Pred : Cond insc)
    B (B' : Parallel ins1 outs1)
    (N : Parallel ins2 outs2)
    (vars : list Var),
  Abstracts_cond (unnext A) Pred ->
  get_next_vars_formula A = vars ->
  Abstracts (copy_next (remove_dup vars)) N ->
  Abstracts B B' ->
  Abstracts (A \\// B) (Ite Pred N B').
Proof.
  intros.
  unfold Abstracts; intros.
  breakAbstraction.
  subst.
  destruct (eval_Cond Pred st1) eqn:?.
  { left.
    clear - H Heqb H4 H1.
    red in H. specialize (H st1 (Stream.Cons st3 sts)).
    rewrite Heqb in H. simpl in H.
    destruct H. clear H. specialize (H0 I). rename H0 into H.
    clear - H H4 H1.

    induction A; try solve [ simpl in *; auto ].
    { simpl in *. admit. }
    { simpl in *.
      split.
      { apply IHA1. tauto.
        clear - H1.
        admit.
      }
      admit.
    }
    admit.
    admit.
    admit.
    admit.
  }
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
  eapply synth_monitor; Synth_Term.
  eapply Le_choice; Synth_Term.
  Grab Existential Variables.
  compute. auto.
Defined.
