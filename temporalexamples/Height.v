Require Import TempLang.Syntax.
Require Import TempLang.Semantics.
Require Import TempLang.ProofRules.
Require Import Rbase.
Require Import Equality.

Open Scope HP_scope.
Open Scope string_scope.

Section HeightCtrl.

  (* The delays for evaluating the condition,
     running the first assignment, and
     running the second assignment. *)
  Variable d1 : ptime.
  Variable d2 : ptime.
  Variable d3 : ptime.

  (* The setpoint of the controller. *)
  Variable c : R.

  (* The controller. *)
  Definition ctrl :=
    IFF `"h" < #c @ d1
    THEN ["v" ::= #1] @ d2
    ELSE ["v" ::= --#1] @ d2.

  (* The continuous dynamics. *)
  Definition world :=
    ["h"' ::= `"v", "t"' ::= #1].

  (* The entire system. The controller runs in
     parallel with the continuous dynamics.
     This just repeats some number of times. *)
  Definition sys :=
    ([[world & T]] || ctrl)**.

  Lemma add_nnreal_0_r : forall r,
    add_nonnegreal T0 r = r.
  Admitted.
(*
  Definition ind_inv : Formula :=
    (`"h"-#c)^^2 <= (#d1+#d2)^^2.

  (* The safety property. Any behavior produced by
     the system has the invariant h > 0. *)
  (* We'll need to add some initial conditions here.
     It remains to be seen what those are. *)
  Lemma safety :
    |- (ind_inv /\ |sys|)
         --> []ind_inv.
    Proof.
    apply rep_rule.
    - reflexivity.
    - simpl. intros.
      destruct H as [Hinit [b [Hbeh Hrest] ] ].
      inversion_clear Hbeh.
      rewrite add_nnreal_0_r.
      destruct (Rlt_dec t b).
      + rewrite H2; auto.
        unfold is_solution in *.
        destruct H0 as [is_derivable [Hsol Hunch] ].
        eapply eval_comp_ind; eauto.
        * destruct b; auto.
        * rewrite <- H2; auto.
          apply (Rle_lt_trans T0 t b); auto.
          destruct t; auto.
        * simpl. unfold eval_comp. simpl. intros.
          match goal with
            |- context [Rle_dec ?e1 ?e2] =>
               remember e1; remember e2
          end.
          field_simplify in Heqr0.
          field_simplify in Heqr1.

*)
  Definition ind_inv : Formula :=
    `"h" >= --`"v"*(#d1+#d2-`"t").

  (* The safety property. Any behavior produced by
     the system has the invariant h > 0. *)
  (* We'll need to add some initial conditions here.
     It remains to be seen what those are. *)
  Lemma safety :
    |- (ind_inv /\ |sys|)
         --> []ind_inv.
  Proof.
    apply rep_rule.
    - reflexivity.
    - simpl. intros.
      destruct H as [Hinit [b [Hbeh Hrest] ] ].
      inversion_clear Hbeh.
      rewrite add_nnreal_0_r.
      destruct (Rlt_dec t b).
      + rewrite H2; auto.
        unfold is_solution in *.
        destruct H0 as [is_derivable [Hsol Hunch] ].
        eapply eval_comp_ind; eauto.
        * destruct b; auto.
        * rewrite <- H2; auto.
          apply (Rle_lt_trans T0 t b); auto.
          destruct t; auto.
        * simpl. unfold eval_comp.
          simpl. intros.
          Close Scope HP_scope.
          assert (((0 - 0) * (d1 + d2 - st "t") +
                  (0 - st "v") * (0 + 0 - 1) =
                  st "v"))%R.
          { field_simplify. admit. }
          rewrite H0. admit.
        * split.
          { destruct t; auto. }
          { apply Rlt_le; auto. }
      + unfold DiscreteJump in *. simpl in H.
        rewrite <- Hrest.
        match goal with
          | [ _ : context [if ?e then _ else _]
              |- _ ] => destruct e eqn:Heq
        end.
        * inversion H.
          Arguments String.string_dec !s1 !s2.
          unfold eval_comp, update_st. simpl.
        
        
    simpl. intros.
    destruct H as [Hinit [b [Hbeh1 Hbeh2] ] ].
    apply 

    dependent induction Hbeh1;
      unfold eval_comp in *; simpl in *.
    - rewrite add_nnreal_0_r. rewrite <- Hbeh2.
      unfold T0 in *; auto. destruct t.
      auto.
    - destruct (Rle_dec t b1).
      unfold merge_fun in H1.
      destruct H1. rewrite H1.
      apply IHHbeh1_1; auto.
      rewrite <- H1. auto.
      split; auto. exact (Rle_refl _).


  (* The liveness property. Any behavior produced by
     the system has some point in time in which h = c. *)
  Lemma liveness :
    |- |sys| --> <>`"h" = #c.
  Admitted.

End HeightCtrl.