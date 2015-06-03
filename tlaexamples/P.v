Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Import LibNotations.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import ChargeTactics.Lemmas.
Require Import ArithFacts.

Open Scope string_scope.
Open Scope HP_scope.

Section P.

  Variable d : R.
  Hypothesis d_gt_0 : (d > 0)%R.

  Definition World : Formula :=
    Continuous (["x"' ::= "v", "v"' ::= 0, "t"' ::= --1]).

  Definition Ctrl : Formula :=
    "v"! = --"x"/d //\\ Unchanged (["x", "t"]).

  Definition Init : Formula :=
    "v" = --"x"/d //\\ "t" <= d.

  Definition Next : Formula :=
    (World \\// (Ctrl //\\ "t"! <= d)) //\\
    "t" >= 0.

  Definition Spec : Formula :=
    Init //\\ []Next.

  Definition Abs (t : Term) (f : Term -> Formula) : Formula :=
    (t > 0 -->> f t) //\\ (t <= 0 -->> f (--t)).

  (* forall e, exists d, |x| <= d -> [] |x| <= e *)
  Definition Stable x : Formula :=
    Forall a : R,
      a > 0 -->>                (* boundary *)
      Exists b : R,
        b > 0 //\\              (* start *)
        ((Abs x (fun t => t < b)) -->> []Abs x (fun t => t < a)).

  (* exists \alpha \beta \delta, exists x_0,
       x = x_0 /\ |x| <= \delta  -> [] |x| <= \alpha * |x_0| * e^(-\beta * t) *)
  (*Definition ExpStable x : Formula :=
    Exists a, b, d, x0 : R,
      ((x = x0) //\\ (Abs x (fun t => t < d))) -->>
         []Abs x (fun z => a * ... * exp_in ...)*)

  Ltac decompose_hyps :=
    repeat first [rewrite land_lor_distr_R |
                  rewrite land_lor_distr_L |
                  apply lorL ].

  Definition IndInv : Formula :=
    ("v" < 0 -->> --"v"*"t" <= "x") //\\
    ("v" >= 0 -->> "v"*"t" <= --"x").

  Lemma indinv_direction :
    IndInv //\\ "t" >= 0 |-- "v"*"x" <= 0.
  Proof.
    solve_nonlinear.
  Qed.

  Lemma spec_indinv :
    |-- Spec -->> []IndInv.
  Proof.
    charge_intros.
    eapply BasicProofRules.discr_indX.
    + tlaIntuition.
    + unfold Spec. charge_tauto.
    + unfold Spec, IndInv, Init.
      charge_split.
      { unfold Next. rewrite landC. tlaRevert.
        rewrite BasicProofRules.Always_now.
        2: charge_assumption.
        tlaRevert. apply forget_prem. charge_intros.
        tlaAssert ("v"*d = --"x").
        { solve_linear. rewrite H0.
          rewrite Raxioms.Rmult_assoc.
          rewrite <- RIneq.Rinv_l_sym;
            solve_linear. }
        { solve_nonlinear. } }
      { unfold Next. rewrite landC. tlaRevert.
        rewrite BasicProofRules.Always_now.
        2: charge_assumption.
        tlaRevert. apply forget_prem. charge_intros.
        tlaAssert ("v"*d = --"x").
        { solve_linear. rewrite H0.
          rewrite Raxioms.Rmult_assoc.
          rewrite <- RIneq.Rinv_l_sym;
            solve_linear. }
        { solve_nonlinear. } }
    + unfold Next.
      decompose_hyps.
      * unfold World.
        eapply diff_ind with (Hyps:=ltrue).
        { tlaIntuition. }
        { tlaIntuition. }
        { charge_tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { repeat tlaSplit;
          try solve [solve_linear |
                     tlaIntro; eapply unchanged_continuous;
                     [ tlaAssume | solve_linear ] ]. }
      * simpl. restoreAbstraction. charge_split.
        { solve_linear. rewrite_next_st.
          repeat rewrite RIneq.Rminus_0_l.
          rewrite <- RIneq.Ropp_mult_distr_l_reverse.
          rewrite RIneq.Ropp_involutive. rewrite Raxioms.Rmult_comm.
          rewrite <- Raxioms.Rmult_assoc. apply Rmult_le_algebra; [ auto | ].
          assert (Stream.hd tr "x" > 0)%R.
          { clear - H0 d_gt_0. assert (/ d > 0)%R.
            { solve_linear. }
            { clear d_gt_0. solve_nonlinear. } }
          { solve_nonlinear. } }
        { solve_linear. rewrite_next_st.
          repeat rewrite RIneq.Rminus_0_l.
          rewrite Raxioms.Rmult_comm.
          rewrite <- Raxioms.Rmult_assoc. apply Rmult_le_algebra; [ auto | ].
          assert (Stream.hd tr "x" <= 0)%R.
          { clear - H0 d_gt_0. assert (/ d > 0)%R.
            { solve_linear. }
            { clear d_gt_0. solve_nonlinear. } }
          { solve_nonlinear. } }
  Qed.

(*
  Lemma indinv_stable :
    |-- []IndInv -->> Stable "x".
  Proof.
    unfold Stable. charge_intros.
    eapply lexistsR. instantiate (1:=x).
    charge_split.
    + charge_tauto.
    + charge_intros.
      tlaAssert ([]IndInv).
      * charge_tauto.
      * apply forget_prem. apply BasicProofRules.always_imp.
        unfold IndInv, Abs. charge_intros. charge_split; charge_intros.
        - tlaAssert ("v" < 0 \\// "v" >= 0);
          [ solve_linear | charge_intros ].
          decompose_hyps.
          { solve_linear. clear H3. z3 solve_dbg.
     *)


  Lemma always_next :
    forall F,
      BasicProofRules.is_st_formula F ->
      []F |-- []BasicProofRules.next F.
  (* is_st_formula : Formula -> Prop (basicproofrules) *)
  Proof.
    intros.
   apply lrevert.
   rewrite BasicProofRules.always_st.
   rewrite <- BasicProofRules.Always_and.
   charge_intros.
   charge_tauto.
   tlaIntuition.
 Qed.

   (* apply lrevert.
    * apply BasicProofRules.next_inv with (N:=true)(I:=IndInv). *)


 Lemma spec_stable :
    |-- Spec -->> Stable "x".
  Proof.
    charge_intros. tlaAssert ([]IndInv).
    { apply lrevert. apply spec_indinv. }
    { unfold Stable. charge_intros.
      rename x into b.
      eapply lexistsR. instantiate (1:=b).
      charge_split.
      - charge_tauto.
      - charge_intros.
        eapply BasicProofRules.discr_indX
        with (A:=IndInv //\\ Next //\\ BasicProofRules.next IndInv //\\ "t"! >= 0).
        + tlaIntuition.
        + unfold Spec. repeat rewrite <- BasicProofRules.Always_and.
          repeat charge_split.
          * charge_tauto.
          * charge_tauto.
          * rewrite always_next with (F := IndInv).
            charge_assumption.
            tlaIntuition.
          * unfold Next.
            rewrite <- BasicProofRules.Always_and.
            rewrite always_next with (F := "t" >= 0).
            charge_tauto.
            tlaIntuition.
        + charge_tauto.
        + unfold Next. simpl BasicProofRules.next.
          restoreAbstraction. decompose_hyps.
          * unfold World.
            tlaAssert ("v"! < 0 \\// "v"! >= 0);
              [ solve_linear | ].
            charge_intros. decompose_hyps.
            { charge_split; charge_intros.
              + unfold IndInv. eapply diff_ind with (Hyps:="v" < 0) (G:="x" < b).
                - tlaIntuition.
                - tlaIntuition.
                - charge_tauto.
                - eapply unchanged_continuous.
                  * charge_tauto.
                  * simpl Unchanged. restoreAbstraction. solve_linear.
                - eapply unchanged_continuous.
                  * charge_tauto.
                  * solve_linear.
                - eapply unchanged_continuous.
                  * charge_tauto.
                  * solve_linear.
                - simpl deriv_formula. solve_linear.
              + unfold IndInv.
                solve_nonlinear. }
            { charge_split; charge_intros.
              + solve_nonlinear.
              + eapply diff_ind with (Hyps:="v" >= 0) (G:=--"x" < b).
                - tlaIntuition.
                - tlaIntuition.
                - charge_tauto.
                - eapply unchanged_continuous.
                  * charge_tauto.
                  * solve_linear.
                - eapply unchanged_continuous.
                  * charge_tauto.
                  * solve_linear.
                - eapply unchanged_continuous.
                  * charge_tauto.
                  * solve_linear.
                - solve_linear. }
          * solve_linear. }
Qed.

End P.

Close Scope string_scope.
Close Scope HP_scope.