Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rtrigo_def.
Require Import TLA.TLA.
Import LibNotations.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import ChargeTactics.Lemmas.
Require Import ArithFacts.

Open Scope string_scope.
Open Scope HP_scope.
Section Exp.
(*
  Variables a : R.
  Hypothesis a_gt_0 : (a > 0)%R.
*)
  Variable t0 : R.
  Hypothesis t0_ge_0 : (t0 >= 0)%R.
  Variable x0 : R.
  Hypothesis x0_ge_0 : (x0 >= 0)%R.
  Variable delta : R.
  Hypothesis delta_gt_0 : (delta > 0)%R.
  Let b : R := (/ delta)%R.

  Definition L : Term :=
    --b * x0 * ("t" - t0) + x0.

  Let World : Formula :=
    Continuous (["x"' ::= "v", "v"' ::= 0, "t"' ::= 1]) //\\ "t"! <= t0 + delta.

  Let Init : Formula :=
    "t" = t0 //\\ "v" = --b * "x" //\\ "x" = x0.

  Definition Safe : Formula :=
    0 <= "x" <= L.

  Local Coercion RealT : R >-> Term.

  Theorem Rmult_0_left : forall r, (eq (0 * r) 0)%R.
  Proof. solve_linear. Qed.

  Theorem Rmult_0_right : forall r, (eq (r * 0) 0)%R.
  Proof. solve_linear. Qed.

  Definition E : Term :=
    x0 * exp(--b * ("t" - t0)).

  (* Does not work with 0 <= "x" < E for some reason... *)
  Definition Exp_Safe : Formula :=
    0 <= "x" <= E.

  Lemma b_gt_0 :
    (b > 0)%R.
  Proof.
    unfold b.
    apply RIneq.Rlt_gt. apply RIneq.Rinv_0_lt_compat.
    solve_linear.
  Qed.

  Lemma prove_always : forall P,
      BasicProofRules.is_st_formula P ->
      (forall st, eval_formula P (Stream.forever st)) ->
      |-- [] P.
  Proof.
    red. red. red. red. simpl. fold eval_formula.
    intros.
    eapply st_formula_hd; [ assumption | eapply H0 | ].
    instantiate (1 := Stream.hd (Stream.nth_suf n tr)).
    reflexivity.
  Qed.

  Lemma R_tricotomy : forall a b : R, (a < b \/ a = b \/ a > b)%R.
  Proof. clear. solve_linear. Qed.


  Ltac simplify_deriv_pt :=
    repeat first
           [ rewrite Rmult_0_right
           | rewrite Rmult_0_left
           | rewrite Raxioms.Rplus_0_l
           | rewrite RIneq.Rplus_0_r
           | rewrite RIneq.Rmult_0_r
           | rewrite RIneq.Rmult_0_l
           | rewrite Ranalysis1.derive_pt_id
           | rewrite Ranalysis4.derive_pt_exp
           | generalize Ranalysis1.derive_pt_minus;
             unfold Ranalysis1.minus_fct;
             intro H'; rewrite H'; clear H'
           | generalize Ranalysis1.derive_pt_const;
             unfold Ranalysis1.fct_cte;
             intro H'; rewrite H'; clear H'
           | generalize Ranalysis1.derive_pt_mult;
             unfold Ranalysis1.mult_fct;
             intro H';
             match goal with
             | |- context [ Ranalysis1.derive_pt (fun x : R => @?F x * @?G x)%R ?X _ ] =>
               erewrite (@H' F G X _ _) ; simpl in H'
             end; clear H'
           | generalize Ranalysis1.derive_pt_plus;
             unfold Ranalysis1.plus_fct;
             intro H';
             match goal with
             | |- context [ Ranalysis1.derive_pt (fun x : R => @?F x + @?G x)%R ?X _ ] =>
               erewrite (@H' F G X _ _) ; simpl in H'
             end; clear H'
           | generalize Ranalysis1.derive_pt_minus;
             unfold Ranalysis1.minus_fct;
             intro H';
             match goal with
             | |- context [ Ranalysis1.derive_pt (fun x : R => @?F x - @?G x)%R ?X _ ] =>
               erewrite (@H' F G X _ _) ; simpl in H'
             end; clear H'
           | generalize Ranalysis1.derive_pt_comp;
             unfold Ranalysis1.comp;
             intro H';
             match goal with
             | |- context [ Ranalysis1.derive_pt (fun x : R => exp (@?F x))%R ?X _ ] =>
               rewrite (H' F exp X _ _); simpl in H' end; clear H'
           | rewrite RIneq.Rminus_0_l
           | rewrite RIneq.Rminus_0_r ].

  (* (1) This is the proof that the exponential is concave up. *)
  Theorem Tangent_le_exp :
    |-- [] (L <= E).
  Proof.
    unfold L, E.
    eapply prove_always.
    { compute. tauto. }
    { intros.
      simpl. generalize (st "t"). clear World Init st. intro t.
      pose (L := (fun t => (0 - b) * x0 * (t - t0) + x0)%R).
      pose (E := (fun t => x0 * exp ((0 - b) * (t - t0)))%R).
      change (L t <= E t)%R.
      cut (0 <= (fun t => E t - L t) t)%R.
      { clear. solve_linear. }
      cutrewrite ((eq 0 (E t0 - L t0))%R).
      { destruct (R_tricotomy t t0) as [ ? | [ ? | ? ] ].
        { cut (L t - E t <= L t0 - E t0)%R; [ clear ; solve_linear | ].
          eapply MVT.derive_increasing_interv_var
            with (a:=t) (b:=t0) (f:=(fun x => L x - E x)%R); try assumption.
          2: solve_linear.
          2: solve_linear.
          intros. unfold L, E.
          Require Import Reals.
          simplify_deriv_pt.
          (* Provable! **)
          assert (exp (- b * (t1 - t0)) > 1)%R.
          { rewrite <- exp_0.
            eapply RIneq.Rlt_gt.
            eapply Rpower.exp_increasing.
            generalize b_gt_0. solve_nonlinear. }
          generalize dependent (exp (- b * (t1 - t0)))%R.
          intros.
          ring_simplify.
          generalize b_gt_0. intro.
          assert (b * x0 >= 0)%R.
          { solve_nonlinear. }
          { generalize dependent (b * x0)%R. solve_nonlinear. } }
        { subst. clearbody L; clearbody E. solve_linear. }
        { eapply MVT.derive_increasing_interv_var
            with (a:=t0) (b:=t) (f:=(fun x => E x - L x)%R); try assumption.
          2: solve_linear.
          2: solve_linear.
          intros; unfold L, E.
          simplify_deriv_pt.
          (* Provable! **)
          assert (exp (- b * (t1 - t0)) < 1)%R.
          { rewrite <- exp_0.
            eapply Rpower.exp_increasing.
            generalize b_gt_0. solve_nonlinear. }
          generalize dependent (exp (- b * (t1 - t0)))%R.
          intros.
          ring_simplify.
          generalize b_gt_0. intro.
          assert (x0 * b >= 0)%R.
          { solve_nonlinear. }
          { cutrewrite (eq (-x0 * r * b) (-r * (x0 * b)))%R.
            generalize dependent (x0 * b) %R.
            solve_nonlinear.
            ring. } } }
      { unfold L, E.
        cutrewrite (eq ((0 - b) * (t0 - t0)) 0)%R.
        rewrite exp_0. solve_linear.
        solve_linear. } }
  Qed.

  (* (2) This is the proof that we are always below
         the tangent drawn at the start of the run. *)
  Theorem Spec_lt_tangent :
    |-- Init //\\ []World -->> []Safe.
  Proof.
    assert (b > 0)%R.
    { unfold b. solve_nonlinear. }
    (* strengthened temporal invariant for discrete induction *)
    eapply BasicProofRules.imp_trans
    with (F2 := [](     "x" = L
                   //\\ "v" = --b * x0
                   //\\ t0 <= "t" <= t0 + delta)).
    { charge_intros. eapply BasicProofRules.discr_indX.
      { compute. tauto. }
      { charge_assumption. }
      { apply landL1.
        unfold Init, Safe.
        charge_split.
        { unfold L.
          eapply lcut with (R := "t" - t0 = 0); [ solve_linear | ].
          charge_intros. solve_linear.
          rewrite H2. solve_linear. }
        charge_split.
        { breakAbstraction. unfold b.
          intuition. subst. rewrite H0.
          reflexivity. }
        { solve_linear. } }
      { unfold Safe, World, L.
        (* this is the differential invariant *)
        transitivity (BasicProofRules.next ("x" = L //\\ "v" = -- (b) * x0 //\\ t0 <= "t")
                 //\\ BasicProofRules.next ("t" <= t0 + delta)).
        { charge_split.
          2: charge_assumption.
          eapply diff_ind with (Hyps := "v" = --b*x0).
          { compute ; tauto. }
          { compute ; tauto. }
          { charge_assumption. }
          { eapply diff_ind with (Hyps := ltrue).
            { compute ; tauto. }
            { compute ; tauto. }
            { charge_assumption. }
            { charge_tauto. }
            { charge_tauto. }
            { charge_tauto. }
            { simpl. solve_linear. } }
          { unfold L.
            charge_split. charge_assumption.
            charge_split. charge_assumption.
            solve_linear. }
          { charge_tauto. }
          { simpl. breakAbstraction.
            repeat rewrite Rmult_0_left.
            repeat rewrite Rmult_0_right.
            solve_linear. } }
        { charge_tauto. } } }
    { unfold Safe.
      eapply BasicProofRules.always_imp.
      unfold L.
      breakAbstraction. split.
      2: solve_linear.
      intuition.
      rewrite H2.
      assert ((Stream.hd tr "t") >= t0)%R.
      solve_nonlinear.
      unfold b.
      clear - x0_ge_0 delta_gt_0 H5.
      assert (x0 * delta >= x0 * (Stream.hd tr "t" - t0))%R.
      { solve_nonlinear. }
      eapply RIneq.Rmult_le_reg_l with (r:=(delta)%R).
      { solve_nonlinear. }
      rewrite Rmult_0_right.
      rewrite Raxioms.Rmult_comm.
      rewrite RIneq.Rmult_plus_distr_r.
      cutrewrite (eq ((0 - / delta) * x0 * (Stream.hd tr "t" - t0) * delta + x0 * delta)%R
                     ((0 - / delta) * delta * x0 * (Stream.hd tr "t" - t0) + x0 * delta)%R).
      2: solve_linear.
      rewrite Rmult_minus_distr_r.
      rewrite Rmult_0_left.
      rewrite (Raxioms.Rmult_comm (/delta) delta).
      rewrite RIneq.Rinv_r.
      2: solve_linear.
      solve_nonlinear. }
  Qed.

  (* Exponential stability is the composition of (1) and (2) *)
  Theorem Exp_stable :
    |-- Init //\\ []World -->> []Exp_Safe.
  Proof.
    charge_intros. tlaAssert ([]Safe).
    { apply lrevert. apply Spec_lt_tangent. }
    apply forget_prem.
    rewrite Tangent_le_exp.
    tlaRevert.
    rewrite <- curry.
    rewrite BasicProofRules.Always_and.
    apply BasicProofRules.always_imp.
    unfold Safe, Exp_Safe.
    solve_linear.
  Qed.

End Exp.

Section P.

  Variable d : R.
  Hypothesis d_gt_0 : (d > 0)%R.

  Let World : Formula :=
    Continuous (["x"' ::= "v", "v"' ::= 0, "t"' ::= --1]).

  Definition Ctrl : Formula :=
    "v"! = --"x"/d //\\ Unchanged (["x", "t"]).

  Let Init : Formula :=
    "v" = --"x"/d //\\ "t" <= d.

  Definition Next : Formula :=
    (World \\// (Ctrl //\\ "t"! <= d)) //\\
    "t" >= 0.

  Definition Spec : Formula :=
    Init //\\ []Next.

  Definition Abs (t : Term) (f : Term -> Formula) : Formula :=
    (t > 0 -->> f t) //\\ (t <= 0 -->> f (--t)).

  (* forall a, exists b, |x| <= b -> [] |x| <= a *)
  Definition Stable (x : Term) : Formula :=
    Forall a : R,
      a > 0 -->>                (* boundary *)
      Exists b : R,
        b > 0 //\\              (* start *)
        ((Abs x (fun t => t < b)) -->> []Abs x (fun t => t < a)).

  (* exists a, b, d, x0 :
       x = x0 /\ |x| <= d  -> [] |x| <= a * |x0| * e^(-b * t) *)
  Definition ExpStable x : Formula :=
    Exists a : R,    a > 0   //\\ (* a = 2 *)
    Exists b : R,    b > 0   //\\ (* b = 1/(a*x0) *)
    Exists x0: R,    x = x0  //\\
    Exists T : R,    T = "t" //\\
    (* Exists d : R,    d > 0  //\\ (Abs x (fun z => z < d)) //\\ *)
       []Abs x (fun z => z < (a * (Rabs x0) * exp(--b * ("t" - T))))%HP.


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


  (* Lemma spec_expstable :
   *   |-- Spec -->> ExpStable "x".
   * Proof.
   *   charge_intros.
   * Qed. *)


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
          * rewrite BasicProofRules.always_next with (F := IndInv).
            charge_assumption.
            tlaIntuition.
          * unfold Next.
            rewrite <- BasicProofRules.Always_and.
            rewrite BasicProofRules.always_next with (F := "t" >= 0).
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

  Lemma Exists_with_st : forall G P (t : Term),
      (forall x : R, G |-- t = x -->> P x) ->
      G |-- Exists x : R, P x.
  Proof.
    breakAbstraction.
    intros.
    specialize (H _ tr H0 eq_refl).
    eexists. eauto.
  Qed.

  Lemma R_tri : forall v : Term,
      |-- v < 0 \\// v = 0 \\// v > 0.
  Proof. solve_linear. Qed.

(*
  Term = state -> R
  "x" * 2 : (state -> R)
*)

  Lemma impl_distr : forall F G H,
      F -->> G -->> H |-- (F -->> G) -->> (F -->> H).
  Proof. solve_linear. Qed.


  Lemma Abs_impl : forall t P Q,
      Abs t (fun x => P x -->> Q x) -|- Abs t P -->> Abs t Q.
  Proof.
    unfold Abs.
    eexists.
    solve_linear.

    admit.
  Qed.

  Lemma spec_exp_stable :
    |-- Spec -->> ExpStable "x".
  Proof.
    unfold ExpStable.
    charge_intro.
    tlaAssert ("x" < 0 \\// "x" = 0 \\// "x" > 0).
    { apply forget_prem. solve_linear. }
    charge_intro.
    decompose_hyps.
    (* x < 0 *)
    { eapply Exists_with_st with (t := --"x"); intro.
      (* charge_intros.
       * charge_split.
       * { solve_linear. }
       * apply @lexistsR with (x:=(2 * d)%R); eauto with typeclass_instances.
       * charge_intros.
       * charge_split. *)
      admit. }

    (*   (* x = 0 *)
     * { eapply Exists_with_st with (t := 0); intro.
     *   admit. } *)
    { admit. }
    { (* pick a *)
      eapply Exists_with_st with (t := 2 * "x"); intro.
      rename x into a.
      charge_intro.
      charge_split.
      { solve_linear. }
      (* pick b
            (x:=(-2 * d)%R)
       *)
      apply @lexistsR with (x:=(d)%R); eauto with typeclass_instances.
      (*      apply Exists_with_st with (t := --2 * d); intro. *)
      charge_intros.
      charge_split.
      { solve_linear. }
      apply Exists_with_st with (t := "x"); intro.
      rename x into x0.
      charge_intro.
      charge_split.
      { charge_tauto. }
      apply Exists_with_st with (t := "t"); intro.
      rename x into T.
      charge_intro.
      charge_split.
      { solve_linear. }
      tlaAssert ([] IndInv). (* inductive invariant *)
      { tlaAssert Spec.
        - charge_tauto.
        - apply forget_prem. eapply spec_indinv. }
      { (* apply forget_prem. *)
        eapply BasicProofRules.always_imp.
        unfold Abs.
        charge_intros.
        charge_split.
        { charge_intros.
          (*    ((Spec //\\ []IndInv) //\\ b > 0) //\\ Abs "x" (fun t : Term => t < b)
   |-- []Abs "x" (fun t : Term => t < b)
           *)
          unfold IndInv.
          tlaAssert ("t" > 0).
          { admit. }
          tlaAssert ("v" < 0 \\// "v" >= 0).
          { solve_linear. }
          charge_intros.
          decompose_hyps.
          { "t" > T /\ "t" > 0 /\ a > 0 /\

}
          { etransitivity. 2: eapply ILogic.lfalseL.
            solve_nonlinear. } }
        {
          SearchAbout R.
          destruct (
          eapply BasicProofRules.discr_indX
          with (A:=IndInv //\\ Next //\\ BasicProofRules.next IndInv //\\ "t"! >= 0).


          admit. }
        { charge_intros. admit.}

        (* |v| * t <= |x| < x * Rabs x0 * exp((-2 * d)%R * ("T" - x1))  *)

        (* rewrite <- Abs_impl. *)

        { admit. }
        { admit. } } }
  Qed.

End P.

Close Scope string_scope.
Close Scope HP_scope.

(*

exp decay function
f = \x -> |x| <= |x0|*a*e^[b*(T-T0)]

Let initial d-t function be y = -x + 1
- if constant interrupts (epsilon ~= 0) , gradient is very similar to original line
- *one* delayed interrupt (epsilon >= 0.5) would force x towards 0, with a long tail.

*)