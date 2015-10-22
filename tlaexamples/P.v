Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rtrigo_def.
Require Import Coq.setoid_ring.RealField.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import TLA.ArithFacts.
Require Import ChargeTactics.Lemmas.

Import LibNotations.

Open Scope string_scope.
Open Scope HP_scope.

Theorem Rmult_0_left : forall r, (eq (0 * r) 0)%R.
Proof. solve_linear. Qed.

Theorem Rmult_0_right : forall r, (eq (r * 0) 0)%R.
Proof. solve_linear. Qed.

Lemma R_tricotomy : forall a b : R, (a < b \/ a = b \/ a > b)%R.
Proof. clear. solve_linear. Qed.

(* TODO(gmalecha): This should go into the TLA automation *)
Ltac decompose_hyps :=
  repeat first [ rewrite land_lor_distr_R
               | rewrite land_lor_distr_L
               | apply lorL ].

(* TODO(gmalecha): This should go in some automation about derivatives. *)
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
             erewrite (@H' F G X _ _) ; simpl in H' end; clear H'
         | generalize Ranalysis1.derive_pt_plus;
           unfold Ranalysis1.plus_fct;
           intro H';
           match goal with
           | |- context [ Ranalysis1.derive_pt (fun x : R => @?F x + @?G x)%R ?X _ ] =>
             erewrite (@H' F G X _ _) ; simpl in H' end; clear H'
         | generalize Ranalysis1.derive_pt_minus;
           unfold Ranalysis1.minus_fct;
           intro H';
           match goal with
           | |- context [ Ranalysis1.derive_pt (fun x : R => @?F x - @?G x)%R ?X _ ] =>
             erewrite (@H' F G X _ _) ; simpl in H' end; clear H'
         | generalize Ranalysis1.derive_pt_comp;
           unfold Ranalysis1.comp;
           intro H';
           match goal with
           | |- context [ Ranalysis1.derive_pt (fun x : R => exp (@?F x))%R ?X _ ] =>
             rewrite (H' F exp X _ _); simpl in H' end; clear H'
         | rewrite RIneq.Rminus_0_l
         | rewrite RIneq.Rminus_0_r
         ].


Definition Inductively (P I : Formula) : Formula :=
  (* P //\\ *) [](P //\\ I -->> next P).

(*
Lemma Inductively_And : forall P Q E,
    Inductively P (Q //\\ E) //\\
    Inductively Q (P //\\ E)
    |-- Inductively (P //\\ Q) E.
Proof.
  unfold Inductively.
  intros. charge_split; try charge_tauto.
  intros.
  transitivity
    ([](P //\\ (Q //\\ E) -->> next P) //\\
       [](Q //\\ (P //\\ E) -->> next Q)).
  - charge_tauto.
  - rewrite Always_and.
    tlaRevert. eapply BasicProofRules.always_imp.
    charge_tauto.
Qed.
*)

Lemma prove_always : forall P,
    is_st_formula P ->
    (forall st, eval_formula P (Stream.forever st)) ->
    |-- [] P.
Proof.
  red. red. red. red. simpl. fold eval_formula.
  intros.
  eapply st_formula_hd; [ assumption | eapply H0 | ].
  instantiate (1 := Stream.hd (Stream.nth_suf n tr)).
  reflexivity.
Qed.


(* Stability Definitions *)
(*************************)

(* Absolute value *)
Definition Abs (t : Term) (f : Term -> Formula) : Formula :=
  (t > 0 -->> f t) //\\ (t <= 0 -->> f (--t)).

(* Lyapunov Stability *)
(* forall a, exists b, |x| <= b -> [] |x| <= a *)
Definition Stable (x : Term) : Formula :=
  Forall a : R,
    a > 0 -->>                (* boundary *)
    Exists b : R,
      b > 0 //\\              (* start *)
      ((Abs x (fun t => t < b)) -->> []Abs x (fun t => t < a)).

(* Exponential Stability *)
(* exists a, b, d, x_start :
     x = x0 /\ |x| <= d  -> [] |x| <= a * |x0| * e^(-b * t) *)
Definition ExpStable x : Formula :=
  Exists a : R,    a > 0   //\\ (* a = 2 *)
  Exists b : R,    b > 0   //\\ (* b = 1/(a*x0) *)
  Exists x0: R,    x = x0  //\\
  Exists T : R,    T = "t" //\\
  (* Exists d : R,    d > 0  //\\ (Abs x (fun z => z < d)) //\\ *)
     []Abs x (fun z => z < (a * (Rabs x0) * exp(--b * ("t" - T))))%HP.


(* This is the formalization of a hybrid P-controller
 *)
Section P.
  Variable delta : R.
  Hypothesis delta_gt_0 : (delta > 0)%R.

  Local Coercion RealT : R >-> Term.
  Local Coercion VarNowT : Var >-> Term.

  (* "T" is the clock which carries the maximum amount of time that
   *     can ellapse before the next discrete transition must run.
   * "t" is the global clock which is necessary for stating properties
   *     such as exponential stability that depend on the total
   *     ellapsed time.
   *)
  Let World : Formula :=
    Continuous (["x"' ::= "v", "v"' ::= 0, "t"' ::= 1, "T"' ::= --1]).

  Definition Init : Formula :=
    "v" = --"x" / delta //\\ "t" = 0 //\\ "T" <= delta.

  Definition Ctrl : Formula :=
    (     "v"! = --"x" / delta
     //\\ Unchanged (["x", "t"]))%HP.

  Definition Next : Formula :=
    (World \\// (Ctrl //\\ "T"! <= delta)) //\\ "T" >= 0.

  Definition Spec : Formula :=
    Init //\\ []Next.

  (* Lyapunov Stability of P *)
Section LyapunovStability.
  Definition IndInv : Formula :=
    ("v" < 0 -->> --"v"*"T" <= "x") //\\
    ("v" >= 0 -->> "v"*"T" <= --"x").

  Lemma indinv_direction :
    IndInv //\\ "T" >= 0 |-- "v"*"x" <= 0.
  Proof. solve_nonlinear. Qed.

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
        tlaAssert ("v"*delta = --"x").
        { solve_linear. rewrite H0.
          rewrite Raxioms.Rmult_assoc.
          rewrite <- RIneq.Rinv_l_sym;
            solve_linear. }
        { solve_nonlinear. } }
      { unfold Next. rewrite landC. tlaRevert.
        rewrite BasicProofRules.Always_now.
        2: charge_assumption.
        tlaRevert. apply forget_prem. charge_intros.
        tlaAssert ("v"*delta = --"x").
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
          { clear - H0 delta_gt_0. assert (/ delta > 0)%R.
            { solve_linear. }
            { clear delta_gt_0. solve_nonlinear. } }
          { solve_nonlinear. } }
        { solve_linear. rewrite_next_st.
          repeat rewrite RIneq.Rminus_0_l.
          rewrite Raxioms.Rmult_comm.
          rewrite <- Raxioms.Rmult_assoc. apply Rmult_le_algebra; [ auto | ].
          assert (Stream.hd tr "x" <= 0)%R.
          { clear - H0 delta_gt_0. assert (/ delta > 0)%R.
            { solve_linear. }
            { clear delta_gt_0. solve_nonlinear. } }
          { solve_nonlinear. } }
  Qed.

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
        with (A:=IndInv //\\ Next //\\ BasicProofRules.next IndInv //\\ "T"! >= 0).
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
            rewrite BasicProofRules.always_next with (F := "T" >= 0).
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
End LyapunovStability.

Section ExponentialStability.

  Let b : R := (/ delta)%R.

  Lemma b_gt_0 :
    (b > 0)%R.
  Proof.
    unfold b.
    apply RIneq.Rlt_gt. apply RIneq.Rinv_0_lt_compat.
    solve_linear.
  Qed.

  Section ContinuousTransition.
    (* The alpha parameter of exponential stability *)
    Variable alpha : R.
    Hypothesis alpha_ge_0 : (alpha > 0)%R.
    (* Beginning of time for exponential stability *)
    Variable t0 : R.
    Hypothesis t0_ge_0 : (t0 >= 0)%R.
    (* Value of "t" at the start of this continuous transition *)
    Variable t_start : R.
    Hypothesis t_start_ge_t0 : (t_start >= t0)%R.
    (* Value of "x" at the start of this continuous transition *)
    Variable x_start : R.
    Hypothesis x_start_ge_0 : (x_start >= 0)%R.

    (* This is the exponential function that we must stay under to
     * satisfy exponential stability.
     *)
    Let E (t : Term) : Term :=
      alpha * exp(--b * (t - t0)).

    (* This is the tangent to E @ t_start
     *)
    Let T (t : Term) : Term :=
      --b * alpha * exp(--b * (t_start - t0)) * (t - t_start) + E t_start.

    (* This is the linear function that we will follow along this
     * continuous evolution.
     *)
    Definition L (t : Term) : Term :=
      --b * alpha * exp(--b * (t_start - t0)) * (t - t_start) + x_start.

    Let Init : Formula :=
           "t" = t_start //\\ "x" = x_start //\\ "x" <= E "t"
      //\\ "v" = --b * "x" //\\ "T" <= delta.

    Definition Lin_Safe : Formula :=
      0 <= "x" <= L "t".

    Definition Exp_Safe : Formula :=
      0 <= "x" <= E "t".

    (* (1) This is the proof that the exponential is concave up.
     * - First we prove the tangent is less than the exponential.
     * - Then we prove the line is less than the tangent.
     * - By transitivity we get that the line is less than the exponential.
     *)
    Theorem T_le_E : forall t, |-- T t <= E t.
    Proof.
      simpl. red. simpl. intros. clear H.
      generalize (eval_term t (Stream.hd tr) (Stream.hd (Stream.tl tr))).
      clear - t_start_ge_t0 x_start_ge_0 alpha_ge_0 b delta_gt_0.
      intro t.
      pose (T := (fun t => (0 - b) * alpha * exp ((0 - b) * (t_start - t0)) * (t - t_start) + alpha * exp ((0 - b) * (t_start - t0)))%R).
      pose (E := (fun t => alpha * exp ((0 - b) * (t - t0)))%R).
      change (T t <= E t)%R.
      cut (0 <= (fun t => E t - T t) t)%R.
      { clear. solve_linear. }
      cutrewrite ((eq 0 (E t_start - T t_start))%R).
      { destruct (R_tricotomy t t_start) as [ ? | [ ? | ? ] ].
        { cut (T t - E t <= T t_start - E t_start)%R; [ clear ; solve_linear | ].
          eapply MVT.derive_increasing_interv_var
          with (a:=t) (b:=t_start) (f:=(fun x => T x - E x)%R); try assumption.
          2: solve_linear.
          2: solve_linear.
          intros. unfold T, E.
          simplify_deriv_pt.
          ring_simplify.
          assert (exp (- b * (t_start - t0)) < exp (- b * (t1 - t0)))%R.
          { eapply Rpower.exp_increasing.
            ring_simplify. solve_linear.
            generalize b_gt_0. clearbody b. clear - H2.
            solve_nonlinear. }
          generalize dependent (exp (- b * (t_start - t0))).
          generalize dependent (exp (- b * (t1 - t0))).
          generalize b_gt_0. clearbody b.
          clear - alpha_ge_0.
          solve_nonlinear. }
        { subst. clearbody T; clearbody E. solve_linear. }
        { eapply MVT.derive_increasing_interv_var
          with (a:=t_start) (b:=t) (f:=(fun x => E x - T x)%R); try assumption.
          2: solve_linear.
          2: solve_linear.
          intros; unfold T, E.
          simplify_deriv_pt.
          ring_simplify.
          assert (exp (- b * (t1 - t0)) < exp (- b * (t_start - t0)))%R.
          { eapply Rpower.exp_increasing.
            ring_simplify. solve_linear.
            generalize b_gt_0. clearbody b. clear - H1.
            solve_nonlinear. }
          generalize dependent (exp (- b * (t1 - t0))).
          generalize dependent (exp (- b * (t_start - t0))).
          generalize b_gt_0. clearbody b.
          clear - alpha_ge_0.
          solve_nonlinear. } }
      { unfold T, E. ring_simplify. reflexivity. }
    Qed.

    Lemma L_le_T : forall t, x_start <= E t_start |-- L t <= T t.
    Proof.
      Opaque E.
      unfold L, T.
      clearbody b. clear.
      red. simpl. red. simpl. intros.
      generalize dependent (eval_term t (Stream.hd tr) (Stream.hd (Stream.tl tr))).
      intros. solve_linear.
    Qed.

    Theorem L_le_E : forall t, x_start <= E t_start |-- L t <= E t.
    Proof.
      intros. rewrite L_le_T with (t:=t).
      tlaAssert (T t <= E t).
      { apply forget_prem. apply T_le_E. }
      clearbody b. clearbody E. clearbody T. clear.
      breakAbstraction. intros. solve_linear.
    Qed.

    Theorem World_LinSafe :
      |-- Inductively (     "x" = L "t"
                       //\\ "v" = --b * x_start
                       //\\ t_start <= "t"
                       //\\ "t" <= t_start + delta)%HP
                      (World //\\ "t"! <= t_start + delta).
    Proof.
      unfold Inductively, World, L.
      eapply always_tauto.

      (* this is the differential invariant *)
      charge_intro.
      transitivity (     BasicProofRules.next ("x" = L "t" //\\ "v" = -- (b) * x_start //\\ t_start <= "t")
                    //\\ BasicProofRules.next ("t" <= t_start + delta));
        [ | charge_tauto ].
      charge_split; [ | charge_tauto ].
      eapply diff_ind with (Hyps := "v" = --b * x_start).
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
      { admit. (*

 simpl. breakAbstraction.
        repeat rewrite Rmult_0_left.
        repeat rewrite Rmult_0_right.
        solve_linear. *) }
    Qed.

(*
    (* (2) This is the proof that we are always below
         the tangent drawn at the start of the run. *)
    Theorem Spec_lt_tangent :
      |-- Init //\\ []World -->> []Lin_Safe.
    Proof.
    assert (b > 0)%R.
    { unfold b. solve_nonlinear. }
    (* strengthened temporal invariant for discrete induction *)
    eapply BasicProofRules.imp_trans
      with (F2 := [](     "x" = L "t"
                     //\\ "v" = --b * x_start
                     //\\ t0 <= "T" <= t0 + delta)).
    { charge_intros. eapply BasicProofRules.discr_indX.
      { compute. tauto. }
      { charge_assumption. }
      { apply landL1.
        unfold Init, Lin_Safe.
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
        transitivity (BasicProofRules.next ("x" = L //\\ "v" = -- (b) * x_start //\\ t0 <= "t")
                 //\\ BasicProofRules.next ("t" <= t0 + delta)).
        { charge_split.
          2: charge_assumption.
          eapply diff_ind with (Hyps := "v" = --b*x_start).
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
      clear - x_start_ge_0 delta_gt_0 H5.
      assert (x_start * delta >= x_start * (Stream.hd tr "t" - t0))%R.
      { solve_nonlinear. }
      eapply RIneq.Rmult_le_reg_l with (r:=(delta)%R).
      { solve_nonlinear. }
      rewrite Rmult_0_right.
      rewrite Raxioms.Rmult_comm.
      rewrite RIneq.Rmult_plus_distr_r.
      cutrewrite (eq ((0 - / delta) * x_start * (Stream.hd tr "t" - t0) * delta + x_start * delta)%R
                     ((0 - / delta) * delta * x_start * (Stream.hd tr "t" - t0) + x_start * delta)%R).
      2: solve_linear.
      rewrite Rmult_minus_distr_r.
      rewrite Rmult_0_left.
      rewrite (Raxioms.Rmult_comm (/delta) delta).
      rewrite RIneq.Rinv_r.
      2: solve_linear.
      solve_nonlinear. }
  Qed.

  (* Exponential stability is the composition of (1) and (2) *)
  Theorem Exp_stable_cont :
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
*)

  End ContinuousTransition.

End ExponentialStability.
End P.





(*   Lemma Exists_with_st : forall G P (t : Term), *)
(*       (forall x : R, G |-- t = x -->> P x) -> *)
(*       G |-- Exists x : R, P x. *)
(*   Proof. *)
(*     breakAbstraction. *)
(*     intros. *)
(*     specialize (H _ tr H0 eq_refl). *)
(*     eexists. eauto. *)
(*   Qed. *)

(*   Lemma R_tri : forall v : Term, *)
(*       |-- v < 0 \\// v = 0 \\// v > 0. *)
(*   Proof. solve_linear. Qed. *)

(* (* *)
(*  * Term = state -> R *)
(*  * "x" * 2 : (state -> R) *)
(*  *) *)

(*   Lemma impl_distr : forall F G H, *)
(*       F -->> G -->> H |-- (F -->> G) -->> (F -->> H). *)
(*   Proof. solve_linear. Qed. *)


(* (* *)
(*   Lemma Abs_impl : forall t P Q, *)
(*       Abs t (fun x => P x -->> Q x) -|- Abs t P -->> Abs t Q. *)
(*   Proof. *)
(*     unfold Abs. *)
(*     eexists. *)
(*     solve_linear. *)

(*     admit. *)
(*   Qed. *)
(* *) *)

(*   Lemma spec_exp_stable : *)
(*     |-- Spec -->> ExpStable "x". *)
(*   Proof. *)
    


(* End P. *)

(* Close Scope string_scope. *)
(* Close Scope HP_scope. *)

(*

exp decay function
f = \x -> |x| <= |x0|*a*e^[b*(T-T0)]

Let initial d-t function be y = -x + 1
- if constant interrupts (epsilon ~= 0) , gradient is very similar to original line
- *one* delayed interrupt (epsilon >= 0.5) would force x towards 0, with a long tail.

*)