Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rtrigo_def.
Require Import Coq.Reals.Rpower.
Require Import Coq.Reals.RIneq.
Require Import Coq.setoid_ring.RealField.
Require Import ExtLib.Tactics.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import TLA.ArithFacts.
Require Import ChargeTactics.Lemmas.

Import ListNotations.

Local Open Scope R_scope.

Theorem Rmult_0_left : forall r, (eq (0 * r) 0)%R.
Proof. solve_linear. Qed.

Theorem Rmult_0_right : forall r, (eq (r * 0) 0)%R.
Proof. solve_linear. Qed.

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

Lemma exp_le : forall a b, (exp a <= exp b)%R <-> (a <= b)%R.
Proof.
  clear. split.
  { destruct 1.
    - left. eapply exp_lt_inv. auto.
    - apply exp_inv in H. subst. reflexivity. }
  { destruct 1.
    - left. eapply exp_increasing. auto.
    - subst. reflexivity. }
Qed.

Lemma R_tricotomy : forall a b : R, (a < b \/ a = b \/ a > b)%R.
Proof. clear. solve_linear. Qed.

Lemma concavity
  : forall (f : R -> R) (x : R) pf_f pf_f',
    (forall z, Ranalysis1.derive (Ranalysis1.derive f pf_f) pf_f' z >= 0)%R ->
    let t z := (Ranalysis1.derive f pf_f x * (z - x) + f x)%R in
    (forall y, t y <= f y)%R.
Proof.
  intros.
  cut (0 <= (fun x => f x - t x) y)%R.
  { clear. solve_linear. }
  cutrewrite ((eq 0 (f x - t x))%R).
  { destruct (R_tricotomy y x) as [ ? | [ ? | ? ] ].
    { cut (t y - f y <= t x - f x)%R; [ clear ; solve_linear | ].
      eapply MVT.derive_increasing_interv_var
      with (a:=y) (b:=x) (f:=(fun x => t x - f x)%R); try assumption.
      2: solve_linear.
      2: solve_linear.
      intros. unfold t.
      simplify_deriv_pt.
      instantiate (1 := pf_f _).
      ring_simplify.
      cut (Ranalysis1.derive_pt f t0 (pf_f t0) <= Ranalysis1.derive f pf_f x)%R;
        [ solve_linear | ].
      unfold Ranalysis1.derive.
      eapply MVT.derive_increasing_interv_var
      with (a:=y) (b:=x) (f:=(fun x => Ranalysis1.derive_pt f x (pf_f x))%R); try assumption.
      2: solve_linear.
      2: solve_linear.
      2: solve_linear.
      instantiate (1 := pf_f').
      intros.
      specialize (H t1).
      solve_linear. }
    { subst. reflexivity. }
    { eapply MVT.derive_increasing_interv_var
      with (a:=x) (b:=y) (f:=(fun x => f x - t x)%R); try assumption.
      2: solve_linear.
      2: solve_linear.
      intros. unfold t.
      simplify_deriv_pt.
      instantiate (1 := pf_f _).
      ring_simplify.
      cut (Ranalysis1.derive f pf_f x <= Ranalysis1.derive_pt f t0 (pf_f t0))%R;
        [ solve_linear | ].
      unfold Ranalysis1.derive.
      eapply MVT.derive_increasing_interv_var
      with (a:=x) (b:=y) (f:=(fun x => Ranalysis1.derive_pt f x (pf_f x))%R); try assumption.
      2: solve_linear.
      2: solve_linear.
      2: solve_linear.
      instantiate (1 := pf_f').
      intros.
      specialize (H t1).
      solve_linear. } }
  { unfold t.
    ring_simplify. reflexivity. }
Qed.

Lemma concavity_eq
  : forall (f f' f'' : R -> R) (x : R) pf_f pf_f',
    (forall x, f' x = Ranalysis1.derive_pt f x (pf_f x)) ->
    (forall x, f'' x = Ranalysis1.derive_pt f' x (pf_f' x)) ->
    (forall z, f'' z >= 0)%R ->
    let t z := f' x * (z - x) + f x%R in
    (forall y, t y <= f y)%R.
Proof.
  intros.
  generalize (concavity f x pf_f). simpl.
  unfold Ranalysis1.derive, Ranalysis1.derivable.
  rewrite <- H.
  assert (forall x0 : R,
               Ranalysis1.derivable_pt
                 (fun x1 : R => Ranalysis1.derive_pt f x1 (pf_f x1)) x0).
  { intros.
    cutrewrite ((fun x1 : R => Ranalysis1.derive_pt f x1 (pf_f x1)) = f').
    eauto.
    eapply FunctionalExtensionality.functional_extensionality. eauto. }
  intros. specialize (@H3 H2).
  rewrite <- H3.
  { unfold t. rewrite H. reflexivity. }
  { intros. clear H3. revert H2.
    cutrewrite ((fun x1 : R => Ranalysis1.derive_pt f x1 (pf_f x1)) = f').
    { intros.
      cutrewrite (Ranalysis1.derive_pt f' z (H2 z) = f'' z); auto.
      rewrite H0.
      eapply Ranalysis1.pr_nu. }
    { eapply FunctionalExtensionality.functional_extensionality. eauto. } }
Qed.

Open Scope string_scope.
Open Scope HP_scope.

(* TODO(gmalecha): This should go into the TLA automation *)
Ltac decompose_hyps :=
  repeat first [ rewrite land_lor_distr_R
               | rewrite land_lor_distr_L
               | apply lorL ].


Definition Inductively (P I : Formula) : Formula :=
  (* P //\\ *) [](P //\\ I -->> next P).

Require Import Coq.Classes.Morphisms.

(** TODO: Using [eq] here is a hack that we should fix! **)
Lemma Proper_Inductively
: Proper (eq ==> lequiv ==> lequiv)%signature Inductively.
Proof.
  red. do 2 red. unfold Inductively. intros.
  apply Proper_Always.
  eapply limpl_lequiv_m.
  { rewrite H. rewrite H0. reflexivity. }
  { subst. reflexivity. }
Qed.

Instance Proper_Always_entails : Proper (lentails ==> lentails) Always.
Proof.
  red. red. intros.
  tlaRevert.
  eapply always_imp. charge_tauto.
Qed.

Lemma Proper_Inductively_entails
: Proper (eq ==> lentails --> lentails)%signature Inductively.
Proof.
  red. do 2 red. unfold Inductively. intros.
  eapply Proper_Always_entails. subst.
  red in H0. rewrite H0. reflexivity.
Qed.

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

Lemma Inductively_equiv
  : forall a b : Formula,
    is_st_formula a -> is_st_formula b ->
    a -|- b ->
    forall c d : Formula,
      c -|- d ->
      Inductively a c -|- Inductively b d.
Proof.
  unfold Inductively. intros.
  apply Proper_Always.
  rewrite H2; clear H2.
  eapply limpl_lequiv_m.
  { rewrite H1. reflexivity. }
  { split; eapply next_st_formula_entails; eauto; eapply H1. }
Qed.

Lemma Inductively_entails
  : forall a b : Formula,
    is_st_formula a -> is_st_formula b ->
    b -|- a ->
    forall c d : Formula,
      d |-- c ->
      Inductively a c |-- Inductively b d.
Proof.
  unfold Inductively. intros.
  eapply Proper_Always_entails.
  rewrite H2; clear H2.
  eapply limpl_lentails_m.
  { red. rewrite H1. reflexivity. }
  { eapply next_st_formula_entails; eauto; eapply H1. }
Qed.

Lemma Inductively_Or : forall P Q S1 S2,
    Inductively P S1 //\\
    Inductively Q S2
    |-- Inductively (P \\// Q) ((P //\\ S1) \\// (Q //\\ S2)).
Proof.
  unfold Inductively.
  intros.
  tlaRevert. tlaRevert.
  rewrite <- curry. rewrite Always_and.
  apply always_imp. simpl. restoreAbstraction.
  charge_intro. charge_intro.
  rewrite <- landA.
  tlaRevert. apply landL1.
  charge_intros. decompose_hyps; charge_tauto.
Qed.

Lemma Inductively_Or' : forall G P Q S1 S2,
    G |-- Inductively P S1 ->
    G |-- Inductively Q S2 ->
    G |-- Inductively (P \\// Q) ((P //\\ S1) \\// (Q //\\ S2)).
Proof.
  intros. charge_apply (Inductively_Or P Q S1 S2).
  charge_tauto.
Qed.


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
Definition LyapunovStable (x : Term) : Formula :=
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
     []Abs x (fun z => z <= (a * (Rabs x0) * exp(--b * ("t" - T))))%HP.


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
    Continuous (fun st' => st' "x" = "v" //\\ st' "v" = 0 //\\ st' "t" = 1 //\\ st' "T" = --1).
(*               ["x"' ::= "v", "v"' ::= 0, "t"' ::= 1, "T"' ::= --1]). *)

  Definition Init : Formula :=
    "v" = --"x" / delta //\\ "t" = 0 //\\ "T" <= delta.

  Definition Ctrl : Formula :=
    (     "v"! = --"x" / delta
     //\\ Unchanged ["x" ; "t"])%HP.

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
        { compute; tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { charge_intro.
          simpl. restoreAbstraction. unfold lift2.
          charge_intros. repeat charge_split.
          { charge_intros.
            eapply zero_deriv with (x:="v").
            { charge_assumption. }
            { charge_intros. compute. tauto. }
            { solve_linear. } }
          { solve_linear. rewrite H; clear H. rewrite <- H1; clear H1. rewrite H4; clear H4.
            ring_simplify. reflexivity. }
          { charge_intros.
            eapply zero_deriv with (x:="v").
            { charge_assumption. }
            { charge_intros. compute. tauto. }
            { solve_linear. } }
          { solve_linear.
            rewrite <- H1; clear H1.
            rewrite H; clear H.
            rewrite H4; clear H4.
            ring_simplify. reflexivity. } }
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

  Theorem Spec_LyapunovStable :
    |-- Spec -->> LyapunovStable "x".
  Proof.
    charge_intros. tlaAssert ([]IndInv).
    { apply lrevert. apply spec_indinv. }
    { unfold LyapunovStable. charge_intros.
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
          * rewrite Always_next with (F := IndInv).
            charge_assumption.
            tlaIntuition.
          * unfold Next.
            rewrite <- BasicProofRules.Always_and.
            rewrite Always_next with (F := "T" >= 0).
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
                - compute. tauto.
                - simpl. restoreAbstraction.
                  eapply zero_deriv with (x:="v");
                    [ charge_assumption | charge_intro; solve_linear | solve_linear ].
                - simpl. restoreAbstraction.
                  eapply zero_deriv with (x:="v");
                    [ charge_assumption | charge_intro; solve_linear | solve_linear ].
                - simpl. restoreAbstraction.
                  eapply zero_deriv with (x:="v");
                    [ charge_assumption | charge_intro; solve_linear | solve_linear ].
                - simpl. restoreAbstraction.
                  solve_linear.
              + unfold IndInv. solve_nonlinear. }
            { charge_split; charge_intros.
              + solve_nonlinear.
              + eapply diff_ind with (Hyps:="v" >= 0) (G:=--"x" < b).
                - tlaIntuition.
                - tlaIntuition.
                - charge_tauto.
                - compute; tauto.
                - simpl. restoreAbstraction.
                  eapply zero_deriv with (x:="v");
                    [ charge_assumption | charge_intro; solve_linear | solve_linear ].
                - simpl. restoreAbstraction.
                  eapply zero_deriv with (x:="v");
                    [ charge_assumption | charge_intro; solve_linear | solve_linear ].
                - simpl. restoreAbstraction.
                  eapply zero_deriv with (x:="v");
                    [ charge_assumption | charge_intro; solve_linear | solve_linear ].
                - simpl. restoreAbstraction.
                  solve_linear. }
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
    Hypothesis alpha_gt_0 : (alpha > 0)%R.
    (* Beginning of time for exponential stability *)
    Variable t0 : R.
    Hypothesis t0_ge_0 : (t0 >= 0)%R.
    (* Value of "t" at the start of this continuous transition *)
    Variable t_start : R.
    Hypothesis t_start_ge_t0 : (t_start >= t0)%R.
    (* Value of "x" at the start of this continuous transition *)
    Variable x_start : R.
    Hypothesis x_start_gt_0 : (x_start > 0)%R.

    Lemma x_start_div_alpha_gt_0 : (x_start * / alpha > 0)%R.
    Proof.
      clear - alpha_gt_0 x_start_gt_0.
      assert (0 < alpha)%R by solve_linear.
      generalize (Rinv_0_lt_compat _ H).
      generalize (/ alpha)%R.
      solve_nonlinear.
    Qed.

    Let ln_x_start_div_alpha : R :=
      Rln (RIneq.mkposreal _ x_start_div_alpha_gt_0)%R.

    Lemma exp_ln_x_div_alpha
    : (eq (exp ln_x_start_div_alpha) (x_start / alpha))%R.
    Proof.
      unfold ln_x_start_div_alpha.
      unfold Rln. simpl.
      destruct (ln_exists (x_start * / alpha) x_start_div_alpha_gt_0); auto.
    Qed.

    Let t_at_x_start := (ln_x_start_div_alpha * / (-b) + t0)%R.

    Lemma exp_t_at_x_start_minus_t0
    : (eq (exp ((-b) * (t_at_x_start - t0))) (x_start / alpha))%R.
    Proof.
      unfold t_at_x_start.
      cutrewrite (eq (- b * (ln_x_start_div_alpha * / (-b) + t0 - t0)) ln_x_start_div_alpha)%R.
      apply exp_ln_x_div_alpha.
      ring_simplify.
      generalize b_gt_0.
      solve_nonlinear.
    Qed.

    (* This is the exponential function that we must stay under to
     * satisfy exponential stability. It combines alpha and x0 for simplicity.
     *)
    Let E (t : Term) : Term :=
      alpha * exp(--b * (t - t0)).

    Let T_slope : R := (-b * x_start)%R.

    (* This is the tangent to E @ [x=x_start]
     * - Note: At this point,
     *       t = - ln (x_start / alpha) / beta + t0
     *         = (ln alpha - ln x_start) / beta + t0
     *   Note that [x_start <= alpha] since [x_start <= x0 <= E 0 = alpha]
     *)
    Let T (t : Term) : Term :=
      T_slope * (t - t_at_x_start) + x_start.

    (* This is the linear function that we will follow along this
     * continuous evolution.
     *)
    Let L (t : Term) : Term :=
      T_slope * (t - t_start) + x_start.

    Definition Lin_Safe : Formula :=
      0 <= "x" <= L "t".

    Definition Exp_Safe : Formula :=
      0 <= "x" <= E "t".

    Lemma alpha_x_start_div_alpha_x_start
      : eq (alpha * (x_start / alpha))%R x_start.
    Proof.
      unfold Rdiv. rewrite Rmult_comm.
      rewrite Rmult_assoc. rewrite <- Rinv_l_sym.
      ring. solve_linear.
    Qed.

    (* (1) This is the proof that the exponential is concave up.
     * - First we prove the tangent is less than the exponential.
     * - Then we prove the line is less than the tangent.
     * - By transitivity we get that the line is less than the exponential.
     *)
    Theorem T_le_E : forall t, |-- T t <= E t.
    Proof.
      simpl. red. simpl. intros. clear H.
      generalize (eval_term t (Stream.hd tr) (Stream.hd (Stream.tl tr))).
      clear - t_start_ge_t0 x_start_gt_0 alpha_gt_0 b delta_gt_0 t_at_x_start.
      intro t.
      pose (T := (fun t => T_slope * (t - t_at_x_start) + x_start)%R).
      pose (E := (fun t => alpha * exp ((0 - b) * (t - t0)))%R).
      change (T t <= E t)%R.
      etransitivity.
      2: eapply (concavity_eq E _ _ t_at_x_start).
      Focus 2.
      intros.
      match goal with
      | |- eq ?X _ => remember X
      end.
      unfold E, Ranalysis1.derive; simplify_deriv_pt. subst. reflexivity.
      Focus 2.
      intros.
      match goal with
      | |- eq ?X _ => remember X
      end.
      unfold E, Ranalysis1.derive; simplify_deriv_pt. subst. reflexivity.
      simpl. unfold E.
      replace (0 - b)%R with (-b)%R by solve_linear.
      rewrite exp_t_at_x_start_minus_t0.
      unfold T, T_slope.
      match goal with
      | |- (?X <= ?Y)%R =>
        cutrewrite (eq X Y)%R
      end.
      { reflexivity. }
      { rewrite alpha_x_start_div_alpha_x_start.
        ring_simplify.
        repeat rewrite Rmult_assoc. rewrite alpha_x_start_div_alpha_x_start.
        ring. }
      { simpl. intros. ring_simplify.
        simpl.
        eapply Rle_ge.
        generalize b_gt_0; intro.
        (repeat eapply Rmult_0_le); solve_linear.
        generalize (Exp_prop.exp_pos (- b * (z - t0))).
        solve_linear. }
    Qed.

    Lemma t_start_le_t_at_x_start
    : x_start <= E t_start |-- t_start <= t_at_x_start.
    Proof.
      unfold E.
      breakAbstraction.
      intro. clear tr.
      unfold t_at_x_start.
      intros.
      assert (x_start / alpha <= exp ((0 - b) * (t_start - t0)))%R.
      { revert H. clear - alpha_gt_0.
        generalize (exp ((0 - b) * (t_start - t0)))%R.
        intros. unfold Rdiv. z3_solve; admit. }
      { clear H.
        cut ((-b) * (t_start - t0) >= ln_x_start_div_alpha)%R.
        { generalize b_gt_0. clearbody b. clearbody ln_x_start_div_alpha.
          clear. intros.
          z3_solve; admit. }
        cut (ln_x_start_div_alpha <= -b * (t_start - t0))%R.
        { clear; solve_linear. }
        eapply exp_le.
        rewrite exp_ln_x_div_alpha.
        clear - H0.
        etransitivity. eassumption.
        eapply exp_le. solve_linear. }
    Qed.

    Lemma T_slope_le_0 : (T_slope <= 0)%R.
    Proof.
      unfold T_slope.
      generalize b_gt_0. clear - x_start_gt_0.
      solve_nonlinear.
    Qed.

    Lemma L_le_T : forall t, x_start <= E t_start |-- L t <= T t.
    Proof.
      Opaque E.
      unfold L, T.
      clearbody b. clear. intros.
      tlaAssert (t_start <= t_at_x_start).
      { apply t_start_le_t_at_x_start. }
      red. simpl. red. simpl. intros.
      generalize dependent (eval_term t (Stream.hd tr) (Stream.hd (Stream.tl tr))).
      intros.
      eapply Rplus_Rle_mor; [ | reflexivity ].
      eapply Rmult_le_compat_neg_l. auto using T_slope_le_0.
      solve_linear.
    Qed.

    Theorem L_le_E : forall t, x_start <= E t_start |-- L t <= E t.
    Proof.
      intros. rewrite L_le_T with (t:=t).
      tlaAssert (T t <= E t).
      { apply forget_prem. apply T_le_E. }
      clearbody b. clearbody E. clearbody T. clear.
      breakAbstraction. intros. solve_linear.
    Qed.

    Theorem World_LinSafe' :
      |-- ("v" = --b * x_start //\\ x_start <= alpha * exp(-- b * (t_start - t0)) //\\ "x" = L "t" //\\ t_start < "t") //\\ (World //\\ "T"! >= 0) -->>
          next ("v" = --b * x_start //\\ x_start <= alpha * exp(-- b * (t_start - t0)) //\\ "x" = L "t" //\\ t_start <= "t").
    Proof.
      unfold Inductively, World, L.
      charge_intro.

      eapply diff_ind with (Hyps := "v" = --b * x_start).
      { compute ; tauto. }
      { compute ; tauto. }
      { charge_assumption. }
      { compute; tauto. }
      { eapply diff_ind with (Hyps := ltrue).
        { compute ; tauto. }
        { compute ; tauto. }
        { charge_assumption. }
        { compute ; tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { simpl. solve_linear. } }
      { unfold L.
        charge_split. charge_assumption.
        charge_split. charge_assumption.
        solve_linear. }
      { charge_tauto. }
      { simpl. unfold lift2. breakAbstraction.
        intros.
        rewrite H in *; clear H.
        destruct H0 as [ ? [ ? [ ? ? ] ] ].
        rewrite H; rewrite H0; rewrite H1; clear H H0 H1.
        unfold state, Value in *.
        rewrite_real_zeros.
        (repeat split); instantiate; repeat progress ring_simplify.
        - reflexivity.
        - solve_linear.
        - reflexivity.
        - solve_linear. }
    Qed.

    Theorem World_LinSafe'' :
      ("t" + "T" <= t_start + delta //\\ "v" = --b * x_start //\\ x_start <= alpha * exp(-- b * (t_start - t0)) //\\ -- "v" * "T" <= "x" <= L "t" //\\ t_start <= "t") //\\ (World //\\ "T"! >= 0) |--
          next ("t" + "T" <= t_start + delta //\\ "v" = --b * x_start //\\ x_start <= alpha * exp(-- b * (t_start - t0)) //\\ -- "v" * "T" <= "x" <= L "t" //\\ t_start <= "t").
    Proof.
      unfold Inductively, World, L.

      eapply diff_ind with (Hyps := "v" = --b * x_start).
      { compute ; tauto. }
      { compute ; tauto. }
      { charge_assumption. }
      { compute; tauto. }
      { eapply diff_ind with (Hyps := ltrue).
        { compute ; tauto. }
        { compute ; tauto. }
        { charge_assumption. }
        { compute ; tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { simpl. solve_linear. } }
      { unfold L.
        charge_split. charge_assumption.
        charge_split. charge_assumption.
        solve_linear. }
      { charge_tauto. }
      { simpl. unfold lift2. breakAbstraction.
        intros.
        rewrite H in *; clear H.
        destruct H0 as [ ? [ ? [ ? ? ] ] ].
        rewrite H; rewrite H0; rewrite H1; clear H H0 H1.
        unfold state, Value in *.
        rewrite_real_zeros.
        (repeat split); instantiate; repeat progress ring_simplify.
        - solve_linear.
        - reflexivity.
        - solve_linear.
        - rewrite H2. solve_linear.
        - reflexivity.
        - solve_linear. }
    Qed.

  End ContinuousTransition.

  Lemma Exists_with_st : forall G P (t : Term),
      (forall x : R, G |-- t = x -->> P x) ->
      G |-- Exists x : R, P x.
  Proof.
    breakAbstraction.
    intros.
    specialize (H _ tr H0 eq_refl).
    eexists. eauto.
  Qed.

  Definition the_ind_inv (x0 t0 : R) : Formula :=
    (Exists t_start : R, Exists x_start : R,
       "t" + "T" <= t_start + delta //\\
       "v" = --b * x_start //\\
       x_start <= x0 * exp(-- b * (t_start - t0)) //\\
       -- "v" * "T" <= "x" <= (- b * x_start)%R * ("t" - t_start) + x_start //\\
       t_start <= "t").

  Lemma World_LinSafeY (x0 t0 : R)
  : |-- Inductively
          (the_ind_inv x0 t0)
          (World //\\ "T"! >= 0).
  Proof.
    unfold Inductively.
    apply always_tauto.
    simpl. restoreAbstraction.
    charge_intros.
    tlaRevert.
    apply lexistsL; intro t_start.
    apply lexistsL; intro x_start.
    charge_intro.
    apply lexistsR with (x :=t_start).
    apply lexistsR with (x :=x_start).
    etransitivity. 2: eapply World_LinSafe''.
    charge_tauto.
  Qed.

(*
  [](Exists t_start : R, Exists x_start : R,
                        t_start <= "t" <= t_start + delta //\\
                        x_start <= x0 * exp(-- b * (t_start - t0)) //\\
                        Lin_Safe t_start x_start) -->>
    [](Exp_Safe t0 x0)
*)

  Lemma Discr_LinSafeY (x0 t0 : R)
  : |-- Inductively (the_ind_inv x0 t0)
                    (Ctrl //\\ ("T") ! <= delta //\\ "T"! >= 0).
  Proof.
    unfold Inductively.
    apply always_tauto.
    simpl; restoreAbstraction.
    charge_intros.
    tlaRevert.
    apply lexistsL; intro t_start.
    apply lexistsL; intro x_start.
    unfold Ctrl.
    charge_intro.
    apply Exists_with_st with (t:="t"!); intro t_start'.
    charge_intro.
    apply Exists_with_st with (t:="x"); intro x_start'.
    charge_intro.
    simpl; breakAbstraction.
    intros. forward_reason.
    rewrite H0 in *; clear H0.
    rewrite H1 in *; clear H1.
    rewrite H5 in *; clear H5.
    rewrite H6 in *; clear H6.
    rewrite H2 in *; clear H2.
    rewrite H8 in *; clear H8.
    split.
    { solve_linear. }
    split.
    { unfold b. solve_linear. }
    split.
    { (* because L_le_E *) admit. }
    split. 
    { unfold Value in *. split.
      { ring_simplify. admit. }
      { ring_simplify. reflexivity. } }
    { reflexivity. }
  Qed.

  Lemma Term_tricotomy : forall (v : Term),
      |-- v < 0 \\// v = 0 \\// v > 0.
  Proof. solve_linear. Qed.


  Lemma lor_same : forall P, P \\// P -|- P.
  Proof. clear. intros.
         eapply lequiv_to_iff.
         intros. simpl. tauto.
  Qed.

  Lemma Spec_Always_T_ge_0
  : Spec |-- Init //\\ [] (World \\// Ctrl //\\ ("T") ! <= delta //\\ "T" >= 0 //\\ "T"! >= 0).
  Proof.
    unfold Spec. charge_split; [ charge_assumption | ].
    tlaAssert ([] "T"! >= 0).
    { unfold Next.
      repeat rewrite <- Always_and.
      change ([]("T") ! >= 0) with ([]next ("T" >= 0)).
      etransitivity; [ | eapply Always_next ].
      charge_tauto. compute; tauto. }
    tlaRevert. rewrite <- curry.
    rewrite Always_and.
    apply always_imp.
    charge_intro. unfold Next.
    decompose_hyps.
    { charge_left. charge_assumption. }
    { charge_right. charge_tauto. }
  Qed.

  Lemma Spec_strengthen
  : Spec |-- Exists t0 : R, "t" = t0 //\\ Exists x0 : R, "x" = x0 //\\
              Init //\\ []((the_ind_inv x0 t0 //\\ (World //\\ "T"! >= 0)) \\//
              (the_ind_inv x0 t0 //\\ (Ctrl //\\ ("T") ! <= delta //\\ "T"! >= 0))).
  Proof.
    intros.
    rewrite Spec_Always_T_ge_0.
    apply Exists_with_st with (t:="t").
    intro t0. charge_intro.
    charge_split; [ charge_assumption | ].
    apply Exists_with_st with (t:="x").
    intro x0. charge_intro.
    charge_split; [ charge_tauto | ].
    charge_split; [ charge_tauto | ].
    tlaAssert ([](the_ind_inv x0 t0)).
    { eapply discr_indX.
      { compute; tauto. }
      { charge_assumption. }
      { unfold the_ind_inv.
        tlaAssert (Init //\\ "t" = t0 //\\ "x" = x0 //\\ "T" >= 0);
          [ try charge_tauto | apply forget_prem; charge_intro ].
        { repeat charge_split; try charge_assumption. admit. }
        apply lexistsR with (x:=t0).
        apply lexistsR with (x:=x0).
        unfold Init.
        repeat charge_split; try solve_linear.
        { unfold b. solve_nonlinear. }
        { cutrewrite (eq ((0-b) * (t0 - t0)) 0)%R.
          { rewrite exp_0. solve_linear. }
          { ring. } }
        { rewrite H. ring_simplify.
          rewrite H2.
          clear - H4 H5 delta_gt_0.
          assert (0 < / delta * Stream.hd tr "T" <= 1)%R.
          { admit. }
          { admit. } }
        { rewrite H2. rewrite H0. ring_simplify. reflexivity. } }
      { admit. } }
    { tlaAssert ([]
                   (World \\// Ctrl //\\ ("T") ! <= delta //\\ "T" >= 0 //\\ ("T") ! >= 0));
      [ charge_assumption | ].
      rewrite <- curry.
      rewrite Always_and.
      apply forget_prem. apply always_imp.
      charge_intros.
      decompose_hyps.
      { charge_left. admit. }
      { charge_right. charge_tauto. } }
  Qed.

  Theorem Spec_ExpStable :
    |-- Spec -->> ExpStable "x".
  Proof.
    (** Instantiate alpha and beta **)
    charge_intro.
    pose (alpha := 1%R).
    apply lexistsR with (x:=alpha).
    charge_split.
    { solve_linear. }
    pose (beta := b).
    apply lexistsR with (x:=beta).
    charge_split.
    { generalize b_gt_0. solve_linear. }
    eapply Exists_with_st with (t:="x").
    intro x0; charge_intro.
    charge_split; [ charge_tauto | ].
    eapply Exists_with_st with (t:="t").
    intro t0; charge_intro.
    charge_split; [ solve_linear | ].

    (**  This is where things start **)
  Admitted.

End ExponentialStability.
End P.

(*
  Lemma Next_LinSafe
  : |-- Inductively
          (let t_start := "T" in
           Exists x_start : R,
           let T_slope := (- b * x_start) in
           let L := fun t : Term => T_slope * (t - t_start) + x_start in
           "x" = L "t" //\\
           "v" = -- (b) * x_start //\\
           t_start <= "t" //\\ "t" <= t_start + delta)
          (Next //\\
           (Exists x_start : R,
    "x" = (- b * x_start)%R * ("t" - "T") + x_start //\\
    "v" = (0 - b) * x_start //\\ "T" <= "t" //\\ "t" <= "T" + delta)).
  Proof.
    erewrite Inductively_equiv.
    - eapply Inductively_Or'.
      + eapply World_LinSafe'.
      + eapply Discr_LinSafe'.
    - compute; tauto.
    - compute; tauto.
    - simpl. restoreAbstraction.
      match goal with
      | |- _ -|- ?X \\// ?Y =>
        assert (X -|- Y)
      end.
      { eapply lexists_lequiv_m; red. intros.
        eapply lequiv_to_iff. intros.
        simpl. split; solve_linear. }
      rewrite H.
      rewrite lor_same. reflexivity.
    - unfold Next. simpl. restoreAbstraction.
      rewrite land_lor_distr_R.
      (* Ctrl matches up.
       * World is a complete disaster! I need to show a simulation
       * between "T" and "t"
       *)
      admit.
  Qed.

  Theorem Spec_ExpStable :
    |-- Spec -->> ExpStable "x".
  Proof.
    charge_intro.
    pose (alpha := 1%R).
    apply lexistsR with (x:=alpha).
    charge_split.
    { solve_linear. }
    pose (beta := b).
    apply lexistsR with (x:=beta).
    charge_split.
    { generalize b_gt_0. solve_linear. }
    eapply Exists_with_st with (t:="x").
    intro x0; charge_intro.
    charge_split; [ charge_tauto | ].
    eapply Exists_with_st with (t:="t").
    intro t0; charge_intro.
    charge_split; [ solve_linear | ].

    tlaAssert ([](Exists x_start : R,
                    let t_start := "T" in
                    let T_slope := (- b * x_start) in
                    let L := fun t : Term => T_slope * (t - t_start) + x_start in
                    x_start <= alpha * Rabs x0 * exp(--beta * (t_start - t0)) //\\
                    "x" = L "t" //\\
                    "v" = -- (b) * x_start //\\
                    t_start <= "t" //\\ "t" <= t_start + delta)).
    { admit. }
    { simpl. restoreAbstraction.
      eapply always_imp. unfold alpha. unfold beta.
      charge_intros.
      apply lexistsL. intro x_start.
      tlaAssert ((fun t1 : Term => (- b * x_start)%R * (t1 - "T") + x_start) "t" <=
                 (fun t1 : Term => alpha * exp(-- (b) * (t1 - t0))) "t").
      { breakAbstraction. intros.
        forward_reason.
        generalize dependent (Stream.hd tr "T").
        generalize dependent (Stream.hd tr "t").
        generalize dependent (Stream.hd tr "x").
        generalize dependent (Stream.hd tr "v").
        intro v. intro. intros x t T. intros.
        subst.
        Check L_le_E.

        generalize (fun X => L_le_E 1%R X t0 T (Rabs x_start)).
      
      
      { 


    (* Trial *)
    unfold Spec; eapply discr_indX.
    { compute; tauto. }
    { charge_assumption. }
    { unfold Init.
      breakAbstraction. intros. forward_reason.
      rewrite H1 in *; rewrite H0 in *; rewrite H5 in *; clear H1 H0 H5.
      subst.
      cutrewrite (eq ((0 - x0) * (0 - 0)) 0)%R ; [ | solve_linear ].
      rewrite exp_0. split; intros.
      { ring_simplify. eapply Rle_abs. }
      { ring_simplify. rewrite Rabs_left1. reflexivity. assumption. } }
    unfold Next.
    decompose_hyps.
    { About World_LinSafe. 
      


    tlaAssert ("x" < 0 \\// "x" = 0 \\// "x" > 0).
    { charge_apply (Term_tricotomy "x"). charge_tauto. }
    charge_intro. decompose_hyps.
    { eapply Exists_with_st with (t:=--"x").
      admit. }
    { admit. }
    { eapply Exists_with_st with (t:=1).
      intros. charge_intros.
      charge_split.
      { solve_linear. }
      eapply Exists_with_st with (t:=b).
      intros; charge_intros.
      charge_split.
      { generalize (b_gt_0). solve_linear. }
      eapply Exists_with_st with (t:="x").
      intros; charge_intro.
      charge_split; [ charge_tauto | ].
      eapply Exists_with_st with (t:="t").
      intros; charge_intro.
      charge_split; [ solve_linear | ].
      eapply discr_indX.
      { compute; tauto. }
      { unfold Spec. charge_assumption. }
      { unfold Spec, Init.
        breakAbstraction. intros.

        forward_reason.
        split.
        { clear H4. intros.
          rewrite H1 in *. rewrite H0 in *. clear H1 H0.
          subst.
          rewrite Rabs_pos_eq by solve_linear.
          cutrewrite (eq ((0 - x0) * (0 - 0)) 0)%R ; [ | solve_linear ].
          rewrite exp_0. solve_linear. }
        { clear - H4. intros. exfalso. solve_linear. }
        repeat match goal with
               | H : _ /\
        
        

  (* This theorem is a complete disaster. I still need
   * - A simulation to reconcile the clocks
   * - A case split for introducing absolute value
   *)

  Theorem Spec_ExpStable :
    |-- Spec -->> ExpStable "x".
  Proof.
    charge_intro.
    tlaAssert ("x" < 0 \\// "x" = 0 \\// "x" > 0).
    { charge_apply (Term_tricotomy "x"). charge_tauto. }
    charge_intro. decompose_hyps.
    { eapply Exists_with_st with (t:=--"x").
      admit. }
    { admit. }
    { eapply Exists_with_st with (t:="x").
      intros. charge_intros.
      charge_split.
      { solve_linear. }
      eapply Exists_with_st with (t:=b).
      intros; charge_intros.
      charge_split.
      { generalize (b_gt_0). solve_linear. }
      eapply Exists_with_st with (t:="x").
      intros; charge_intro.
      charge_split; [ charge_tauto | ].
      eapply Exists_with_st with (t:="t").
      intros; charge_intro.
      charge_split; [ solve_linear | ].
      Print Next.

  Qed.
*)


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
*)






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


(*
  Lemma Discr_LinSafeY (x0 t0 : R)
  : |-- Inductively (Exists t_start : R, Exists x_start : R,
                        t_start <= "t" <= t_start + delta //\\
                        x_start <= x0 * exp(-- b * (t_start - t0)) //\\ (* line line *)
                        Lin_Safe t_start x_start)
                    (Ctrl //\\ ("T") ! <= delta //\\ "T" >= 0).
  Proof.
    unfold Inductively.
    apply always_tauto.
    simpl; restoreAbstraction.
    charge_intros.
    tlaRevert.
    apply lexistsL; intro t_start.
    apply lexistsL; intro x_start.
    unfold Ctrl.
    charge_intro.
    apply Exists_with_st with (t:="t"!); intro t_start'.
    charge_intro.
    apply Exists_with_st with (t:="x"); intro x_start'.
    charge_intro.
    simpl; breakAbstraction.
    intros. forward_reason.
    rewrite H0 in *; clear H0.
    rewrite H1 in *; clear H1.
    rewrite H5 in *; clear H5.
    rewrite H6 in *; clear H6.
    clear H2.
    split.
    { split; solve_linear. }
    split.
    { (* because L_le_E *)
    }
    { solve_linear. }
  Qed.

    Theorem World_LinSafe' :
      |-- Inductively
          (let t_start := "T" in Exists x_start : R,
           let T_slope := (- b * x_start)%R in
           let L := fun t : Term => T_slope * (t - t_start) + x_start in
           "x" = L "t" //\\
           "v" = -- (b) * x_start //\\
           t_start <= "t" //\\ "t" <= t_start + delta)
          (World //\\ "t"! <= "T" + delta)%HP.
    Proof.
      unfold Inductively, World.
      eapply always_tauto.

      (* this is the differential invariant *)
      charge_intro.
(*
      tlaRevert. 

      transitivity (     BasicProofRules.next ("x" = L "t" //\\
                                               "v" = -- (b) * x_start //\\
                                               t_start <= "t")
                    //\\ BasicProofRules.next ("t" <= t_start + delta));
        [ | charge_tauto ].
      charge_split; [ | charge_tauto ].
      eapply diff_ind with (Hyps := "v" = --b * x_start).
      { compute ; tauto. }
      { compute ; tauto. }
      { charge_assumption. }
      { compute; tauto. }
      { eapply diff_ind with (Hyps := ltrue).
        { compute ; tauto. }
        { compute ; tauto. }
        { charge_assumption. }
        { compute ; tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { simpl. solve_linear. } }
      { unfold L.
        charge_split. charge_assumption.
        charge_split. charge_assumption.
        solve_linear. }
      { charge_tauto. }
      { simpl. unfold lift2. breakAbstraction.
        intros.
        rewrite H in *; clear H.
        destruct H0 as [ ? [ ? [ ? ? ] ] ].
        rewrite H; rewrite H0; rewrite H1; clear H H0 H1.
        unfold state, Value in *.
        (repeat split); instantiate; repeat progress ring_simplify.
        - reflexivity.
        - reflexivity.
        - solve_linear. }
*)
    Admitted.


  Lemma Discr_LinSafe : forall t0 alpha : R,
    |-- Inductively
          (Exists t_start : R, Exists x_start : R,
           let T_slope := (- b * x_start)%R in
           let L := fun t : Term => T_slope * (t - t_start) + x_start in
           "x" = L "t" //\\
           "v" = -- (b) * x_start //\\
           t_start <= "t" //\\ "t" <= t_start + delta)
          (Ctrl //\\ "T" <= delta).
  Proof.
    unfold Inductively, Ctrl. intros.
    eapply always_tauto.
    simpl; restoreAbstraction.
    charge_intro.
    apply landL2.
    apply Exists_with_st with (t:="t"); intro t_start; charge_intro.
    apply Exists_with_st with (t:="x"); intro x_start; charge_intro.
    breakAbstraction; intros.
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           end.
    rewrite H0 in *; clear H0.
    rewrite H4 in *; clear H4.
    rewrite H1 in *; clear H1.
    rewrite H3 in *; clear H3.
    rewrite H in *; clear H.
    split; [ solve_linear | ].
    split; [ | solve_linear ].
    ring_simplify.
    change (/ delta)%R with b.
    reflexivity.
  Qed.

  Lemma Discr_LinSafe' :
    |-- Inductively
          (let t_start : Term := "T" in
           Exists x_start : R,
           let T_slope := (- b * x_start) in
           let L := fun t : Term => T_slope * (t - t_start) + x_start in
           "x" = L "t" //\\
           "v" = -- (b) * x_start //\\
           t_start <= "t" //\\ "t" <= t_start + delta)
          (Ctrl //\\ next_term "T" <= delta)%HP.
  Proof.
(*
    unfold Inductively, Ctrl. intros.
    eapply always_tauto.
    simpl; restoreAbstraction.
    charge_intro.
    apply landL2.
    breakAbstraction; intros.
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           end.
    rewrite H1 in *; clear H1.
    rewrite H2 in *; clear H2.
    rewrite H in *; clear H.
    split; [ solve_linear | ].
    split; [ | solve_linear ].
    ring_simplify.
    change (/ delta)%R with b.
    reflexivity.
  Qed.
*)
  Admitted.
*)


(*
  Lemma World_LinSafeY (x0 t0 : R)
  : |-- Inductively
          (Exists t_start : R, Exists x_start : R,
              t_start <= "t" <= t_start + delta //\\
              x_start <= x0 * exp(-- b * (t_start - t0)) //\\
              Lin_Safe t_start x_start)
          (World //\\ "T"! >= 0).
  Proof.
    unfold Inductively.
    apply always_tauto.
    simpl. restoreAbstraction.
    charge_intros.
    tlaRevert.
    apply lexistsL; intro t_start.
    apply lexistsL; intro x_start.
    tlaRevert. tlaRevert. tlaRevert.
    etransitivity.
    eapply (World_LinSafeX x0 t0 t_start x_start).
    charge_intros.
    tlaAssert (next (Lin_Safe t_start x_start //\\ x_start <= x0 * exp((0 - b) * ("t" - t0)))).
    { simpl. restoreAbstraction.
      repeat charge_split; try charge_tauto. }
    apply forget_prem.
    charge_intro.
    apply lexistsR with (x :=t_start).
    apply lexistsR with (x :=x_start).
    simpl. restoreAbstraction. charge_split; solve_linear.
  Qed.
*)

(*
  Lemma World_LinSafeY (x0 t0 : R)
  : |-- Inductively (Exists t_start : R, Exists x_start : R, x_start < x0 * exp(-- b * ("t" - t0)) //\\ Lin_Safe t_start x_start)
                    (World //\\ "T"! >= 0).
  Proof.
    unfold Inductively.
    apply always_tauto.
    simpl. restoreAbstraction.
    charge_intros.
    tlaRevert.
    apply lexistsL; intro t_start.
    apply lexistsL; intro x_start.
    tlaRevert. tlaRevert.
    etransitivity.
    eapply (World_LinSafeX t_start x_start).
    charge_intros.
    tlaAssert (next (Lin_Safe t_start x_start)).
    { charge_tauto. }
    apply forget_prem.
    charge_intro.
    apply lexistsR with (x :=t_start).
    apply lexistsR with (x :=x_start).
    simpl. restoreAbstraction. charge_split; solve_linear.
  Qed.
*)


(*
    Lemma T_inductively :
      |-- ("t" + "T" <= t_start + delta) //\\ (World //\\ "T"! >= 0) -->>
          next ("t" + "T" <= t_start + delta).
    Proof.
      charge_intros.
      tlaAssert (next ("t" + "T" <= t_start + delta)).
      { eapply diff_ind with (Hyps := ltrue).
        { compute; tauto. }
        { compute; tauto. }
        { unfold World. charge_assumption. }
        { compute; tauto. }
        { charge_tauto. }
        { revert delta_gt_0. clear. solve_linear. }
        { charge_tauto. }
        { simpl; unfold lift2; restoreAbstraction.
          charge_intros.
          solve_linear. } }
      { charge_tauto. }
    Qed.

    Lemma World_full
    : |-- (
              "v" = -b * x_start //\\
              t_start <= "t" <= t_start + delta //\\
              x_start <= alpha * exp(-- b * (t_start - t0)) //\\
              Lin_Safe) //\\
          (World //\\ "T"! >= 0) -->>
          next (
              "v" = -b * x_start //\\
              t_start <= "t" <= t_start + delta //\\
              x_start <= alpha * exp(-- b * (t_start - t0)) //\\
              Lin_Safe).
    Proof.
      charge_intros.
      generalize T_inductively.
      generalize World_LinSafe'.
      clear.
      Opaque World.
      breakAbstraction. intros.
      specialize (H0 tr I).
      specialize (H tr I).
      forward_reason.
      destruct H.
      { repeat split. solve_linear.
        solve_linear.
*)
(*
    Theorem World_LinSafeX :
      |-- Inductively Lin_Safe (World //\\ "T"! >= 0).
    Proof. clear - delta_gt_0. admit. Qed.
*)
(*
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
      transitivity (     BasicProofRules.next ("x" = L "t" //\\
                                               "v" = -- (b) * x_start //\\
                                               t_start <= "t")
                    //\\ BasicProofRules.next ("t" <= t_start + delta));
        [ | charge_tauto ].
      charge_split; [ | charge_tauto ].
      eapply diff_ind with (Hyps := "v" = --b * x_start).
      { compute ; tauto. }
      { compute ; tauto. }
      { charge_assumption. }
      { compute; tauto. }
      { eapply diff_ind with (Hyps := ltrue).
        { compute ; tauto. }
        { compute ; tauto. }
        { charge_assumption. }
        { compute ; tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { charge_tauto. }
        { simpl. solve_linear. } }
      { unfold L.
        charge_split. charge_assumption.
        charge_split. charge_assumption.
        solve_linear. }
      { charge_tauto. }
      { simpl. unfold lift2. breakAbstraction.
        intros.
        rewrite H in *; clear H.
        destruct H0 as [ ? [ ? [ ? ? ] ] ].
        rewrite H; rewrite H0; rewrite H1; clear H H0 H1.
        unfold state, Value in *.
        (repeat split); instantiate; repeat progress ring_simplify.
        - reflexivity.
        - reflexivity.
        - solve_linear. }
    Qed.
(*
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
*)
(*
  Lemma Spec_strengthen t0 x0
  : Init //\\ []((the_ind_inv t0 x0 //\\ (World //\\ "T"! >= 0)) \\//
              (the_ind_inv t0 x0 //\\ (Ctrl //\\ ("T") ! <= delta //\\ "T"! >= 0))) |-- Spec.
  Proof.
    intros.
    unfold Spec.
    charge_split; [ charge_tauto | ].
    tlaAssert ([]("T" >= 0 //\\ the_ind_inv t0 x0)).
    { eapply discr_indX.
      { compute; tauto. }
      { charge_assumption. }
      { admit. }
      { decompose_hyps.
        { tlaAssert (the_ind_inv t0 x0 //\\ (World //\\ ("T") ! >= 0)); [ charge_tauto | ].
          apply forget_prem.
          rewrite (World_LinSafeY t0 x0).
          unfold Inductively.
          eapply Always_now. Opaque the_ind_inv.
          simpl. restoreAbstraction.
          tlaRevert. apply always_imp. charge_tauto. }
        { charge_split; fold next.
          { charge_tauto. }
          { admit. } } } }
    { tlaRevert. rewrite <- curry.
      rewrite Always_and.
      apply always_imp.
      unfold Next.
      charge_intros. decompose_hyps.
      { charge_left. charge_tauto. }
      { charge_right. charge_tauto. } }
  Qed.
*)
