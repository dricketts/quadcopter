Require Import Logic.Syntax.
Require Import Logic.Semantics.
Require Import Logic.ProofRules.
Require Import String.
Local Open Scope HP_scope.
Local Open Scope string_scope.
Require Import List.
Require Import Strings.String.
Import ListNotations.
Require Import Rdefinitions.
Require Import ExtLib.Core.RelDec.
Require Import Coq.Reals.Rbase.
Require Import SMT.Tactic.
Require Import Abstractor.Embed.
Require Import Abstractor.FloatEmbed.
Require Import Logic.Automation.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Tactics.
Require Import Abstractor.FloatOps.
Require Import Abstractor.FloatLang.
Require Import Abstractor.Automation.

(* Implementation of postprocessing automation for the Abstractor,
   using the Z3 plugin to simplify the terms produced by the abstractor *)

(* test case: proportional controller *)

(* c is constant and goal is 0 *)

Definition proportional_controller : fcmd :=
  FAsn "a" (FMinus (FConst fzero) (FVar "x")).

Definition proportional_controller_ivs : list (Var * Var) :=
  [("a", "a"); ("x", "x")].


(* Very simple program for testing. We want to prove that x stays >0 *)
Definition float_one := nat_to_float 1.
Definition simple_prog : fcmd :=
  FAsn "x" (FPlus (FConst float_one) (FVar "x")).

Definition simple_prog_ivs : list (Var) :=
  [("x")].

Definition simpler_prog : fcmd :=
  FAsn "x" (FConst float_one).


(* Version of HoareA_embed_ex we can use for rewriting. *)
Require Import ExtLib.Tactics.
Import FloatEmbed.
Locate Ltac breakAbstraction.

(*
Axiom Always_proper : Proper (lentails ==> lentails) Syntax.Always.
Existing Instance Always_proper.
*)


(* velocity-shim controller *)
(*
Definition velshim : fcmd :=
  FIte (FMinus (FVar "ub") (FPlus (FMult (FVar "a") (FVar "d")) (FVar "vmax")))
       (FAsn "a" (FVar "a"))
       (FAsn "a" (FConst fzero)).
 *)

Definition f10 := Eval lazy in (concretize_float (nat_to_float 10)).

(*
Definition velshim : fcmd :=
  FIte (FMinus (FConst f10) (FPlus (FMult (FVar "a") (FConst float_one)) (FVar "v")))
       (FAsn "a" (FConst fzero))
       (FAsn "a" (FVar "a")).
*)

Definition f9 := Eval lazy in (concretize_float (nat_to_float 9)).

Definition velshim2 : fcmd :=
  FIte (FPlus (FVar "a") (FVar "v")) (FConst f9)
       (FAsn "a" (FVar "a"))
       (FAsn "a" (FConst fzero)).

(* variables we read in *)
Definition velshim_vs_in : list (Var) :=
  ["a"; "v"].

(* variables we're allowed to modify *)
Definition velshim_vs_out : list (Var) :=
  ["a"].

(* use theorem to hide tail. then use cbv whitelist that doesn't
           reduce the tail *)

Definition bound_fexpr2 := bound_fexpr.
Opaque bound_fexpr2.

Transparent ILInsts.ILFun_Ops.
Require Import Coq.Logic.ClassicalFacts.
Axiom pe_ax : prop_extensionality.

(*
Lemma varIsValid :
  forall (v : Var) (fs : fstate) (x : float),
    fstate_lookup fs v = Some x ->
    forall (r : R),
      F2OR x = Some r ->
      isVarValid v fs.
Proof.
  intros.
  unfold isVarValid.
  eexists. split; [eauto|].
  consider x; intros; simpl in *; congruence.
Qed.
*)

Require Import Coq.micromega.Psatz.


Definition pred1 (r : R) : Prop :=
  (-(100000*100000) < r < (100000*100000))%R.

Require Import Abstractor.Bound.
Require Import Coq.micromega.Psatz.

Require Import Examples.System.
Require Import Examples.Velocity.

Module MyVelocityShimParams <: VelocityShimParams.
                                Definition ub := 10%R.
                                Definition d := 1%R.
                                Lemma d_gt_0 : (d > 0)%R.
                                                 unfold d; lra.
                                Qed.
End MyVelocityShimParams.

Module MyVelocityShim := VelocityShim(MyVelocityShimParams).
Import MyVelocityShim.

Locate fstate_get_rval.

(* proof is 198 lines *)
Theorem fwp_velshim2_full
: (*preVarPred pred1 "a" //\\ preVarPred pred1 "v" //\\*)
  (embed_ex_seal velshim_vs_in velshim_vs_out velshim2)
  |-- Ctrl //\\ Lib.Unchanged ["v"]%HP.
Proof.
  (*rewrite landC. rewrite landA. rewrite landC. rewrite landA.*)
  (*tlaRevert.*)
  
  erewrite -> Hoare__embed_seal_rw.
  {
    eapply lforallL.
    (*instantiate (1 := (fstate_get_rval "a" (fun a =>
                                              fstate_get_rval "v" (fun v _ => (a = 0 \/ v + a < 10)%R)))).*)
    (* this should be the models fact. *)
    instantiate (1 := fun st fst => (models M.asReal_in velshim_vs_in fst st)).
    eapply lequiv_rewrite_left.

    {
      cbn beta zeta iota delta [Lib.Unchanged list_minus string_dec velshim_vs_in velshim_vs_out in_dec string_dec].
      Print fpig_vcgen.
      (* comparisons? *)
      
      cbn beta zeta iota delta -[bound_fexpr].
      rewrite <- embed_push_And.
      instantiate (2 := (fun x y => eq (x "v") (y "v"))).
      2: reflexivity.
      2: compute; intros; split; destruct tr; intros; destruct tr; fwd; auto.

      crunch_embeds.
      simpl.
      instantiate (1 := (Embed (fun x y : state => (x "v" = y "v")%type))).
      split; breakAbstraction; auto.
    }

    apply landAdj.
    apply lexistsL.
    intros.
    simpl bound_fexpr.
    apply land_comm_left.

    (* need some kind of way to teach z3 about nan... *)
    

    breakAbstraction.
    
    intros.
    fwd.
    split; auto.
    unfold absFloatConst, fstate_lookup_nan in *. simpl in *.
    destruct H2.
    {
      fwd.
      apply models_exploit in H1. apply models_exploit in H. apply models_exploit in H2.
      simpl in H, H1, H2. fwd.
      inversion H2; subst; clear H2.
      unfold pl_data in *.
      rewrite H in H3.
      rewrite H9 in H4.

      Print asReal_in.

      Lemma asReal_in_B2Rinf :
        forall f r, asReal_in f r ->
               exists ri, eq (B2Rinf f) (Some ri).
      Admitted.
      
      generalize (asReal_in_B2Rinf _ _ H12).
      generalize (asReal_in_B2Rinf _ _ H11).
      intros. fwd.
      rewrite H2 in H4.
      rewrite H15 in H4.
      rewrite H15 in H3.
      unfold maybe_lt, absFloatPlus' in H4.
      simpl in H4.
      consider (Rinf_plus x1 x7); simpl; intros.
      {
        unfold roundDown_Rinf, roundDown_Rinf in H16.
        consider r; intros.
        { subst.
          consider (Rlt_dec r0 (-floatMax)); intros.
          assert (RinfR (Stream.hd (Stream.tl tr) "a") = x1) by admit.
          Print intervalD.
          Print asReal_out.
          unfold intervalD in H3.
          subst.
          simpl in *.
          show_z3_hints.
          show_values.
          do_F2Rs.
          unfold MyVelocityShimParams.ub, MyVelocityShimParams.d.
          assert (x1 = (Stream.hd (Stream.tl tr) "a") by admit.
          z3 solve.


              fo
      
      consider (B2Rinf x4); simpl; intros; consider (B2Rinf x5); simpl; intros.
      { 
        destruct H3; fwd; try congruence.
        consider (B2Rinf x6); intros; try congruence. fwd. 
        assert (r = r1) by admit. subst.
        Print maybe_lt. 
        unfold maybe_lt, absFloatPlus' in *. simpl in *.
        consider (Rinf_plus r1 r0); intros. simpl in H18.
        unfold roundDown_Rinf in H18.
        consider r; intros.
        subst.
        consider (Rlt_dec r2 (- floatMax)%R); intros.
        show_values.
        unfold MyVelocityShimParams.d, MyVelocityShimParams.ub.
        assert (x4 = x2) by admit. subst.
        assert (x5 = x3) by admit. subst.
        assert (x2 = x6) by admit. subst.
        unfold M.asReal_in in *.
        consider x6; simpl; intros; consider x3; simpl; intros.
        inversion H11; subst.
        show_z3_hints.
        show_values.
        do_F2Rs.
        subst.
        inversion H8; subst; clear H8.
        inversion H23; subst; clear H23.
        unfold M.asReal_out in H14.
        simpl in H14.
        inversion H14; subst; clear H14.
        z3 solve.


        { simpl in *.
          unfold roundDown_Rinf in *.
          consider r; intros.
          { consider (Rlt_dec r2 (-floatMax)).
            { intros.
              do_F2Rs.
              assert (Stream.hd (Stream.tl tr) "a" = Stream.hd tr "a") by admit.
              subst.
              show_values.
              unfold MyVelocityShimParams.d, MyVelocityShimParams.ub.
              assert (x4 = x2) by admit. subst.
              assert (x5 = x3) by admit. subst.
              z3 solve.
              

              z3 solve.
              
          consider 
          simpl in *.
        
        fwd.
      {
      
      fwd.
      consider (fm_lookup x0 "v");
        consider (fm_lookup x0 "a"); simpl; intros.
      { consider (B2Rinf x1); consider (B2Rinf f0); intros.
        apply models_exploit in H2. simpl in H2. fwd.
        unfold maybe_lt, absFloatPlus' in H7. simpl in H7.
        fwd.
        consider 
        apply Bool.orb_false_iff in H8. fwd.
        consider (B2Rinf f0); intros.
        Focus 2.
        unfold absFloatPlus' in *. simpl in *.
        { 

          simp
        Check Bool.orb_alse_iff
        .
      

    
    destruct H4; fwd; try congruence.
    consider (fm_lookup x0 "a"); try contradiction; intros.
    consider (B2Rinf f); try contradiction; intros.
    fwd.

    (* derive a contradiction if B2Rinf x2 is nan. *)
    consider (B2Rinf x2); intros.
    Focus 2.
    {
      simpl in H11.
      fwd.
      unfold Fappli_IEEE.is_nan in H11.
      destruct H11.
      { consider f; simpl; intros; fwd; try congruence. }
      { consider (B2Rinf f); simpl; intros; try contradiction.
        fwd.
        consider (fm_lookup x0 "v"); intros.
        { unfold definitely_lt, maybe_not_lt in *. simpl in *.
          fwd.
          consider (B2Rinf x1); simpl; intros; subst.
          consider (B2Rinf f0); simpl; intros; subst.
          simpl in H15.
          

            unfold absFloatPlus' in H15.,
            simpl in H15.
            unfold maybe_not_lt in H14.
            simpl in *.
    {
      

    unfold pl_data in *.
    destruct H2.
    { fwd.
      unfold fstate_lookup_nan in *.
      split; auto.
      simpl in H4, H3.
      apply models_exploit in H1. apply models_exploit in H. apply models_exploit in H2.
      simpl in H, H1, H2. fwd.
      unfold pl_data in *.
      rewrite H9 in H4.
      rewrite H in H3.
      
      (* need to rework absFloatPlus' so that it uses rounding... *)
      unfold absFloatConst, absFloatPlus', Rinf_plus in H4.
      simpl in H4.


      Lemma asReal_in_B2Rinf :
        forall f r, M.asReal_in f r ->
               exists ri, eq (B2Rinf f) (Some ri).
      Proof.
        intros. unfold M.asReal_in in H. consider f; simpl; intros; try congruence.
        { eexists. inversion H0; subst. reflexivity. }
        { consider b; intros; eexists; reflexivity. }
        { eexists; reflexivity. }
      Qed.
      apply asReal_in_B2Rinf in H11.
      apply asReal_in_B2Rinf in H12.
      fwd. inversion H2; subst; clear H2.
      rewrite H12 in H4.
      rewrite H11 in H4.
      simpl in H4.
      SearchAbout ((_ || _)%bool).

      unfold intervalD in H3.
      consider (absFloatConst x4); intros.
      simpl in H3.
      destruct H3.
      {
        Lemma asReal_out_nonnan :
          forall f r, asReal_out f r ->
                 Fappli_IEEE.is_nan _ _ f = false.
        Proof.
          intros. consider f; intros; simpl; try reflexivity.
          unfold asReal_out in H0.
          simpl in H0.
          congruence.
        Qed.

        idtac.
        fwd.
        apply asReal_out_nonnan in H14; congruence.
      }
      {
        Lemma asReal_out_B2Rinf :
          forall f r, asReal_out f r ->
                 B2Rinf f = Some (RinfR r).
        Proof.
          intros.
          consider f; simpl; intros; unfold asReal_out in *; simpl in *;
          try solve [congruence];
          try solve [inversion H0; subst; auto].
        Qed.

        idtac.
        rewrite (asReal_out_B2Rinf _ _ H14) in H3. fwd.
        assert (lb = x8) by admit.
        assert (ub = x8) by admit.
        subst.
        assert (x8 = RinfR (Stream.hd (Stream.tl tr) "a")) by admit.
        rewrite H16 in H4.
        unfold definitely_lt in H4. simpl in H4.
        rewrite Bool.orb_false_r in H4.
        fwd.
        do_F2Rs.
        show_values.
        subst.
        unfold MyVelocityShimParams.ub, MyVelocityShimParams.d.
        

        consider x7; simpl; intros.
        {
          
          
          consider (Rlt_dec (Stream.hd (Stream.tl tr) "a" + r) (-floatMax)); intros.
          z3 solve.

                                              
        
        inversion H4.

        consider (Rlt_dec (Stream.hd (Stream.tl tr) "a" + r) (- floatMax)); intros.
        
        { unfold maybe_lt in *. simpl in *.
           consider (Rlt_dec (r0 + r) (-floatMax)); intros.
          {
            show_values.
            do_F2Rs.
            unfold MyVelocityShimParams.d, MyVelocityShimParams.ub in *.
            subst.
            assert (lb = RinfR (Stream.hd (Stream.tl tr) "a")) by admit.
            assert (ub = RinfR (Stream.hd (Stream.tl tr) "a")) by admit.
            subst.
            assert (B2Rinf x4 = Some (RinfR (Stream.hd (Stream.tl tr) "a"))) by admit.
            rewrite H4 in H16.
            inversion H16; subst.
            z3 solve.

      consider (Rlt_dec (r + r0) (-floatMax)); intros.
      do_F2Rs.
      

      inversion H3; subst.

      
      Lemma Rinf_leR :
        forall r1 r2,
          Rinf_le (RinfR r1) (RinfR r2) <-> (r1 <= r2)%R.
      Proof.
        split.
        { intros. inversion H; inversion H0; lra. }
        { intros. unfold Rinf_le.
          destruct H; [left|right]; constructor; lra. }
      Qed.
      
      apply Rinf_leR in H11.
      apply Rinf_leR in H12.
      lra. }
    { fwd.
      unfold fstate_lookup_nan in *.
      simpl in H4. simpl in H3.
      apply models_exploit in H1. apply models_exploit in H. simpl in H1, H. fwd.

      apply models_
      simpl

      
      
      unfold maybe_lt, absFloatPlus', absFloatConst in H12.
      consider (fm_lookup (fm_unset x0) "a"); intros.
      Focus 2.
      { fwd.
        
        unfold M.asReal_out, asReal_out in H8.
        show_values.
      unfold MyVelocityShimParams.ub. unfold MyVelocityShimParams.d.
      fwd.
      inversion H10.
      z3 solve.

    
    destruct H6; [fwd; congruence|].
    unfold fstate_lookup_nan in H6.
    rewrite H in H6.
    unfold M.asReal_out in H13.
    consider x3; simpl in *; intros.
    inversion H13; subst.
    lra.
    subst.
    unfold intervalD in H4.
    congruence.
    contradiction.
    inversion H13; subst. fwd.
    split; auto.
    right.
    inversion H14; subst.
    { inversion H15; subst. lra. }
    { inversion H15; subst. lra. }
    
    
    
    unfold B2Rinf x3.
    Print asReal_in.
    unfold M.asReal_in in *.
    { fwd. congruence. }
    {
    destruct H.
    { unfold fstate_get_rval.
      rewrite H1.
      rewrite H2.
      unfold M.asReal_in in *.
      consider x0; consider x1; simpl; intros; try lra.
      subst.

      intros.
      simpl.
    setoid_rewrite H1 in H.
    rewrite H2 in H.
    consider (fm_lookup x "a"); intros.
    Focus 2. fwd.
    Print embed_ex_seal.
Admitted.
(*
    apply and_assoc_left.
    SearchAbout land.
    apply landAdj. apply land_curry1.

    (*apply landAdj.*)
    apply land_curry1. apply landAdj. apply land_curry1.
    
    apply lentail_cut2.

    { Opaque bound_fexpr.
      breakAbstraction.
      Transparent bound_fexpr.
      intros. forward_reason.

      generalize (models_exploit _ _ _ _ H); intros Hme; simpl in Hme; fwd.

      cbv beta zeta iota delta
          [lift2 float_plus float_mult float_one fzero Fappli_IEEE.Bopp Fappli_IEEE.Bplus Fappli_IEEE.Bmult custom_prec custom_emax prec emax custom_nan].

      unfold M.asReal_in in *.
      split.
      {
        simpl.
        (* 9 - (a + v) < 0 -> 9 < a + v *)
        intros.
        simpl.
        left.
        split; auto.
        intros.
        unfold fstate_get_rval.
        simpl.
        rewrite H7. rewrite H12.
        rewrite H9.

        left.
        lra.
      }
      split.
      { (* 9 - (a + v) >= 0 -> 9 >= a + v *)
        intros.
        left.
        simpl.

        assert (isVarValid "a" x) by (eapply varIsValid; eauto).
        split; eauto.
        intros.
        unfold fstate_get_rval.
        simpl.
        rewrite H13.
        rewrite H7.
        rewrite H9.

        unfold maybe_ge0 in H11.
        simpl in H11.
        fwd.
        do_F2Rs.

        clear H12.

        unfold fstate_lookup_force in *.

        rewrite H6 in *.
        rewrite H7 in *.

        unfold float_bounded in *.

        repeat match goal with
               | H : F2OR ?X = Some ?Y |- _ =>
                 apply F2OR_FloatToR' in H
               end.
        show_value floatMin.
        show_value floatMax.
        show_value error.
        unfold pred1 in *.

        show_z3_hints.

        z3 solve!.
      }
      {
        simpl.

        assert (isVarValid "a" x).
        { eapply varIsValid; eauto. }

        assert (isVarValid "v" x).
        { eapply varIsValid; eauto. }

        left.
        split; auto.

        unfold float_bounded, fstate_lookup_force in *.
        repeat match goal with
               | H : fstate_lookup _ _ = Some _ |- _ =>
                 try (rewrite H in * ); clear H
               end.

        unfold pred1 in *.
        do_F2Rs.
        weaken_F2ORs.
        show_z3_hints.
        show_values. 

        z3 solve!. }
      }
      { breakAbstraction.
        intros.
        unfold fstate_get_rval in *.
        fwd.
        consider (fstate_lookup x0 "a"); intros; try contradiction.
        consider (F2OR f); intros; try contradiction.
        consider (fstate_lookup x0 "v"); intros; try contradiction.
        consider (F2OR f0); intros; try contradiction.
        unfold models in *.
        generalize (H "a"). 
        clear H.
        unfold velshim_vs_out in *.
        simpl in *.  intros.
        destruct H.
        left; auto.
        fwd.
        destruct H4; [left | right].
        { unfold M.asReal_out in *.
          rewrite <- fstate_lookup_fm_lookup in H. assert (f = x1) by congruence.
          subst.
          rewrite H1 in H5; inversion H5.
          reflexivity. }
        { unfold M.asReal_out in *.
          rewrite <- fstate_lookup_fm_lookup in H.
          assert (f = x1) by congruence; subst.
          assert (r = (Stream.hd (Stream.tl tr) "a")) by congruence; subst.
          z3 solve.
          rewrite H
        fwd.
        rewrite <- fstate_lookup_fm_lookup in H5, H6.
        unfold asReal in *.

        rewrite H6 in H0. inversion H0.
        rewrite H5 in H2. inversion H2. } }
                      Qed.

*)
                      
                      Definition MyNext := Sys (embed_ex_seal velshim_vs_in velshim_vs_out velshim2) w 1.

                      (* need to prove versions of these *)
                      Theorem SysNeverStuck_Next
                        : |-- SysNeverStuck 1 IndInv MyNext.
                      Proof.
                        eapply SysNeverStuck_Sys'; [ refine _ | lra | | ].
                        { admit. (*enable_ex_st.
                          pose proof d_gt_0.
                          do 2 eexists; exists d; solve_linear. *) }
                        { admit. (** Provable, but we won't worry about it *) }
                      Admitted.


                      Instance Proper_sys_lentails :
                        Proper (lentails ==> lentails ==> eq ==> lentails) Sys.
                      Proof.
                        morphism_intro.
                        unfold Sys. subst.
                        unfold Discr.
                        rewrite H; clear H.
                        rewrite H0.
                        reflexivity.
                      Qed.

                      Theorem TimedPreserves_Refine :
                        forall IndInv MyNext MyNext' d,
                          IndInv |-- MyNext' -->> MyNext ->
                          TimedPreserves d IndInv MyNext
                                         |-- TimedPreserves d IndInv MyNext'.
                      Proof.
                        intros.
                        unfold TimedPreserves, Inductively.Preserves.
                        charge_intro.
                        charge_tauto.
                      Qed.
                      
                      Theorem TimedPreserves_MyNext
                        : |-- TimedPreserves 1 IndInv MyNext.
                      Proof.
                        rewrite <- TimedPreserves_Refine.
                        eapply MyVelocityShim.TimedPreserves_Next.
                        unfold Next.
                        rewrite <- fwp_velshim2_full.
                        
                        unfold MyNext.

                        (* we need to take a different var for a_proposed *)
                        (* change input-rounding to round-with-truncate
                           go to -FloatMax or FloatMax for Inf/NaN *)

                        Print pred1.
                        Lemma Sys_imp_env :
                          forall P Q X,
                            (P |-- Q -->> X) ->
                            forall y z,
                              (P |-- Sys Q y z) ->
                              (P |-- Sys X y z).
                        Proof.
                          intros.
                          unfold Sys, Discr in *.
                          apply landAdj in H.
                          rewrite <- H.
                          rewrite land_dup at 1.
                          rewrite H0 at 1.
                          charge_cases; charge_tauto.
                        Qed.

                        idtac.
                        charge_intros.
                        eapply Sys_imp_env.
                        2: charge_assumption.
                        charge_intro.
                        rewrite <- landA.
                        charge_split; [|charge_assumption].
                        charge_assert IndInv; [charge_assumption|].
                        charge_clear.

                        breakAbstraction.
                        intros.
                        split.
                        {

                        
                        unfold IndInv.
                        unfold MyVelocityShimParams.d, MyVelocityShimParams.ub in *.

                        unfold Sys, Discr.
                        charge_intros.
                        charge_split.
                        { charge_assumption. }
                        { charge_cases.
                          { charge_left.
                            repeat charge_split.
                            { unfold Lib.Unchanged. charge_assumption. }
                            { charge_tauto. }
                            { unfold preVarPred.
                              (* need to change models so that we round the pre state ?*)
                              (* need separate input, output variables *)
                             
                        
                        idtac.
                        rewrite land_comm.

                        2: eapply Proper_TimedPreserves_lentails.
                        unfold MyNext.
                        eapply Preserves_Sys.
                        { refine _. }
                        { charge_split; fold next.
                          - eapply diff_ind with (Hyps:=ltrue).
                            + tlaIntuition.
                            + tlaIntuition.
                            + unfold World. tlaAssume.
                            + tlaIntuition.
                            + tlaAssume.
                            + tlaIntuition.
                            + charge_tauto.
                            + simpl deriv_formula. restoreAbstraction.
                              charge_intros.
                              unfold lift2, mkEvolution, w.
                              repeat charge_split; charge_intros;
                              try solve [ solve_linear
                                        | eapply zero_deriv with (x:="a");
                                          [ charge_tauto | tlaIntuition |
                                            solve_linear ] ].
                              solve_nonlinear.
                          - solve_linear. }
                        { solve_nonlinear. }
                      Qed.


                      Theorem Spec_safe :
                        |-- (IndInv //\\ 0 <= "T" <= 1) //\\ []SysSystem (Sys (embed_ex velshim_vs velshim2) w 1) -->> []"v" <= 10.
                      Proof.
                        
                        SearchAbout Sys.


Print Velocity.
