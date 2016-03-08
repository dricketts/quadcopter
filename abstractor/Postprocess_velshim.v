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

Definition velshim : fcmd :=
  FIte (FMinus (FConst f10) (FPlus (FMult (FVar "a") (FConst float_one)) (FVar "v")))
       (FAsn "a" (FConst fzero))
       (FAsn "a" (FVar "a")).

Definition f9 := Eval lazy in (concretize_float (nat_to_float 9)).

Definition velshim2 : fcmd :=
  FIte (FMinus (FConst f9) (FPlus (FVar "a") (FVar "v")))
       (FAsn "a" (FConst fzero))
       (FAsn "a" (FVar "a")).

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

Require Import Coq.micromega.Psatz.


Definition pred1 (r : R) : Prop :=
  (-(100000*100000) < r < (100000*100000))%R.

Require Import Abstractor.Bound.
Require Import Coq.micromega.Psatz.

(* proof is 198 lines *)
Theorem fwp_velshim2_full
: preVarPred pred1 "a" //\\ preVarPred pred1 "v" //\\
  (embed_ex velshim_vs_in velshim_vs_out velshim2)
  |-- (VarNextT "a" = 0 \\// (VarNextT "v") + ((VarNextT "a") * NatT 1) < NatT 10)%HP.
Proof.
  rewrite landC. rewrite landA. rewrite landC. rewrite landA.
  tlaRevert.
  erewrite -> Hoare__embed_rw.
  {
    eapply lforallL.
    instantiate (1 := (fstate_get_rval "a" (fun a =>
                                              fstate_get_rval "v" (fun v _ => (a = 0 \/ v + a < 10)%R)))).
    eapply lequiv_rewrite_left.

    {
      cbn beta zeta iota delta -[bound_fexpr].
      crunch_embeds.
    }

    apply lexistsL. intros.
    apply land_comm_left.

    apply landAdj.
    apply land_curry1.

    apply lentail_cut2.

    { Opaque bound_fexpr.
      breakAbstraction.
      Transparent bound_fexpr.
      intros. forward_reason.

      generalize (models_Forall _ _ _ H); intros.
      
      unfold velshim_vs_in in H6. inversion H6 as [| Hk2 Hk3 Hnew Hrem]; clear H6.
      inversion Hrem; clear Hrem. subst. fwd.

      fwd.
      cbv beta zeta iota delta
          [lift2 float_plus float_mult float_one fzero Fappli_IEEE.Bopp Fappli_IEEE.Bplus Fappli_IEEE.Bmult custom_prec custom_emax prec emax custom_nan].

      split.
      {
        (* 9 - (a + v) < 0 -> 9 < a + v *)
        intros.
        simpl.
        left.
        split; auto.
        intros.
        unfold fstate_get_rval.
        simpl.
        rewrite H6. rewrite H12.
        rewrite H8.
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
        rewrite H6.
        rewrite H8.

        unfold maybe_ge0 in H10.
        simpl in H10.
        do_F2Rs.

        unfold isVarValid in *.

        generalize fstate_lookup_fstate_lookup_force; intros Hfls.
        unfold asReal in Hfls.
        unfold fstate_lookup_force in *.

        repeat match goal with
               | H : fstate_lookup _ _ = Some _ |- _ =>
                 try (rewrite H in *);
                 try erewrite (Hfls _ _ _ _ H) in H10 by eassumption;
                 try erewrite (Hfls _ _ _ _ H) in H12 by eassumption;
                 try erewrite (Hfls _ _ _ _ H) in H14 by eassumption; clear H
               end.


        unfold float_bounded, asReal in *.

        repeat match goal with
               | H : F2OR ?X = Some ?Y |- _ =>
                 apply F2OR_FloatToR' in H
               end.
        show_value floatMin.
        show_value floatMax.
        show_value error.
        unfold pred1 in *.

        simpl in H8.

        repeat match goal with
               | H : context [roundUp ?r] |- _ =>
                 generalize (roundUp_fact r);
                   assert (dummy r (roundUp r)) by exact I;
                   generalize dependent (roundUp r);
                   intros
               | H : context [roundDown ?r] |- _ =>
                 generalize (roundDown_fact r);
                   assert (dummy r (roundDown r)) by exact I;
                   generalize dependent (roundDown r);
                   intros
               end.

        unfold float_bounded, fstate_lookup_force in *.
        fwd.

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


        (*generalize fstate_lookup_fstate_lookup_force; intros Hfls.
        unfold asReal in Hfls.

        repeat match goal with
               | H : fstate_lookup _ _ = Some _ |- _ =>
                 try (rewrite H in * ); try repeat erewrite (Hfls _ _ _ _ H) by eassumption; clear H
                      end.
*)
        unfold float_bounded, fstate_lookup_force in *.

        unfold asReal in *.

        weaken_F2ORs.
        do_F2Rs.

        repeat match goal with
               | H : fstate_lookup _ _ = Some _ |- _ =>
                 try (rewrite H in * ); clear H
               end.
        
        show_z3_hints.
        show_value floatMin.
        show_value floatMax.
        show_value error.
        unfold pred1 in *.


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
        Locate embed_ex.
        generalize (H "a"); generalize (H "v"); intros.
        clear H.
        unfold velshim_vs_out in *.
        simpl in *.
        destruct H5; destruct H6.
        destruct H6; auto.
        assert ( ~ ("a" = "v" \/ False)).
        { intro Hcon. destruct Hcon; [congruence | contradiction]. }
        fwd.
        rewrite <- fstate_lookup_fm_lookup in H5, H6.
        unfold asReal in *.
(*        rewrite H5 in H2. inversion H2.*)
        rewrite H6 in H0. inversion H0.
        rewrite H5 in H2. inversion H2.
        subst.
        rewrite H1 in H9. inversion H9.
        show_z3_hints.
        z3 solve!. } }
                      Qed.


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
                      
                      Check (Sys (embed_ex velshim_vs velshim2) w 1).
                      Print SysSystem.

                      Definition MyNext := Sys (embed_ex velshim_vs velshim2 //\\ Logic.Lib.Unchanged ["v"]) w 1.

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

                        Lemma Ctrl_connect_velshim :
                          Logic.Lib.Unchanged ["v"] //\\
                          (("a") ! = 0 \\// ("v") ! + ("a") ! * NatT 1 < NatT 10) |-- Ctrl //\\ Logic.Lib.Unchanged ["v"].
                        Proof.
                          breakAbstraction.
                          intros.
                          unfold MyVelocityShimParams.ub, MyVelocityShimParams.d.
                          lra.
                        Qed.

                        rewrite <- Ctrl_connect_velshim.
                        rewrite <- fwp_velshim2_full.
                        unfold MyNext.
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
