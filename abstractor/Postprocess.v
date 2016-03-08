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
Require Import ExtLib.Tactics.
Locate RelDec.
Import ExtLib.Core.RelDec.
Require Import Coq.Reals.Rbase.
Require Import SMT.Tactic.
Require Import Abstractor.Embed.
Require Import Abstractor.FloatEmbed.
Require Import Logic.Automation.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Tactics.
Require Import Abstractor.Automation.

Lemma Z3Test : forall (a : R), (a + 1 = 3)%R%type -> ((a + 2 = 3)%R /\ ((1+1)%R=2%R)%R)%type.
Proof.
  intros.
  (* z3 solve. *)
  Abort.

(* Implementation of postprocessing automation for the Abstractor,
   using the Z3 plugin to simplify the terms produced b ythe abstractor *)

(* test case: proportional controller *)

(* c is constant and goal is 0 *)
Require Import Abstractor.FloatLang.

Definition proportional_controller : fcmd :=
  FAsn "a" (FMinus (FConst fzero) (FVar "x")).

Definition proportional_controller_ivs : list (Var * Var) :=
  [("a", "a"); ("x", "x")].

(* "Pushing" Embed through connectives *)
(*Fact fwp_simple : |-- "x" > 0 //\\ [](oembed_fcmd simple_prog_ivs simple_prog_ivs simple_prog) -->> []("x" > 0).*)
Locate embed_ex.
Import Embedding.

Definition simple_prog_ivs : list (Var) :=
  [("x")].

Require Import Abstractor.FloatOps.


Definition float_one := Eval compute in (concretize_float (FloatOps.nat_to_float 1)).

Definition simpler_prog : fcmd :=
  FAsn "x" (FConst float_one).

Fact fwp_simpler : |-- "x" > 0 //\\ [](embed_ex simple_prog_ivs simpler_prog) -->> []("x" > 0).
Proof.
  erewrite -> Hoare__embed_rw.
  charge_intros.
  eapply discr_indX.
  { red; intuition. }
  { charge_assumption. }
  { charge_assumption. }
  {
    (* rhs *)
    rewrite landforallDL. eapply lforallL.
    instantiate (1 := (fun fst => exists f, fstate_lookup fst "x" = Some f /\ exists r, F2OR f = Some r /\ (r > 0)%R)).
    tlaRevert.
    simpl fpig_vcgen.
    eapply lequiv_rewrite_left.

    {
      crunch_embeds.
    }


    apply lexistsL.
    intro.
    
    apply land_comm_left.
    apply landAdj.
    apply limpl_comm1.
    apply lentail_cut2.

    Require Import Coq.micromega.Psatz.
    {
      idtac.
      breakAbstraction.
      intros.
      left.
      split; auto. 
      intros.
      (*generalize fstate_lookup_update_match; intro Hflum.
      symmetry in Hflum.
      rewrite Hflum.*)
      exists x0.
      split; try reflexivity.
      exists x1.
      split; auto.
      unfold F2OR, FloatToR in H0.
      destruct x0; simpl in *; try congruence.
      - lazy in H0. lazy in H1. (* contradiction *) psatz R.
      - lazy in H1. psatz R.
    }
    {
      breakAbstraction.
      intros.
      fwd.
      unfold models in H.
      specialize (H "x"). fwd. unfold simple_prog_ivs in H. simpl in H.
      destruct H; auto. fwd.
      rewrite FloatEmbed.fstate_lookup_fm_lookup in H1.
      unfold Var, M.pl_data in *.
      rewrite H1 in H. inversion H; subst.
      unfold M.asReal in *. rewrite H2 in H5. inversion H5. lra.
    }
  }
Qed.

Lemma F2OR_FloatToR :
  forall (f : float) (r r' : R),
    F2OR f = Some r ->
    FloatToR f = r' ->
    r = r'.
Proof.
  intros.
  unfold F2OR, FloatToR in *.
  destruct f; try congruence.
Qed.

(* generalized version of Enabled_action, needed to prove
   enabledness goals *)
(* Used to get pre-state variable values *)
(*
Lemma inject_var :
  forall (s : Var) G P,
    (G |-- Forall x : R, (RealT x = VarNowT s)%HP -->> P) ->
    (G |-- P).
Proof.
  tlaIntuition.
  eapply H. eassumption.
  reflexivity.
Qed.
 *)
  

Ltac show_value val :=
  let x := eval compute in val in
      assert (val = x) by reflexivity.

(*
Ltac try_it HH :=
  unfold premise;
  show_value error; show_value floatMin; show_value floatMax;
  intros;
  repeat match goal with
         | H: context[Fappli_IEEE.B2R ?x1 ?x2 ?x3] |- _ => 
           let X2 := eval lazy in (Fappli_IEEE.B2R x1 x2 x3) in change (Fappli_IEEE.B2R x1 x2 x3) with X2 in H
         end;
  repeat match goal with
         | H : context[Fcore_Raux.bpow ?x1 ?x2] |- _ =>
           let X2 := eval compute in (Fcore_Raux.bpow x1 x2) in
               change (Fcore_Raux.bpow x1 x2) with X2 in H
         end;
  repeat match type of HH with
         | context[nat_to_float ?x1]  =>
           idtac "1" x1 ; 
             let X2 := eval lazy in (nat_to_float x1) in
                 idtac "2" ;
               change (nat_to_float x1) with X2 in HH
         end;
  repeat match goal with
         | H : _ = _ |- _ => rewrite H in *
         end;
  try (z3 solve; admit).
*)


(*
Fact fwp_velshim_full : preVarIsFloat "a" //\\ preVarIsFloat "v" //\\ 
                                      (embed_ex velshim_vs velshim)
                                                   (*(Enabled (embed_ex velshim_ivs velshim_ivs velshim) -->> lfalse))*)
                                      |-- (VarNextT "a" = 0 \\// "v" + ((VarNextT "a") * NatT 1) < NatT 10 )%HP.
 *)


(* use firstN, skipN *)
Lemma hide_tail :
  forall {T : Type} (ls : list T),
    ls = match ls with
         | h :: t => h :: tl ls
         | nil => nil
         end.
Proof.
  induction ls; reflexivity.
Qed.

Definition bound_fexpr2 := bound_fexpr.
Opaque bound_fexpr2.

Transparent ILInsts.ILFun_Ops.
(* Now we are going to do the height shim *)

Definition fhalf : float.
                     refine (Fappli_IEEE.B754_finite 24 128 false 8388608 (-24) _).
                     unfold Fappli_IEEE.bounded, Fappli_IEEE.canonic_mantissa.
                     simpl. reflexivity.
Defined.

Definition fminus_half : float.
                          refine (Fappli_IEEE.B754_finite 24 128 true 8388608 (-24) _).
                          reflexivity.
Defined.

Definition f9 := Eval lazy in (concretize_float (nat_to_float 9)).

Definition posshim_ub := f9.
Definition fminus1 : float.
                       refine  (Fappli_IEEE.B754_finite 24 128 true 8388608 (-23) _).
                       reflexivity.
Defined.

Definition minus2amin := float_one.

Definition amin := fminus_half.

Definition fmax_with_zero (v : Var) (x1 : fexpr) : fcmd :=
  FIte x1 (FAsn v (FConst fzero)) (FAsn v x1).

(*
if (y+v*d+(1/2)*Max(A,0)*d^2+Max(v+Max(A,0)*d,0)^2/(-2*amin) <= ub)
then a := A
else a := amin

where d = 1
where (-1 / (2 * amin)) = 1; i.e., amin = -1/2
 *)
Print fexpr.

Definition posshim_lhs : fexpr :=
  FPlus (FVar "y") (FPlus (FVar "v")
                          (FPlus (FMult (FConst fhalf) (FVar "maxa0"))
                                 ((FMult (FVar "max2") (FVar "max2"))))).                                        
Definition posshim : fcmd :=
  FSeq (FAsn "maxa0" (FMax (FVar "a") (FConst fzero)))
       (FSeq (FAsn "max2" (FMax (FPlus (FVar "v") (FVar "maxa0")) (FConst fzero)))
                (FIte (FMinus posshim_lhs (FConst posshim_ub))
                      (FAsn "a" (FVar "a"))
                      (FAsn "a" (FConst amin)))).

Definition posshim_vs :=
  ["y"; "v"; "a"; "max2"; "maxa0"].


(*Definition posshim_lhs' : fexpr :=
  FPlus (FVar "y") (FPlus (FVar "v")
                          (FPlus (FMult (FConst fhalf) (* max a 0 *))
                                 ((FMult (* max 2 *) (* max 2 *)

Definition posshim' : fexpr :=
  FIte (FMinus posshim_lhs (FConst posshim_ub)
*)


Definition preVarPred (pred : R -> Prop) (v : Var) : Formula :=
  Syntax.Exists float
                (fun f : float =>
                   Syntax.Embed (fun st st' =>
                                   (eq (F2OR f) (Some (st v)))%R /\ pred (st v))).

Definition pred1 (r : R) : Prop :=
  (-(100000*100000) < r < (100000*100000))%R.


Require Import ClassicalFacts.

Axiom pe_ax : prop_extensionality.

Lemma F2OR_quant_rew :
  forall (P : _ -> Prop),
  (forall a b, F2OR a = Some b -> P (F2OR a)) =
  (forall a b, F2OR a = Some b -> P (Some b)).
Proof.
  intros.
  apply pe_ax.
  split.
  - intros.
    generalize (H _ _ H0). intros.
    rewrite H0 in H1.
    assumption. 
  - intros.
    rewrite H0.
    specialize (H _ _ H0). apply H. 
Qed.

Definition posshim_tla : Formula :=
  ("a"! = (-1/2)%R) \\//
  ("y"! + "v"! + (1/2)*(MaxT ("a"!) 0) + (MaxT ("v"! + (MaxT ("a"!) 0)) 0) <= 10).

Require Import Rbasic_fun.

Require Import Coq.Logic.FunctionalExtensionality.

Fixpoint fstate_lookup_force' (fst : fstate) (v : Var) : R :=
  match fst with
  | nil => 0%R
  | cons (v', b) t =>
    if v ?[eq] v' then FloatToR b else fstate_lookup_force' t v
  end.

Lemma fstate_lookup_force_eq :
  fstate_lookup_force = fstate_lookup_force'.
Proof.
  apply functional_extensionality.
  induction x.
  - reflexivity.
  - unfold fstate_lookup_force. simpl. destruct a.
    apply functional_extensionality.
    intros.
    consider (x0 ?[eq] v); intros.
    + reflexivity.
    + rewrite <- IHx. reflexivity. 
Qed.

Lemma F2OR_is_finite :
  forall f r,
    F2OR f = Some r -> Fappli_IEEE.is_finite f = true.
Proof.
  intros; consider f; intros; simpl in *; congruence.
Qed.

(* for playing Ltac tricks *)
Definition isVarValid' := isVarValid.
Definition roundUp' := Bound.roundUp.
Definition roundDown' := Bound.roundDown.
Definition Rmax' := Rmax.


Ltac proveVarValid v vs fs Hmodels :=
  assert (isVarValid v fs); [
    specialize (Hmodels v);
    destruct (in_dec string_dec v vs) eqn:Hindec; simpl in Hindec; [clear Hindec | solve[inversion Hindec]];
    destruct Hmodels as [H Hdead]; destruct H; [assumption|]; destruct H as [H H'];
    unfold isVarValid; try (rewrite <- FloatEmbed.fstate_lookup_fm_lookup in Hmodels);
    eexists; split; [|eapply F2OR_is_finite]; eassumption
   |].

Lemma isVarValid_fstate_set :
  forall fst v,
    isVarValid v fst ->
    forall v' f,
      Fappli_IEEE.is_finite f = true ->
      isVarValid v (fstate_set fst v' f).
Proof.
  unfold isVarValid; simpl; intros.
  fwd.
  consider (v ?[eq] v'); intros; subst;
  eexists; split; eauto.
Qed.

Fixpoint AllOf
         (Ps : list Prop) : Prop :=
  match Ps with
  | nil => True
  (*        | P :: nil => P*)
  | P :: Ps' => P /\ AllOf Ps'
  end.

(* used to get more useful information out of models *)
Lemma models_exploit :
  forall vs fs ss,
    models vs fs ss ->
    AllOf (map (fun v => (exists d : float, fstate_lookup fs v = Some d /\ F2OR d = Some (ss v))) vs).
Proof.
  intros.
  unfold models in H.
  assert (forall s : string, In s vs -> exists d : M.pl_data, fm_lookup fs s = Some d /\ M.asReal d (ss s)).
  { intros. specialize (H s). fwd. eexists; split; eauto. }
  clear H.
  revert H0; revert ss; revert fs.
  induction vs; simpl; intros; auto.
  split.
  { specialize (H0 a). destruct H0; [left; auto|].
    fwd.
    eexists; split; try eassumption.
    rewrite FloatEmbed.fstate_lookup_fm_lookup; eassumption. }
  { eapply IHvs. intros.
    specialize (H0 s); destruct H0; [right; auto|].
    fwd.
    eexists; split; eassumption. }
Qed.

(* another z3 hint *)
Lemma Rmax_z3_fact :
  forall r1 r2,
    (Rmax r1 r2 = r2 /\ r1 < r2)%R \/
    (Rmax r1 r2 = r1 /\ r1 >= r2)%R.
Proof.
  intros.
  consider (Rlt_dec r1 r2); intros.
  { left. split; auto.
    apply Rmax_right. lra. }
  { right. split.
    { apply Rmax_left. lra. }
    { lra. } }
Qed.


Ltac show_roundDown_z3_hint r :=
  let H := fresh "H" in
  generalize (Bound.roundDown_fact r); intro H;
  generalize dependent (Bound.roundDown r); intros.

Ltac show_roundUp_z3_hint r :=
  let H := fresh "H" in
  generalize (Bound.roundUp_fact r); intro H;
  generalize dependent (Bound.roundUp r); intros.

Ltac show_Rmax_z3_hint r1 r2 :=
  let H := fresh "H" in
  generalize (Rmax_z3_fact r1 r2); intro H;
  generalize dependent (Rmax r1 r2); intros.

Ltac show_z3_hints :=
  repeat match goal with
         | H : context[Bound.roundDown ?r] |- _ =>
           show_roundDown_z3_hint r
         | |- context[Bound.roundDown ?r] =>
           show_roundDown_z3_hint r
         | H : context[Bound.roundUp ?r] |- _ =>
           show_roundUp_z3_hint r
         | |- context[Bound.roundUp ?r] =>
           show_roundUp_z3_hint r
         | H : context[Rmax ?r1 ?r2] |- _ =>
           show_Rmax_z3_hint r1 r2
         | |- context[Rmax ?r1 ?r2] =>
           show_Rmax_z3_hint r1 r2
         end.

Ltac show_values :=
  show_value Bound.floatMax;
  show_value Bound.floatMin;
  show_value Bound.error.

Ltac weaken_F2ORs :=
  repeat match goal with
         | H : F2OR ?f = Some ?r |- _ =>
           apply F2OR_weaken in H
         end.


Theorem fwp_posshim :
  preVarPred pred1 "y" //\\
  preVarPred pred1 "v" //\\
  preVarPred pred1 "a" //\\
  embed_ex posshim_vs posshim
  |-- posshim_tla.
Proof.
  assert (embed_ex posshim_vs posshim |--
                   (preVarPred pred1 "y" //\\
                               preVarPred pred1 "v" //\\
                               preVarPred pred1 "a") -->> posshim_tla).
  2 : rewrite H; tlaIntuition.

  erewrite -> Hoare__embed_rw.
  {
    eapply lforallL.
    Show Existentials.

    instantiate (1 := (fstate_get_rval "y" (fun y =>
                      (fstate_get_rval "v" (fun v =>
                      (fstate_get_rval "a" (fun a _ => (eq a (-1/2))%R \/
                                                     (y + v + (1/2)*(Rmax a 0) + (Rmax (v + (Rmax a 0)) 0)*(Rmax (v + (Rmax a 0)) 0) <= 10)%R))))))).
    Check lequiv_rewrite_left.
    cbv beta iota zeta delta [fpig_vcgen posshim fexprD fexpr_check].

    (* for dealing with variable-validity *)
    cbn beta iota zeta delta -[bound_fexpr land lor limpl lentails].
    eapply lequiv_rewrite_left.
    {
      crunch_embeds.
    }

    apply lexistsL. intros.
    apply land_comm_left.
    apply landAdj.
    apply land_curry1.
    
    apply lentail_cut2.

    {
      Opaque bound_fexpr.
      breakAbstraction.
      Transparent bound_fexpr.
      
      intros. forward_reason.
      simpl.

      Require Import Coq.Lists.List.
      left.
      generalize (models_exploit _ _ _ H); intro Hme.
      simpl in Hme. fwd.

      idtac.

      split; eauto.
      { proveVarValid "a" posshim_vs x H.
        split; auto.
        split; auto.
        lra. }
      intros.
      left.
      split; eauto.
      { split.
        { split; eauto.
          proveVarValid "v" posshim_vs x H.
          eapply isVarValid_fstate_set; [eassumption|].
          eapply F2OR_is_finite; eassumption.
          split.
          { eapply isVarValid_fstate_set.
            proveVarValid "maxa0" posshim_vs x H. assumption.
            eapply F2OR_is_finite; eassumption. }
          { unfold fstate_lookup_force in *.
            simpl.

            rewrite H8 in H18.
            rewrite H7.
            unfold Bound.float_bounded.


            show_z3_hints.
            show_values.
            unfold pred1 in *.
            weaken_F2ORs.
            z3 solve!. } }
        { split; try reflexivity.
          unfold fstate_lookup_force.
          simpl.

          Ltac do_lookup_rewrites :=
            unfold fstate_lookup_force in *; simpl;
            repeat match goal with
                   | H : context[fstate_lookup ?fs ?v = Some ?f] |- _ =>
                     match goal with
                     | H2 : context[match fstate_lookup fs v with | _ => _ end] |- _ =>
                       rewrite H in H2
                     | |- context[match fstate_lookup fs v with | _ => _ end] =>
                       rewrite H
                     end
                   end.
          do_lookup_rewrites.
          show_z3_hints.
          show_values.
          z3 solve!. } }
      { intros.
        split.
        { left.
          split.
          eapply isVarValid_fstate_set. eapply isVarValid_fstate_set.
          proveVarValid "a" posshim_vs x H. assumption.
          eapply F2OR_is_finite. eapply H17.
          eapply F2OR_is_finite. eassumption.
          intros.
          unfold maybe_lt0 in H21.
          simpl in H21.

          unfold fstate_get_rval in *.
          unfold fstate_lookup_force in *.
          cbv delta [Fcore_defs.F2R] in H21.
          simpl in *.
          do_lookup_rewrites.

          Ltac do_F2OR_rewrites :=
            unfold fstate_lookup_force in *; simpl;
            repeat match goal with
                   | H : context[F2OR ?f = Some ?r] |- _ =>
                     match goal with
                     | H2 : context[match F2OR f with | _ => _ end] |- _ =>
                       rewrite H in H2
                     | |- context[match F2OR f with | _ => _ end] =>
                       rewrite H
                     end
                   end.

          do_F2OR_rewrites.

        show_values.
        weaken_F2ORs.
        
(*
        repeat match goal with
               | H : context[Fcore_defs.F2R ?f] |- _ =>
                 cbv beta zeta iota delta [Fcore_defs.F2R Fcore_Raux.Z2R Fcore_Raux.bpow Fcore_Zaux.radix2
                                                          Fcore_defs.Fexp Z.pow_pos Fcore_Zaux.radix_val Fcore_defs.Fnum
                                          Pos.iter Fcore_Raux.P2R] in H
               end.
*)
        simpl in *.
        unfold Bound.float_bounded, Bound.Rmax4 in *.

        Print Ltac show_z3_hints.

        (* given a term to look for hints in *)
        Ltac show_z3_hints' T tac :=
          let has_bad_subterm T' :=
              lazymatch T' with
              | context[Bound.roundUp ?r] => fail
              | context[Bound.roundDown ?r] => fail
              | context[Rmax ?r1 ?r2] => fail
              | _ => tac
              end
            in
              match T with
              | context[Bound.roundUp ?r] =>
                
          let rec show' T :=
              repeat match T with
                     | context[Bound.roundUp ?r] =>
                       show' r; generalize dependent (Bound.roundUp r)
                     | context[Bound.roundDown ?r] =>
                       idtac "point 2"; show' r; generalize dependent (Bound.roundDown r)
                     | context[Rmax ?r1 ?r2] =>
                       show' r1; show' r2;
                       generalize dependent (Rmax r1 r2)
                     | _ => fail 1                                
                     end
          in show' T.

        let H := type of H21 in
          show_z3_hints' H.


        
          match goal with
          | H:context [Bound.roundDown ?r] |- _ =>
            
            match r with
            | context[Bound.roundDown ?r'] =>
              idtac "hi"
            end
          end.
            show_roundDown_z3_hint r
          (*| |- context [Bound.roundDown ?r] => show_roundDown_z3_hint r
          | H:context [Bound.roundUp ?r] |- _ => show_roundUp_z3_hint r
          | |- context [Bound.roundUp ?r] => show_roundUp_z3_hint r
          | H:context [Rmax ?r1 ?r2] |- _ => show_Rmax_z3_hint r1 r2
          | |- context [Rmax ?r1 ?r2] => show_Rmax_z3_hint r1 r2*)
          end
        
        show_z3_hints.
        z3 solve.
            simpl; auto.
            unfold Bound.lb, Bound.ub in *.
            eapply fstate_lookup_fstate_lookup_force in H16; [|eauto].
            apply F2OR_weaken in H17.

            generalize (Fappli_IEEE.abs_B2R_lt_emax); intros.
            specialize (H28 _ _ x6).
            simpl in H28.
            apply Fcore_Raux.Rabs_lt_inv in H28.
            change (Fappli_IEEE.B2R custom_prec custom_emax x6) with (FloatToR x6) in H28.
            subst.
            assert (exists r, eq r (FloatToR x6 + FloatToR val))%R by (eexists;  reflexivity).
            destruct H14.
            rewrite <- H14 in H19, H20.
            rewrite <- H14.

            unfold pred1 in *.

            assert (eq (Stream.hd tr "y") x5)%R by admit.
            assert (eq (Stream.hd tr "v") x4)%R by admit.
            assert (eq (Stream.hd tr "a") x3)%R by admit.
            replace (roundDown' x7) with (x7 * (1 + Bound.error))%R by admit.

            (* somewhere we lost the fact that x6 + val is finte. *)
            (* need a better way of using H *)
            z3 solve.
            
            reflexivity.

            Print FloatEmbed.bound_fexpr.
            Lemma F2OR_bounded :
              forall f r,
                F2OR f = Some r ->
                (-Bound.floatMax < r < Bound.floatMax)%R.
            Proof.
              intros.
              consider f; simpl; intros; try congruence.
              { inversion H0; subst. unfold Bound.floatMax. simpl. lra. }
              { inversion H0; subst.
                SearchAbout Fappli_IEEE.bounded.
                unfold Fappli_IEEE.bounded in e0.
                unfold Fcore_defs.F2R, Fcore_defs.Fnum, Fcore_Raux.Z2R.
                unfold Fcore_Zaux.cond_Zopp. simpl.
                consider b; intros; subst.
                { SearchAbout Fcore_Raux.INR.
                SearchAbout Fcore_defs.F2R.
              
            apply F2OR_weaken in H17.
            Lemma F2
            z3 solve.
            destruct H24.
            
            assert (exists r1 : r, r1 = (FloatMoR )
            z3 solve!.
            generalize (Bound.roundUp_fact 
            Locate roundUp_fact.


              assert (exists r, eq (fstate_lookup fs v) (Some r) fs); [
                specialize (Hmodels v);
                destruct (in_dec string_dec v vs) eqn:Hindec; simpl in Hindec; [clear Hindec | solve[inversion Hindec]];
                destruct Hmodels as [H Hdead]; destruct H; [assumption|]; destruct H as [H H'];
                unfold isVarValid; try (rewrite <- FloatEmbed.fstate_lookup_fm_lookup in Hmodels);
                eexists; split; [|eapply F2OR_is_finite]; eassumption
               |].

            proveFstateLookup "v" posshim_vs x H.
            
            specialize (H "v").
            
          unfold is
          split; eauto.
        


        unfold isVarValid.
      


      Ltac proveVarsValid vs fs Hmodels :=
        match vs with
        | nil => idtac
        | cons ?v ?vs' =>
          proveVarValid v vs fs Hmodels;
            idtac v " done!";
            proveVarsValid vs' fs Hmodels
        | _ =>
          idtac "uh oh! vs is " vs;
          let vs_r := eval red in vs in
              proveVarsValid vs_r fs Hmodels
        end.

      proveVarsValid posshim_vs x H.

      Eval red in posshim_vs.

      assert (isVarValid "v" x); [
          specialize (H "v");
          destruct (in_dec string_dec "v" posshim_vs) eqn:Hindec; simpl in Hindec; [clear Hindec | solve[inversion Hindec]];
          destruct H as [H Hdead]; destruct H; [assumption|]; destruct H as [H H'];
          unfold isVarValid; try (rewrite <- FloatEmbed.fstate_lookup_fm_lookup in H);
          eexists; split; [|eapply F2OR_is_finite]; eassumption
         |].

      proveVarValid "v" ["v"; "a"; "max2"; "maxa0"] x H.

      proveVarValid "v" posshim_vs x H.

      let k := (eval red in posshim_vs) in
      proveVarsValid k x H.
      
      
      match k with
      | (?v :: ?vs') => (*proveVarValid v k x Hmodels*)
        idtac v k
        | nil => idtac
      end.
      proveVarsValid (["y"; "v"; "a"; "max2"; "maxa0"]) x H.

      

          Ltac  proveVarsValid' vs fs Hmodels :=
          proveVarsValid vs vs fs Hmodels.
      proveVarValid "a" posshim_vs x H.
      proveVarValid (fstate_)


      assert (isVarValid "a" x).
      { specialize (H "a").
        destruct (in_dec string_dec "a" posshim_vs) eqn:Hindec; simpl in Hindec; [clear Hindec | simpl in Hindec; solve[inversion Hindec]].
        destruct H as [H Hdead]. destruct H; [assumption |]; destruct H as [H H'].
        unfold isVarValid.
        rewrite <- FloatEmbed.fstate_lookup_fm_lookup in H.
        eexists; split; [eassumption | eapply F2OR_is_finite; eassumption].
      }
        eapply F2OR_is_finite.
        SearchAbout Fappli_IEEE.is_finite.
        
        simpl  in Hindec.
        

        x unfold isVarValid.
        
      repeat match goal with
             | |- context[isVarValid ?s ?x] =>
               assert (isVarValid2 s x);
                 [destruct (in_dec string_dec s posshim_vs) eqn:Hindec; intros; [clear Hindec | simpl in Hindec; solve[inversion Hindec]];
                  specialize (H s); destruct H as [H Hdead]; destruct H; [assumption|]; destruct H as [H H'];
                  unfold isVarValid2, isVarValid;
                  rewrite FloatEmbed.fstate_lookup_fm_lookup;
                  eexists; split; [eassumption|];
                  unfold M.asReal in H';
                  eapply F2OR_is_finite; eassumption
                 | change (isVarValid s x) with (isVarValid2 s x)]
      end.
      split.
      { split; auto. split; auto. lra. }
      intros.
      left.

      assert (isVarValid2 "maxa0" (fstate_set x "maxa0" val)).
      destruct (in_dec string_dec "max02" (map fst (fstate_set x "maxa0" val))) eqn: Hindec.
      Focus 2.
      simpl in n. simpl in Hindec.
      unfold in_dec in Hindec. simpl in Hindec.

        [destruct (in_dec string_dec s (map fst x)) eqn:Hindec; intros; [clear Hindec | simpl in Hindec; solve[inversion Hindec]];
         specialize (H s); destruct H as [H Hdead]; destruct H; [assumption|]; destruct H as [H H'];
         unfold isVarValid2, isVarValid;
         rewrite FloatEmbed.fstate_lookup_fm_lookup;
         eexists; split; [eassumption|];
         unfold M.asReal in H';
         eapply F2OR_is_finite; eassumption
        | change (isVarValid s x) with (isVarValid2 s x)]

      match goal with
             | |- context[isVarValid ?s ?x] =>
               assert (isVarValid2 s x);
                 [destruct (in_dec string_dec s (map fst x)) eqn:Hindec; intros; [clear Hindec | simpl in Hindec; solve[inversion Hindec]];
                  specialize (H s); destruct H as [H Hdead]; destruct H; [assumption|]; destruct H as [H H'];
                  unfold isVarValid2, isVarValid;
                  rewrite FloatEmbed.fstate_lookup_fm_lookup;
                  eexists; split; [eassumption|];
                  unfold M.asReal in H';
                  eapply F2OR_is_finite; eassumption
                 | change (isVarValid s x) with (isVarValid2 s x)]
             end.

      split.
      { split; auto. split; auto. split; auto.

      match goal with
             | |- context[isVarValid ?s ?x] => idtac s x end.
               assert (isVarValid2 s x);
                 [destruct (in_dec string_dec s posshim_vs) eqn:Hindec; intros; [clear Hindec | simpl in Hindec; solve[inversion Hindec]];
                  specialize (H s); destruct H as [H Hdead]; destruct H; [assumption|]; destruct H as [H H'];
                  unfold isVarValid2, isVarValid;
                  rewrite FloatEmbed.fstate_lookup_fm_lookup;
                  eexists; split; [eassumption|];
                  unfold M.asReal in H';
                  eapply F2OR_is_finite; eassumption
                 | change (isVarValid s x) with (isVarValid2 s x)]
             end.
      
      assert (isVarValid "y" x).
      { destruct (in_dec string_dec "y" posshim_vs) eqn:Hindec; intros; [clear Hindec | simpl in Hindec; inversion Hindec].
        specialize (H "y"). destruct H as [H Hdead]; destruct H; [assumption|]; destruct H as [H H'].
        unfold isVarValid.
        rewrite FloatEmbed.fstate_lookup_fm_lookup.
        eexists; split; [eassumption|].
        unfold M.asReal in H'.
        eapply F2OR_is_finite; eassumption.
        

        eexists.
        split.
        
        unfold fstate_lookup, fm_lookup, M.pl_data in *.
        eapply H.
        unfold fstate_lookup, fm_lookup in *.
        fwd.
        simpl in Hello.
        inversion Hello.

        specialize (H "y"); fwd; unfold posshim_vs in H; .
      unfold isVarValid.

      destruct (fstate_lookup x "y"); [|simpl in Hfhv; inversion Hfhv].
      eexists; split; [reflexivity|]. 

      unfold fstate_lookup_force in *.
      simpl.

      repeat match goal with
             | H : context [match (fstate_lookup ?s ?v) with _ => _ end] |- _ =>
               let Hq := fresh in
               destruct (fstate_lookup s v) eqn:Hq; simpl in H; [|clear -H; congruence] end.

      simpl.

      repeat match goal with
             | |- _ \/ False => left
             end.
      split.
      split.
      split.
      split; [try eexists; eauto|].

      split.
      repeat (split; [try eexists; eauto|]).
      unfold Fappli_IEEE.is_finite, f1.
left.
      intros.
      




      Focus 2.
      simpl in Hfhv.
      inversion Hfhv.
      intros. Focus 2.
      intros.

      simpl in H.
          intros; [simpl in H; inversion H]
      end.
      
      consider (fstate_lookup x "y"); intros; .
      Focus 2.
      
      unfold vmodels, posshim_vs, models in H.
      generalize (H "y"); intro Hy.
      destruct Hy as [Hy dead]; clear dead.
      destruct Hy; [left; reflexivity|].
      generalize (H "v"); intro Hv.
      destruct Hv as [Hv dead]; clear dead.
      destruct Hv; [intuition|].
      generalize (H "a"); intro Ha.
      destruct Ha as [Ha dead]; clear dead.
      destruct Ha; [intuition|].
      generalize (H "maxa0"); intro Hmaxa0.
      destruct Hmaxa0 as [Hmaxa0 dead]; clear dead.
      destruct Hmaxa0; [intuition|].
      generalize (H "max2"); intro Hmax2.
      destruct Hmax2 as [Hmax2 dead]; clear dead.
      destruct Hmax2; [intuition|].

      fwd.
      rewrite <- fstate_lookup_fm_lookup in *.
      unfold asReal in *.
      assert (isVarValid "a" x) by proveVarValid.
      assert (isVarValid "y" x) by proveVarValid.
      assert (isVarValid "v" x) by proveVarValid.
      assert (isVarValid "maxa0" x) by proveVarValid.
      assert (isVarValid "max2" x) by proveVarValid.

      (* first if-statement *)
      split.
      {
        intros.
        cbv beta zeta iota delta [
              fstate_lookup fstate_set rel_dec
              AnyOf map cross bound_fexpr flat_map app lofst lift2
                  land lor limpl ILInsts.ILFun_Ops ILogicOps_Prop
                  bound_term fexpr_to_NowTerm combineTripleMinus combineTriplePlus combineTripleMult
                  eval_NowTerm
                  a_minus a_mult a_plus lb ub premise c_le c_lt c_ge c_gt
                  fzero f10
                  isFloatConstValid (*isVarValid*)
                  Arithable_Applicative Fun.Applicative_Fun
                  Arithable_Lift Arithable_R
                  Comparable_Lift Comparable_R Comparable_Applicative
                  Applicative.pure Applicative.ap
                  simpleBound simpleBound2 simpleBound3 simpleBound4 simpleBound5
                  simpleBound6 simpleBound7 simpleBound8 simpleBound9 simpleBound10 simpleBound11 simpleBound12 simpleBound13
                  simpleBound14 simpleBound15 simpleBound16 simpleBound17 simpleBound18 simpleBound19 simpleBound20
                  simpleBound21 simpleBound22 simpleBound23 simpleBound24 simpleBound25 simpleBound26 simpleBound27
                  simpleBound28 simpleBound29 simpleBound30 simpleBound31 simpleBound32 simpleBound33
                  (*simpleBoundM1 simpleBoundM2 simpleBoundM3 simpleBoundM4*)
            ].

        cbv beta zeta iota delta [ub lb premise].

        rewrite fstate_lookup_force_eq.

         unfold simpleBound, simpleBound2, simpleBound3, simpleBound4, simpleBound5,
                  simpleBound6, simpleBound7, simpleBound8, simpleBound9, simpleBound10, simpleBound11, simpleBound12, simpleBound13,
                  simpleBound14, simpleBound15, simpleBound16, simpleBound17, simpleBound18, simpleBound19, simpleBound20,
                  simpleBound21, simpleBound22, simpleBound23, simpleBound24, simpleBound25, simpleBound26, simpleBound27,
                  simpleBound28, simpleBound29, simpleBound30, simpleBound31, simpleBound32, simpleBound33.

         unfold simpleBoundM3, simpleBoundM4, simpleBoundM5, simpleBoundM6, simpleBoundM7, simpleBoundM8, simpleBoundM9,
         simpleBoundM10, simpleBoundM11.
         unfold maybe_lt0, maybe_ge0. unfold map.

        cbv beta zeta iota delta [lofst fstate_set fstate_lookup_force' fstate_lookup fstate_set lofst rel_dec RelDec_string String.string_dec ascii_dec ascii_rec sumbool_rec eq_ind_r f_equal Bool.bool_dec sumbool_rect ascii_rect bool_rec bool_rect eq_ind eq_rect eq_sym].
        rewrite <- fstate_lookup_force_eq.
        
        unfold fstate_lookup_force, lofst.
        rewrite H10.
        simpl Fappli_IEEE.B2R.
        unfold simpleBound, simpleBound2, simpleBound3, simpleBound4, simpleBound5,
                  simpleBound6, simpleBound7, simpleBound8, simpleBound9, simpleBound10, simpleBound11, simpleBound12, simpleBound13,
                  simpleBound14, simpleBound15, simpleBound16, simpleBound17, simpleBound18, simpleBound19, simpleBound20,
                  simpleBound21, simpleBound22, simpleBound23, simpleBound24, simpleBound25, simpleBound26, simpleBound27,
                  simpleBound28, simpleBound29, simpleBound30, simpleBound31, simpleBound32, simpleBound33.

        
        
        unfold a_mult, a_plus, Arithable_Lift, Arithable_R, Arithable_Applicative, Comparable_Lift, Comparable_R, Comparable_Applicative,
        Applicative.pure, Applicative.ap, Fun.Applicative_Fun, lb, ub, premise, a_mult, a_minus, a_plus, maybe_lt0.

        cbv beta zeta iota delta [
              fstate_lookup fstate_set rel_dec
              AnyOf map cross bound_fexpr flat_map app lofst lift2
                  land lor limpl ILInsts.ILFun_Ops ILogicOps_Prop
                  bound_term fexpr_to_NowTerm combineTripleMinus combineTriplePlus combineTripleMult
                  eval_NowTerm
                  a_minus a_mult a_plus lb ub premise c_le c_lt c_ge c_gt
                  fzero f10
                  isFloatConstValid (*isVarValid*) fstate_lookup_force
                  Arithable_Applicative Fun.Applicative_Fun
                  Arithable_Lift Arithable_R
                  Comparable_Lift Comparable_R Comparable_Applicative
                  Applicative.pure Applicative.ap
                  simpleBound simpleBound2 simpleBound3 simpleBound4 simpleBound5
                  simpleBound6 simpleBound7 simpleBound8 simpleBound9 simpleBound10 simpleBound11 simpleBound12 simpleBound13
                  simpleBound14 simpleBound15 simpleBound16 simpleBound17 simpleBound18 simpleBound19 simpleBound20
                  simpleBound21 simpleBound22 simpleBound23 simpleBound24 simpleBound25 simpleBound26 simpleBound27
                  simpleBound28 simpleBound29 simpleBound30 simpleBound31 simpleBound32 simpleBound33
                  (*simpleBoundM1 simpleBoundM2 simpleBoundM3 simpleBoundM4*)
            ].

        unfold RelDec_string.
        
        simpl.
        
        
        assert (forall v x, isVarValid v x = True) as Hivv by admit.
                  

        Print isVarValid.

        assert (forall val, (lofst 0 (fstate_set x "maxa0" val) -
                        fstate_lookup_force (fstate_set x "maxa0" val) "v" +
                        (lofst 0 (fstate_set x "maxa0" val) -
                         fstate_lookup_force (fstate_set x "maxa0" val) "maxa0")))%type.
        cbn beta zeta iota delta [lofst fstate_lookup_force fstate_lookup fstate_set lofst rel_dec RelDec_string String.string_dec ascii_dec ascii_rec sumbool_rec eq_ind_r f_equal Bool.bool_dec sumbool_rect].

        left.

        unfold fstate_lookup_force, fstate_lookup, fstate_set.
        Print RelDec_string.
        Print String.string_dec.
        Locate String.string_dec.
        unfold rel_dec RelDec_string String.string_dec ascii_dec ascii_rec

        cbn beta zeta iota delta [simpleBound].

        unfold lofst, fstate_set, fstate_lookup_force.
        unfold fstate_lookup, isVarValid.
        cbn beta zeta iota delta [rel_dec RelDec_string String.string_dec ascii_dec ascii_rec sumbool_rec eq_ind_r, f_equal, Bool.bool_dec].

        idtac.
        cbn beta zeta iota delta [String.string_dec ascii_dec].
        cbn beta zeta iota delta [fplus lift2 fminus fmult].
        (* here... *)
        cbn

        idtac.

        unfold rel_dec.

      fwd. rewrite <- fstate_lookup_fm_lookup in H4, H5.
      cbv beta zeta iota delta
          [lift2 fplus fmult float_one fzero Fappli_IEEE.Bopp Fappli_IEEE.Bplus Fappli_IEEE.Bmult custom_prec custom_emax prec emax custom_nan].
      rewrite H4, H5.
      eexists.
      split; [reflexivity|].

    
    
  rewrite landC. rewrite landA. rewrite landC. rewrite landA. rewrite landC.
  rewrite landA. rewrite <- landC. tlaRevert.
  
(* position controller... *)

Definition p_ctrl : fcmd :=
  FAsn "v" (FMult (FMinus (FConst fzero) (FVar "x")) (FConst fhalf)).

Check fwp_velshim2_full.
Print preVarIsFloat.



Definition p_vs := ["v"; "x"].

Definition p_eps : R := (1/10000)%R.

Theorem fwp_p :
  preVarPred pred1 "v" //\\
  preVarPred pred1 "x" //\\
  embed_ex p_vs p_ctrl
  |--  (--"x"/2 - p_eps < "v"! < --"x"/2 + p_eps).
Proof.
  rewrite <- landA. rewrite landC.
  tlaRevert.
  erewrite Hoare__embed_rw.
  {
    eapply lforallL.
    instantiate (1 := (fstate_get_rval "v" (fun v =>
                                              fstate_get_rval "x" (fun x _ =>
                                                                     (x/2 - p_eps < v < x/2 + p_eps)%R)))).
    cbv beta zeta iota delta [fwp velshim2 fexprD].
    eapply lequiv_rewrite_left.
    {
      crunch_embeds.
    }

    apply lexistsL. intros.
    apply land_comm_left.
    apply landAdj.
    apply lentail_cut2.

    (* bounds hold *)
    {
      Opaque bound_fexpr. breakAbstraction. Transparent bound_fexpr.
      intros. fwd.
      unfold vmodels, p_vs, models in H.
      generalize (H "v"); intro Hv.
      destruct Hv as [Hv dead]; clear dead.
      destruct Hv; [intuition|].
      generalize (H "x"); intro Hx.
      destruct Hx as [Hx dead]; clear dead.
      destruct Hx; [intuition|].

      fwd. rewrite <- fstate_lookup_fm_lookup in *.
      unfold fstate_lookup_force in *.
      rewrite H1.
      cbv beta zeta iota delta
          [lift2 fplus fmult float_one fzero Fappli_IEEE.Bopp Fappli_IEEE.Bplus Fappli_IEEE.Bmult custom_prec custom_emax prec emax custom_nan].
      eexists.
      split; [reflexivity|].
      simpl.
      unfold fstate_lookup_force.
      rewrite H1.
      unfold isFloatConstValid, lofst, fstate_get_rval in *.
      simpl.
      rewrite H1.
      

              repeat match goal with
               | |- context[isVarValid ?str ?sta] =>
                 let HV := fresh "Hvalid" in
                 assert (isVarValid str sta) as HV by proveVarValid;
                   rewrite (pe_triv _ HV)
                     end.

              unfold fstate_lookup_force.
              unfold asReal in *.

              rewrite H2.
              
        repeat match goal with
               | H : fstate_lookup _ _ = Some _ |- _ =>
                 rewrite H in *; clear H
               end.


        repeat match goal with
               | H : F2OR ?X = Some ?Y |- _ =>
                 apply F2OR_FloatToR' in H
               end.
        show_value floatMin.
        show_value floatMax.
        show_value error.
        unfold lift2, lofst.
        do_F2Rs.


      do_F2Rs.
      show_value floatMin.
      show_value floatMax.
      show_value error.
      
    }

    (* bounds imply spec *)
    {

    }
    

  }

Admitted.
