(*
 * FloatEmbed.v
 * Specialization of the Embedding framework to our floating-point language
 *)
Require Import Source.
Require Import Embed.
Require Import Logic.Syntax.
Require Import Logic.Semantics.
Require Import Logic.Automation.
Require Import Coq.Reals.Rbase.
Require Import Coq.Strings.String.
Require Import micromega.Psatz.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Option.
Require Import RelDec.

Inductive fexpr :=
| FVar : Var -> fexpr
| FConst : Source.float -> fexpr
| FPlus : fexpr -> fexpr -> fexpr
| FMinus : fexpr -> fexpr -> fexpr
| FMult : fexpr -> fexpr -> fexpr
(*| FDiv : fexpr -> fexpr -> fexpr*)
.
(* TODO - other ops? *)

Definition fplus : Source.float -> Source.float -> Source.float :=
  Fappli_IEEE.Bplus custom_prec custom_emax custom_precGt0
                    custom_precLtEmax custom_nan Fappli_IEEE.mode_ZR.

Definition fminus : Source.float -> Source.float -> Source.float :=
  Fappli_IEEE.Bminus custom_prec custom_emax custom_precGt0
                     custom_precLtEmax custom_nan Fappli_IEEE.mode_ZR.

Definition fmult : Source.float -> Source.float -> Source.float :=
  Fappli_IEEE.Bmult custom_prec custom_emax custom_precGt0
                    custom_precLtEmax custom_nan Fappli_IEEE.mode_ZR.

Definition fdiv : Source.float -> Source.float -> Source.float :=
  Fappli_IEEE.Bdiv custom_prec custom_emax custom_precGt0
                   custom_precLtEmax custom_nan Fappli_IEEE.mode_ZR.

(* TODO pretty sure we need to do variable translation here *)
Fixpoint fexprD (fx : fexpr) (sf : fstate) : option Source.float :=
  match fx with
    | FVar s         => fstate_lookup sf s
    | FConst f       => Some f
    | FPlus fx1 fx2  => lift2 fplus  (fexprD fx1 sf) (fexprD fx2 sf)
    | FMinus fx1 fx2 => lift2 fminus (fexprD fx1 sf) (fexprD fx2 sf)
    | FMult fx1 fx2  => lift2 fmult  (fexprD fx1 sf) (fexprD fx2 sf)
    (*| FDiv fx1 fx2   => lift2 fdiv   (fexprD fx1 sf) (fexprD fx2 sf)*)
  end.

Inductive fcmd : Type :=
| FSeq   : fcmd -> fcmd -> fcmd
| FSkip  : fcmd
| FAsn   : Var -> fexpr -> fcmd
| FIte   : fexpr -> fcmd -> fcmd -> fcmd
| FFail  : fcmd
.

(*Definition fzero := Eval compute in (nat_to_float 0).*)
Definition fzero : float := Fappli_IEEE.B754_zero 24 128 false.
Definition fnegzero : float := Fappli_IEEE.B754_zero 24 128 true.

Require Import Flocq.Core.Fcore_ulp.

Definition F2OR (f : float) : option R :=
  match f with
    | Fappli_IEEE.B754_zero   _ _ _      => Some (FloatToR f)
    | Fappli_IEEE.B754_finite _ _ _ _ _ _ => Some (FloatToR f)
    | _                               => None
  end.

Definition float_lt (f1 f2 : float)  : Prop :=
  (FloatToR f1 < FloatToR f2)%R.

Definition float_ge (f1 f2 : float) : Prop :=
  (FloatToR f1 >= FloatToR f2)%R.

Inductive feval : fstate -> fcmd -> fstate -> Prop :=
| FESkip : forall s, feval s FSkip s
| FESeqS : forall s s' os'' a b,
    feval s a s' ->
    feval s' b os'' ->
    feval s (FSeq a b) os''
| FEAsnS : forall s v e val,
    fexprD e s = Some val ->
    feval s (FAsn v e) ((fstate_set s v val))
| FEIteT :
    forall s os' ex c1 c2 f,
      fexprD ex s = Some f ->
      float_lt f fzero ->
      feval s c1 os' ->
      feval s (FIte ex c1 c2) os'
| FEIteF:
    forall s os' ex c1 c2 f,
      fexprD ex s = Some f ->
      float_ge f fzero ->
      feval s c2 os' ->
      feval s (FIte ex c1 c2) os'
.

Require Import Flocq.Appli.Fappli_IEEE.

Inductive pl_eq : float -> float -> Prop :=
| pl_zero : forall b b', pl_eq (B754_zero _ _ b) (B754_zero _ _ b')
| pl_inf : forall b b', pl_eq (B754_infinity _ _ b) (B754_infinity _ _ b')
| pl_nan : forall b b' p p', pl_eq (B754_nan _ _ b p) (B754_nan _ _ b' p')
| pl_except : forall b b' p, pl_eq (B754_infinity _ _ b) (B754_nan _ _ b' p)
| pl_refl : forall (p1 : float), pl_eq p1 p1
| pl_symm : forall p1 p2, pl_eq p1 p2 -> pl_eq p2 p1
| pl_trans : forall p1 p2 p3, pl_eq p1 p2 -> pl_eq p2 p3 -> pl_eq p1 p3
.

Definition real_float (r : R) (f : float): Prop :=
  (F2OR f = Some r)%type.

(* Instantiate our general embedding module for our particular case
   (floating-point, non-looping, imperative language) *)
Module FloatEmbed <: EMBEDDING.
  Definition ast := fcmd.
  Definition pl_data := float.
  Definition eval := feval.
  Definition istate := list (string * float).
  Definition pl_equ := pl_eq.
  Definition pl_equ_refl : forall p : pl_data, pl_equ p p := pl_refl.
  Definition pl_equ_trans : forall p p' p'' : pl_data, pl_equ p p' -> pl_equ p' p'' -> pl_equ p p'' := pl_trans.
  Definition pl_equ_symm : forall p p' : pl_data, pl_equ p p' -> pl_equ p' p := pl_symm.

  (* Definition required by EMBEDDING *)
  Definition states_iso (st st' : istate) : Prop :=
    forall (s : string),
      match (fm_lookup st s), (fm_lookup st' s) with
      | None, None => True
      | Some f1, Some f2 => pl_equ f1 f2
      | _, _ => False
      end.

  (* Definition we use for our purposes; equivalent to the above *)
  Definition states_iso' (st st' : istate) : Prop :=
    forall (s : string),
      match fm_lookup st s with
      | None => fm_lookup st' s = None
      | Some f =>
        exists f', fm_lookup st' s = Some f' /\
              F2OR f = F2OR f'
      end.

  Lemma pl_eq_F2OR :
    forall a b,
      pl_eq a b ->
      F2OR a = F2OR b.
  Proof.
    induction 1; simpl; try reflexivity; auto.
    rewrite IHpl_eq1. auto.
  Qed.

  Lemma bpow_nonzero :
    forall radix2 e, (~Fcore_Raux.bpow radix2 e = 0)%R.
  Proof.
    intros. intro.
    destruct e.
    - simpl in *. lra.
    - simpl in *.
      destruct radix2.
      generalize (Fcore_Zaux.Zpower_pos_gt_0); intro Hzpg.
      simpl in H.
      specialize (Hzpg radix_val p).
      apply Zle_bool_imp_le in radix_prop.
      assert (0 < radix_val)%Z by lia. specialize (Hzpg H0).
      apply Fcore_Raux.Z2R_lt in Hzpg.
      simpl in Hzpg. lra.
    - simpl in *.
      destruct radix2.
      simpl in H.
      generalize (Rinv_neq_0_compat (Fcore_Raux.Z2R (Z.pow_pos radix_val p))%R); intro Hin0.
      assert (~Fcore_Raux.Z2R (Z.pow_pos radix_val p) = 0)%R.
      { intro.
        generalize (Fcore_Zaux.Zpower_pos_gt_0); intro Hzpg.
        apply Zle_bool_imp_le in radix_prop.
        assert (0 < radix_val)%Z by lia.
        specialize (Hzpg radix_val p H1).
        apply Fcore_Raux.Z2R_lt in Hzpg.
        simpl in Hzpg. lra. }
      specialize (Hin0 H0).
      lra.
  Qed.
  
  Require Import ArithFacts.
  Require Import Flocq.Core.Fcore_float_prop.
  Require Import Flocq.Core.Fcore_Zaux.
  Lemma F2OR_pl_eq :
    forall f f',
      F2OR f = F2OR f' ->
      pl_eq f f'.
  Proof.
    intros.
    unfold F2OR in H.
    consider f; consider f'; intros; subst; simpl in *; try constructor; try congruence.
    { consider b; intros; subst.
      { simpl in *.
        unfold Fcore_defs.F2R, Fcore_Raux.Z2R, Fcore_defs.Fnum in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        simpl in H0.
        inversion H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. }
      { simpl in *.
        unfold Fcore_defs.F2R, Fcore_Raux.Z2R, Fcore_defs.Fnum in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        simpl in H0. inversion H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. } }
    { constructor. }
    (* copypasta *)
    { consider b0; intros; subst.
      { simpl in *.
        unfold Fcore_defs.F2R, Fcore_Raux.Z2R, Fcore_defs.Fnum in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        simpl in H0.
        inversion H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. }
      { simpl in *.
        unfold Fcore_defs.F2R, Fcore_Raux.Z2R, Fcore_defs.Fnum in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        simpl in H0. inversion H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. } }
    { pose proof e0 as e0'. pose proof e2 as e2'.
      unfold Fappli_IEEE.bounded in e0', e2'.
      apply Bool.andb_true_iff in e2'. apply Bool.andb_true_iff in e0'.
      forward_reason.
      inversion H1.
      generalize (Fcore_generic_fmt.canonic_unicity radix2 (Fcore_FLT.FLT_exp (3 - custom_emax - custom_prec) custom_prec)); intro Huni.
      eapply canonic_canonic_mantissa in H2. eapply canonic_canonic_mantissa in H.
      symmetry in H5.
      specialize (Huni _ _ H2 H H5).
      inversion Huni.
      subst.
      eapply F2R_eq_reg in H5.
      consider b; consider b0; intros; subst; try solve [simpl in *; congruence].
      { simpl in H6. inversion H6.
        subst.
        clear.
        cutrewrite (eq e2 e0).
        - apply pl_refl.
        - generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
          intros.
          auto. }
      { simpl in H6. inversion H6.
        subst.
        clear.
        cutrewrite (eq e0 e2).
        - apply pl_refl.
        - generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
          intros. auto. } }
  Qed.
  
  Lemma states_iso_iso' : forall (st st' : istate),
      states_iso st st' <-> states_iso' st st'.
  Proof.
    intros.
    split.
    { intros. unfold states_iso, states_iso' in *.
      intro s. specialize (H s).
      consider (fm_lookup st s); intros; subst.
      { consider (fm_lookup st' s); intros; subst; try contradiction.
        apply pl_eq_F2OR in H1. eexists; split; eauto. }
      { consider (fm_lookup st' s); intros; subst; try contradiction; try reflexivity. } }
    { intros. unfold states_iso, states_iso' in *.
      intro s. specialize (H s).
      consider (fm_lookup st s); intros; subst.
      { consider (fm_lookup st' s); intros; subst.
        { apply F2OR_pl_eq. forward_reason. inversion H1. auto. }
        { forward_reason. congruence. } }
      { rewrite H0. auto. } }
  Qed.

  Definition asReal (f : float) (r : R) :=
    (F2OR f = Some r)%type.

  Definition asReal_is : asReal = (fun f r => F2OR f = Some r)%type := eq_refl.

  (* we may perhaps need a notion of validity *)
  Lemma states_iso_nil :
    forall ist,
      states_iso nil ist <-> ist = nil.
  Proof.
    split.
    - rewrite states_iso_iso'.
      intros. simpl in H.
      induction ist.
      * reflexivity.
      * simpl in H. destruct a.
        specialize (H s). simpl in *.
        consider (string_dec s s); intros; try congruence.
    - intros. subst. rewrite states_iso_iso'. unfold states_iso'. simpl. auto.
  Qed.

  Lemma fstate_lookup_update_match :
    forall fst v val,
      Some val = fstate_lookup (fstate_set fst v val) v.
  Proof.
    intros.
    simpl.
    consider (v ?[eq] v); intro; subst; congruence.
  Qed.

  Lemma fstate_lookup_irrelevant_update :
    forall fst v v' val,
      v <> v' ->
      fstate_lookup fst v = fstate_lookup (fstate_set fst v' val) v.
  Proof.
    intros.
    simpl.
    consider (v ?[eq] v'); intro; subst; congruence.
  Qed.
  
  Lemma fstate_lookup_fm_lookup :
    forall fst v,
      fstate_lookup fst v = fm_lookup fst v.
  Proof.
    induction fst.
    - reflexivity.
    - simpl. intros.
      destruct a.
      consider (v ?[eq] v0); intro; subst.
      + consider (string_dec v0 v0); try congruence.
      + consider (string_dec v v0); try congruence.
  Qed.

  Lemma pl_eq_asReal' :
    forall (p1 p2 : pl_data) (r : R),
      pl_equ p1 p2 -> (asReal p1 r <-> asReal p2 r).
  Proof.
    unfold pl_equ.
    induction 1; split; auto;
    try solve [destruct IHpl_eq; auto];
    try solve [destruct IHpl_eq1; destruct IHpl_eq2; auto].
  Qed.

  Lemma pl_eq_asReal :
    forall (p1 p2 : pl_data) (r : R),
      pl_eq p1 p2 -> asReal p1 r -> asReal p2 r.
  Proof.
    intros.
    generalize (pl_eq_asReal' p1 p2 r H). intro Hplear.
    destruct Hplear. auto.
  Qed.

  Lemma states_iso_set' :
    forall ist ist',
      states_iso ist ist' ->
      forall val val', pl_eq val val' ->
                  forall v,
                    states_iso (fstate_set ist v val) (fstate_set ist' v val').
  Proof.
    intros.
    rewrite states_iso_iso' in H. rewrite states_iso_iso'.
    unfold states_iso' in *.
    induction H0.
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists. split; reflexivity.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        rewrite <- fstate_lookup_fm_lookup in H.
        consider (fstate_lookup ist s); intros; subst.
        + forward_reason. eexists. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; auto.
            rewrite <- fstate_lookup_fm_lookup in H0. eauto.
          * auto.
        + rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; auto.
          rewrite fstate_lookup_fm_lookup. auto. }
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        consider (fm_lookup ist s); intros; subst.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          forward_reason.
          exists x. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; eauto.
            rewrite fstate_lookup_fm_lookup. eauto.
          * auto.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          rewrite <- fstate_lookup_fm_lookup.
          erewrite <- fstate_lookup_irrelevant_update; eauto.
          rewrite fstate_lookup_fm_lookup. auto. }
    (* the following three are copy-paste of the previous block *)
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        consider (fm_lookup ist s); intros; subst.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          forward_reason.
          exists x. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; eauto.
            rewrite fstate_lookup_fm_lookup. eauto.
          * auto.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          rewrite <- fstate_lookup_fm_lookup.
          erewrite <- fstate_lookup_irrelevant_update; eauto.
          rewrite fstate_lookup_fm_lookup. auto. }
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        consider (fm_lookup ist s); intros; subst.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          forward_reason.
          exists x. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; eauto.
            rewrite fstate_lookup_fm_lookup. eauto.
          * auto.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          rewrite <- fstate_lookup_fm_lookup.
          erewrite <- fstate_lookup_irrelevant_update; eauto.
          rewrite fstate_lookup_fm_lookup. auto. }
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        consider (fm_lookup ist s); intros; subst.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          forward_reason.
          exists x. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; eauto.
            rewrite fstate_lookup_fm_lookup. eauto.
          * auto.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          rewrite <- fstate_lookup_fm_lookup.
          erewrite <- fstate_lookup_irrelevant_update; eauto.
          rewrite fstate_lookup_fm_lookup. auto. }
    (* interesting cases again *)
    { intros.
      specialize (IHpl_eq s).
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup in IHpl_eq. rewrite <- fstate_lookup_update_match in IHpl_eq.
        rewrite <- fstate_lookup_fm_lookup in IHpl_eq. rewrite <- fstate_lookup_update_match in IHpl_eq.
        forward_reason. inversion H1; subst.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        rewrite <- fstate_lookup_fm_lookup in IHpl_eq. rewrite <- fstate_lookup_irrelevant_update in IHpl_eq; [|auto].
        specialize (H s). rewrite <- fstate_lookup_fm_lookup in H.
        consider (fstate_lookup ist s); intros; subst.
        + rewrite <- fstate_lookup_fm_lookup.
          rewrite <- fstate_lookup_irrelevant_update; [|auto].
          rewrite fstate_lookup_fm_lookup. auto.
        + rewrite <- fstate_lookup_fm_lookup.
          rewrite <- fstate_lookup_irrelevant_update; [|auto].
          rewrite <- fstate_lookup_fm_lookup in H2.
          rewrite <- fstate_lookup_irrelevant_update in H2; auto. }
    { intros. specialize (IHpl_eq1 s). specialize (IHpl_eq2 s).
      consider (string_dec v s); intros; subst.
      - do 2 (rewrite <- fstate_lookup_fm_lookup; rewrite <- fstate_lookup_update_match).
        do 2 (rewrite <- fstate_lookup_fm_lookup in IHpl_eq1; rewrite <- fstate_lookup_update_match in IHpl_eq1).
        do 2 (rewrite <- fstate_lookup_fm_lookup in IHpl_eq2; rewrite <- fstate_lookup_update_match in IHpl_eq2).
        forward_reason.
        inversion H1; subst. inversion H0; subst.
        eexists.
        split; eauto. rewrite <- H2. auto.
      - do 2 (rewrite <- fstate_lookup_fm_lookup; rewrite <- fstate_lookup_irrelevant_update; [|auto]).
        do 2 (rewrite <- fstate_lookup_fm_lookup in IHpl_eq1; rewrite <- fstate_lookup_irrelevant_update in IHpl_eq1; [|auto]).
        do 2 (rewrite <- fstate_lookup_fm_lookup in IHpl_eq2; rewrite <- fstate_lookup_irrelevant_update in IHpl_eq2; [|auto]).
        specialize (H s). rewrite <- fstate_lookup_fm_lookup in H.
        consider (fstate_lookup ist s); intros; subst; eauto. }
  Qed.

  Ltac fwd := forward_reason.

  Definition pl_eq_lift (of1 of2 : option float) : Prop :=
    match of1, of2 with
    | None, None => True
    | Some f1, Some f2 => pl_eq f1 f2
    | _, _ => False
    end.

  Lemma INR_gt_zero :
    forall (n : nat), (INR n >= 0)%R.
  Proof.
    induction n.
    - simpl. lra.
    - simpl.
      destruct n.
      + lra.
      + lra.
  Qed.

  (* some copypasta in here as well *)
  Lemma pl_eq_finite_eq :
    forall b0 m0 e1 e2 b1 m1 e1' e2',
      let f  := B754_finite custom_prec custom_emax b0 m0 e1 e2 in
      let f' := B754_finite custom_prec custom_emax b1 m1 e1' e2' in
      pl_eq f f' ->
      f = f'.
  Proof.
    intros.
    apply pl_eq_F2OR in H.
    unfold f, f' in *. simpl in H.
    clear f f'.
    inversion H; clear H.
    generalize (Fcore_generic_fmt.canonic_unicity radix2 (Fcore_FLT.FLT_exp (3 - custom_emax - custom_prec) custom_prec)); intro Huni.
    apply Huni in H1.
    { inversion H1; subst.
      consider b0; intros.
      { consider b1; intros.
        { simpl in H1. inversion H1. subst.
          cutrewrite (eq e2 e2'); [reflexivity|].
          generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec). intros. auto. }
        { simpl in H1. inversion H1. } }
      { consider b1; intros.
        { simpl in H1. inversion H1. }
        { simpl in H1. inversion H1. subst.
          cutrewrite (eq e2 e2'); [reflexivity|].
          generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec). intros. auto. } } }
    { eapply canonic_canonic_mantissa.
      pose proof e2 as p2.
      apply Bool.andb_true_iff in p2. fwd. auto. }
    { eapply canonic_canonic_mantissa.
      pose proof e2' as p2'.
      apply Bool.andb_true_iff in p2'. fwd. auto. }
  Qed.
  
  (* For brutal case-analysis *)
  Ltac smash :=
    let rec smash' E :=
        match E with
        | context[match ?X with | _ => _ end] =>
          match X with
          | context[match ?Y with | _ => _ end] =>
            smash' X
          | _ => consider X; intros; subst
          end
            (* this branch could be smarter, but in practice we don't really use it here *)
        | context[if ?X then _ else _] =>
          consider X; intros; subst
        end
    in
    match goal with
    | |- ?G => smash' G
    end.

    Ltac smashs := repeat smash.

    Lemma pl_finite_neq_zero :
      forall b0 m e e0 b1,
        ~(pl_eq (B754_finite custom_prec custom_emax b0 m e e0)
                (B754_zero custom_prec custom_emax b1)).
    Proof.
      intros.
      intro.
      apply pl_eq_F2OR in H. simpl in H. inversion H; clear H.
      unfold Fcore_Zaux.cond_Zopp in H1. simpl in H1.
      consider b0; intros; subst.
      { unfold Fcore_defs.F2R in H0. simpl in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. }
      { unfold Fcore_defs.F2R in H0. simpl in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. }
    Qed.
    
  Lemma states_iso_fexprD :
    forall ist ist',
      states_iso ist ist' ->
      forall fx, pl_eq_lift (fexprD fx ist) (fexprD fx ist').
  Proof.
    induction fx; rewrite states_iso_iso' in H.
    { simpl. unfold pl_eq_lift.
      consider (fstate_lookup ist v); intros; subst;
      consider (fstate_lookup ist' v); intros; subst; try auto.
      { unfold states_iso' in H. specialize (H v). rewrite <- fstate_lookup_fm_lookup in H.
        rewrite H0 in H. forward_reason.
        apply F2OR_pl_eq in H2.
        eapply pl_equ_trans. apply H2.
        rewrite <- fstate_lookup_fm_lookup in H. rewrite H in H1. inversion H1; subst.
        constructor. }
      { unfold states_iso' in H. specialize (H v).
        rewrite <- fstate_lookup_fm_lookup in H.
        rewrite -> H0 in H. fwd.
        rewrite <- fstate_lookup_fm_lookup in H.
        congruence. }
      { unfold states_iso' in H. specialize (H v).
        rewrite <- fstate_lookup_fm_lookup in H.
        rewrite H0 in H.
        rewrite <- fstate_lookup_fm_lookup in H.
        congruence. } }
    { simpl. constructor. }
    { simpl.
      unfold pl_eq_lift in IHfx1. unfold pl_eq_lift in IHfx2.
      unfold lift2, pl_eq_lift.
      smashs; try congruence; auto.
      (* begin experiment *)
      unfold fplus, Bplus.
      smashs; try solve [constructor]; try solve [apply pl_symm; constructor];
      try solve [apply pl_eq_F2OR in IHfx1; simpl in IHfx1; congruence];
      try solve [apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_symm in IHfx1; apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_eq_F2OR in IHfx2; simpl in IHfx2; congruence];
      try solve [apply pl_finite_neq_zero in IHfx2; contradiction];
      try solve [apply pl_symm in IHfx2; apply pl_finite_neq_zero in IHfx2; contradiction].
      apply pl_eq_finite_eq in IHfx1. apply pl_eq_finite_eq in IHfx2.
      inversion IHfx1; inversion IHfx2; subst.
      apply pl_refl. }
    (* copypasta *)
    { simpl.
      unfold pl_eq_lift in IHfx1. unfold pl_eq_lift in IHfx2.
      unfold lift2, pl_eq_lift.
      smashs; try congruence; auto.
      (* begin experiment *)
      unfold fminus, Bplus, Bminus, Bplus. (* wtf *)
      smashs; try solve [constructor]; try solve [apply pl_symm; constructor];
      try solve [apply pl_eq_F2OR in IHfx1; simpl in IHfx1; congruence];
      try solve [apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_symm in IHfx1; apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_eq_F2OR in IHfx2; simpl in IHfx2; congruence];
      try solve [unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence;
                 apply pl_eq_F2OR in IHfx2; simpl in IHfx2; congruence];
      try solve [unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence;
                 apply pl_symm in IHfx2; apply pl_finite_neq_zero in IHfx2; contradiction];
      try solve [unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence;
                 apply pl_finite_neq_zero in IHfx2; contradiction].
      { unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence.
        apply pl_eq_finite_eq in IHfx2.
        inversion IHfx2; subst; clear IHfx2.
        inversion H7; subst; clear H7.
        inversion H2; subst; clear H2.
        cutrewrite (eq e0 e2); [apply pl_refl|].
        generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
        intros.
        auto. }
      { unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence.
        apply pl_eq_finite_eq in IHfx1.
        inversion IHfx1; subst; clear IHfx1.
        inversion H2; subst; clear H2.
        inversion H7; subst; clear H7.
        apply pl_eq_finite_eq in IHfx2.
        inversion IHfx2; subst; clear IHfx2.
        apply pl_refl. } }
    (* copypasta *)
    { simpl.
      unfold pl_eq_lift in IHfx1. unfold pl_eq_lift in IHfx2.
      unfold lift2, pl_eq_lift.
      smashs; try congruence; auto.
      unfold fmult, Bmult.
      smashs; try solve [constructor]; try solve [apply pl_symm; constructor];
      try solve [apply pl_eq_F2OR in IHfx1; simpl in IHfx1; congruence];
      try solve [apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_symm in IHfx1; apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_eq_F2OR in IHfx2; simpl in IHfx2; congruence];
      try solve [apply pl_finite_neq_zero in IHfx2; contradiction];
      try solve [apply pl_symm in IHfx2; apply pl_finite_neq_zero in IHfx2; contradiction].
      { apply pl_eq_finite_eq in IHfx1.
        inversion IHfx1; subst; clear IHfx1.
        apply pl_eq_finite_eq in IHfx2.
        inversion IHfx2; subst; clear IHfx2.
        cutrewrite (eq e0 e4).
        { cutrewrite (eq e2 e6).
          { apply pl_refl. }
          { generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
            intros.
            auto. } }
        { generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
          intros.
          auto. } } }
  Qed.

  (*
  Lemma  eval_det1:
    forall prg isti istf istf',
      eval isti prg istf ->
      eval isti prg istf' ->
      states_iso istf istf'.
  Proof.
    intros.
        
  Axiom eval_det2 :
    forall prg isti istf istf',
      (istf ~~ istf') ->
      eval isti prg istf ->
      exists isti', isti ~~ isti' /\ eval isti' prg istf'
*)
  
  Lemma eval_det :
    forall prg isti isti' istf,
      (states_iso isti isti') ->
      eval isti prg istf ->
      exists istf', states_iso istf istf' /\ eval isti' prg istf'.
  Proof.
    induction prg.
    - intros. inversion H0; subst; clear H0.
      specialize (IHprg1 _ _ _ H H4). forward_reason.
      specialize (IHprg2 _ _ _ H0 H6). forward_reason.
      eexists. split; eauto.
      econstructor; eauto.
    - intros.
      inversion H0; subst; clear H0.
      eexists; split; eauto. econstructor.
    - intros.
      inversion H0; subst; clear H0.
      generalize (states_iso_fexprD _ _ H f); intro Hsif.
      unfold pl_eq_lift in Hsif.
      rewrite H5 in Hsif.
      consider (fexprD f isti'); intros; try contradiction.
      exists (fstate_set isti' v f0).
      split.
      + eapply states_iso_set'; auto.
      + econstructor; auto.
    - intros.
      generalize (states_iso_fexprD _ _ H f); intro Hsif.
      inversion H0; subst; clear H0.
      + specialize (IHprg1 _ _ _ H H8).
        forward_reason.
        unfold pl_eq_lift in Hsif.
        rewrite H5 in Hsif.
        consider (fexprD f isti'); intros; try contradiction.
        exists x; split; eauto.
        eapply FEIteT; eauto.
        apply pl_eq_F2OR in Hsif.
        unfold float_lt in *.
        unfold F2OR in *.
        consider f0; consider f1; intros; subst; auto; simpl in *;
        try lra; try solve [inversion Hsif; lra].
      + specialize (IHprg2 _ _ _ H H8).
        forward_reason.
        unfold pl_eq_lift in Hsif.
        rewrite H5 in Hsif.
        consider (fexprD f isti'); intros; try contradiction.
        exists x; split; auto.
        eapply FEIteF; eauto.
        apply pl_eq_F2OR in Hsif.
        unfold float_ge in *.
        unfold F2OR in *.
        consider f0; consider f1; intros; subst; auto; simpl in *;
        try lra; try solve [inversion Hsif; lra].
    - intros.
      inversion H0.
  Qed.      
  
  Lemma asReal_det :
    forall (p p' : pl_data) (r : R),
      asReal p r ->
      asReal p' r ->
      pl_eq p p'.
  Proof.
    unfold asReal.
    intros. rewrite <- H in H0.
    apply F2OR_pl_eq in H0. apply pl_symm. auto.
  Qed.

  Definition models (vars : list string) (ist : istate) (sst : Syntax.state) : Prop :=
    forall (s : string),
      (In s vars ->
      exists (d : pl_data),
        fm_lookup ist s = Some d /\
        asReal d (sst s)) /\
      (~In s vars -> fm_lookup ist s = None).

  Definition embedding : Type := list string -> ast -> Syntax.Formula.

  Definition embedding_correct1 (embed : embedding) : Prop :=
    forall (v : list string) (prg : ast) (is is' : istate) (ls ls' : Syntax.state) (tr : Stream.stream Syntax.state),
      models v is ls ->
      models v is' ls' ->
      eval is prg is' ->
      Semantics.eval_formula
        (embed v prg)
        (Stream.Cons ls (Stream.Cons ls' tr)).

  Definition embedding_correct2 (embed : embedding) : Prop :=
    forall (v : list string) (prg : ast) (is : istate) (ls : Syntax.state) (tr : Stream.stream Syntax.state),
      models v is ls ->
      ~(exists is', eval is prg is') ->
      ~(Semantics.eval_formula
        (Enabled (embed v prg))
        (Stream.Cons ls tr)).

  (* Here is a correct embedding function.
     Note that its correctness depends on the semantics being
     deterministic *)
  Definition embed_ex (v : list string) (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun lpre lpost =>
                    exists cpre cpost,
                      models v cpre lpre /\
                      models v cpost lpost /\
                      eval cpre prg cpost).


  (** Next, some definitions for Hoare-style reasoning about programs.
      We use this to implement weakest-precondition.
   **)
  Section Hoare.
    Variables (P : istate -> Prop) (c : ast) (Q : istate -> Prop).

    Definition HoareProgress : Prop :=
      forall s, P s -> exists s', eval s c s'.

    Definition HoarePreservation : Prop :=
      forall s, P s ->
           forall s', eval s c s' ->
                 Q s'.

    (* safety no longer needed *)

    Definition Hoare' : Prop :=
      (HoareProgress /\ HoarePreservation)%type.

    Definition Hoare : Prop :=
      (forall s, P s ->
            (exists s', eval s c s') /\
            (forall s', eval s c s' -> Q s'))%type.

  End Hoare.
  
End FloatEmbed.

(* The following is a Hoare logic implementation for floating-point language *)
(*Require Import Bound.*)
Import FloatEmbed.

Definition vmodels := models.

(** This is the semantic side condition **)
(* slightly different way of stating models_det facts *)
Definition SEMR (vs : list Var) (P : Syntax.state -> Prop) : Prop :=
  forall (c : istate) (a b : Syntax.state), vmodels vs c a -> vmodels vs c b -> P a -> P b.

Definition Hoare_ := Hoare.

(* These are no longer used; we're performing the abstraction at the level
   of fwp rather than here. This was due to underlying changes to bound.v *)
  Definition HoareA_all (vs : list string)
             (P : Syntax.state -> Prop) (c : ast) (Q : Syntax.state -> Prop)
    : Prop :=
    Hoare_ (fun fst => forall rst : Syntax.state, vmodels vs fst rst -> P rst)%type
           c
           (fun fst => forall rst : Syntax.state, vmodels vs fst rst -> Q rst)%type.

  Definition HoareA_ex (vs : list string)
             (P : Syntax.state -> Prop) (c : ast) (Q : Syntax.state -> Prop)
    : Prop :=
    Hoare_ (fun fst => exists rst : Syntax.state, vmodels vs fst rst /\ P rst)%type
           c
           (fun fst => exists rst : Syntax.state, vmodels vs fst rst /\ Q rst)%type.

  Definition fembed_ex :=
    embed_ex. 

  Lemma Hoare__embed :
    forall P c Q vs,
      Hoare_ P c Q ->
      (|-- fembed_ex vs c -->>
           Embed (fun st st' =>
                    exists fst,
                      vmodels vs fst st /\
                      (P fst ->
                       exists fst',
                         vmodels vs fst' st' /\
                         Q fst'))).
  Proof.
    simpl. intros. unfold tlaEntails. simpl.
    intros.
    fwd.
    unfold Hoare_, Hoare in H.
    exists x. unfold vmodels. split; auto.
    intros.
    exists x0.
    split; auto.
    specialize (H _ H4). fwd.
    auto.
  Qed.
    
  Lemma Hoare__skip :
    forall (P : istate -> Prop),
      Hoare_ P FSkip P.
  Proof.
    red. red. intros.
    split.
    { eexists; constructor. }
    { intros. inversion H0. subst. auto. }
  Qed.

  Lemma Hoare__seq :
    forall P Q R c1 c2,
      Hoare_ P c1 Q ->
      Hoare_ Q c2 R ->
      Hoare_ P (FSeq c1 c2) R.
  Proof.
    unfold Hoare_, Hoare.
    intros.
    split.
    { eapply H in H1.
      forward_reason.
      specialize (H0 _ (H2 _ H1)).
      forward_reason.
      eexists. econstructor; eauto. }
    { intros. inversion H2; subst; clear H2.
      specialize (H _ H1). fwd.
      specialize (H2 _ H6).
      specialize (H0 _ H2).
      fwd; auto. }
  Qed.
  
  (* this plus consequence should be enough to get our real assignment rule
   that talks about bounds *)
  Lemma Hoare__asn :
    forall P v e,
      Hoare_
        (fun fs : fstate =>
           exists val : float,
             fexprD e fs = Some val /\
             P (fstate_set fs v val))%type
        (FAsn v e)
        P.
  Proof.
    intros. red. red.
    intros. fwd.
    split.
    - eexists. constructor. eassumption.
    - intros. inversion H1; subst; clear H1.
      rewrite H6 in H. inversion H; subst; clear H. assumption.
  Qed.



  (* Calculating bounds for expressions *)
  Fixpoint fexpr_to_NowTerm (fx : fexpr) : NowTerm :=
    match fx with
    (*| FVar v   => VarNowN (vtrans_flt2tla ivs v)*)
    | FVar v => VarNowN v
    | FConst f => FloatN f
    | FPlus fx1 fx2 =>
      PlusN (fexpr_to_NowTerm fx1) (fexpr_to_NowTerm fx2)
    | FMinus fx1 fx2 =>
      MinusN (fexpr_to_NowTerm fx1) (fexpr_to_NowTerm fx2)
    | FMult fx1 fx2 =>
      MultN (fexpr_to_NowTerm fx1) (fexpr_to_NowTerm fx2)
    end.

  Require Import Bound2.

  (* need an implementation of bound_term *)
  Print All_predInt.
  Print predInt.
  (*Require Import Bound.*)
  (*Print Bound.bound_term.
  Print isVarValid.
  Print isFloatConstValid.
  Print fstate_lookup_force.
  Print isVarValid.
  Print fexpr.
   *)

  Print fstate_lookup.

  Fixpoint fstate_lookup_force (fs : fstate) (v : Var) : R :=
    match fs with
    | nil => 0%R (* "bogus" value *)
    | (v', f') :: fs' => if v ?[eq] v' then FloatToR f' else fstate_lookup_force fs' v
    end.

  (* unneeded, we use Flocq's is_finite instead *)
  (*
  Inductive isFloatConstValid : float -> Prop :=
  | valid_zero : forall s, isFloatConstValid (B754_zero _ _ s)
  | valid_finite : forall s m e (b : bounded prec emax m e = true),
      isFloatConstValid (B754_finite _ _ s m e b).
   *)

  Definition isVarValid (v:Var) (fState : fstate) : Prop
    :=
      exists f, fstate_lookup fState v = Some f /\ is_finite f = true.

  (*Require Import Bound.
  Print Bound.bound_term.
  Print fexpr.
  Print natBound.*)
  
  Fixpoint bound_fexpr (fx : fexpr) : All_predInt :=
    match fx with
    | FVar v =>
      {| lb := fun fst => fstate_lookup_force fst v;
         ub := fun fst => fstate_lookup_force fst v;
         (* TODO: this premise is suspect; perhaps with fwp it can be eliminated *)
         premise := fun fst => isVarValid v fst |}
        :: nil
    | FConst f =>
      {| lb := fun _ => FloatToR f;
         ub := fun _ => FloatToR f;
         premise := fun _ => is_finite f = true |} :: nil
    | FPlus fx1 fx2 =>
      cross absFloatPlus' (bound_fexpr fx1) (bound_fexpr fx2)
    | FMinus fx1 fx2 =>
      cross absFloatMinus' (bound_fexpr fx1) (bound_fexpr fx2)
    | FMult fx1 fx2 =>
      cross absFloatMult' (bound_fexpr fx1) (bound_fexpr fx2)
    end.

(*  
  Definition bounds_to_formula (sbt : singleBoundTerm) (fs : fstate) : (Prop * (R -> Prop)) :=
    denote_singleBoundTermNew fs sbt.
*)
    
  (* another lemma needed for bound_fexpr_sound *)
  Lemma fexpr_NowTerm_related_eval :
    forall fst,
    forall fx f,
      fexprD fx fst = Some f ->
      eval_NowTerm fst (fexpr_to_NowTerm fx) = Some f.
  Proof.
    Locate fplus.
    Print float_plus.
    induction fx; eauto;
    try (intros; simpl; simpl in *; fwd;
         unfold lift2, fplus, float_plus in *;
           consider (fexprD fx1 fst); intros; try congruence;
         consider (fexprD fx2 fst); intros; try congruence;
         erewrite IHfx1; eauto;
         erewrite IHfx2; eauto).
  Qed.

  Print predIntD.
  Check bound_fexpr.

  Lemma fstate_lookup_miss :
    forall fs v f,
      fstate_lookup fs v = Some f ->
      forall v' f',
        v <> v' ->
        fstate_lookup ((v',f') :: fs) v = Some f.
  Proof.
    induction fs; simpl; intros.
    { congruence. }
    { destruct a.
      consider (v ?[eq] v'); intros; congruence. }
  Qed.

  (* TODO: include the fact that expr evaluates successfully in
     the soundness statement *)
  Lemma bound_fexpr_sound :
    forall (fx : fexpr) (fs : fstate) (f : float),
      fexprD fx fs = Some f ->      
      All_predIntD (bound_fexpr fx) f fs.
  Proof.
    induction fx; simpl in *; intros.
    { generalize dependent v. generalize dependent f.
      induction fs; simpl in *; intros; try congruence.
      destruct a. unfold All_predIntD in *.
      constructor; auto.
      consider (v ?[eq] v0); intros.
      {
        inversion H0; subst.
        unfold predIntD; simpl.
        intros.
        unfold isVarValid in H. fwd.
        simpl in H.
        consider (v0 ?[eq] v0); intros; try congruence.
        inversion H2; subst.
        split; auto.
        unfold fstate_lookup_force.
        unfold FloatToR.
        lra.
      }
      {
      specialize (IHfs _ _ H0). inversion IHfs; subst; clear IHfs.
      unfold predIntD in *. simpl in *.
      intros.
      unfold isVarValid in *. fwd.
      destruct H3.
      {
        eexists; split; eauto.
        apply fstate_lookup_miss with (v' := v0) (f' := f0) in H0; auto.
        rewrite H0 in H1. inversion H1; subst.
        auto. }
      {
        split; auto.
        consider (v ?[eq] v0); intros; congruence. } } }
    {
      inversion H; subst. unfold All_predIntD.
      constructor; auto.
      unfold predIntD. intros.
      simpl in H0.
      split; auto.
      simpl.
      unfold FloatToR; lra. }
    {
      unfold lift2 in *.
      consider (fexprD fx1 fs); intros; try congruence.
      consider (fexprD fx2 fs); intros; try congruence.
      inversion H1; subst.
      specialize (IHfx1 _ _ H).
      specialize (IHfx2 _ _ H0).
      generalize (absFloatPlus'_ok); intros.
      generalize (@cross_In _ _ _ absFloatPlus' (bound_fexpr fx1) (bound_fexpr fx2)); intros.
      unfold All_predIntD in *.
      apply Forall_forall; intros.
      specialize (H3 x). destruct H3. fwd.
      subst.
      apply H2.
      eapply Forall_forall in IHfx1; eauto.
      eapply Forall_forall in IHfx2; eauto. }
      (* TODO the following two are copy pastes of the previous one.
         We should automate this more. *)    
    {
      unfold lift2 in *.
      consider (fexprD fx1 fs); intros; try congruence.
      consider (fexprD fx2 fs); intros; try congruence.
      inversion H1; subst.
      specialize (IHfx1 _ _ H).
      specialize (IHfx2 _ _ H0).
      generalize (absFloatMinus'_ok); intros.
      generalize (@cross_In _ _ _ absFloatMinus' (bound_fexpr fx1) (bound_fexpr fx2)); intros.
      unfold All_predIntD in *.
      apply Forall_forall; intros.
      specialize (H3 x). destruct H3. fwd.
      subst.
      apply H2.
      eapply Forall_forall in IHfx1; eauto.
      eapply Forall_forall in IHfx2; eauto. }
    {
      unfold lift2 in *.
      consider (fexprD fx1 fs); intros; try congruence.
      consider (fexprD fx2 fs); intros; try congruence.
      inversion H1; subst.
      specialize (IHfx1 _ _ H).
      specialize (IHfx2 _ _ H0).
      generalize (absFloatMult'_ok); intros.
      generalize (@cross_In _ _ _ absFloatMult' (bound_fexpr fx1) (bound_fexpr fx2)); intros.
      unfold All_predIntD in *.
      apply Forall_forall; intros.
      specialize (H3 x). destruct H3. fwd.
      subst.
      apply H2.
      eapply Forall_forall in IHfx1; eauto.
      eapply Forall_forall in IHfx2; eauto. }
  Qed.
      
  (* Useful prop combinator *)
  Fixpoint AnyOf (Ps : list Prop) : Prop :=
    match Ps with
    | nil => False
    | P :: Ps => P \/ AnyOf Ps
    end%type.

  (* Lemmas aboutt Forall, needed for HoareA_ex_asn *)
  Lemma Forall_impl : forall T (P Q : T -> Prop) ls,
      List.Forall (fun x => P x -> Q x) ls ->
      (List.Forall P ls -> List.Forall Q ls).
  Proof.
    induction 2.
    - constructor.
    - inversion H; clear H; subst.
      constructor; eauto.
  Qed.

  Lemma Forall_tauto : forall T (P : T -> Prop) ls,
      (forall x, P x) ->
      List.Forall P ls.
  Proof.
    induction ls; simpl; intros; eauto.
  Qed.

  (*
  Lemma floatConstValid_toR :
    forall val,
      isFloatConstValid val -> exists r,
        (F2OR val = Some r)%type.
  Proof.
    intros.
    unfold isFloatConstValid in H.
    destruct val; try contradiction; solve [eexists; reflexivity].
  Qed.
*)


  (* original *)
  Check bound_fexpr_sound.

  Lemma Hoare__bound_asn :
    forall (P : _ -> Prop) v e,
      Hoare_ (fun fst : fstate =>
                exists res, fexprD e fst = Some res /\
                       (forall res',
                           All_predIntD (bound_fexpr e) res' fst ->
                           P (fstate_set fst v res')))
             (FAsn v e)
             P.
  Proof.
    intros.
    red; red. intros.
    fwd.
    split.
    { eexists; econstructor; eauto. }
    { intros.
      inversion H1; subst; clear H1.
      rewrite H in H6. inversion H6; subst.
      generalize bound_fexpr_sound; intro Hbfs.
      specialize (Hbfs _ _ _ H).
      auto. }
  Qed.

  Lemma Hoare__conseq :
    forall (P P' Q Q' : fstate -> Prop) (c : fcmd),
      (forall (st : fstate), P st  -> P' st) ->
      (forall (st : fstate), Q' st -> Q  st) ->
      Hoare_ P' c Q' ->
      Hoare_ P c Q.
  Proof.
    intros. unfold Hoare_, Hoare in *.
    intros. apply H in H2. apply H1 in H2. fwd.
    split; try eexists; eauto.
  Qed.

  (* A couple of lemmas used for ITE rule *)
  Lemma Hoare__or :
    forall (P1 P2 Q : _ -> Prop) c,
      Hoare_ P1 c Q ->
      Hoare_ P2 c Q ->
      Hoare_ (fun st => P1 st \/ P2 st)%type c Q.
  Proof.
    intros.
    unfold Hoare_, Hoare in *.
    intros.
    destruct H1; eauto.
  Qed.    

  Lemma Hoare__False :
    forall (P : _ -> Prop) c,
      Hoare_ (fun _ => False) c P.
  Proof.
    intros.
    unfold Hoare_, Hoare. intros. contradiction.
  Qed.

  (*
  Definition maybe_lt0 (sbts : list singleBoundTerm) (fst : fstate) : Prop :=
    AnyOf (List.map
             (fun sbt =>
                (lb sbt fst <  0)%R /\
                (premise sbt fst)) sbts).

  Definition maybe_ge0 (sbts : list singleBoundTerm) (fst : fstate) : Prop :=
    AnyOf (List.map
             (fun sbt =>
                (ub sbt fst >=  0)%R /\
                (premise sbt fst)) sbts).
*)

  (* proposed new defs *)
  (*
  (* based on Hoare__bound_asn *)
  (* defs, v2. better, but not in a useful form for things to be provable *)
    Definition maybe_lt0 (fx : fexpr) (fst : fstate) (r : R) : Prop :=
    AnyOf (List.map
             (fun sbt : singleBoundTerm =>
                let '(prem, bound) := bounds_to_formula sbt fst in
                (lb sbt fst < 0)%R /\
                prem /\
                bound r
             )
             (bound_fexpr fx)).

  Definition maybe_ge0 (fx : fexpr) (fst : fstate) (r : R) : Prop :=
    AnyOf (List.map
             (fun sbt : singleBoundTerm =>
                let '(prem, bound) := bounds_to_formula sbt fst in
                (ub sbt fst >= 0)%R /\
                prem /\
                bound r
             )
             (bound_fexpr fx)).  
   *)
  
  Lemma or_distrib_imp :
    forall A B C : Prop,
      (A \/ B -> C) <->
      (A -> C) /\ (B -> C).
  Proof.
    tauto.
  Qed.

  Lemma and_distrib_or :
    forall A B C : Prop,
      A /\ (B \/ C) <->
      (A /\ B) \/ (A /\ C).
  Proof.
    tauto.
  Qed.

  Lemma float_lt_ge_trichotomy :
    forall f f', (float_lt f f' \/ float_ge f f').
  Proof.
    intros. unfold float_lt, float_ge.
    lra.
  Qed.

  Lemma float_lt_ge_trichotomy_contra :
    forall f f', float_lt f f' /\ float_ge f f' -> False.
  Proof.
    intros. unfold float_lt, float_ge in H. lra.
  Qed.

  Check Hoare__bound_asn.
  Check All_predIntD.
  
  Lemma Hoare__bound_ite :
    forall ex (P Q1 Q2 : _ -> Prop) c1 c2,
      Hoare_ Q1 c1 P ->
      Hoare_ Q2 c2 P ->
      Hoare_ (fun fst =>
                exists res, fexprD ex fst = Some res /\
                       let bs := bound_fexpr ex in
                       (maybe_lt0 bs fst -> Q1 fst) /\
                       (maybe_ge0 bs fst -> Q2 fst) /\
                       (AnyOf (List.map
                                 (fun sbt => let '(prem, _) := denote_singleBoundTermNew fst sbt in prem)
                                 (bound_fexpr ex))))%type
             (FIte ex c1 c2)
             P.
  (* original *)
  (*
Lemma Hoare__bound_ite :
    forall ex (P Q1 Q2 : _ -> Prop) c1 c2,
      Hoare_ Q1 c1 P ->
      Hoare_ Q2 c2 P ->
      Hoare_ (fun fst =>
                exists res, fexprD ex fst = Some res /\
                       let bs := bound_fexpr ex in
                       (maybe_lt0 bs fst -> Q1 fst) /\
                       (maybe_ge0 bs fst -> Q2 fst) /\
                       (AnyOf (List.map
                                 (fun sbt => let '(prem, _) := denote_singleBoundTermNew fst sbt in prem)
                                 (bound_fexpr ex))))%type
             (FIte ex c1 c2)
             P.
   *)
  Proof.
  intros.
  generalize (bound_fexpr_sound ex (bound_fexpr ex) eq_refl).
  induction 1.
  { simpl. eapply Hoare__conseq.
    3: eapply Hoare__False.
    - simpl. intros. fwd. auto.
    - exact (fun _ x => x). }
  { simpl.
    eapply Hoare__conseq.
    2: exact (fun _ x => x).
    unfold maybe_lt0. unfold maybe_ge0.
    simpl. intros.
    repeat setoid_rewrite or_distrib_imp in H3.
    repeat setoid_rewrite and_distrib_or in H3.
    eapply H3.
    eapply Hoare__conseq.
    2: exact (fun _ x => x).
    2: eapply Hoare__or.
    3: eapply IHForall.
    simpl. intros. fwd.
    destruct H3.
    { fwd.
      left.
      exact (conj (Logic.ex_intro (fun x0 => eq (fexprD ex st) (Some x0)) _ H3) (conj H6 (conj H8 (conj H7 (conj H4 H5))))). }
    { right.
      fwd.
      unfold maybe_lt0, maybe_ge0.
      eexists. split; eauto. }
    clear H2 IHForall.
    do 2 red. intros.
    fwd.
    simpl in H1.
    do 2 red in H, H0.
    specialize (H1 _ _ H2 H3). fwd.
    assert (x1 = x0).
    { rewrite H1 in H2. inversion H2; auto. }
    subst.
    destruct (float_lt_ge_trichotomy x0 fzero).
    { pose proof H11 as H11'.
      unfold float_lt in H11. simpl in H11.
      unfold F2OR in H8. consider x0; intros; try congruence.
      { simpl in H12. lra. }
      { inversion H11.
        assert (x2 < 0)%R.
        { rewrite <- H14 in H9.
          simpl in H12.
          lra. }
        assert (lb x s < 0)%R by lra.
        fwd.
        specialize (H _ H6). fwd.
        split.
        { eexists. eapply FEIteT; eauto. }
        { intros. inversion H17; subst; clear H17; auto.
          rewrite H2 in H22. inversion H22; subst.
          generalize (float_lt_ge_trichotomy_contra _ _ (conj H11' H24)).
          intro; contradiction. } } }
    { pose proof H11 as H11'.
      unfold float_ge in H11. simpl in H11.
      unfold F2OR in H8. consider x0; intros; try congruence.
      { inversion H11. subst.
        apply Rle_ge in H10.
        fwd.
        specialize (H0 _ H7). fwd.
        split.
        { eexists. eapply FEIteF; eauto. }
        { intros. inversion H13; subst; clear H13; auto.
          rewrite H2 in H18. inversion H18; subst.
          generalize (float_lt_ge_trichotomy_contra _ _ (conj H20 H11')).
          intros; contradiction. } }
      { inversion H11.
        assert (x2 >= 0)%R.
        { simpl in H12.
          rewrite H14 in H12.
          assumption. }
        assert (ub x s >= 0)%R by lra.
        fwd.
        specialize (H0 _ H7). fwd.
        split.
        { eexists. eapply FEIteF; eauto. }
        { intros.
          inversion H17; subst; clear H17; auto.
          rewrite H2 in H22. inversion H22; subst.
          generalize (float_lt_ge_trichotomy_contra _ _ (conj H24 H11')).
          intros; contradiction. } } } }
  Qed.

  (* proof of an alternate version *)
(*    
  intros.
  unfold maybe_ge0, maybe_lt0.
  generalize (bound_fexpr_sound ex (bound_fexpr ex) eq_refl).
  induction 1.
  { simpl. eapply Hoare__conseq.
    3: eapply Hoare__False.
    - simpl. intros. fwd. auto.
    - exact (fun _ x => x). }
  { simpl.
    eapply Hoare__conseq.
    2: exact (fun _ x => x).
    simpl. intros.
    repeat setoid_rewrite or_distrib_imp in H3.
    repeat setoid_rewrite and_distrib_or in H3.
    eapply H3.
    eapply Hoare__conseq.
    2: exact (fun _ x => x).
    2: eapply Hoare__or.
    3: eapply IHForall.
    simpl. intros. fwd.
    destruct H3.
    { fwd.
      left.
      (*exact (conj (Logic.ex_intro (fun x0 => eq (fexprD ex st) (Some x0)) _ H3) (conj H6 (conj H8 (conj H7 (conj H4 H5))))). }*)
      exact (conj (Logic.ex_intro (fun x0 => eq (fexprD ex st) (Some x0)) _ H3) (conj H6 (conj H8 (conj H7 (conj H4 H5))))). }
    { right.
      fwd.
      eexists. split; eauto. }
    clear H2 IHForall. (* maybe don't clear H2? *)
    do 2 red. intros.
    fwd.
    simpl in H1.
    do 2 red in H, H0.
    specialize (H1 _ _ H2 H3). fwd.
    assert (x1 = x0).
    { rewrite H1 in H2. inversion H2; auto. }
    subst.
    destruct (float_lt_ge_trichotomy x0 fzero).
    { pose proof H11 as H11'.
      unfold float_lt in H11. simpl in H11.
      unfold F2OR in H8. consider x0; intros; try congruence.
      { simpl in H12. lra. }
      { inversion H11.
        assert (x2 < 0)%R.
        { rewrite <- H14 in H9.
          simpl in H12.
          lra. }
        assert (lb x s < 0)%R by lra.
        rewrite H2 in *. simpl in *. subst.
        specialize (H6 (conj H15 (conj H3 (conj H9 H10)))).
        specialize (H _ H6). fwd.
        split.
        { eexists. eapply FEIteT; eauto. }
        { intros.
          inversion H14; subst; clear H14; auto.
          rewrite H2 in H20. inversion H20; subst.
          generalize (float_lt_ge_trichotomy_contra _ _ (conj H11' H22)).
          intro; contradiction. } } }
    { pose proof H11 as H11'.
      unfold float_ge in H11. simpl in H11.
      unfold F2OR in H8. consider x0; intros; try congruence.
      { inversion H11. subst.
        pose proof H10 as H10'.
        apply Rle_ge in H10.
        fwd.
        rewrite H2 in *. simpl in *. subst.
        specialize (H7 (conj H10 (conj H3 (conj H9 H10')))).
        specialize (H0 _ H7). fwd.
        split.
        { eexists. eapply FEIteF; eauto. }
        { intros. inversion H13; subst; clear H13; auto.
          rewrite H2 in H18. inversion H18; subst.
          generalize (float_lt_ge_trichotomy_contra _ _ (conj H20 H11')).
          intros; contradiction. } }
      { inversion H11.
        assert (x2 >= 0)%R.
        { simpl in H12.
          rewrite H14 in H12.
          assumption. }
        assert (ub x s >= 0)%R by lra.
        rewrite H2 in *. simpl in *. subst.
        specialize (H7 (conj H15 (conj H3 (conj H9 H10)))). fwd.
        specialize (H0 _ H7). fwd.
        split.
        { eexists. eapply FEIteF; eauto. }
        { intros.
          inversion H14; subst; clear H14; auto.
          rewrite H2 in H20. inversion H20; subst.
          generalize (float_lt_ge_trichotomy_contra _ _ (conj H22 H11')).
          intros; contradiction. } } } }
Qed.
*)

(*
(* propsed alternate ITE rule: *)
(fun fst =>
                        exists res, fexprD e fst = Some res /\
                               exists r, F2OR res = Some r /\
                                    (* RIGHT ANSWER (we think): *)
                                    (forall r, F2OR res = Some r -> maybe_lt0 e fst r -> fwp c1 P fst) /\
                                    (maybe_ge0 e fst r -> fwp c2 P fst) /\
                                    (AnyOf (List.map
                                              (fun sbt => let '(prem, _) := denote_singleBoundTermNew fst sbt in prem)
                                              (bound_fexpr e))))%type

 *)

  (*
  (* to be used with our new vc gen *)
  Lemma Hoare__seq' :
    forall P Q R c1 c2,
      Hoare_ 

  Lemma Hoare__seq :
    forall P Q R c1 c2,
      Hoare_ P c1 Q ->
      Hoare_ Q c2 R ->
      Hoare_ P (FSeq c1 c2) R.
  Proof.
   *)

  Print fexpr.

  Check in_dec.
  Print fstate_lookup.
  Print fstate_lookup.

  Fixpoint varmap_has_var (vs : list Var) (v : Var) : bool :=
    match vs with
    | nil => false
    | vh :: vt => if v ?[eq] vh then true
                  else varmap_has_var vt v
    end.

  Fixpoint fexpr_check (e : fexpr) (vs : list Var) : bool :=
    match e with
    | FVar v => varmap_has_var vs v
    | FConst _ => true
    | FPlus e1 e2 => andb (fexpr_check e1 vs) (fexpr_check e2 vs)
    | FMinus e1 e2 => andb (fexpr_check e1 vs) (fexpr_check e2 vs)
    | FMult e1 e2 => andb (fexpr_check e1 vs) (fexpr_check e2 vs)
    end.

  (* new weakest-precondition function *)
  (* P is postcondition *)
  (* vs is var list going into the command *)
  
  Fixpoint fpig_vcgen
           (c : fcmd)
           (vs : list Var)
           (P : fstate -> Prop) : (list Var * (fstate -> Prop)) :=
    match c with
    | FSkip => (vs, P)
    | FSeq c1 c2 =>
      let (vs', _) := fpig_vcgen c1 vs (fun _ => True) in
      let (vs'', P') := fpig_vcgen c2 vs' P in
      let (_, P'') := fpig_vcgen c1 vs P' in
      (vs'', P'')
    | FAsn v e =>
      if fexpr_check e vs then
        (v :: vs, (fun fs  =>
                     AnyOf
                       (map
                          (fun sbt : singleBoundTerm =>
                             let '(pred, bound) := bounds_to_formula sbt fs in
                             pred /\
                             (forall (val : float) (r : R),
                                 F2OR val = Some r ->
                                 bound r -> P (fstate_set fs v val)))
                          (bound_fexpr e))))
      else
        (v :: vs, (fun _ => False))
    | FIte e c1 c2 =>
      if fexpr_check e vs then
        (vs, (fun fs =>
                        (*exists res, fexprD e fst = Some res /\*)
                               (let bs := bound_fexpr e in
                                (maybe_lt0 bs fs -> snd (fpig_vcgen c1 vs P) fs) /\
                                (maybe_ge0 bs fs -> snd (fpig_vcgen c2 vs P) fs) /\
                                AnyOf
                                  (map
                                     (fun sbt : singleBoundTerm =>
                                        let '(prem, _) := denote_singleBoundTermNew fs sbt in prem)
                                     bs))))
      else
        (vs, (fun _ => False))
    | FFail => (vs, (fun _ => False))
    end.

  Print fstate.

  Check (forall a b : string, a ?[eq] b = true).
  
  Fixpoint fstate_has_var (fst : fstate) (v : Var) :=
    match fst with
    | nil => false
    | (v',_) :: fst' => if v ?[eq] v' then true
                       else fstate_has_var fst' v
    end.

  Lemma exists_and_pull :
    forall {T : Type} (P : T -> Prop) (P' : Prop),
      (exists (e : T), P e) -> P' ->
      exists (e : T), (P e /\ P').
  Proof.
    intros.
    fwd.
    exists x. auto.
  Qed.
  
  Fixpoint fstate_has_vars (fst : fstate) (vs : list Var) :=
    match vs with
    | nil => true
    | v :: vs' => andb (fstate_has_var fst v) (fstate_has_vars fst vs')
    end.

  Lemma fstate_has_var_sound :
    forall fst a,
      fstate_has_var fst a = true ->
      exists (d : float), fstate_lookup fst a = Some d.
  Proof.
    induction fst; intros; simpl in *; try congruence.
    destruct a.
    consider (a0 ?[eq] v); intros.
    { eexists; reflexivity. }
    { auto. }
  Qed.

  Lemma varmap_has_var_sound :
    forall vs v,
      varmap_has_var vs v = true ->
      forall fst,
        fstate_has_vars fst vs = true ->
        exists d : float, fstate_lookup fst v = Some d.
  Proof.
    induction vs; intros; simpl in *; try congruence.
    consider (v ?[eq] a); intros; subst.
    { clear IHvs.
      apply Bool.andb_true_iff in H0. fwd.
      apply fstate_has_var_sound; auto. }
    { apply Bool.andb_true_iff in H0. fwd.
      apply IHvs; auto. }
  Qed.

  Lemma fexpr_check_sound :
    forall fx vs,
      fexpr_check fx vs = true ->
      forall fst,
        fstate_has_vars fst vs = true ->
        exists (d : float), fexprD fx fst = Some d.
  Proof.
    induction fx; intros; simpl in *;
    (* take care of recursive cases *)
    try (unfold lift2;
         apply Bool.andb_true_iff in H; fwd;
         specialize (IHfx1 _ H _ H0);
         specialize (IHfx2 _ H1 _ H0);
         fwd;
         rewrite H2; rewrite H3;
         eexists; reflexivity).
    { generalize (varmap_has_var_sound _ _ H _ H0); intro.
      auto. }
    { eexists; reflexivity. }
  Qed.

  (* TODO: weaker Hoare rule for assignment, for use in the
     vcgen correctness theorem for the variable list *)
(*
  Lemma Hoare__asn_vmap :
  forall v f vs,
    Hoare_ (fun fst => fstate_has_vars fst vs = true)
           (FAsn v f)
           (fun fst' => fstate_has_vars fst' (v :: vs) = true).
Proof.
    intros.
    unfold Hoare_, Hoare.
    intros. split.
    {
      generalize fexpr_check_sound; intro.
      eexists. econstructor.
      specia
      
      
      
      
    induction f; intros; simpl in *.
    { unfold Hoare_, Hoare.
      intros.
      split.
      { eexists. econstructor.
        SearchAbout fstate_has_vars.
        Check fexpr_check_sound.
        eapply fexpr_check_sound.
        simpl.
        SearchAbout fstate_has_vars
    
    
    
  Admitted.
 *)

  Lemma fstate_has_var_fstate_set :
    forall (fst : fstate) (v : Var) (val : float),
      fstate_has_var (fstate_set fst v val) v = true.
  Proof.
    induction fst; intros; simpl;
    consider (v ?[eq] v); intros; congruence.
  Qed.

  Lemma fstate_has_var_fstate_set' :
    forall vs fst v val,
      fstate_has_vars fst vs = true ->
      fstate_has_vars (fstate_set fst v val) vs = true.
  Proof.
    induction vs; intros; simpl in *; auto.
    apply Bool.andb_true_iff in H. fwd.
    consider (a ?[eq] v); intros;
    apply Bool.andb_true_iff; split; auto.
  Qed.

  (* doesn't decompose in this way sadly... *)
  (* used to prove the full correctness theorem.
     basically states that var-map checking doesn't depend on VC gen *)

  Print Hoare.

(*
  Lemma fpig_vcgen_var_correct :
    forall (c : fcmd) (vs : list Var) (P : fstate -> Prop),
      let (vs', P') := fpig_vcgen c vs P in
      forall (fst : fstate),
        fstate_has_vars fst vs = true ->
        forall (fst' : fstate),
          eval fst c fst' -> fstate_has_vars fst' vs = true.
  Proof.
    induction c.
    { intros. simpl. lazy.
 *)

  Fixpoint vars_subset (lhs : list Var) (rhs : list Var) : bool :=
    match lhs with
    | nil => true
    | v :: lhs' => andb (varmap_has_var rhs v) (vars_subset lhs' rhs)
    end.
  
  Lemma vars_subset_cons:
      forall vs vs' v, vars_subset vs vs' = true ->
                  vars_subset vs (v :: vs') = true.
    Proof.
      induction vs; simpl; try reflexivity; intros.
      consider (a ?[eq] v); intros; simpl.
      { apply Bool.andb_true_iff in H. fwd. subst. auto. }
      { apply Bool.andb_true_iff. apply Bool.andb_true_iff in H. fwd.
        auto. }
    Qed.

    Lemma vars_subset_sound :
      forall vs vs' a,
        varmap_has_var vs a = true ->
        vars_subset vs vs' = true ->
        varmap_has_var vs' a = true.
    Proof.
      induction vs; simpl; try congruence.
      intros.
      apply Bool.andb_true_iff in H0. fwd.
      consider (a0 ?[eq] a); intros; subst; auto.
    Qed.
      
  Lemma vars_subset_trans :
    forall (vs vs' vs'': list Var),
      vars_subset vs vs' = true -> vars_subset vs' vs'' = true ->
      vars_subset vs vs'' = true.
  Proof.
    induction vs; simpl; try reflexivity; intros.
    apply Bool.andb_true_iff; apply Bool.andb_true_iff in H. fwd.
    specialize (IHvs _ _ H1 H0). split; auto.
    eapply vars_subset_sound; eauto.
  Qed.

  Lemma vars_subset_refl :
    forall vs, vars_subset vs vs = true.
  Proof.
    induction vs; simpl; try reflexivity.
    consider (a ?[eq] a); intros; try congruence.
    simpl. apply vars_subset_cons. auto.
  Qed.

  Lemma fstate_has_var_varmap :
    forall vs fst a,
      fstate_has_vars fst vs = true ->
      varmap_has_var vs a = true ->
      fstate_has_var fst a = true.
  Proof.
    induction vs; simpl; intros; try congruence.
    apply Bool.andb_true_iff in H. fwd.
    consider (a0 ?[eq] a); intros; subst; auto.
  Qed.
  
  Lemma vars_subset_sound' :
    forall vs' vs fst,
      fstate_has_vars fst vs = true ->
      vars_subset vs' vs = true ->
      fstate_has_vars fst vs' = true.
  Proof.
    induction vs'; simpl; intros; auto.
    apply Bool.andb_true_iff. apply Bool.andb_true_iff in H0. fwd.
    split; auto.
    eapply fstate_has_var_varmap; eauto.
    eapply IHvs'; eauto.
  Qed.

  Lemma fpig_vcgen_var_indep :
    forall c vs P P',
      fst (fpig_vcgen c vs P) = fst (fpig_vcgen c vs P').
  Proof.
    induction c; simpl; intros; try reflexivity.
    { repeat match goal with
             | |- context[let (_,_) := ?X in _] => consider X; intros
             end.
      simpl.
      specialize (IHc2 l P' P).
      rewrite H2 in IHc2.
      rewrite H0 in IHc2.
      simpl in IHc2; inversion IHc2; subst.
      reflexivity. }
    { destruct (fexpr_check f vs); reflexivity. }
    { destruct (fexpr_check f vs); reflexivity. }
  Qed.
 
  (* partial correctness *)
  Lemma fpig_vcgen_var_correct :
    forall (c : fcmd) (vs : list Var) (P : fstate -> Prop) (fst fst' : fstate),
      fstate_has_vars fst vs = true ->
      eval fst c fst' ->
      let (vs', P') := fpig_vcgen c vs P in
      (fstate_has_vars fst' vs' = true /\
       vars_subset vs vs' = true).
  Proof.
    induction c.
    { intros. simpl.
      inversion H0; subst; clear H0.

      generalize IHc1; intro IHc1'.
      specialize (IHc1' vs (fun _ => True)).
      consider (fpig_vcgen c1 vs (fun _ => True)); intros.
      specialize (IHc2 l P).
      consider (fpig_vcgen c2 l P); intros.
      specialize (IHc1 vs P1).
      consider (fpig_vcgen c1 vs P1); intros.

      assert (l = l1).
      { generalize (fpig_vcgen_var_indep c1 vs (fun _ => True) P1); intros.
        rewrite H0 in H3. rewrite H2 in H3. simpl in H3. auto. }

      subst.
      specialize (IHc1 _ _ H H4). fwd.
      specialize (IHc2 _ _ H3 H6). fwd.
      split; auto.
      eapply vars_subset_trans; eauto. }
    { simpl; intros.
      inversion H0; subst; split; auto.
      apply vars_subset_refl. }
    { simpl; intros.
      inversion H0; subst; clear H0.
      consider (fexpr_check f vs); intros.
      { simpl.
        consider (v ?[eq] v); intros; try congruence.
        simpl. split.
        { apply fstate_has_var_fstate_set'. auto. }
        { apply vars_subset_cons. apply vars_subset_refl. } }
      { simpl.
        consider (v ?[eq] v); intros; try congruence.
        simpl. split.
        { apply fstate_has_var_fstate_set'. auto. }
        { apply vars_subset_cons. apply vars_subset_refl. } } }
    { simpl; intros.
      inversion H0; subst; clear H0.
      { specialize (IHc1 _ P _ _ H H8).
        consider (fexpr_check f vs); intros.
        { consider (fpig_vcgen c1 vs P); intros.
          fwd. split.
          { eapply vars_subset_sound'; eauto. }
          { apply vars_subset_refl. } }
        { consider (fpig_vcgen c1 vs P); intros.
          fwd. split.
          { eapply vars_subset_sound'; eauto. }
          { eapply vars_subset_refl; eauto. } } }
      { specialize (IHc2 _ P _ _ H H8).
        consider (fexpr_check f vs); intros.
        { consider (fpig_vcgen c2 vs P); intros.
          fwd. split.
          { eapply vars_subset_sound'; eauto. }
          { apply vars_subset_refl. } }
        { consider (fpig_vcgen c2 vs P); intros.
          fwd. split.
          { eapply vars_subset_sound'; eauto. }
          { apply vars_subset_refl. } } } }
    { intros. simpl.
      inversion H0. }
  Qed.

  Require Import Coq.Logic.ClassicalFacts.
  Axiom pe_ax : prop_extensionality.

  Lemma vars_subset_fstate :
    forall vs' s vs,
      fstate_has_vars s vs = true ->
      vars_subset vs' vs = true ->
      fstate_has_vars s vs' = true.
  Proof.
    induction vs'; intros; simpl in *; auto.
    apply Bool.andb_true_iff.
    apply Bool.andb_true_iff in H0. fwd.
    SearchAbout fstate_has_var.
    generalize (fstate_has_var_varmap _ _ _ H H0); intros.
    split; auto.
    eapply IHvs'; eauto.
  Qed.

  Lemma fpig_vcgen_correct :
    forall (c : fcmd) (vs : list Var) (P : fstate -> Prop),
      let (vs',P') := fpig_vcgen c vs P in
       Hoare_ (fun fst => P' fst /\ fstate_has_vars fst vs = true) c (fun fst' => P fst' /\ fstate_has_vars fst' vs' = true).
  Proof.
    induction c; intros.
    { simpl.
      generalize IHc1; intro IHc1'.
      specialize (IHc1' vs (fun _ => True)). simpl in IHc1'.
      consider (fpig_vcgen c1 vs (fun _ : fstate => True)); intros.
      specialize (IHc2 l P).
      consider (fpig_vcgen c2 l P); intros.
      specialize (IHc1 vs P1).
      consider (fpig_vcgen c1 vs P1); intros.
      generalize fpig_vcgen_var_indep; intros.
      specialize (H2 c1 vs (fun _ => True) P1).
      rewrite H, H1 in H2. simpl in H2. inversion H2; subst.

      eapply Hoare__conseq.
      3: eapply Hoare__seq.
      4: eapply IHc2.
      3: eapply IHc1.
      { intros. fwd. auto. }
      { intros. fwd. auto. } }
    { simpl. apply Hoare__skip. }
    { simpl.
      consider (fexpr_check f vs); intros.
      { eapply Hoare__conseq.
        3: eapply Hoare__bound_asn.
        { intros. simpl in *. fwd.
          apply fexpr_check_sound with (fst := st) in H; eauto. fwd.
          eexists. split; [eauto|].
          instantiate (1 := (fun fst => P fst /\ fstate_has_vars fst (v :: vs) = true)). simpl.
          consider (v ?[eq] v); intros; try congruence.
          simpl.

          replace (fun sbt : singleBoundTerm =>
                     premise sbt st /\
                     (forall (val : float) (r : R),
                         F2OR val = Some r ->
                         (lb sbt st <= r <= ub sbt st)%R -> P (fstate_set st v val)))
          with
          (fun sbt : singleBoundTerm =>
             premise sbt st /\
             (forall (val : float) (r : R),
                 F2OR val = Some r ->
                 (lb sbt st <= r <= ub sbt st)%R -> P (fstate_set st v val) /\ fstate_has_vars (fstate_set st v val) vs = true)) in H0; auto.

          Require Import Coq.Logic.FunctionalExtensionality.

          extensionality sbt.

          replace ((forall (val : float) (r : R),
                       F2OR val = Some r ->
                       (lb sbt st <= r <= ub sbt st)%R -> P (fstate_set st v val)))
          with
          (forall (val : float) (r : R),
              F2OR val = Some r ->
              (lb sbt st <= r <= ub sbt st)%R -> P (fstate_set st v val) /\ fstate_has_vars (fstate_set st v val) vs = true); auto.

          extensionality val.
          extensionality r.

          extensionality Hn.
          extensionality Hn2.
          apply fstate_has_var_fstate_set' with (v := v) (val := val) in H1.
          apply pe_ax.
          split; intros; fwd; auto. }
        intros. simpl in *. auto. }
      { do 2 red. intros. fwd. contradiction. } }
    { simpl.
      consider (fexpr_check f vs); intros.
      { eapply Hoare__conseq.
        3: eapply Hoare__bound_ite.
        2: instantiate (1 := (fun st => P st /\ fstate_has_vars st vs = true)).
        2: eauto.
        2: instantiate (1 := (fun fst => snd (fpig_vcgen c1 vs P) fst /\ fstate_has_vars fst vs = true)).
        3: instantiate (1 := (fun fst => snd (fpig_vcgen c2 vs P) fst /\ fstate_has_vars fst vs = true)).
        { intros. fwd.
          generalize (fexpr_check_sound _ _ H _ H1). intros. fwd.
          eexists. split; eauto.
          generalize dependent (bound_fexpr f). intros.
          split; auto. }
        { specialize (IHc1 vs P).
          consider (fpig_vcgen c1 vs P); intros.
          simpl.
          do 2 red. do 2 red in IHc1. intros. fwd.
          specialize (IHc1 s). fwd.
          split; [eexists; eauto|].
          intros.

          Check fpig_vcgen_var_correct.

          generalize (fpig_vcgen_var_correct c1 vs P s s').
          intros. fwd.
          rewrite H0 in H6. fwd.
          specialize (H4 _ H5).
          fwd.
          split; auto.


          idtac.

          eapply vars_subset_fstate; eauto. }
        { specialize (IHc2 vs P).
          consider (fpig_vcgen c2 vs P); intros.
          simpl.
          do 2 red. do 2 red in IHc2. intros. fwd.
          specialize (IHc2 s). fwd.
          split; [eexists; eauto|].
          intros.

          generalize (fpig_vcgen_var_correct c2 vs P s s').
          intros. fwd.
          rewrite H0 in H6. fwd.
          
          specialize (H4 _ H5). fwd.
          split; auto.
          eapply vars_subset_fstate; eauto. } }
      { do 2 red. intros. fwd. contradiction. } }
    { simpl. do 2 red. intros. fwd. contradiction. }
  Qed.

  (* auxiliary lemmas for the rewriting vcgen rule below *)

  Lemma fstate_has_var_sound' :
        forall (fst : fstate) (a : Var) (d : float),
          fstate_lookup fst a = Some d ->
          fstate_has_var fst a = true.
      Proof.
        induction fst; simpl; intros; try congruence.
        destruct a. consider (a0 ?[eq] v); intros; auto.
        eapply IHfst; eauto.
      Qed.

      Require Import Coq.Lists.List.
      Import ListNotations.

      Lemma app_cons_last :
        forall (T : Type) (l l' : list T) (a : T),
          l ++ (a :: l') =
          (l ++ [a]) ++ l'.
      Proof.
        induction l; simpl; intros; auto.
        rewrite IHl. reflexivity.
      Qed.

      Lemma models_fstate_has_vars :
        forall vs vs' fst st,
          models (vs' ++ vs) fst st ->
          fstate_has_vars fst vs = true.
      Proof.
        induction vs; simpl; intros; auto.
        apply Bool.andb_true_iff.
        split.
        {
          unfold models in H.
          specialize (H a).
          fwd.
          generalize (Coqlib.in_app); intros.
          specialize (H1 _ a vs' (a :: vs)).
          simpl in H1. destruct H1.
          specialize (H2 (or_intror (or_introl eq_refl))).
          fwd.

          
          idtac.
          rewrite <- fstate_lookup_fm_lookup in H.
          
          eapply fstate_has_var_sound'; eauto.
        }      
        {
          rewrite app_cons_last in H.
          eapply IHvs; eauto. }
      Qed.

  (* Finally here is a rule for using the vc gen in rewrting
     (see Postprocess*.v *)
  Lemma Hoare__embed_rw :
  forall (c : fcmd)
         (vs : list string),
    (*var_spec_valid' vs ->*)
    (*varmap_check_fcmd vs c ->*)
    fembed_ex vs c |--
                Forall Q : fstate -> Prop,
  let (vs', P) := fpig_vcgen c vs Q in
  Embed (fun st st' : state =>
           (exists fst : fstate,
             vmodels vs fst st /\
             (P fst -> exists fst' : fstate, vmodels vs fst' st' /\ Q fst'))).
Proof.
  intros.
  breakAbstraction.
  intros.
  fwd.
  generalize (fpig_vcgen_correct); intro Hfpc.
  specialize (Hfpc c vs x).
  consider (fpig_vcgen c vs x); intros.
  unfold Hoare_, Hoare in *. simpl.
  unfold vmodels in *.
  eexists x0. split; auto.
  intros.
  exists x1. split; auto.
  specialize (Hfpc x0).
  Check models_fstate_has_vars.
  generalize models_fstate_has_vars as Hmfv; intros.
  specialize (Hmfv vs nil x0 (Stream.hd tr) H).
  fwd.
  specialize (H5 _ H1). fwd. auto.
Qed.


  (* the following is the old weakest-precondition calculation *)
(*  
  (* Weakest-precondition calcluation function for fcmd language *)
  Fixpoint fwp (c : fcmd)
           (P : fstate  -> Prop) : fstate -> Prop :=
    match c with
    | FSkip => P
    | FSeq c1 c2 => fwp c1 (fwp c2 P)
    | FAsn v e => (fun fst  =>
                    (*exists res, fexprD e fst = Some res /\*)
                           AnyOf
                             (map
                                (fun sbt : singleBoundTerm =>
                                   let '(pred, bound) := bounds_to_formula sbt fst in
                                   pred /\
                                   (forall (val : float) (r : R),
                                       F2OR val = Some r ->
                                       bound r -> P (fstate_set fst v val)))
                                (bound_fexpr e)))
    | FFail => fun fst => False
    | FIte e c1 c2 => (fun fst =>
                        (*exists res, fexprD e fst = Some res /\*)
                               (let bs := bound_fexpr e in
                                (maybe_lt0 bs fst -> fwp c1 P fst) /\
                                (maybe_ge0 bs fst -> fwp c2 P fst) /\
                                AnyOf
                                  (map
                                     (fun sbt : singleBoundTerm =>
                                        let '(prem, _) := denote_singleBoundTermNew fst sbt in prem)
                                     bs)))
    end.
  
  Lemma fwp_correct :
    forall c P,
      Hoare_ (fwp c P)
             c
             P.
  Proof.
    intros c.
    induction c; intros; eauto using Hoare__False.
    { eapply Hoare__seq.
      Focus 2.
      eapply IHc2; eauto.
      simpl.
      eapply Hoare__conseq.
      3: eapply IHc1; eauto.
      2: exact (fun _ x => x).
      intros; eassumption.
    }
    { eapply Hoare__skip. }
    { (*eapply Hoare__bound_asn.*) admit. }
    { (*eapply Hoare__bound_ite; eauto.*) admit. }
  Admitted.
*)
