(*
 * FloatEmbed.v
 * Specialization of the Embedding framework to our floating-point language
 *)

Require Import Coq.Reals.Rbase.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.

Require Import Logic.Syntax.
Require Import Logic.Automation.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.

Require Import Flocq.Core.Fcore_float_prop.
Require Import Flocq.Core.Fcore_Zaux.
Require Import Flocq.Appli.Fappli_IEEE.

Require Import Abstractor.FloatOps.
Require Import Abstractor.FloatLang.
Require Import Abstractor.Embed.
Require Import Abstractor.Bound_Reimp.

(* YAAY we don't need this awfulness anymore... *)
(*
Inductive pl_eq : float -> float -> Prop :=
| pl_zero : forall b b', pl_eq (B754_zero _ _ b) (B754_zero _ _ b')
| pl_inf : forall b b', pl_eq (B754_infinity _ _ b) (B754_infinity _ _ b')
| pl_nan : forall b b' p p', pl_eq (B754_nan _ _ b p) (B754_nan _ _ b' p')
| pl_except : forall b b' p, pl_eq (B754_infinity _ _ b) (B754_nan _ _ b' p)
| pl_refl : forall (p1 : float), pl_eq p1 p1
| pl_symm : forall p1 p2, pl_eq p1 p2 -> pl_eq p2 p1
| pl_trans : forall p1 p2 p3, pl_eq p1 p2 -> pl_eq p2 p3 -> pl_eq p1 p3
.
 *)

Definition pl_eq (f1 f2 : float) : Prop :=
  float_compare f1 f2 = Some Datatypes.Eq.

Local Ltac fwd := forward_reason.

Definition real_float (r : R) (f : float) : Prop :=
  (F2OR f = Some r)%type.

(* Instantiate our general embedding module for our particular case
   (floating-point, non-looping, imperative language) *)
Module FloatEmbed <: EmbeddedLang.
  Definition ast := fcmd.
  Definition pl_data := float.
  Definition eval := feval.
  Definition istate := list (string * float).
  Definition pl_equ (x y : pl_data) : Prop := exists r, B2Rinf x = Some r /\ B2Rinf y = Some r.
  (* Definition pl_equ_refl : forall p : pl_data, pl_equ p p := pl_refl. 
  Definition pl_equ_trans : forall p p' p'' : pl_data,
      pl_equ p p' -> pl_equ p' p'' -> pl_equ p p'' := pl_trans.
  Definition pl_equ_symm : forall p p' : pl_data, pl_equ p p' -> pl_equ p' p :=
    pl_symm.
   *)

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

  (*
  Lemma pl_eq_F2OR :
    forall a b,
      pl_eq a b ->
      F2OR a = F2OR b.
  Proof.
    induction 1; simpl; try reflexivity; auto.
    rewrite IHpl_eq1. auto.
  Qed.
*)

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
  
  Definition asReal_in (f : float) (r : R) : Prop :=
    match f with
    | Fappli_IEEE.B754_infinity _ _ true => (r > floatMax)%R
    | Fappli_IEEE.B754_infinity _ _ false => (r < -floatMax)%R
    | _ => (F2OR f = Some (the_round r))%type
    end.


  Definition asReal_out (f : float) (r : R) : Prop :=
    match f with
    | Fappli_IEEE.B754_nan _ _ _ _ => True
    | _ => (F2OR f = Some r)%type
    end.

  (* we may need a notion of validity *)
  Lemma states_iso_nil :
    forall ist,
      states_iso nil ist <-> ist = nil.
  Admitted.
  (*
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
*)


  (*
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
*)

  (*
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
   *)

  Lemma asReal_in_det :
    forall (p p' : pl_data) (r : R),
      asReal_in p r ->
      asReal_in p' r ->
      pl_equ p p'.
  Admitted.
  (*
  Proof.
    unfold asReal_in.
    intros.
    apply F2OR_pl_eq. rewrite <- H in H0. auto.
  Qed.
   *)

  Lemma asReal_in_equ' :
    forall (p p' : pl_data),
      pl_equ p p' -> forall r, asReal_in p r <-> asReal_in p' r.
  Admitted.
  (*
  Proof.
    intros p p' H.
    induction H; split; auto; intros;
    try (edestruct IHpl_eq);
    try (edestruct IHpl_eq1);
    try (edestruct IHpl_eq2);
    eauto.
  Qed.
   *)

  Lemma asReal_in_equ :
    forall (p p' : pl_data),
      pl_equ p p' -> forall (r : R), asReal_in p r -> asReal_in p' r.
  Admitted.
  (*
  Proof.
    intros.
    generalize (asReal_in_equ' _ _ H r); intros.
    destruct H1. auto.
  Qed.
   *)

  Lemma asReal_out_det :
    forall (p : pl_data) (r r' : R),
      asReal_out p r ->
      asReal_out p r' ->
      r = r'.
  (*
  Proof.
    unfold asReal_out. intros.
    rewrite H0 in H. inversion H. reflexivity.
  Qed.*)
  Admitted.

  Lemma states_iso_set' :
    forall ist ist',
      states_iso ist ist' ->
      forall val val', pl_eq val val' ->
                  forall v,
                    states_iso (fm_update ist v val) (fm_update ist' v val').
  Proof.
  Admitted.

  Definition pl_eq_lift := Roption pl_eq.

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
  Admitted.
  (*
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
*)

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
    | H1 : ?H |- _ => smash' H
    end.

  Ltac smashs := repeat smash.

  Lemma pl_finite_neq_zero :
    forall b0 m e e0 b1,
      ~(pl_eq (B754_finite custom_prec custom_emax b0 m e e0)
              (B754_zero custom_prec custom_emax b1)).
  Proof.
  Admitted.
  (*
    intros.
    intro.
    apply pl_eq_F2OR in H. simpl in H. inversion H; clear H.
    unfold Fcore_Zaux.cond_Zopp in H1. simpl in H1.
    consider b0; intros; subst.
    { unfold Fcore_defs.F2R in H0. simpl in H0.
      rewrite Fcore_Raux.P2R_INR in H0.
      generalize (pos_INR_nat_of_P m); intro Hpinr.
      generalize (bpow_nonzero radix2 e); intro Hbpnz.
      generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m))
                                                (Fcore_Raux.bpow radix2 e));
        intro Hric.
      destruct Hric.
      { split. lra. lra. }
      lra. }
    { unfold Fcore_defs.F2R in H0. simpl in H0.
      rewrite Fcore_Raux.P2R_INR in H0.
      generalize (pos_INR_nat_of_P m); intro Hpinr.
      generalize (bpow_nonzero radix2 e); intro Hbpnz.
      generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m))
                                                (Fcore_Raux.bpow radix2 e));
        intro Hric.
      destruct Hric.
      { split. lra. lra. }
      lra. }
  Qed.
   *)

  (*
  Instance Reflexive_pl_eq : Reflexive pl_eq.
  Proof.
  Admitted.
   *)
  (*
    red. eapply pl_refl.
  Qed.
   *)

  Instance Transitive_pl_eq : Transitive pl_eq.
  Proof.
  Admitted.
  (*
    red. eapply pl_trans.
  Qed.
   *)

  Instance Proper_lift2 {T : Type} {R : T -> T -> Prop} f
    : Proper (R ==> R ==> R) f ->
      Proper (Roption R ==> Roption R ==> Roption R) (lift2 f).
  Proof.
    compute. intros.
    destruct H0; try constructor.
    destruct H1; constructor.
    eapply H; eauto.
  Qed.

  (*
  Instance Proper_float_plus_pl_eq
  : Proper (pl_eq ==> pl_eq ==> pl_eq) float_plus.
  Proof.
    red. red.
    induction 1; red.
    { induction 1; try solve [ constructor ].
      simpl; smashs; constructor.
      simpl; smashs; constructor.
      + eapply pl_symm.
        eapply pl_trans; [ eapply pl_trans ; [ | eassumption ] | ];
        simpl; smashs; constructor.
      + eapply pl_trans; [ eapply IHpl_eq1 | ].
        eapply pl_trans; [ | eapply IHpl_eq2 ].
        simpl; smashs; constructor. }
    { induction 1;
      try solve [ constructor
                | eapply pl_symm;
                  eapply pl_trans; [ eapply pl_trans ; [ | eassumption ] | ];
                  simpl; smashs; repeat constructor
                | eapply pl_trans; [ eapply IHpl_eq1 | ];
                  eapply pl_trans; [ | eapply IHpl_eq2 ];
                  simpl; smashs; repeat constructor
                | simpl; smashs; repeat constructor ]. }
    { simpl. constructor. }
    { simpl. destruct x; try constructor.
      smashs; repeat constructor. }
    { induction 1; try solve [ constructor
                             | eapply pl_symm; eassumption
                             | etransitivity; eauto
                             | destruct p1; simpl; solve [ constructor
                                                         | smashs; constructor ]
                             | destruct p1; simpl; smashs;
                               repeat constructor ]. }
    { red in IHpl_eq.
      intros. eapply pl_symm.
      eapply IHpl_eq. eapply pl_symm; eauto. }
    { intros. etransitivity. eapply IHpl_eq1. eassumption.
      eapply IHpl_eq2. reflexivity. }
  Qed.

  Instance Proper_float_minus_pl_eq
  : Proper (pl_eq ==> pl_eq ==> pl_eq) float_minus.
  Proof.
    red. red.
    induction 1; red.
    { induction 1; try solve [ constructor ].
      simpl; smashs; constructor.
      simpl; smashs; constructor.
      + eapply pl_symm.
        eapply pl_trans; [ eapply pl_trans ; [ | eassumption ] | ];
        simpl; smashs; constructor.
      + eapply pl_trans; [ eapply IHpl_eq1 | ].
        eapply pl_trans; [ | eapply IHpl_eq2 ].
        simpl; smashs; constructor. }
    { induction 1;
      try solve [ constructor
                | eapply pl_symm;
                  eapply pl_trans; [ eapply pl_trans ; [ | eassumption ] | ];
                  simpl; smashs; repeat constructor
                | eapply pl_trans; [ eapply IHpl_eq1 | ];
                  eapply pl_trans; [ | eapply IHpl_eq2 ];
                  simpl; smashs; repeat constructor
                | simpl; smashs; repeat constructor ]. }
    { simpl. constructor. }
    { simpl. destruct x; try constructor.
      smashs; repeat constructor. }
    { induction 1; try solve [ constructor
                             | eapply pl_symm; eassumption
                             | etransitivity; eauto
                             | destruct p1; simpl; solve [ constructor
                                                         | smashs; constructor ]
                             | destruct p1; simpl; smashs; repeat constructor ]. }
    { red in IHpl_eq.
      intros. eapply pl_symm.
      eapply IHpl_eq. eapply pl_symm; eauto. }
    { intros. etransitivity. eapply IHpl_eq1. eassumption.
      eapply IHpl_eq2. reflexivity. }
  Qed.

  Instance Proper_float_mult_pl_eq
  : Proper (pl_eq ==> pl_eq ==> pl_eq) float_mult.
  Proof.
    red. red.
    induction 1; red.
    { induction 1; try solve [ constructor
                             | destruct p1; simpl; try solve [ constructor ] ].
      + eapply pl_symm.
        eapply pl_trans; [ eapply pl_trans ; [ | eassumption ] | ];
        simpl; smashs; constructor.
      + eapply pl_trans; [ eapply IHpl_eq1 | ].
        eapply pl_trans; [ | eapply IHpl_eq2 ].
        simpl; smashs; constructor. }
    { induction 1;
      try solve [ constructor
                | eapply pl_symm;
                  eapply pl_trans; [ eapply pl_trans ; [ | eassumption ] | ];
                  simpl; smashs; repeat constructor
                | eapply pl_trans; [ eapply IHpl_eq1 | ];
                  eapply pl_trans; [ | eapply IHpl_eq2 ];
                  simpl; smashs; repeat constructor
                | simpl; smashs; repeat constructor ]. }
    { simpl. constructor. }
    { simpl. destruct x; try constructor. }
    { induction 1; try solve [ constructor
                             | eapply pl_symm; eassumption
                             | etransitivity; eauto
                             | destruct p1; simpl; solve [ constructor
                                                         | smashs; constructor ]
                             | destruct p1; simpl; smashs; repeat constructor ]. }
    { red in IHpl_eq.
      intros. eapply pl_symm.
      eapply IHpl_eq. eapply pl_symm; eauto. }
    { intros. etransitivity. eapply IHpl_eq1. eassumption.
      eapply IHpl_eq2. reflexivity. }
  Qed.

  Lemma finite_nonzero :
    forall b m z P,
      (Some 0%R = F2OR (B754_finite _ _ b m z P)) -> False%R.
  Proof.
    intros.
    inversion H.
    symmetry in H1.
    apply F2R_eq_0_reg in H1.
    unfold bounded in P.
    unfold cond_Zopp in H1.
    consider b; intros; inversion H1.
  Qed.
  
Lemma zero_pl_neq_finite :
  forall b b' m z p,
    pl_eq (B754_zero _ _ b) (B754_finite _ _ b' m z p) -> False.
Proof.
  intros.
  apply pl_eq_F2OR in H. unfold F2OR in H at 1.
  unfold FloatToR, B2R in H.
  apply finite_nonzero in H.
  auto.
Qed.

Lemma finite_pl_neq_zero :
  forall b b' m z p,
    pl_eq (B754_finite _ _ b' m z p) (B754_zero _ _ b) -> False.
      intros.
      apply pl_symm in H.
      apply zero_pl_neq_finite in H.
      assumption.
Qed.

Ltac convert_pl_eqs :=
  repeat match goal with
         | H : pl_eq ?f1 ?f2 |- _ =>
           apply pl_eq_F2OR in H
         end.

Ltac finite_neq_zero_tac :=
  repeat match goal with
         | H : pl_eq ?f1 ?f2 |- _ =>
           first [apply zero_pl_neq_finite in H | apply finite_pl_neq_zero in H]
         end.

Ltac invert_solve :=
  repeat match goal with
         | H : _ |- _ => try solve [inversion H]
         end.

Ltac fm_tac :=
  solve [first [solve [constructor]
               |solve [apply pl_symm; assumption]
               |solve [invert_solve]
               |solve [convert_pl_eqs; simpl in *; congruence]
               |solve [finite_neq_zero_tac; exfalso; auto]
               |solve [apply pl_except]
               |solve [apply pl_symm; apply pl_except]
               |solve [eapply pl_trans; eauto]
        ]].
  Instance Proper_float_max_pl_eq : Proper (pl_eq ==> pl_eq ==> pl_eq) float_max.
  Proof.
    red. red. red.
    induction 1; try solve [constructor].
    { induction 1; smashs; simpl in *; smashs;
      try solve [constructor | congruence | eapply pl_trans; eauto | eapply pl_symm; eauto |
                 eapply pl_trans; apply pl_symm; eauto; constructor |
                 match goal with
                 | H : pl_eq (B754_zero _ _ _) (B754_finite _ _ _ _ _ _) |- _ => generalize (zero_pl_neq_finite _ _ _ _ _ H); intros; contradiction
                 | H : pl_eq (B754_finite _ _ _ _ _ _) (B754_zero _ _ _) |- _ => generalize (finite_pl_neq_zero _ _ _ _ _ H); intros; contradiction
                 end
                ]. }
    { induction 1; smashs; simpl in *; smashs;
      try solve [constructor | congruence | eapply pl_trans; eauto | eapply pl_symm; eauto |
                 eapply pl_trans; apply pl_symm; eauto; constructor |
                 match goal with
                 | H : pl_eq (B754_zero _ _ _) (B754_finite _ _ _ _ _ _) |- _ => generalize (zero_pl_neq_finite _ _ _ _ _ H); intros; contradiction
                 | H : pl_eq (B754_finite _ _ _ _ _ _) (B754_zero _ _ _) |- _ => generalize (finite_pl_neq_zero _ _ _ _ _ H); intros; contradiction
                 end
                ]. }
    { induction 1; smashs; simpl in *; smashs;
      try solve [constructor | congruence | eapply pl_trans; eauto | eapply pl_symm; eauto |
                 eapply pl_trans; apply pl_symm; eauto; constructor |
                 match goal with
                 | H : pl_eq (B754_zero _ _ _) (B754_finite _ _ _ _ _ _) |- _ => generalize (zero_pl_neq_finite _ _ _ _ _ H); intros; contradiction
                 | H : pl_eq (B754_finite _ _ _ _ _ _) (B754_zero _ _ _) |- _ => generalize (finite_pl_neq_zero _ _ _ _ _ H); intros; contradiction
                 end
                ]. }
    { induction 1; try solve [ constructor
                             | eapply pl_symm; eassumption
                             | etransitivity; eauto
                             | destruct p1; simpl; solve [ constructor
                                                         | smashs; constructor ]
                             | destruct p1; simpl; smashs;
                               repeat constructor ]. }
    { intros. apply pl_symm. apply IHpl_eq. apply pl_symm. assumption. }
    { intros. specialize (IHpl_eq1 _ _ H1).
      eapply pl_trans; eauto.
      eapply IHpl_eq2. constructor. }
    Unshelve.
     auto. auto. auto. auto.
  Qed.
      
  Lemma states_iso_fexprD :
    forall ist ist',
      states_iso ist ist' ->
      forall fx, pl_eq_lift (fexprD fx ist) (fexprD fx ist').
  Proof.
    induction fx; rewrite states_iso_iso' in H.
    { simpl.
      consider (fstate_lookup ist v); intros; subst;
      consider (fstate_lookup ist' v); intros; subst; try auto.
      { unfold states_iso' in H. specialize (H v). rewrite <- fstate_lookup_fm_lookup in H.
        rewrite H0 in H. forward_reason.
        apply F2OR_pl_eq in H2.
        constructor.
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
        congruence. }
      { constructor. } }
    { simpl. constructor. reflexivity. }
    { simpl.
      destruct IHfx1; try constructor.
      destruct IHfx2; try constructor; eapply Proper_float_plus_pl_eq; eauto. }
    { simpl.
      destruct IHfx1; try constructor.
      destruct IHfx2; try constructor; eapply Proper_float_minus_pl_eq; eauto. }
    { simpl.
      destruct IHfx1; try constructor.
      destruct IHfx2; try constructor; eapply Proper_float_mult_pl_eq; eauto. }
    { simpl.
      destruct IHfx1; try constructor.
      destruct IHfx2; try constructor; eapply Proper_float_max_pl_eq; eauto. }
  Qed.

  Instance Proper_float_lt : Proper (pl_eq ==> pl_eq ==> iff) float_lt.
  Proof.
    red. red. red.
    intros.
    eapply pl_eq_F2OR in H.
    eapply pl_eq_F2OR in H0.
    unfold float_lt.
    unfold F2OR in *.
    destruct x; destruct y; try congruence; inv_all; try rewrite H; clear H;
    destruct x0; destruct y0; try congruence; inv_all; try rewrite H0; clear H0;
      tauto.
  Qed.

  Instance Proper_float_ge : Proper (pl_eq ==> pl_eq ==> iff) float_ge.
  Proof.
    red. red. red.
    intros.
    eapply pl_eq_F2OR in H.
    eapply pl_eq_F2OR in H0.
    unfold float_ge.
    unfold F2OR in *.
    destruct x; destruct y; try congruence; inv_all; try rewrite H; clear H;
    destruct x0; destruct y0; try congruence; inv_all; try rewrite H0; clear H0;
      tauto.
  Qed.

  Lemma eval_det' :
    forall prg isti istf,
      eval isti prg istf ->
      forall isti', states_iso isti isti' ->
      exists istf', states_iso istf istf' /\ eval isti' prg istf'.
  Proof.
    induction 1; simpl; intros.
    { eexists. split; eauto. constructor. }
    { eapply IHfeval1 in H1. fwd.
      eapply IHfeval2 in H1; fwd.
      eexists. split; eauto. econstructor; eauto. }
    { generalize (states_iso_fexprD _ _ H0 e).
      inversion 1.
      congruence.
      rewrite H in H2. inv_all. subst.
      eexists. split.
      eapply states_iso_set'; eauto.
      constructor. eauto. }
    { generalize (states_iso_fexprD _ _ H2 ex).
      rewrite H.
      eapply IHfeval in H2; clear IHfeval.
      inversion 1; subst.
      fwd.
      eexists; split; eauto.
      econstructor; eauto.
      eapply Proper_float_lt.
      - eapply pl_symm. eassumption.
      - reflexivity.
      - eassumption. }
    { generalize (states_iso_fexprD _ _ H2 ex).
      rewrite H.
      eapply IHfeval in H2; clear IHfeval.
      inversion 1; subst.
      fwd.
      eexists; split; eauto.
      eapply FEIteF; eauto.
      eapply Proper_float_ge.
      - eapply pl_symm. eassumption.
      - reflexivity.
      - eassumption. }
    { generalize (states_iso_fexprD _ _ H2 ex).
      rewrite H.
      eapply IHfeval in H2; clear IHfeval. inversion 1; subst. fwd.
      exists x; split; eauto.
      eapply FEIFinT; try eassumption.


      Print pl_eq_lift.
      
      inversion H3; subst.
      inversion
      eexists; split; eauto.
      eapply FEIFinT; eauto.
      inversion H4; subst; try congruence.
      inversion H7; subst. try solve [simpl in *; congruence].
      
      inversion H7; subst; try solve [simpl in *; congruence].
      { 
      rewrite H in H6.
      inversion H4.
      eexists; split; eauto.
  Qed.

  Lemma eval_det : forall prg isti isti' istf,
      states_iso isti isti' ->
      eval isti prg istf ->
      exists istf', states_iso istf istf' /\ eval isti' prg istf'.
  Proof.
    intros. eapply eval_det'; eauto.
  Qed. *)

  Definition pl_equ_refl : forall (p : pl_data), pl_equ p p.
  Admitted.

  Definition pl_equ_trans : forall (p p' p'' : pl_data),
      pl_equ p p' -> pl_equ p' p'' -> pl_equ p p''. Admitted.
  Definition pl_equ_symm : forall (p p' : pl_data),
      pl_equ p p' -> pl_equ p' p. Admitted.

  Definition eval_det :
    forall prg isti isti' istf,
      (states_iso isti isti') ->
      eval isti prg istf ->
      exists istf', states_iso istf istf' /\ eval isti' prg istf'. Admitted.


End FloatEmbed.

Module Import Embedding := Embedding FloatEmbed.
Definition astate := list (Var * interval).

(* Hoare rules over abstract states *)
Inductive fstate_astate' : fstate -> astate -> Prop :=
| FSAS_nil : fstate_astate' nil nil
| FSAS_cons :
    forall fv av,
      intervalD av fv ->
      forall fst ast,
        fstate_astate' fst ast ->
        forall k,
          fstate_astate' ((k,fv) :: fst) ((k,av) :: ast)
.

Definition astate_lookup_nan (ast : astate) (v : string) : interval :=
  match fm_lookup ast v with
  | Some i => i
  | None => nan_const
  end.

Fixpoint bound_fexpr (fx : fexpr) (aState : astate) : interval :=
  match fx with
  | FVar v => astate_lookup_nan aState v
  | FConst f => absFloatConst f
  | FPlus fx1 fx2 =>
    absFloatPlus' (bound_fexpr fx1 aState) (bound_fexpr fx2 aState)
  | FMax fx1 fx2 =>
    absFloatMax' (bound_fexpr fx1 aState) (bound_fexpr fx2 aState)
  | _ => top_const
  end.

(* abstract evaluation *)

Definition maybe_lt0 (i : interval) : Prop :=
  Rinf_lt i.(lb) (RinfR 0).

Definition maybe_ge0_or_nan (i : interval) : Prop :=
  Rinf_ge i.(ub) (RinfR 0) \/ i.(nan) = true.

Inductive afeval : astate -> fcmd -> astate -> Prop :=
| AFESkip : forall s : astate, afeval s FSkip s
| AFESeqS : forall (s s' os'' : astate) (a b : fcmd),
    afeval s a s' -> afeval s' b os'' -> afeval s (FSeq a b) os''
| AFEAsnS : forall (s : astate) (v : Var) (e : fexpr),
    afeval s (FAsn v e) (fm_update s v (bound_fexpr e s))
(* ambiguous ifs captured as nondeterminism *)
| AFEIteT : forall (s os' : astate) (ex : fexpr) (c1 c2 : fcmd),
    maybe_lt0 (bound_fexpr ex s) ->
    afeval s c1 os' ->
    afeval s (FIte ex c1 c2) os'
| AFEIteF : forall (s os' : astate) (ex : fexpr) (c1 c2 : fcmd),
    maybe_lt0 (bound_fexpr ex s) ->
    afeval s c1 os' ->
    afeval s (FIte ex c1 c2) os'
.

Lemma afeval_correct :
  forall ast ast' prog,
    afeval ast prog ast' ->
    forall (fst : fstate),
      fstate_astate' fst ast ->
      exists fst', feval fst prog fst' /\
              forall fst', feval fst prog fst' -> fstate_astate' fst' ast'.
Proof.
  induction 1.
  { intros. eexists.
    split; [econstructor|].
    intros.
    inversion H0; subst; auto. }
  { intros.
    generalize (IHafeval1 _ H1); intros; fwd.
    generalize (H3 _ H2); intros; fwd.
    generalize (IHafeval2 _ H4). intros; fwd.
    eexists.
    split; [econstructor; eauto|].
    intros.
    inversion H7; subst; clear H7.
    apply H6.

Definition HoareA (P : astate -> Prop) (c : fcmd) (Q : astate -> Prop) : Prop :=
  forall (ast : astate),
    P ast ->
    forall (fst : fstate),
      fstate_astate' fst ast ->
      (exists fst' : fstate, M.eval fst c fst' /\
                        forall ast' : astate, fstate_astate' fst' ast' -> Q ast').

Lemma Hoare__skip :
  forall (P : fstate -> Prop),
    Hoare P FSkip P.
Proof.
  red. intros.
  split.
  { eexists; constructor. }
  { intros. inversion H0. subst. auto. }
Qed.

Lemma HoareA_skip :
  forall (P : astate -> Prop),
    HoareA P FSkip P.
Proof.
  red. intros.
  eexists. split; [econstructor|].
  intros
  { intros. inversion H0. subst. auto. }
Qed.



Lemma Hoare__seq :
  forall P Q R c1 c2,
    Hoare P c1 Q ->
    Hoare Q c2 R ->
    Hoare P (FSeq c1 c2) R.
Proof.
  unfold Hoare.
  intros.
  split.
  { eapply H in H1.
    fwd.
    specialize (H0 _ (H2 _ H1)).
    forward_reason.
    eexists. econstructor; eauto. }
  { intros. inversion H2; subst; clear H2.
    specialize (H _ H1).
    forward_reason.
    specialize (H2 _ H6).
    specialize (H0 _ H2).
    forward_reason; auto. }
Qed.

(* this plus consequence should be enough to get our real assignment rule
   that talks about bounds *)
Lemma Hoare__asn :
  forall P v e,
    Hoare
      (fun fs : fstate =>
           P (fm_update fs v (fexprD e fs)))%type
      (FAsn v e)
      P.
Proof.
  intros. red.
  intros. fwd.
  split.
  - eexists. constructor.
  - intros. inversion H0; subst; clear H0.
    assumption.
Qed.

Definition fm_lookup_force (fs : fstate) (v : Var) : R :=
  match fm_lookup fs v with
  | None => 0%R
  | Some r => FloatToR r
  end.

Definition isVarValid (v:Var) (aState : astate) : Prop
  := exists i, fm_lookup aState v = Some i.


Lemma F2OR_FloatToR' :
  forall (f : float) (r : R),
    F2OR f = Some r ->
    FloatToR f = r.
Proof.
  destruct f; simpl; congruence.
Qed.

Lemma fm_lookup_fm_lookup_force :
  forall (s : fstate) (v : Var) (f : float) (r : R),
    fm_lookup s v = Some f ->
    F2OR f = Some r ->
    fm_lookup_force s v = r.
Proof.
  induction s; intros; simpl in *; try congruence.
  destruct a.
  unfold fm_lookup_force. simpl.
  rewrite H.
  apply F2OR_FloatToR'; auto.
Qed.

Lemma is_finite_FloatToR : forall x,
    is_finite _ _ x = true ->
    FloatToR x = B2R custom_prec custom_emax x.
Proof.
  destruct x; simpl; congruence.
Qed.

Definition interval_entails (il : interval) (ir : interval) : Prop :=
  forall (f : float),
    intervalD il f -> intervalD ir f.

Definition interval_bientails (il ir : interval) : Prop :=
  interval_entails il ir /\ interval_entails ir il.

(* we need some kind of way of relating
   astates to fstates? *)
(* NOTE: this just says that the astate has
   everything the fstate has. This is probably sufficent. *)
Fixpoint fstate_astate (fs : fstate) (ast : astate) : Prop :=
  match fs with
  | nil => True
  | (v,vf):: fs' => exists va, fm_lookup ast v = Some va /\
                         intervalD va vf /\
                         fstate_astate fs' ast
  end.


(* encodes that they must be over the same variables *)
(* better make this an inductive *)


Lemma absFloatConst_sound :
  forall fval,
    intervalD (absFloatConst fval) fval.
Proof.
  intros.
  consider fval; intros; subst; unfold intervalD, absFloatConst; simpl.
  { right. split; right; constructor; lra. }
  { consider b; intros; right; simpl; split; right; constructor. }
  { left; auto. }
  { right. split; right; constructor; lra. }
Qed.

(* sometimes admit seems to mess up bulleting... *)
Ltac admit' :=
  assert False by admit; contradiction.

Lemma top_const_top :
  forall (f : float),
    intervalD top_const f.
Proof.
  simpl; intros.
  consider f; simpl; intros; subst.
  { right; split; left; constructor. }
  { consider b; simpl; intros;
    right; split; try solve [left; constructor]; try solve [right; constructor]. }
  { left; auto. }
  { right; split; left; constructor. }
Qed.

Lemma bot_const_bot :
  forall (f : float),
    intervalD bot_const f -> False.
Proof.
  simpl; intros.
  consider f; simpl; intros; subst; try destruct H0;
  fwd; try solve [congruence];
  try solve [destruct H; inversion H];
  destruct b; fwd;
  try solve [destruct H; inversion H];
  try solve [destruct H0; inversion H0].
Qed.

Print fstate_lookup_nan.

Lemma fstate_astate_intervalD :
  forall fst ast,
    fstate_astate' fst ast ->
    forall v,
      intervalD (astate_lookup_nan ast v) (fstate_lookup_nan fst v).
Proof.
  induction 1.
  { intros. simpl. auto. }
  { simpl. intros.
    unfold astate_lookup_nan, fstate_lookup_nan in *.
    simpl.
    consider (string_dec v k); intros; subst; auto. }
Qed.

(*
Lemma astate_implies_fstate :
  forall fst ast,
    fstate_astate' fst ast ->
    forall v aval,
      fm_lookup ast v = Some aval ->
      exists fval, fm_lookup fst v = Some fval /\
      intervalD aval fval.
Proof.
  induction 1.
  { intros. simpl in H. congruence. }
  { simpl. intros.
    consider (string_dec v k); intros; subst.
    { inversion H1; subst.
      eexists. split; eauto. }
    { apply IHfstate_astate'; auto. } }
Qed.

Lemma fstate_implies_astate_not :
  forall fst ast,
    fstate_astate' fst ast ->
    forall v,
      fm_lookup fst v = None ->
      fm_lookup ast v = None.
Proof.
  induction 1.
  { intros. reflexivity. }
  { simpl. intros.
    consider (string_dec v k); intros; subst.
    { congruence. }
    { apply IHfstate_astate'; auto. } }
Qed.

Lemma astate_implies_fstate_not :
  forall fst ast,
    fstate_astate' fst ast ->
    forall v,
      fm_lookup ast v = None ->
      fm_lookup fst v = None.
Proof.
  induction 1.
  { intros. simpl. reflexivity. }
  { simpl. intros.
    consider (string_dec v k); intros; subst; [congruence|].
    apply IHfstate_astate'; auto. }
Qed.
*)

Lemma bound_fexpr_sound
  : forall fx fst fval,
    fexprD fx fst = fval ->
    forall ast,
      fstate_astate' fst ast ->
      intervalD (bound_fexpr fx ast) (fexprD fx fst).
Proof.
  induction fx.
  { simpl. intros.
    apply fstate_astate_intervalD; auto. }
  { simpl. intros.
    inversion H; subst.
    apply absFloatConst_sound. }
  { admit'. (* plus soundness. *) }
  { intros. unfold bound_fexpr. apply top_const_top. (* minus soundness, unimplemented *) }
  { intros. unfold bound_fexpr. apply top_const_top. (* times soundness, unimplemented *) }
  { admit'. (* max soundness *) }
Admitted.

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

Lemma Hoare_conseq : forall (P P' Q Q' : _ -> Prop) c,
    Hoare P c Q ->
    (forall fst, P' fst -> P fst) ->
    (forall fst, Q fst -> Q' fst) ->
    Hoare P' c Q'.
Proof.
  unfold Hoare. intros.
  eapply H0 in H2. eapply H in H2.
  destruct H2.
  split; eauto.
Qed.

(* need Hoare_, Hoare rules over abstract states *)
Lemma Hoare__asn' :
  forall (P : fstate -> Prop) v e,
    Hoare 
      P 
      (FAsn v e)
      (fun fst : fstate =>
         P (fm_unset fst) /\
         forall ast, fstate_astate' fst ast ->
                intervalD (bound_fexpr e ast) (fexprD e fst)).
Proof.
  intros. red.
  intros.
  split.
  - eexists.
    constructor. 
  - intros. inversion H0; subst; clear H0.
    simpl. split; [assumption|].
    intros.
    eapply bound_fexpr_sound; auto.
Qed.

(*
Lemma Hoare_bound_asn :
  forall (P : _ -> Prop) v e,
    Hoare P
          (FAsn v e)
          (fun fst : fstate =>
             P (fm_unset fst) /\
             exists f, fm_lookup fst v = Some f /\
             forall ast : astate,
               fstate_astate fst ast ->
               intervalD (bound_fexpr e ast) f).
Proof.
  intros.
  Check Hoare__asn.
  eapply Hoare_conseq; [ eapply Hoare__asn | | ].
      
             exists res, fexprD e fst = Some res /\
                    (forall res',
                        intervalD (bound_fexpr e) res' fst ->
                        P (fstate_set fst v res')))
          (FAsn v e)
          P.
*)  

(* original *)
(*
Lemma Hoare__bound_asn :
  forall (P : _ -> Prop) v e,
    Hoare (fun fst : fstate =>
             exists res, fexprD e fst = Some res /\
                         (forall res',
                             All_predIntD (bound_fexpr e) res' fst ->
                             P (fstate_set fst v res')))
          (FAsn v e)
          P.
Proof.
  intros.
  eapply Hoare_conseq; [ eapply Hoare__asn | | exact (fun _ x => x) ].
  intros. forward_reason.
  eexists; split; eauto.
  eapply H0.
  eapply bound_fexpr_sound; auto.
Qed.
*)

(* A couple of lemmas used for ITE rule *)
Lemma Hoare__or :
  forall (P1 P2 Q : _ -> Prop) c,
    Hoare P1 c Q ->
    Hoare P2 c Q ->
    Hoare (fun st => P1 st \/ P2 st)%type c Q.
Proof.
  intros.
  unfold Hoare in *.
  intros.
  destruct H1; eauto.
Qed.

Lemma Hoare__False :
  forall (P : _ -> Prop) c,
    Hoare (fun _ => False) c P.
Proof.
  intros.
  unfold Hoare. intros. contradiction.
Qed.

Lemma or_distrib_imp :
  forall A B C : Prop,
    (A \/ B -> C) <->
    (A -> C) /\ (B -> C).
Proof. tauto. Qed.

Lemma and_distrib_or :
  forall A B C : Prop,
    A /\ (B \/ C) <->
    (A /\ B) \/ (A /\ C).
Proof. tauto. Qed.


Lemma float_lt_ge :
  forall f1 f2,
    float_lt f1 f2 \/ float_ge_or_nan f1 f2.
Proof.
  intros.
  unfold float_lt, float_ge_or_nan.
  consider f1; consider f2; intros; try solve [simpl; left; congruence]; try solve [simpl; right; congruence];
  consider b; intros; try solve [simpl; left; congruence]; try solve [simpl; right; congruence];
  consider b0; intros; try solve [simpl; left; congruence]; try solve [simpl; right; congruence].
  (* finite cases *)
  { generalize (Bcompare_correct); intros.
    assert (Fappli_IEEE.is_finite _ _ f1 = true) by (rewrite H2; reflexivity).
    assert (Fappli_IEEE.is_finite _ _ f2 = true) by (rewrite H1; reflexivity).
    specialize (H3 _ _ _ _ H4 H5).
    consider (Rlt_le_dec (B2R custom_prec custom_emax f1) (B2R custom_prec custom_emax f2)).
    { apply Fcore_Raux.Rcompare_Lt in r.
      subst.
      unfold float_compare.
      rewrite H3.
      left. rewrite r. reflexivity. }
    { unfold Rge in r. destruct r.
      { apply Fcore_Raux.Rcompare_Gt in H6.
        subst.
        unfold float_compare.
        rewrite H3.
        right. rewrite H6.
        congruence. }
      { symmetry in H6.
        apply Fcore_Raux.Rcompare_Eq in H6.
        subst.
        unfold float_compare.
        rewrite H3.
        right. rewrite H6.
        congruence. } } }
  { generalize (Bcompare_correct); intros.
    assert (Fappli_IEEE.is_finite _ _ f1 = true) by (rewrite H2; reflexivity).
    assert (Fappli_IEEE.is_finite _ _ f2 = true) by (rewrite H1; reflexivity).
    specialize (H3 _ _ _ _ H4 H5).
    consider (Rlt_le_dec (B2R custom_prec custom_emax f1) (B2R custom_prec custom_emax f2)).
    { apply Fcore_Raux.Rcompare_Lt in r.
      subst.
      unfold float_compare.
      rewrite H3.
      left. rewrite r. reflexivity. }
    { unfold Rge in r. destruct r.
      { apply Fcore_Raux.Rcompare_Gt in H6.
        subst.
        unfold float_compare.
        rewrite H3.
        right. rewrite H6.
        congruence. }
      { symmetry in H6.
        apply Fcore_Raux.Rcompare_Eq in H6.
        subst.
        unfold float_compare.
        rewrite H3. 
        right. rewrite H6.
        congruence. } } }
Qed.

Lemma float_lt_ge_contra :
  forall f1 f2,
    float_lt f1 f2 /\ float_ge_or_nan f1 f2 -> False.
Proof.
  unfold float_lt, float_ge_or_nan.
  intros. fwd.
  consider f1; consider f2; intros; try solve [simpl; congruence]; try solve [simpl; congruence].
Qed.

Lemma Hoare__ite :
  forall P Q1 Q2 ex c1 c2,
    Hoare (fun fs => P fs /\ float_lt (fexprD ex fs) fzero) c1 Q1 ->
    Hoare (fun fs => P fs /\ float_ge_or_nan (fexprD ex fs) fzero) c2 Q2 ->
    Hoare
      P
      (FIte ex c1 c2)
      (fun fs : fstate =>
         Q1 fs \/ Q2 fs).
Proof.
  intros. red.
  intros.
  split.
  { destruct (float_lt_ge (fexprD ex s) fzero).
    { specialize (H _ (conj H1 H2)). fwd.
      eexists.
      eapply FEIteT; eauto. }
    { specialize (H0 _ (conj H1 H2)). fwd.
      eexists.
      eapply FEIteF; eauto. } }
  { intros.
    inversion H2; subst.
    { left.
      specialize (H _ (conj H1 H8)). fwd.
      eapply H3; eauto. }
    { right.
      specialize (H0 _ (conj H1 H8)). fwd.
      eapply H3; eauto. } }
Qed.

Lemma AnyOf_exists : forall Ps,
    AnyOf Ps <->
    exists P, In P Ps /\ P.
Proof.
  induction Ps.
  { simpl. intuition. fwd; auto. }
  { simpl. rewrite IHPs.
    intuition.
    { eexists; split; [ left | ]; eauto. }
    { destruct H0. destruct H. eexists; split; [ right | ]; eauto. }
    { destruct H1. destruct H1. destruct H1; subst; auto.
      right. eexists; eauto. } }
Qed.


Lemma Hoare__ite' :
  forall ex (P Q1 Q2 : _ -> Prop) c1 c2,
    Hoare (fun fs => P fs /\
                  exists ast, fstate_astate' fs ast /\
                         maybe_lt0 (bound_fexpr ex ast)) c1 Q1 ->
    Hoare (fun fs => P fs /\
                  exists ast, fstate_astate' fs ast /\
                         maybe_ge0_or_nan (bound_fexpr ex ast)) c2 Q2 ->
    Hoare P
          (FIte ex c1 c2)
          (fun fst => Q1 fst \/ Q2 fst).
Proof.
  intros.
  eapply Hoare_conseq.
  eapply Hoare__ite with (P := P) (Q1 := Q1) (Q2 := Q2).
  { red. intros. fwd.
    SearchAbout float_lt.
    red in H. specialize (H _
  apply H.
  ;
    [ eapply Hoare__ite; eassumption | | exact (fun _ x => x) ].
  intros. fwd.
  eexists; split; eauto.

             
Lemma Hoare__bound_ite :
  forall ex (P Q1 Q2 : _ -> Prop) c1 c2,
    let bs := bound_fexpr ex in
    Hoare Q1 c1 P ->
    Hoare Q2 c2 P ->
    Hoare (fun fst => exists res, fexprD ex fst = Some res
              /\ (maybe_lt0 bs fst -> Q1 fst)
              /\ (maybe_ge0_or_nan bs fst -> Q2 fst)
              /\ (AnyOf (List.map
                           (fun pi =>
                              let '(prem, _) := predInt_to_pair pi fst in prem)
                           bs)))%type
           (FIte ex c1 c2)
           P.
Proof.
  intros.
  eapply Hoare_conseq;
    [ eapply Hoare__ite; eassumption | | exact (fun _ x => x) ].
  intros. fwd.
  eexists; split; eauto.
  generalize (bound_fexpr_sound _ _ _ H1).
  eapply AnyOf_exists in H4.
  destruct H4.
  rewrite in_map_iff in H4. fwd. subst.
  unfold All_predIntD.
  rewrite Forall_forall. intros.
  specialize (H4 _ H6).
  destruct x1; simpl in *.
  fwd.
  split; intros.
  { apply H2.
    unfold maybe_lt0.
    eapply AnyOf_exists.
    eexists. rewrite in_map_iff. split.
    eexists. split. reflexivity. eassumption.
    simpl.
    unfold float_lt in *.
    red in H4. simpl in H4.
    specialize (H4 H5). split; auto.
    destruct H4.
    simpl in H7.
    rewrite is_finite_FloatToR in H7 by eauto. psatz R. }
  { apply H3.
    unfold maybe_ge0.
    eapply AnyOf_exists.
    eexists. rewrite in_map_iff. split.
    eexists. split. reflexivity. eassumption.
    simpl.
    unfold float_ge in *.
    red in H4. simpl in H4.
    specialize (H4 H5). split; auto.
    destruct H4.
    simpl in H7.
    rewrite is_finite_FloatToR in H7 by eauto. psatz R. }
Qed.

Fixpoint fexpr_check (e : fexpr) (vs : list Var) : bool :=
  match e with
  | FVar v => if in_dec string_dec v vs then true else false
  | FConst _ => true
  | FPlus e1 e2
  | FMinus e1 e2
  | FMult e1 e2
  | FMax e1 e2 => andb (fexpr_check e1 vs) (fexpr_check e2 vs)
  end.

Definition fstate_has_vars vs fst : Prop :=
  List.Forall (fun x => fstate_lookup fst x <> None)%type vs.

Lemma fexpr_check_sound :
  forall fx vs,
    fexpr_check fx vs = true ->
    forall fst,
      fstate_has_vars vs fst ->
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
  { destruct (in_dec string_dec v vs); try congruence.
    eapply Forall_forall in H0; eauto.
    destruct (fstate_lookup fst v); intuition. eauto. }
  { eexists; reflexivity. }
Qed.

(** Weakest pre-condition function
 **)
Fixpoint fpig_vcgen (c : fcmd) (vs : list Var)
: (list Var * forall P : fstate -> Prop, fstate -> Prop) :=
  match c with
  | FSkip => (vs, fun P => P)
  | FSeq c1 c2 =>
    let (vs', t1) := fpig_vcgen c1 vs in
    let (vs'', t2) := fpig_vcgen c2 vs' in
    (vs'', fun P => t1 (t2 P))
  | FAsn v e =>
    if fexpr_check e vs then
      (v :: vs,
       fun (P : fstate -> Prop) fst  =>
(*
         forall res',
           All_predIntD (bound_fexpr e) res' fst ->
           P (fstate_set fst v res'))
*)
         AnyOf
           (map
              (fun pi : predInt =>
                 let '(pred, bound) := predInt_to_pair pi fst in
                 pred /\
                 (forall (val : float) (r : R),
                     F2OR val = Some r ->
                     bound r -> P (fstate_set fst v val)))
              (bound_fexpr e)))
    else
      (v :: vs, fun P _ => False)
  | FIte e c1 c2 =>
    if fexpr_check e vs then
      let (_,P1) := fpig_vcgen c1 vs in
      let (_,P2) := fpig_vcgen c2 vs in
      let bs := bound_fexpr e in
      (vs, fun (P : fstate -> Prop) fs =>
             (maybe_lt0 bs fs -> P1 P fs) /\
             (maybe_ge0 bs fs -> P2 P fs) /\
             AnyOf
               (map
                  (fun pi : predInt =>
                     let '(prem, _) := predInt_to_pair pi fs in prem)
                  bs))
    else
      (vs, fun P _ => False)
  | FFail => (vs, (fun P _ => False))
  end.

Lemma fstate_has_var_fstate_set :
  forall vs fst v val,
    fstate_has_vars vs fst ->
    fstate_has_vars (v :: vs) (fstate_set fst v val).
Proof.
  intros. constructor.
  simpl. consider (v ?[ eq ] v); eauto. congruence.
  unfold fstate_set; simpl.
  induction vs.
  - constructor.
  - inversion H; clear H; subst.
    constructor; eauto.
    destruct (a ?[ eq ] v); eauto. congruence.
Qed.


Lemma fpig_vcgen_correct_lem :
  forall (c : fcmd) (vs vs' : list Var)
         (P : (fstate -> Prop) -> fstate -> Prop),
    fpig_vcgen c vs = (vs', P) ->
    (forall fs, fstate_has_vars vs' fs -> fstate_has_vars vs fs) /\
    forall Q,
      Hoare (fun fst => P Q fst /\ fstate_has_vars vs fst)
            c
            (fun fst' => Q fst' /\ fstate_has_vars vs' fst').
Proof.
  induction c; simpl; intros.
  { specialize (IHc1 vs).
    destruct (fpig_vcgen c1 vs).
    specialize (IHc1 _ _ eq_refl).
    specialize (IHc2 l).
    destruct (fpig_vcgen c2 l).
    specialize (IHc2 _ _ eq_refl).
    inversion H; clear H; subst.
    fwd. split; eauto.
    intros.
    eapply Hoare__seq; eauto. }
  { inversion H; clear H; subst.
    split; eauto using Hoare__skip. }
  { generalize (fexpr_check_sound f vs).
    destruct (fexpr_check f vs).
    { intros. inversion H; clear H; subst.
      split; [ inversion 1; auto | ].
      intros.
      eapply Hoare_conseq; [ eapply Hoare__bound_asn | | exact (fun _ x => x) ].
      simpl. intros.
      fwd.
      specialize (H0 _ H1).
      fwd. eexists; split; eauto.
      intros.
      red in H2.
      eapply AnyOf_exists in H; fwd.
      eapply in_map_iff in H.
      fwd.
      eapply Forall_forall in H2; eauto.
      red in H2.
      subst.
      destruct x1; simpl in *.
      split; eauto using fstate_has_var_fstate_set.
      destruct H3.
      specialize (H2 H).
      destruct H2.
      eapply H3 in H5; eauto.
      clear - H2. destruct res'; simpl in *; congruence. }
    { intros. inversion H; clear H; subst.
      split; [ inversion 1; auto | ]; intros.
      eapply Hoare_conseq.
      eapply Hoare__False.
      tauto.
      exact (fun _ x => x). } }
  { generalize (fexpr_check_sound f vs).
    destruct (fexpr_check f vs).
    { specialize (IHc1 vs).
      specialize (IHc2 vs).
      destruct (fpig_vcgen c1 vs);
        destruct (fpig_vcgen c2 vs).
      inversion H; clear H; subst.
      specialize (IHc1 _ _ eq_refl).
      specialize (IHc2 _ _ eq_refl).
      split; eauto.
      intros.
      eapply Hoare_conseq.
      eapply Hoare__bound_ite.
      4: exact (fun _ x => x).
      + eapply Hoare_conseq; [ eapply IHc1 | exact (fun _ x => x) | simpl ].
        intros. destruct H0. split. apply H0.
        destruct IHc1; eauto.
      + eapply Hoare_conseq; [ eapply IHc2 | exact (fun _ x => x) | simpl ].
        intros. destruct H0. split. apply H0.
        destruct IHc2; eauto.
      + simpl.
        intros.
        fwd.
        specialize (H fst H1).
        fwd.
        eexists; split; eauto.
        split; eauto. }
    { inversion H; clear H; subst.
      intros.
      split; auto; intros.
      eapply Hoare_conseq.
      eapply Hoare__False.
      tauto.
      exact (fun _ x => x). } }
  { inversion H; clear H; subst.
    split; auto; intros.
    eapply Hoare_conseq.
    eapply Hoare__False.
    tauto.
    exact (fun _ x => x). }
Qed.

Fixpoint fstate_has_vars_b (fst : fstate) (vs : list Var) :=
  match vs with
  | nil => true
  | v :: vs' => andb (match fstate_lookup fst v with
                      | None => false
                      | Some _ => true
                      end)
                     (fstate_has_vars_b fst vs')
  end.

Lemma fstate_has_vars_b_ok : forall fs vs,
    fstate_has_vars_b fs vs = true ->
    fstate_has_vars vs fs.
Proof.
  induction vs; simpl; intros.
  - constructor.
  - eapply Bool.andb_true_iff in H.
    destruct H.
    constructor; [ | eapply IHvs; eauto ].
    destruct (fstate_lookup fs a); congruence.
Qed.

Theorem fpig_vcgen_correct :
  forall (c : fcmd) (vs : list Var) (P : fstate -> Prop),
    let (vs',P') := fpig_vcgen c vs in
    Hoare (fun fst => if fstate_has_vars_b fst vs then P' P fst
                      else False)
          c
          (fun fst' => P fst').
Proof.
  intros.
  generalize (fpig_vcgen_correct_lem c vs).
  destruct (fpig_vcgen c vs).
  intros.
  specialize (H _ _ eq_refl).
  destruct H. clear H.
  specialize (H0 P).
  eapply Hoare_conseq. eassumption.
  2: simpl; intros; tauto.
  simpl.
  intros.
  generalize (fstate_has_vars_b_ok fst vs).
  destruct (fstate_has_vars_b fst vs); tauto.
Qed.

(* Finally here is a rule for using the vc gen in rewrting
     (see Postprocess*.v *)

Lemma Hoare__embed_rw
: forall (c : fcmd) (vs vs' : list string),
    embed_ex vs vs' c |--
    Forall Q : fstate -> Prop,
      let (_, P) := fpig_vcgen c vs in
      Embed (fun st st' : state =>
               exists fst : fstate,
                 models M.asReal_in vs fst st /\
                 (P Q fst ->
                  exists fst' : fstate, models M.asReal_out vs' fst' st' /\ Q fst')).
Proof.
  intros.
  generalize (fpig_vcgen_correct_lem c vs); intro Hfpc.
  destruct (fpig_vcgen c vs); intros.
  specialize (Hfpc _ _ eq_refl).
  destruct Hfpc.
  eapply lforallR. intro Q.
  specialize (H0 Q).
  eapply Hoare__embed with (vs:=vs) in H0.
  charge_revert.
  rewrite H0. clear - H.
  breakAbstraction; intros.
  fwd.
  eexists; split; eauto.
  intros.
  destruct H2.
  - split; auto.
    clear - H0.
    unfold models, fstate_has_vars in *.
    rewrite Forall_forall; intros.
    eapply H0 in H.
    fwd.
    rewrite FloatEmbed.fstate_lookup_fm_lookup.
    clear - H.
    unfold M.pl_data in *. congruence.
  - fwd. eexists; eauto.
Qed.

Export Embedding.


  

