Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
Require Import ExtLib.Tactics.
Require Import SMT.Tactic.
Require Import Flocq.Appli.Fappli_IEEE.
Require Import Flocq.Core.Fcore_Raux.
Require Import Flocq.Prop.Fprop_relative.
Require Import Flocq.Core.Fcore_FLT.
Require Import Flocq.Core.Fcore_generic_fmt.
Require Import Flocq.Core.Fcore_defs.
Require Import Abstractor.FloatOps.
Require Import Abstractor.FloatLang.

Import ListNotations.

Definition error    : R := bpow radix2 (- (custom_prec) + 1).
Definition floatMax : R := bpow radix2 custom_emax.
Definition floatMin : R := bpow radix2 custom_emin%Z.

Arguments is_finite {_ _} _.

(** * Predicated Intervals **)
Record predInt : Type :=
  mkPI { lb : fstate -> R
       ; ub : fstate -> R
       ; premise : fstate -> Prop }.

Definition predIntD (p : predInt) (f : float) (fs : fstate) : Prop :=
  p.(premise) fs ->
  is_finite f = true /\
  (p.(lb) fs <= B2R _ _ f <= p.(ub) fs)%R.

Definition predInt_entails (a b : predInt) : Prop :=
  forall f fs, predIntD a f fs -> predIntD b f fs.

Theorem prove_predInt_entails : forall a b,
    (forall fs, b.(premise) fs -> a.(premise) fs)%R ->
    (forall fs, a.(premise) fs -> b.(premise) fs ->
                b.(lb) fs <= a.(lb) fs /\ a.(ub) fs <= b.(ub) fs)%R ->
    predInt_entails a b.
Proof.
  unfold predInt_entails, predIntD.
  intros.
  specialize (H _ H2).
  specialize (H1 H).
  destruct H1. split; auto.
  specialize (H0 _ H H2).
  destruct H0. split;  psatz R.
Qed.

(** * Rounding Approximation **)
Definition the_round : R -> R :=
  round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
        (round_mode mode_ZR).

Definition Rsign (r : R) : R :=
  if Rlt_dec r 0 then -1%R
  else if Rlt_dec 0 r then 1%R
       else R0.

Definition roundDown_relative (r : R) : R :=
  r * (R1 - (Rsign r) * error).

Definition roundDown_subnormal (a : R) : R := -floatMin.

Definition roundDown (r : R) : R :=
  if Rlt_dec (Rabs r) floatMin then
    roundDown_subnormal r
  else
    roundDown_relative r.

Lemma relative_error_prem : forall k : Z,
    (custom_emin < k)%Z ->
    (custom_prec <= k - FLT_exp (3 - custom_emax - custom_prec)
                                custom_prec k)%Z.
Proof.
  intros; simpl.
  unfold FLT_exp, custom_prec, prec, custom_emin, emin in *.
  destruct (Zmax_spec (k - 24) (-149))%Z; omega.
Qed.

Lemma Rsign_mult : forall x, (Rsign x * x = Rabs x)%R.
Proof.
  unfold Rsign.
  intros.
  destruct (Rlt_dec x 0).
  - rewrite Rabs_left; auto. psatz R.
  - destruct (Rlt_dec 0 x).
    + rewrite Rabs_right; psatz R.
    + cutrewrite (x = 0)%R; [| psatz R ].
      rewrite Rabs_R0. psatz R.
Qed.

Lemma roundDown_relative_round : forall a,
    (floatMin <= Rabs a ->
     roundDown_relative a <= the_round a)%R.
Proof.
  intros.
  generalize (@relative_error
                radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                (fexp_correct _ _ custom_precGt0) custom_emin custom_prec
                relative_error_prem
                (round_mode mode_ZR) (valid_rnd_round_mode _)
                a H).
  intros.
  unfold the_round.
  generalize dependent (round radix2 (FLT_exp (3 - custom_emax - custom_prec)
                                              custom_prec) (round_mode mode_ZR)
                              a).
  clear H.
  intros.
  unfold roundDown_relative.
  rewrite Rmult_minus_distr_l.
  rewrite <- Rmult_assoc.
  rewrite (Rmult_comm a (Rsign a)). rewrite Rsign_mult.
  cut (- Rabs a * error <= r - a)%R; [ psatz R | ].
  apply Rabs_lt_inv in H0. destruct H0.
  eapply Rle_trans; [ | left; eassumption ].
  cut (error >= bpow radix2 (-custom_prec + 1))%R.
  { clear. intros.
    generalize dependent (bpow radix2 (- custom_prec + 1)).
    intros. generalize (Rabs_pos a). intros.
    rewrite (Rmult_comm r _).
    rewrite Ropp_mult_distr_l.
    psatz R. }
  { compute. tauto. }
Qed.

Lemma round_floatMin_is_floatMin
: the_round floatMin = floatMin.
Proof.
  simpl. unfold the_round.
  erewrite Fcalc_round.inbetween_float_ZR.
  Focus 2.
  instantiate (1:=Fcalc_bracket.loc_Exact).
  constructor.
  unfold canonic_exp. unfold floatMin.
  rewrite ln_beta_bpow.
  simpl. unfold F2R. simpl. instantiate (1:=8388608%Z).
  simpl. psatz R.
  simpl. unfold canonic_exp. unfold floatMin.
  rewrite ln_beta_bpow. simpl.
  unfold F2R. simpl.
  psatz R.
Qed.

Lemma roundDown_subnormal_round : forall a,
    (Rabs a < floatMin ->
     roundDown_subnormal a <= the_round a)%R.
Proof.
  intros.
  unfold roundDown_subnormal.
  rewrite <- round_floatMin_is_floatMin.
  { unfold the_round. rewrite <- round_ZR_opp.
    eapply round_le.
    - eapply fexp_correct. eapply custom_precGt0.
    - eapply valid_rnd_round_mode.
    - eapply Rabs_lt_inv in H.
      psatz R. }
Qed.

Lemma roundDown_round : forall a,
    (roundDown a <= the_round a)%R.
Proof.
  intros.
  unfold roundDown.
  destruct (Rlt_dec (Rabs a) floatMin).
  * eapply roundDown_subnormal_round; auto.
  * eapply roundDown_relative_round. psatz R.
Qed.

Definition roundUp_relative (r : R) : R :=
  r * (1 + (Rsign r) * error).

Definition roundUp_subnormal (a : R) : R := floatMin.

Definition roundUp (r : R) : R :=
  if Rlt_dec (Rabs r) floatMin then
    roundUp_subnormal r
  else
    roundUp_relative r.

Lemma roundUp_relative_round : forall a,
    (floatMin <= Rabs a ->
     the_round a <= roundUp_relative a)%R.
Proof.
  intros.
  generalize (@relative_error
                radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                (fexp_correct _ _ custom_precGt0) custom_emin custom_prec
                relative_error_prem
                (round_mode mode_ZR) (valid_rnd_round_mode _)
                a H).
  intros.
  unfold the_round.
  generalize dependent (round radix2 (FLT_exp (3 - custom_emax - custom_prec)
                                              custom_prec) (round_mode mode_ZR)
                              a).
  clear H.
  intros.
  unfold roundUp_relative.
  rewrite Rmult_plus_distr_l.
  rewrite <- Rmult_assoc.
  rewrite (Rmult_comm a (Rsign a)). rewrite Rsign_mult.
  cut (r - a <= Rabs a * error)%R; [ psatz R | ].
  apply Rabs_lt_inv in H0. destruct H0.
  eapply Rle_trans; [ left; eassumption | ].
  cut (error >= bpow radix2 (-custom_prec + 1))%R.
  { clear. intros.
    generalize dependent (bpow radix2 (- custom_prec + 1)).
    intros. generalize (Rabs_pos a). intros.
    rewrite (Rmult_comm r _).
    eapply Rmult_le_compat_l; auto. psatz R. }
  { compute. tauto. }
Qed.

Lemma roundUp_subnormal_round : forall a,
    (Rabs a < floatMin ->
     the_round a <= roundUp_subnormal a)%R.
Proof.
  intros.
  unfold roundUp_subnormal.
  rewrite <- round_floatMin_is_floatMin.
  { unfold the_round.
    eapply round_le.
    - eapply fexp_correct. eapply custom_precGt0.
    - eapply valid_rnd_round_mode.
    - eapply Rabs_lt_inv in H.
      psatz R. }
Qed.

Lemma roundUp_round : forall a,
    (the_round a <= roundUp a)%R.
Proof.
  unfold roundUp. intros.
  destruct (Rlt_dec (Rabs a) floatMin).
  + eapply roundUp_subnormal_round; auto.
  + eapply roundUp_relative_round; psatz R.
Qed.

(** * roundUp and roundDown facts **)
Local Open Scope R_scope.
Lemma roundDown_fact :
  forall (r : R),
    (r <= -floatMin /\ roundDown r = r * (1 + error))%R \/
    (r >= floatMin /\ roundDown r = r * (1 - error)) \/
    (r > -floatMin /\ r < floatMin /\ roundDown r = -floatMin).
Proof.
  intros.
  generalize (Rle_dec r 0); intros.
  destruct H.
  { generalize (Rle_dec r (-floatMin)); intros.
    destruct H.
    { left. unfold roundDown.
      split; try lra.
      consider (Rlt_dec (Rbasic_fun.Rabs r) floatMin); intros.
      { apply Fcore_Raux.Rabs_lt_inv in r2. lra. }
      { unfold roundDown_relative. unfold Rsign.
        consider (Rlt_dec r 0); intros; try lra.
        consider (Rlt_dec 0 r); intros; try lra.
        assert (r = 0) by lra. subst. lra. } }
    { assert (r >= -floatMin) by lra.
      right. right.
      split; try lra. split; try lra.
      unfold roundDown.
      consider (Rlt_dec (Rbasic_fun.Rabs r) floatMin); intros.
      { reflexivity. }
      { assert (floatMin <= Rbasic_fun.Rabs r) by lra.
        apply Fcore_Raux.Rabs_ge_inv in H0.
        destruct H0; lra. } } }
  { assert (r > 0) by lra.
    right.
    generalize (Rlt_dec r floatMin); intros.
    destruct H0.
    { right. split; try lra. split; try lra.
      unfold roundDown.
      consider (Rlt_dec (Rbasic_fun.Rabs r) floatMin).
      { reflexivity. }
      { unfold roundDown_relative.
        assert (floatMin <= Rbasic_fun.Rabs r)%R by lra.
        apply Fcore_Raux.Rabs_ge_inv in H0.
        destruct H0; lra. } }
    { assert (r >= floatMin) by lra.
      left.
      split; try lra.
      unfold roundDown.
      consider (Rlt_dec (Rbasic_fun.Rabs r) floatMin); intros.
      { apply Fcore_Raux.Rabs_lt_inv in r0. lra. }
      { unfold roundDown_relative. unfold Rsign.
        consider (Rlt_dec r 0); try lra.
        consider (Rlt_dec 0 r); lra. } } }
Qed.

Local Ltac considif := match goal with | |- context[if ?X then _ else _] => consider X end.

Lemma roundUp_fact :
  forall (r : R),
    (r <= -floatMin /\ roundUp r = r * (1 - error)) \/
    (r >= floatMin /\ roundUp r = r * (1 + error)) \/
    (r > -floatMin /\ r < floatMin /\ roundUp r = floatMin).
Proof.
  intros.
  generalize (Rle_dec r 0); intros.
  destruct H.
  { generalize (Rle_dec r (-floatMin)); intros.
    destruct H.
    { left. split; try lra.
      unfold roundUp.
      considif.
      { apply Fcore_Raux.Rabs_lt_inv in r2. lra. }
      { unfold roundUp_relative.
        unfold Rsign.
        consider (Rlt_dec r 0); try lra.
        consider (Rlt_dec 0 r); try lra.
        assert (r = 0) by lra. subst. lra. } }
    { assert (r > -floatMin) by lra.
      right. right.
      split; try lra. split; try lra.
      unfold roundUp.
      considif.
      { reflexivity. }
      { assert (floatMin <= Rbasic_fun.Rabs r) by lra.
        apply Fcore_Raux.Rabs_ge_inv in H0.
        destruct H0; lra. } } }
  { assert (r > 0) by lra.
    right.
    generalize (Rlt_dec r floatMin); intros.
    destruct H0.
    { right.
      split; try lra.
      split; try lra.
      unfold roundUp.
      consider (Rlt_dec (Rbasic_fun.Rabs r) floatMin).
      { reflexivity. }
      { assert (floatMin <= Rbasic_fun.Rabs r) by lra.
        apply Fcore_Raux.Rabs_ge_inv in H0.
        destruct H0; lra. } }
    { assert (r >= floatMin) by lra.
      left.
      split; try lra.
      unfold roundUp.
      considif.
      { apply Fcore_Raux.Rabs_lt_inv in r0. lra. }
      { unfold roundUp_relative.
        unfold Rsign.
        considif; try lra.
        considif; lra. } } }
Qed.

Close Scope R_scope.

Definition float_bounded (r : R) : Prop :=
  (- floatMax < r < floatMax)%R.

Lemma float_bounded_Rlt_bool
  : forall a b c,
    float_bounded (roundDown a) ->
    float_bounded (roundUp b) ->
    (a <= c <= b)%R ->
    (roundDown a <= the_round c <= roundUp b)%R /\
    Rlt_bool (Rabs (the_round c))
             (bpow radix2 custom_emax) = true.
Proof.
  intros.
  match goal with
  | |- ?X /\ ?Y =>
    assert X; [ | intros; split; [ assumption | ] ]
  end.
  { destruct H1.
    split.
    { eapply Rle_trans.
      eapply roundDown_round.
      eapply round_le; eauto.
      - eapply fexp_correct. eapply custom_precGt0.
      - eapply valid_rnd_round_mode. }
    { eapply Rle_trans; [ | eapply roundUp_round ].
      eapply round_le; eauto.
      - eapply fexp_correct. eapply custom_precGt0.
      - eapply valid_rnd_round_mode. } }
  rename H2 into Hxxx.
  match goal with
  | |- context [ Rlt_bool ?X ?Y ] =>
    case (Rlt_bool_spec X Y)
  end; auto.
  { intros.
    exfalso.
    change (bpow radix2 custom_emax) with floatMax in *.
    eapply Rabs_ge_inv in H2.
    destruct H2.
    { destruct H.
      cut (roundDown a <=
           round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                 (round_mode mode_ZR) c)%R;
        [ psatz R | ].
      eapply Rle_trans; [ eapply roundDown_round | ].
      eapply Rle_trans; [ eapply round_le | eapply Rle_refl ].
      - eapply fexp_correct. eapply custom_precGt0.
      - eapply valid_rnd_round_mode.
      - psatz R. }
    { destruct H0.
      cut (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                 (round_mode mode_ZR) c
           <= roundUp b)%R; [ psatz R | ].
      eapply Rle_trans; [ | eapply roundUp_round ].
      eapply Rle_trans; [ eapply Rle_refl | eapply round_le ].
      - eapply fexp_correct. eapply custom_precGt0.
      - eapply valid_rnd_round_mode.
      - psatz R. } }
Qed.

Lemma apply_float_bounded_lt : forall a b c P,
    float_bounded (roundDown a) ->
    float_bounded (roundUp b) ->
    (a <= c <= b)%R ->
    (roundDown a <= the_round c <= roundUp b ->
     P true)%R ->
    P (Rlt_bool (Rabs (the_round c))
                (bpow radix2 custom_emax)).
Proof.
  intros.
  eapply float_bounded_Rlt_bool in H1; eauto.
  destruct H1.
  rewrite H2. auto.
Qed.

(** * Predicated Interval Abstractions **)

(** * Constants **)
Definition absFloatConst (f : float) : predInt :=
  {| premise := fun _ => is_finite f = true
   ; lb := fun _ => B2R _ _ f ; ub := fun _ => B2R _ _ f |}%R.

Theorem absFloatConst_ok : forall f fs,
    predIntD (absFloatConst f) f fs.
Proof.
  red. intros. simpl. split.
  apply H.
  psatz R.
Qed.

(** * Addition **)
Definition absFloatPlus' (l r : predInt) : predInt :=
  let min fst := roundDown (l.(lb) fst + r.(lb) fst) in
  let max fst := roundUp   (l.(ub) fst + r.(ub) fst) in
  {| premise := fun fst => l.(premise) fst /\ r.(premise) fst
                        /\ float_bounded (min fst) /\ float_bounded (max fst)
                        /\ min fst <= max fst
   ; lb := min
   ; ub := max |}%R.

Theorem absFloatPlus'_ok : forall lp lv rp rv fs,
    predIntD lp lv fs ->
    predIntD rp rv fs ->
    predIntD (absFloatPlus' lp rp) (float_plus lv rv) fs.
Proof.
  unfold predIntD. simpl; intros.
  forward_reason.
  unfold float_plus.
  generalize (@Bplus_correct _ _ custom_precGt0 custom_precLtEmax custom_nan
                             mode_ZR _ _ H H0).
  eapply apply_float_bounded_lt; eauto. psatz R.
  intros.
  split; try tauto.
  destruct H10.
  destruct H11. rewrite H11.
  tauto.
Qed.

(** * Subtraction **)
Definition absFloatMinus' (l r : predInt) : predInt :=
  let min fst := roundDown (l.(lb) fst - r.(ub) fst) in
  let max fst := roundUp   (l.(ub) fst - r.(lb) fst) in
  {| premise := fun fst => l.(premise) fst /\ r.(premise) fst
                        /\ float_bounded (min fst) /\ float_bounded (max fst)
                        /\ min fst <= max fst
   ; lb := min
   ; ub := max |}%R.

Theorem absFloatMinus'_ok : forall lp lv rp rv fs,
    predIntD lp lv fs ->
    predIntD rp rv fs ->
    predIntD (absFloatMinus' lp rp) (float_minus lv rv) fs.
Proof.
  unfold predIntD. simpl; intros.
  forward_reason.
  unfold float_minus.
  generalize (@Bminus_correct _ _ custom_precGt0 custom_precLtEmax custom_nan mode_ZR _ _ H H0).
  eapply apply_float_bounded_lt; eauto. psatz R.
  intros.
  split; try tauto.
  destruct H10.
  destruct H11; rewrite H11.
  tauto.
Qed.

Definition Rmin4 (a b c d : R) : R :=
  Rmin (Rmin a b) (Rmin c d).
Definition Rmax4 (a b c d : R) : R :=
  Rmax (Rmax a b) (Rmax c d).

Lemma Rmin4_ok : forall a b c d e,
    (a <= e \/ b <= e \/ c <= e \/ d <= e ->
     Rmin4 a b c d <= e)%R.
Proof.
  unfold Rmin4. intros.
  destruct H as [ ? | [ ? | [ ? | ? ] ] ];
    do 3 first [ eapply Rle_trans; [ eapply Rmin_l + eapply Rmin_r | ]
               | eassumption ].
Qed.

Lemma Rmax4_ok : forall a b c d e,
    (e <= a \/ e <= b \/ e <= c \/ e <= d ->
     e <= Rmax4 a b c d)%R.
Proof.
  unfold Rmax4; intros.
  destruct H as [ ? | [ ? | [ ? | ? ] ] ];
    do 3 first [ eapply Rle_trans; [ | eapply Rmax_l + eapply Rmax_r ]
               | eassumption ].
Qed.

(** * Multiplication **)
Definition absFloatMult' (l r : predInt) : predInt :=
  let min fst := roundDown (Rmin4 (l.(lb) fst * r.(lb) fst)
                                  (l.(lb) fst * r.(ub) fst)
                                  (l.(ub) fst * r.(lb) fst)
                                  (l.(ub) fst * r.(ub) fst)) in
  let max fst := roundUp   (Rmax4 (l.(lb) fst * r.(lb) fst)
                                  (l.(lb) fst * r.(ub) fst)
                                  (l.(ub) fst * r.(lb) fst)
                                  (l.(ub) fst * r.(ub) fst)) in
  {| premise := fun fst => l.(premise) fst /\ r.(premise) fst
                        /\ float_bounded (min fst) /\ float_bounded (max fst)
(*                      /\ min fst <= max fst *)
   ; lb := min
   ; ub := max |}%R.

Lemma Rsign_id : forall x, x = (Rsign x * Rabs x)%R.
Proof.
  intros.
  rewrite <- Rsign_mult.
  unfold Rsign.
  destruct (Rlt_dec x 0); auto.
  - psatz R.
  - destruct (Rlt_dec 0 x); psatz R.
Qed.

Ltac try_elim :=
  try solve [ z3 solve; psatz R | exfalso; z3 solve; psatz R ].

Theorem absFloatMult'_ok : forall lp lv rp rv fs,
    predIntD lp lv fs ->
    predIntD rp rv fs ->
    predIntD (absFloatMult' lp rp) (float_mult lv rv) fs.
Proof.
  unfold predIntD. simpl; intros.
  forward_reason.
  unfold float_mult.
  generalize (@Bmult_correct _ _ custom_precGt0 custom_precLtEmax
                             custom_nan mode_ZR lv rv).
  eapply apply_float_bounded_lt; eauto.
  { clear - H7 H8 H5 H6.
    generalize dependent (lb lp fs);
    generalize dependent (ub lp fs);
    generalize dependent (lb rp fs);
    generalize dependent (ub rp fs);
    generalize dependent (B2R custom_prec custom_emax lv);
    generalize dependent (B2R custom_prec custom_emax rv); clear; intros.
    split.
    { apply Rmin4_ok.
      destruct (Rle_dec r 0); destruct (Rle_dec r0 0); try_elim;
      destruct (Rle_dec r1 0); try_elim;
      destruct (Rle_dec r2 0); try_elim;
      destruct (Rle_dec r3 0); try_elim;
      destruct (Rle_dec r4 0); try_elim. }
    { apply Rmax4_ok.
      destruct (Rle_dec 0 r); destruct (Rle_dec 0 r0); try_elim;
      destruct (Rle_dec 0 r1); try_elim;
      destruct (Rle_dec 0 r2); try_elim;
      destruct (Rle_dec 0 r3); try_elim;
      destruct (Rle_dec 0 r4); try_elim;
        solve [ right; right; right; psatz R ].
    }
  }
  { intros.
    rewrite H in *. rewrite H0 in *. simpl in H10.
    split; try tauto.
    destruct H10. rewrite H10. tauto. }
Qed.

(** * Max **)
Definition float_max (a b : float) : float :=
  match Fappli_IEEE_extra.Bcompare _ _ a b with
  | Some Datatypes.Eq => a
  | Some Datatypes.Lt => b
  | Some Datatypes.Gt => a
  | None => a
  end.

Definition absFloatMax' (l r : predInt) : predInt :=
  let min fst := Rmax (l.(lb) fst) (r.(lb) fst) in
  let max fst := Rmax (l.(ub) fst) (r.(ub) fst) in
  {| premise := fun fst => l.(premise) fst /\ r.(premise) fst
                        /\ min fst <= max fst
   ; lb := min
   ; ub := max |}%R.

Theorem absFloatMax'_ok : forall lp lv rp rv fs,
    predIntD lp lv fs ->
    predIntD rp rv fs ->
    predIntD (absFloatMax' lp rp) (float_max lv rv) fs.
Proof.
  unfold predIntD. simpl; intros.
  forward_reason.
  unfold float_max.
  rewrite (@Fappli_IEEE_extra.Bcompare_finite_correct _ _ _ _ H H0).
  case (Rcompare_spec (B2R custom_prec custom_emax lv)
                      (B2R custom_prec custom_emax rv));
    intros; subst; split; auto;
  generalize dependent (B2R custom_prec custom_emax lv);
  generalize dependent (B2R custom_prec custom_emax rv); intros;
    split; eapply Rmax_case_strong; psatz R.
Qed.

(** * Intersections of Predicated Intervals **)
Definition All_predInt : Type := list predInt.

Definition All_predIntD (p : All_predInt) (f : float) (fs : fstate) : Prop :=
  Forall (fun x => predIntD x f fs) p.

Definition All_predInt_entails (a b : All_predInt) : Prop :=
  forall f fs, All_predIntD a f fs -> All_predIntD b f fs.

Section cross_product.
  Context {T U V : Type}.
  Variable f : T -> U -> V.
  Fixpoint cross (x : list T) (y : list U) : list V :=
    match x with
    | List.nil => List.nil
    | x :: xs => map (f x) y ++ cross xs y
    end.

  Theorem cross_In : forall xs ys z,
      List.In z (cross xs ys) <->
      exists x y, z = f x y /\ List.In x xs /\ List.In y ys.
  Proof.
    induction xs; simpl; intros.
    { split; destruct 1. destruct H; tauto. }
    { rewrite in_app_iff.
      rewrite IHxs.
      rewrite in_map_iff.
      split.
      { destruct 1; forward_reason;
        do 2 eexists; eauto. }
      { destruct 1; forward_reason.
        destruct H0; subst; eauto.
        right. do 2 eexists; eauto. } }
  Qed.
End cross_product.

Definition lift (abs : predInt -> predInt -> predInt) (l r : All_predInt)
: All_predInt :=
  cross abs l r.

Fixpoint flatten {T} (ls : list (list T)) : list T :=
  match ls with
  | List.nil => List.nil
  | l :: ls => l ++ flatten ls
  end.

Definition lift_flatten (abs : predInt -> predInt -> All_predInt) (l r : All_predInt)
: All_predInt :=
  flatten (cross abs l r).


Theorem lift_sound : forall op abs_op fs,
    (forall a b c d,
        predIntD a b fs ->
        predIntD c d fs ->
        predIntD (abs_op a c) (op b d) fs) ->
    forall l r c d,
      All_predIntD l c fs ->
      All_predIntD r d fs ->
      All_predIntD (lift abs_op l r) (op c d) fs.
Proof.
  unfold All_predIntD. intros.
  unfold lift.
  eapply Forall_forall.
  intros.
  eapply cross_In in H2.
  forward_reason.
  subst.
  eapply Forall_forall in H0; eauto.
  eapply Forall_forall in H1; eauto.
Qed.

Definition split_All_predInt (P : fstate -> Prop) (Ps : All_predInt)
: All_predInt :=
  List.map (fun x =>
              {| premise := fun f => x.(premise) f /\ P f
               ; lb := x.(lb)
               ; ub := x.(ub) |}) Ps ++
  List.map (fun x =>
              {| premise := fun f => x.(premise) f /\ ~P f
               ; lb := x.(lb)
               ; ub := x.(ub) |}) Ps.


Theorem All_predInt_split : forall Ps (P : fstate -> Prop),
    (forall fs, P fs \/ ~P fs) ->
    All_predInt_entails (split_All_predInt P Ps) Ps.
Proof.
  intros. red. intros.
  unfold All_predIntD in *.
  eapply Forall_forall. intros.
  rewrite Forall_forall in H0.
  setoid_rewrite in_app_iff in H0.
  setoid_rewrite in_map_iff in H0.
  specialize (H fs).
  destruct H.
  { specialize (H0 ({|
          lb := lb x;
          ub := ub x;
          premise := fun f : fstate => premise x f /\ P f |})).
    red in H0. simpl in H0.
    red. intros.
    eapply H0.
    left. eauto.
    tauto. }
  { specialize (H0 ({|
          lb := lb x;
          ub := ub x;
          premise := fun f : fstate => premise x f /\ ~P f |})).
    red in H0. simpl in H0.
    red. intros.
    eapply H0.
    right. eauto.
    tauto. }
Qed.
