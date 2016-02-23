Require Import SMT.Tactic.
Require Import Coq.micromega.Psatz.
Require Import Coq.Reals.Raxioms.
Require Import Coq.micromega.Psatz.
Require Import Abstractor.Source.
Require Import Flocq.Core.Fcore_defs.

Require Import Integers.
Require Import Coq.Reals.Rdefinitions.
Require Import List.
Import ListNotations.
Require Import Flocq.Appli.Fappli_IEEE.
Require Import Flocq.Appli.Fappli_IEEE_bits.
Require Import Flocq.Core.Fcore_Raux.
Require Import Source.
Require Import Coq.Reals.Raxioms.
Require Import Coq.micromega.Psatz.
Require Import Flocq.Prop.Fprop_relative.
Require Import Flocq.Core.Fcore_Raux.
Require Import Flocq.Core.Fcore_FLT.
Require Import Flocq.Core.Fcore_generic_fmt.


Require Import Flocq.Core.Fcore_Raux.


Local Open Scope HP_scope.

Definition error    : R := bpow radix2 (- (custom_prec) + 1).
Definition floatMax : R := bpow radix2 custom_emax.
Definition floatMin : R := bpow radix2 custom_emin%Z.

Record predInt : Type :=
  mkPI { lb : fstate -> R
       ; ub : fstate -> R
       ; premise : fstate -> Prop }.

Arguments is_finite {_ _} _.

Definition predIntD (p : predInt) (f : float) (fs : fstate) : Prop :=
  p.(premise) fs ->
  is_finite f = true /\
  (p.(lb) fs <= B2R _ _ f <= p.(ub) fs)%R.

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

(** * Rounding Approximation **)
Let the_round : R -> R :=
  round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_ZR).

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
    (custom_prec <= k - FLT_exp (3 - custom_emax - custom_prec) custom_prec k)%Z.
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
  generalize (@relative_error radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                              (fexp_correct _ _ custom_precGt0) custom_emin custom_prec
                              relative_error_prem
                              (round_mode mode_ZR) (valid_rnd_round_mode _)
                              a H).
  intros.
  unfold the_round.
  generalize dependent (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_ZR) a).
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
  generalize (@relative_error radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                              (fexp_correct _ _ custom_precGt0) custom_emin custom_prec
                              relative_error_prem
                              (round_mode mode_ZR) (valid_rnd_round_mode _)
                              a H).
  intros.
  unfold the_round.
  generalize dependent (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_ZR) a).
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

Definition float_bounded (r : R) : Prop :=
  (- floatMax < r < floatMax)%R.

Definition absFloatPlus' (l r : predInt) : predInt :=
  let min fst := roundDown (l.(lb) fst + r.(lb) fst) in
  let max fst := roundUp   (l.(ub) fst + r.(ub) fst) in
  {| premise := fun fst => l.(premise) fst /\ r.(premise) fst
                        /\ float_bounded (min fst) /\ float_bounded (max fst)
   ; lb := min
   ; ub := max |}%R.

Require Import ExtLib.Tactics.

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
           round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_ZR) c)%R;
        [ psatz R | ].
      eapply Rle_trans; [ eapply roundDown_round | ].
      eapply Rle_trans; [ eapply round_le | eapply Rle_refl ].
      - eapply fexp_correct. eapply custom_precGt0.
      - eapply valid_rnd_round_mode.
      - psatz R. }
    { destruct H0.
      cut (round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec) (round_mode mode_ZR) c
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

Theorem absFloatPlus'_ok : forall lp lv rp rv fs,
    predIntD lp lv fs ->
    predIntD rp rv fs ->
    predIntD (absFloatPlus' lp rp) (float_plus lv rv) fs.
Proof.
  unfold predIntD. simpl; intros.
  forward_reason.
  unfold float_plus.
  generalize (@Bplus_correct _ _ custom_precGt0 custom_precLtEmax custom_nan mode_ZR _ _ H H0).
  eapply apply_float_bounded_lt; eauto. psatz R.
  intros.
  split; try tauto.
  destruct H10. rewrite H10. tauto.
Qed.

Definition absFloatMinus' (l r : predInt) : predInt :=
  let min fst := roundDown (l.(lb) fst - r.(ub) fst) in
  let max fst := roundUp   (l.(ub) fst - r.(lb) fst) in
  {| premise := fun fst => l.(premise) fst /\ r.(premise) fst /\ float_bounded (min fst) /\ float_bounded (max fst)
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
  destruct H10. rewrite H10. tauto.
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
      destruct (Rle_dec 0 r4); try_elim.
      - right. right. right. psatz R.
      - right. right. right. psatz R. } }
  { intros.
    rewrite H in *. rewrite H0 in *. simpl in H10.
    split; try tauto.
    destruct H10. rewrite H10. tauto. }
Qed.
