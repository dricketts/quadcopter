Require Import Coq.micromega.Psatz.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.

Require Import ExtLib.Data.List.
Require Import ExtLib.Tactics.

Require Import SMT.Tactic.

Require Import Flocq.Appli.Fappli_IEEE.
Require Import Flocq.Appli.Fappli_IEEE_bits.
Require Import Flocq.Core.Fcore_Raux.
Require Import Flocq.Prop.Fprop_relative.
Require Import Flocq.Core.Fcore_FLT.
Require Import Flocq.Core.Fcore_generic_fmt.
Require Import Flocq.Core.Fcore_defs.
Require Import Abstractor.FloatOps.
Require Import Abstractor.FloatLang.
Require Import Abstractor.Integers.
Require Import Abstractor.Bound.

Import ListNotations.

(** * "Simplified" Addition **)

Open Scope R_scope.

Definition absFloatPlus_demo_spec (l r : predInt) : All_predInt :=
  let min fst := roundDown (l.(lb) fst + r.(lb) fst) in
  let max fst := roundUp   (l.(ub) fst + r.(ub) fst) in
  let result :=
    {| premise := fun fst => l.(premise) fst /\ r.(premise) fst
                        /\ float_bounded (min fst) /\ float_bounded (max fst)
                        /\ l.(lb) fst <= l.(ub) fst /\ r.(lb) fst <= r.(ub) fst
    ; lb := min
    ; ub := max |}
  in
  split_All_predInt (fun fst => floatMin <= (l.(lb) fst + r.(lb) fst))%R (result :: List.nil).

Record Refine_All_pred_f (x : predInt -> predInt -> All_predInt) :=
  { optimized : predInt -> predInt -> All_predInt
  ; optimized_proof : forall a b, All_predInt_entails (optimized a b) (x a b) }.

Lemma done : All_predInt_entails List.nil List.nil.
Proof.
  unfold All_predInt_entails.
  intros. apply H.
Qed.

Lemma drop : forall P Ps Ps',
    (forall fs, P.(premise) fs -> False) ->
    All_predInt_entails Ps Ps' ->
    All_predInt_entails (P :: Ps) Ps'.
Proof.
  intros.
  unfold All_predInt_entails in *.
  intros.
  assert (All_predIntD Ps f fs).
  unfold All_predIntD in *.
  apply List.Forall_cons_iff in H1.
  destruct H1.
  apply H2.
  specialize (H0 f fs H2).
  apply H0.
Qed.

Lemma keep : forall P P' Ps Ps',
    predInt_entails P P' ->
    All_predInt_entails Ps Ps' ->
    All_predInt_entails (P :: Ps) (P' :: Ps').
Proof. 
 intros.
 unfold All_predInt_entails in *.
 intros.
 specialize (H0 f fs).
 unfold All_predIntD in *.
 apply List.Forall_cons_iff in H1.
 destruct H1.
 specialize (H0 H2).
 apply Forall_cons.
 unfold predInt_entails in *.
 specialize (H _ _ H1).
 apply H.
 apply H0.
Qed.

Lemma refine_predInt_entails_flip : forall a (P : _ -> Prop) l u,
    (forall fs, P fs -> a.(premise) fs)%R ->
    (forall fs, a.(premise) fs -> P fs -> l fs <= a.(lb) fs /\ a.(ub) fs <= u fs)%R ->
    predInt_entails a {| premise := P ; lb := l ; ub := u |}.
Proof.
  intros.
  unfold predInt_entails in *.
  intros.
  unfold predIntD in *.
  intros.
  simpl in *.
  specialize (H _ H2).
  specialize (H0 _ H H2).
  specialize (H1 H).
  destruct H1.
  split.
  apply H1.
  destruct H0.
  psatz R.
Qed.

Lemma refine_predInt_entails : forall a (P : _ -> Prop) l u,
    (forall fs, a.(premise) fs -> P fs)%R ->
    (forall fs, a.(premise) fs -> P fs -> a.(lb) fs <= l fs /\ a.(ub) fs >= u fs)%R ->
    predInt_entails {| premise := P ; lb := l ; ub := u |} a.
Proof. 
  intros.
  unfold predInt_entails in *.
  unfold predIntD in *.
  intros.
  specialize (H _ H2).
  specialize (H0 _ H2 H).
  simpl in *.
  specialize (H1 H).
  destruct H1.
  split.
  apply H1.
  psatz R.
Qed.

Axiom todo: forall T : Prop, T.

Ltac use H :=
  match goal with
  | |- _ ?fs => refine (conj H _)
  end.

Lemma boundLbGtFloatMin : forall x, floatMin <= x -> roundDown x = roundDown_relative x.
Proof.
  unfold roundDown; simpl. 
  intros. 
  unfold Rabs.
  assert (floatMin > 0).
  unfold floatMin.
  pose proof bpow_gt_0.
  apply H0.
  destruct Rcase_abs.
  psatz R.
  destruct Rlt_dec.
  psatz R.
  reflexivity.
Qed.

Lemma floatMinGt0 : floatMin > 0.
  unfold floatMin.
  pose proof bpow_gt_0.
  specialize (H radix2 custom_emin).
  psatz R.
Qed.

Lemma floatMinGe0 : floatMin >= 0.
  unfold floatMin.
  pose proof bpow_gt_0.
  specialize (H radix2 custom_emin).
  psatz R.
Qed.

Lemma boundUbGtFloatMin : forall x, floatMin <= x -> roundUp x = roundUp_relative x.
Proof. 
  unfold roundUp; simpl.
  intros.
  unfold Rabs.
  assert (floatMin > 0).
  unfold floatMin.
  pose proof bpow_gt_0.
  apply H0.
  destruct Rcase_abs.
  psatz R.
  destruct Rlt_dec.
  psatz R.
  reflexivity.
Qed.

Lemma boundUbBet0AndFloatMin : forall x, 0 <= x /\ x < floatMin -> roundUp x = roundUp_subnormal x.
Proof. 
  unfold roundUp; simpl.
  intros.
  unfold Rabs.
  destruct Rcase_abs.
  psatz R.
  destruct Rlt_dec.
  reflexivity.
  psatz R.
Qed.  

Lemma boundUbBetNegFloatMinAnd0 : forall x, x < 0 /\ x > - floatMin -> roundUp x = roundUp_subnormal x.
  Proof.
    unfold roundUp; simpl.
    intros.
    unfold Rabs.
    destruct Rcase_abs.
    destruct Rlt_dec.
    reflexivity.
    psatz R.
    psatz R.
  Qed.

  Lemma boundUbLessThanFloatMin : forall x,  x <= - floatMin -> roundUp x = roundUp_relative x.
  Proof.
    unfold roundUp; simpl.
    intros.
    unfold Rabs.
    pose proof floatMinGt0.
    destruct Rcase_abs.
    destruct Rlt_dec.
    psatz R.
    reflexivity.
    psatz R.
  Qed.
  
Lemma drop1 : forall p p1,
                (forall fs, p.(premise) fs -> False) ->
                All_predInt_entails (p1) (List.nil)->
                All_predInt_entails (p1) (p::List.nil).
Proof.
  intros.
  unfold All_predInt_entails.
  unfold All_predIntD in *.
  intros.
  SearchAbout Forall.
  apply Forall_cons.
  unfold predIntD.
  intros.
  specialize (H _ H2).
  intuition.
  apply Forall_nil.
Qed.

Lemma boundLbBet0AndFloatMin : forall x, x >= 0 -> x < floatMin -> roundDown x = -floatMin.
 Proof.
   intros.
   unfold roundDown.
   unfold Rabs.
   assert (floatMin > 0).
   unfold floatMin.
   pose proof bpow_gt_0.
   apply H1.
   destruct Rcase_abs.
   psatz R.
   destruct Rlt_dec.
   unfold roundDown_subnormal.
   psatz R.
   psatz R.
Qed.

Lemma boundLbBetNegFloatMinAnd0 : forall x, x < 0 -> x > -floatMin -> roundDown x = -floatMin.
 Proof.
   intros.
   unfold roundDown.
   unfold Rabs.
   pose proof floatMinGt0.
   destruct Rcase_abs.
   destruct Rlt_dec.
   unfold roundDown_subnormal.
   reflexivity.
   psatz R.
   psatz R.
Qed.

Lemma boundLbLessThanFloatMin : forall x, x <= - floatMin -> roundDown x = roundDown_relative x.
  intros.
  pose proof floatMinGt0.
  unfold roundDown.
  unfold Rabs.
  destruct Rcase_abs.
  {
    destruct Rlt_dec.
    psatz R.
   reflexivity.
  }
  psatz R.
Qed.
 
 Lemma simpl : forall pUnk pNew pOld, All_predInt_entails pNew pOld ->  All_predInt_entails pUnk pNew -> All_predInt_entails pUnk pOld.
  intros.
  unfold All_predInt_entails in *. intros.
  specialize (H0 _ _ H1).
  specialize (H _ _  H0).
  apply H.
  Qed.

Lemma simpl2 : forall pred p1 p2, All_predInt_entails p1 (split_All_predInt pred p2) -> All_predInt_entails p1 p2. 
  intros.
  eapply simpl.
  eapply All_predInt_split.
  intros.
  assert (pred fs \/ ~(pred fs)).
  tauto.
  exact H0.
  apply H.
Qed.


 Lemma AllPredImpl : forall p p1 p2, All_predInt_entails p1 (p :: List.nil) -> All_predInt_entails p1 p2 -> All_predInt_entails p1 (p :: p2).
  Proof. 
    intros. 
    unfold All_predInt_entails in *.
    intros.
    unfold All_predIntD in *.
    specialize (H f fs H1).
    specialize (H0 f fs H1).
    SearchAbout Forall.
    apply Forall_cons.
    apply List.Forall_cons_iff in H.
    destruct H.
    apply H.
    apply H0.
  Qed.




  Lemma AllPredEntImplPredEnt : forall p1 p2, All_predInt_entails (p1 :: List.nil) (p2 :: List.nil) -> predInt_entails p1 p2.
    Proof.
      intros.
      unfold All_predInt_entails in *.
      unfold All_predIntD in *.
      unfold predInt_entails.
      intros.
      specialize (H f fs).
      SearchAbout Forall.
      apply List.Forall_cons_iff in H.
      destruct H.
      apply H.
      apply Forall_cons. 
      apply H0.
      apply Forall_nil.
    Qed.

  Lemma simpl1 : forall (A:Type) (pred:A ->Prop) p1 p2, Forall pred (p1 ++ p2) -> (Forall pred p1) /\ (Forall pred p2). 
    Proof.
      intros.
      split.
      apply Forall_forall.
      pose proof Forall_forall.
      specialize (H0 _ pred (p1 ++ p2) ).
      destruct H0.
      specialize (H0 H).
      intros.
      specialize (H0 x).
      SearchAbout List.In.
      pose proof in_or_app.
      specialize (H3 _ p1 p2 x).
      assert (List.In x p1 \/ List.In x p2).
      constructor 1.
      apply H2.
      specialize (H3 H4).
      specialize (H0 H3).
      apply H0.
      

      apply Forall_forall.
      pose proof Forall_forall.
      specialize (H0 _ pred (p1 ++ p2) ).
      destruct H0.
      specialize (H0 H).
      intros.
      specialize (H0 x).
      SearchAbout List.In.
      pose proof in_or_app.
      specialize (H3 _ p1 p2 x).
      assert (List.In x p1 \/ List.In x p2).
      constructor 2.
      apply H2.
      specialize (H3 H4).
      specialize (H0 H3).
      apply H0.
    Qed.
 Lemma AllPredIntKeep :  forall p p1 p2 p3,  All_predInt_entails p1 [p] -> All_predInt_entails p2 p3-> All_predInt_entails (p1 ++ p2) (p :: p3). 
  Proof.
    intros.
    unfold All_predInt_entails in *.
    intros.
    specialize (H f fs).
    specialize (H0 f fs).
    unfold All_predIntD in *.
   
    Check Forall.
  
    intros.
    apply simpl1 in H1.
    destruct H1.
    specialize (H H1).
    specialize (H0 H2).
    SearchAbout Forall.
    apply Forall_cons.
    apply List.Forall_cons_iff in H.
    destruct H.
    apply H.
    apply H0.
  Qed.
    

Definition absFloatPlus_demo : predInt -> predInt -> All_predInt.
refine (@optimized absFloatPlus_demo_spec _).
econstructor.
intros. unfold absFloatPlus_demo_spec.
unfold split_All_predInt; simpl.
eapply keep.
{ eapply refine_predInt_entails; simpl; intros.
  exact H.  
  simpl in H0.
  forward_reason.
  split.
  { 
    rewrite boundLbGtFloatMin.
    apply Rle_refl. assumption. }
  { rewrite boundUbGtFloatMin. apply Rle_refl. psatz R. } }
{ 
 
  eapply simpl2 with ((fun f:fstate => lb a f + lb b f >= 0)).
  eapply simpl2 with ((fun f:fstate => ub a f + ub b f >= floatMin)).
  unfold split_All_predInt; simpl.
  eapply keep.
  {
    eapply refine_predInt_entails; simpl; intros.
    exact H.
    simpl in H0.
    forward_reason.
    split.
    {
      rewrite boundLbBet0AndFloatMin. 
      pose proof floatMinGt0.
      assert (- floatMin <= 0).
      psatz R.
      exact H18.
      psatz R.
      psatz R.
    }
    {
      rewrite boundUbGtFloatMin.
      apply Rle_refl. 
      psatz R.
    }
  }
 
  intros.
   
 
  eapply AllPredIntKeep.
  {
    eapply simpl2 with ((fun f:fstate => lb a f + lb b f > -floatMin)).
    unfold split_All_predInt; simpl.
    eapply keep.
    {
      eapply refine_predInt_entails; simpl; intros.
      exact H.
      simpl in H0.
      forward_reason.
      split.
      {
        rewrite boundLbBetNegFloatMinAnd0.
        eapply Rle_refl.
        psatz R.
        psatz R.
      }
      {
        rewrite boundUbGtFloatMin.
        apply Rle_refl. 
        psatz R.
      }
    }
    {
      eapply keep.
      {
        eapply refine_predInt_entails; simpl; intros.
        exact H.
        simpl in H0.
        forward_reason.
        split.
        {
          rewrite boundLbLessThanFloatMin.
          eapply Rle_refl.
          psatz R.
        }
        {
          rewrite boundUbGtFloatMin.
          apply Rle_refl. 
          psatz R.
        }
      }
      {
        eapply done.
      }
    }
  }
  {
    eapply AllPredIntKeep.
    {
      eapply simpl2 with ((fun f:fstate => ub a f + ub b f >= 0)).
      unfold split_All_predInt; simpl.
      eapply keep.
      {
        eapply refine_predInt_entails; simpl; intros.
        exact H.
        simpl in H0.
        forward_reason.
        split.
        {
          rewrite boundLbBet0AndFloatMin.
          assert (-floatMin <= 0).
          pose proof floatMinGt0.
          psatz R.
          exact H19.
          psatz R.
          psatz R.
        }
        {
          rewrite boundUbBet0AndFloatMin.
          unfold roundUp_subnormal.
          apply Rle_refl.
          psatz R.
        }
      }      
      { 
        intros.
        eapply drop1.
        intros.
        simpl in *.
        psatz R.
        eapply done.
      }
    }
    {
      eapply simpl2 with ((fun f:fstate => lb a f + lb b f <= -floatMin)).
      eapply simpl2 with ((fun f:fstate => ub a f + ub b f >= R0)).
      unfold split_All_predInt; simpl.
      eapply keep.
      {
        eapply refine_predInt_entails; simpl; intros.
        exact H.
        simpl in H0.
        forward_reason.
        split.
        {
          rewrite boundLbLessThanFloatMin.
          eapply Rle_refl.
          psatz R.
        }
        {
          rewrite boundUbBet0AndFloatMin.
          unfold roundUp_subnormal.
          apply Rle_refl.
          psatz R.
        }
      }     
      {        
        eapply keep.
        {
          eapply refine_predInt_entails; simpl; intros.
          exact H.
          simpl in H0.
          forward_reason.
          split.
          {
            rewrite boundLbBetNegFloatMinAnd0.
            eapply Rle_refl.
            psatz R.
            psatz R.
          }
          {
            rewrite boundUbBet0AndFloatMin.
            unfold roundUp_subnormal.
            apply Rle_refl.
            psatz R.
          }
        }
        {
          eapply AllPredIntKeep.
          {
             eapply simpl2 with ((fun f:fstate => ub a f + ub b f <= -floatMin)).
             unfold split_All_predInt; simpl.
             eapply keep.
             {
               eapply refine_predInt_entails; simpl; intros.
               exact H.
               simpl in H0.
               forward_reason.
               split.
               {
                 rewrite boundLbLessThanFloatMin.
                 eapply Rle_refl.
                 psatz R.
               }
               {
                 rewrite boundUbLessThanFloatMin.
                 apply Rle_refl.
                 psatz R.
               }
             }
             {
               eapply keep.
               {
                 eapply refine_predInt_entails; simpl; intros.
                 exact H.
                 simpl in H0.
                 forward_reason.
                 split.
                 {
                   rewrite boundLbLessThanFloatMin.
                   eapply Rle_refl.
                   psatz R.
                 }
                 {
                   rewrite boundUbBetNegFloatMinAnd0.
                   unfold roundUp_subnormal.
                   pose proof floatMinGt0.
                   assert (floatMin >= 0).
                   psatz R.
                   exact H24.
                   psatz R.
                 }
               }
               {
                 apply done.
               }
             }
          }
          {
            eapply simpl2 with ((fun f:fstate => ub a f + ub b f <= -floatMin)).
            unfold split_All_predInt; simpl.
            eapply keep.
            {
              eapply refine_predInt_entails; simpl; intros.
                 exact H.
                 simpl in H0.
                 forward_reason.
                 split.
                 {
                   rewrite boundLbLessThanFloatMin.
                   eapply Rle_refl.
                   psatz R.
                 }
                 {
                   rewrite boundUbLessThanFloatMin.
                   apply Rle_refl.
                   psatz R.
                 }
            }
            {
              eapply keep. 
              eapply refine_predInt_entails; simpl; intros.
              exact H.
              simpl in H0.
              forward_reason.
              split.
              {
                rewrite boundLbBetNegFloatMinAnd0.
                eapply Rle_refl.
                psatz R.
                psatz R.
              }
              {
                rewrite boundUbBetNegFloatMinAnd0.
                unfold roundUp_subnormal.
                pose proof floatMinGt0.
                assert (floatMin >= 0).
                psatz R.
                exact H24.
                psatz R.
              }
              
              eapply done.
            }
          }
        }
      }
    }
  }
}
Defined.

Eval cbv beta iota zeta delta [ absFloatPlus_demo optimized ] in absFloatPlus_demo.


Definition absFloatMinus_demo_spec (l r : predInt) : All_predInt :=
  let min fst := roundDown (l.(lb) fst - r.(ub) fst) in
  let max fst := roundUp   (l.(ub) fst - r.(lb) fst) in
  let result :=
    {| premise := fun fst => l.(premise) fst /\ r.(premise) fst
                        /\ float_bounded (min fst) /\ float_bounded (max fst)
                        /\ l.(lb) fst <= l.(ub) fst /\ r.(lb) fst <= r.(ub) fst
    ; lb := min
    ; ub := max |}
  in
  split_All_predInt (fun fst => floatMin <= (l.(lb) fst - r.(ub) fst))%R (result :: List.nil).

Definition absFloatMult_demo_spec (l r : predInt) : All_predInt :=
  let min fst := roundDown (Rmin4 (l.(lb) fst * r.(lb) fst)
                                  (l.(lb) fst * r.(ub) fst)
                                  (l.(ub) fst * r.(lb) fst)
                                  (l.(ub) fst * r.(ub) fst)) in
  let max fst := roundUp   (Rmax4 (l.(lb) fst * r.(lb) fst)
                                  (l.(lb) fst * r.(ub) fst)
                                  (l.(ub) fst * r.(lb) fst)
                                  (l.(ub) fst * r.(ub) fst)) in
  let result := 
      {| premise := fun fst => l.(premise) fst /\ r.(premise) fst
                        /\ float_bounded (min fst) /\ float_bounded (max fst)
                        /\ l.(lb) fst <= l.(ub) fst /\ r.(lb) fst <= r.(ub) fst
(*                      /\ min fst <= max fst *)
   ; lb := min
   ; ub := max |}
    in
      split_All_predInt (fun fst => l.(ub) fst < 0 /\ r.(ub) fst < 0)%R (result :: List.nil). 


Lemma multRoundMin1 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> u1 < 0 -> u2 < 0 -> (Rmin4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = u1 * u2.
Proof.
  intros.
  unfold Rmin4.
  unfold Rmin.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma multRoundMax1 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> u1 < 0 -> u2 < 0 ->
(Rmax4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = l1 * l2.
Proof.
  intros.
  unfold Rmax4.
  unfold Rmax.
   destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
   Qed.

Lemma multRoundMin2 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 < 0 -> u1 >= 0 -> l2 < 0 -> u2 < 0 ->  (Rmin4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = u1 * l2.
Proof.
  intros.
  unfold Rmin4.
  unfold Rmin.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.
Lemma multRoundMax2 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 < 0 -> u1 >= 0 -> l2 < 0 -> u2 < 0 ->  (Rmax4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = l1 * l2.
Proof.
  intros.
  unfold Rmax4.
  unfold Rmax.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma multRoundMin3 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 >= 0 -> u1 >= 0 -> l2 < 0 -> u2 < 0 ->  (Rmin4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = u1 * l2.
Proof.
  intros.
  unfold Rmin4.
  unfold Rmin.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.
Lemma multRoundMax3 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 >= 0 -> u1 >= 0 -> l2 < 0 -> u2 < 0 ->  (Rmax4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = l1 * u2.
Proof.
  intros.
  unfold Rmax4.
  unfold Rmax.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma multRoundMin4 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 < 0 -> u1 < 0 -> l2 < 0 -> u2 >= 0 ->  (Rmin4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = l1 * u2.
Proof.
  intros.
  unfold Rmin4.
  unfold Rmin.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma multRoundMax4 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 < 0 -> u1 < 0 -> l2 < 0 -> u2 >= 0 ->  (Rmax4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = l1 * l2.
Proof.
  intros.
  unfold Rmax4.
  unfold Rmax.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma multRoundMin5 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 < 0 -> u1 >= 0 -> l2 < 0 -> u2 >= 0 -> u1 * l2 <= l1 * u2 ->  (Rmin4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = u1 * l2.
Proof.
  intros.
  unfold Rmin4.
  unfold Rmin.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma multRoundMax5 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 < 0 -> u1 >= 0 -> l2 < 0 -> u2 >= 0 -> l1 * l2 >= u1 * u2 ->  (Rmax4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = l1 * l2.
Proof.
  intros.
  unfold Rmax4.
  unfold Rmax.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

 Lemma multRoundMin6 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 < 0 -> u1 >= 0 -> l2 < 0 -> u2 >= 0 -> u1 * l2 > l1 * u2 ->  (Rmin4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = l1 * u2.
Proof.
  intros.
  unfold Rmin4.
  unfold Rmin.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma multRoundMax6 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 < 0 -> u1 >= 0 -> l2 < 0 -> u2 >= 0 -> l1 * l2 < u1 * u2 ->  (Rmax4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = u1 * u2.
Proof.
  intros.
  unfold Rmax4.
  unfold Rmax.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma multRoundMin7 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 >= 0 -> u1 >= 0 -> l2 < 0 -> u2 >= 0 ->  (Rmin4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = u1 * l2.
Proof.
  intros.
  unfold Rmin4.
  unfold Rmin.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma multRoundMax7 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 >= 0 -> u1 >= 0 -> l2 < 0 -> u2 >= 0 ->  (Rmax4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = u1 * u2.
Proof.
  intros.
  unfold Rmax4.
  unfold Rmax.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.


         Lemma multRoundMin8 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 < 0 -> u1 < 0 -> l2 >= 0 -> u2 >= 0 ->  (Rmin4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = l1 * u2.
Proof.
  intros.
  unfold Rmin4.
  unfold Rmin.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma multRoundMax8 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 < 0 -> u1 < 0 -> l2 >= 0 -> u2 >= 0 ->  (Rmax4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = l2 * u1.
Proof.
  intros.
  unfold Rmax4.
  unfold Rmax.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma multRoundMin9 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 < 0 -> u1 >= 0 -> l2 >= 0 -> u2 >= 0 ->  (Rmin4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = l1 * u2.
Proof.
  intros.
  unfold Rmin4.
  unfold Rmin.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma multRoundMax9 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 < 0 -> u1 >= 0 -> l2 >= 0 -> u2 >= 0 ->  (Rmax4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = u1 * u2.
Proof.
  intros.
  unfold Rmax4.
  unfold Rmax.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.


Lemma multRoundMin10 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 >= 0 -> u1 >= 0 -> l2 >= 0 -> u2 >= 0 ->  (Rmin4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = l1 * l2.
Proof.
  intros.
  unfold Rmin4.
  unfold Rmin.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma multRoundMax10 : forall l1 l2 u1 u2, l1 <= u1 -> l2 <= u2 -> l1 >= 0 -> u1 >= 0 -> l2 >= 0 -> u2 >= 0 ->  (Rmax4 (l1 * l2) (l1 * u2) (u1 * l2) (u1 * u2)) = u1 * u2.
Proof.
  intros.
  unfold Rmax4.
  unfold Rmax.
  destruct Rle_dec;
    destruct Rle_dec;
    destruct Rle_dec;
    psatz R;
    psatz R.
Qed.

Lemma roundDownMultGeFloatMin : forall u1 u2, u1 * u2 >= floatMin \/ u1 * u2 <= -floatMin -> roundDown (u1 * u2) = roundDown_relative (u1 * u2).
Proof.
  intros; unfold roundDown. 
  destruct H.
  rewrite Rabs_right.
  destruct Rlt_dec.
  psatz R. reflexivity.
  pose proof floatMinGt0;
    psatz R.
  rewrite Rabs_left.
  destruct Rlt_dec.
  psatz R. reflexivity.
  pose proof floatMinGt0;
    psatz R.
Qed.

Lemma roundDownMultLtFloatMin : forall u1 u2, R0 <= u1 * u2 < floatMin \/ -floatMin < u1 * u2 < R0  -> roundDown (u1 * u2) = roundDown_subnormal (u1 * u2).
Proof.
  intros; unfold roundDown. 
  destruct H.
  rewrite Rabs_right.
  destruct Rlt_dec.
  reflexivity. psatz R. psatz R.
  rewrite Rabs_left.
  destruct Rlt_dec.
  reflexivity. psatz R. psatz R.
Qed.
(*
  unfold Rabs. destruct Rcase_abs.
  destruct Rlt_dec.
  reflexivity. 
  psatz R. 
  apply Rge_le in r.
  apply Rle_lt_or_eq_dec in r.
  destruct r. psatz R. 
  destruct Rlt_dec. reflexivity.
  unfold roundDown_relative.
  rewrite <- e.
  
  unfold roundDown_subnormal.
  Check Rcase_abs.
  SearchAbout (_ >= _ -> _ <= _)%R.
  SearchAbout ({_ < _} + {_ = _})%R.
  psatz R.
  psatz R.
 .*)

      
Lemma roundUpMultGeFloatMin : forall u1 u2, u1 * u2 >= floatMin \/ u1 * u2 <= -floatMin -> roundUp (u1 * u2) = roundUp_relative (u1 * u2).
      Proof.
        intros; unfold roundUp.
        destruct H.
        rewrite Rabs_right.
        destruct Rlt_dec.
        psatz R. reflexivity.
        pose proof floatMinGt0;
        psatz R.
        rewrite Rabs_left.
        destruct Rlt_dec.
        psatz R. reflexivity.
        pose proof floatMinGt0;
        psatz R.
      Qed.

Lemma roundUpMultLtFloatMin : forall u1 u2, R0 <= u1 * u2 < floatMin \/ -floatMin < u1 * u2 < R0 -> roundUp (u1 * u2) = roundUp_subnormal (u1 * u2).
Proof.
  intros; unfold roundUp.
  destruct H.
  rewrite Rabs_right.
  destruct Rlt_dec.
  reflexivity. psatz R.
  psatz R.
  rewrite Rabs_left.
  destruct Rlt_dec.
  reflexivity. psatz R.
  psatz R.
Qed.

Lemma lbProofLtFloatMin1 : 
  forall l1 l2 u1 u2,     
    l1 <= u1 -> l2 <= u2 -> u1 < 0 -> u2 < 0 -> u1 * u2 >= 0 -> u1 * u2 < floatMin ->
    roundDown (Rmin4 (l1 * l2) (l1 * u2) 
                     (u1 * l2) (u1 * u2)) = -floatMin.
Proof.
  intros.
  rewrite multRoundMin1.
  rewrite roundDownMultLtFloatMin.
  unfold roundDown_subnormal.
  psatz R. psatz R. psatz R.
  psatz R. psatz R. psatz R. 
Qed.


Lemma UbProofGtFloatMin1 : 
  forall l1 l2 u1 u2,
    l1 <= u1 -> l2 <= u2 -> u1 < 0 -> u2 < 0 -> l1 * l2 >= floatMin ->
    roundUp (Rmax4 (l1 * l2) (l1 * u2) 
                     (u1 * l2) (u1 * u2)) = roundUp_relative(l1 * l2).
Proof.
  intros.
  rewrite multRoundMax1.
  rewrite roundUpMultGeFloatMin.
  reflexivity.
  psatz R. psatz R. psatz R.
  psatz R. psatz R. 
Qed.

Lemma negFloatMinLe0 : -floatMin <= 0.
  pose proof floatMinGt0.
  psatz R.
Qed.

Definition absFloatMult_demo : predInt -> predInt -> All_predInt.
  refine (@optimized absFloatMult_demo_spec _).
   econstructor; intros.
   unfold absFloatMult_demo_spec.
   unfold split_All_predInt; simpl.
   eapply AllPredIntKeep.
   {
     eapply simpl2 with ((fun f:fstate => ub a f * ub b f >= floatMin)).
     unfold split_All_predInt; simpl.
     eapply keep.
     { 
       eapply refine_predInt_entails; simpl; intros.
       exact H. simpl in H0. forward_reason.
       split.
       {
         rewrite multRoundMin1. rewrite roundDownMultGeFloatMin.
         apply Rle_refl. psatz R. psatz R. psatz R. psatz R. psatz R.
       }
       {
         rewrite UbProofGtFloatMin1. apply Rle_refl.
         psatz R. psatz R. psatz R. psatz R. psatz R.        
       }
     }
     {
       eapply AllPredIntKeep.
       {
         eapply simpl2 with ((fun f:fstate => ub a f * ub b f >= R0)).
         eapply simpl2 with ((fun f:fstate => lb a f * lb b f >= floatMin)).
         unfold split_All_predInt; simpl.
         eapply keep.
         { eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           { rewrite lbProofLtFloatMin1. pose proof negFloatMinLe0.
             apply Rle_refl.  psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite UbProofGtFloatMin1. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. 
           }
         }
         eapply AllPredIntKeep.
         { intros. eapply drop1. intros.
           simpl in *. psatz R. eapply done.
         }
         eapply simpl2 with ((fun f:fstate => lb a f * lb b f >= 0)).
         unfold split_All_predInt; simpl. eapply keep.
         { eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           { rewrite lbProofLtFloatMin1. pose proof negFloatMinLe0. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax1. rewrite roundUpMultLtFloatMin. unfold roundUp_subnormal.
             pose proof floatMinGt0. assert (floatMin >= 0). psatz R. exact H24.
             psatz R. psatz R. psatz R. psatz R. psatz R. 
           }
         }        
         eapply AllPredIntKeep.
         { intros. eapply drop1. intros.
           simpl in *. psatz R. eapply done.
         }
         eapply AllPredIntKeep.
         { intros. eapply drop1. intros.
           simpl in *. psatz R. eapply done.
         }
         eapply AllPredIntKeep.
         { intros. eapply drop1. intros.
           simpl in *. psatz R. eapply done.
         }
         eapply done.
       }
       eapply done.
     }
   }
   {
     eapply simpl2 with ((fun f:fstate => lb a f < 0 /\ ub a f >= 0 /\ lb b f < 0 /\ ub b f < 0)).
     unfold split_All_predInt; simpl.
     eapply AllPredIntKeep.
     {
       eapply simpl2 with ((fun f:fstate => ub a f * lb b f > - floatMin)).
       eapply simpl2 with((fun f:fstate => lb a f * lb b f >= floatMin)).
       unfold split_All_predInt; simpl.
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         { rewrite multRoundMin2. rewrite roundDownMultLtFloatMin.
           unfold roundDown_subnormal. apply Rle_refl.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
         }
         { rewrite multRoundMax2. rewrite roundUpMultGeFloatMin.
           unfold roundUp_relative. apply Rle_refl.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
         }
       }
       eapply keep.
       { eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         { rewrite multRoundMin2. rewrite roundDownMultGeFloatMin.
           apply Rle_refl.  psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
         { rewrite multRoundMax2. rewrite roundUpMultGeFloatMin.
           apply Rle_refl.  psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
         }
       }
       {
         eapply keep.
         { eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           { rewrite multRoundMin2. rewrite roundDownMultLtFloatMin.
             unfold roundDown_subnormal. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
           }
           { rewrite multRoundMax2. rewrite roundUpMultLtFloatMin.
             unfold roundUp_subnormal. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           } 
         }
         eapply keep.
         { eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           { rewrite multRoundMin2. rewrite roundDownMultGeFloatMin.
             apply Rle_refl. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
           }
           { rewrite multRoundMax2. rewrite roundUpMultLtFloatMin.
             unfold roundUp_subnormal. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           } 
         }
         eapply done.
       }
     }
     eapply simpl2 with ((fun f:fstate => lb a f >= 0 /\ ub a f >= 0 /\ lb b f < 0 /\ ub b f < 0)).
     unfold split_All_predInt; simpl.
     eapply AllPredIntKeep.
     {
       eapply simpl2 with ((fun f:fstate => ub a f * lb b f > - floatMin)).
       eapply simpl2 with((fun f:fstate => lb a f * ub b f > - floatMin)).
       {
         unfold split_All_predInt; simpl.
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           { rewrite multRoundMin3. rewrite roundDownMultLtFloatMin.
             unfold roundDown_subnormal. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
           }
           { rewrite multRoundMax3. rewrite roundUpMultLtFloatMin.
             unfold roundUp_subnormal. pose proof floatMinGt0. assert (floatMin >= 0).
             psatz R. exact H28. psatz R. psatz R. psatz R. psatz R. psatz R. 
             psatz R. psatz R. 
           }
         }
         eapply keep.
         { eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           { rewrite multRoundMin3. rewrite roundDownMultGeFloatMin.
             apply Rle_refl.  psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
           }
           { rewrite multRoundMax3. rewrite roundUpMultLtFloatMin.
             unfold roundUp_subnormal. pose proof floatMinGt0. assert (floatMin >= 0). psatz R.
             exact H28. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
           }
         }
         { eapply AllPredIntKeep.
           { intros. eapply drop1. intros.
             simpl in *. psatz R. eapply done.
           }
           eapply keep.
           {
             eapply refine_predInt_entails; simpl; intros.
             exact H. simpl in H0. forward_reason.
             split.
             { rewrite multRoundMin3. rewrite roundDownMultGeFloatMin.
               apply Rle_refl.  psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
             }
             { rewrite multRoundMax3. rewrite roundUpMultGeFloatMin.
               apply Rle_refl. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
             }
           }
           eapply done.
         }
       }
     }
     eapply simpl2 with ((fun f:fstate => lb a f < 0 /\ ub a f < 0 /\ lb b f < 0 /\ ub b f >= 0)).
     unfold split_All_predInt; simpl.
     eapply AllPredIntKeep.
     {
       eapply simpl2 with ((fun f:fstate => lb a f * ub b f > - floatMin)).
       eapply simpl2 with((fun f:fstate => lb a f * lb b f >= floatMin)).
       {
         unfold split_All_predInt; simpl.
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           { rewrite multRoundMin4. rewrite roundDownMultLtFloatMin.
             unfold roundDown_subnormal. apply Rle_refl.    
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
           }
           { rewrite multRoundMax4. rewrite roundUpMultGeFloatMin.
             unfold roundUp_relative. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply keep.
         { eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           { rewrite multRoundMin4. rewrite roundDownMultGeFloatMin.
             apply Rle_refl.  psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
           }
           { rewrite multRoundMax4. rewrite roundUpMultGeFloatMin.
             apply Rle_refl.  psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         {
           eapply keep.
           { eapply refine_predInt_entails; simpl; intros.
             exact H. simpl in H0. forward_reason.
             split.
             { rewrite multRoundMin4. rewrite roundDownMultLtFloatMin.
               unfold roundDown_subnormal. apply Rle_refl. 
               psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
             }
             { rewrite multRoundMax4. rewrite roundUpMultLtFloatMin.
               unfold roundUp_subnormal. apply Rle_refl.
               psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
             } 
           }
           eapply keep.
           { eapply refine_predInt_entails; simpl; intros.
             exact H. simpl in H0. forward_reason.
             split.
             { rewrite multRoundMin4. rewrite roundDownMultGeFloatMin.
               apply Rle_refl. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
             }
             { rewrite multRoundMax4. rewrite roundUpMultLtFloatMin.
               unfold roundUp_subnormal. apply Rle_refl. 
               psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
             } 
           }
           eapply done.
         }
       }
     }
     eapply simpl2 with ((fun f:fstate => lb a f < 0 /\ ub a f >= 0 /\ lb b f < 0 /\ ub b f >= 0)).
     unfold split_All_predInt; simpl.
     eapply AllPredIntKeep.
     {
       eapply simpl2 with ((fun f:fstate => lb a f * lb b f >= ub a f * ub b f)).
       eapply simpl2 with ((fun f:fstate => ub a f * lb b f <= lb a f * ub b f)).
       unfold split_All_predInt; simpl.
       eapply AllPredIntKeep.
       {
         eapply simpl2 with ((fun f:fstate => lb a f * lb b f >= floatMin)).
         eapply simpl2 with((fun f:fstate => ub a f * lb b f > - floatMin)).
         unfold split_All_predInt; simpl.
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin5. rewrite roundDownMultLtFloatMin.
             unfold roundDown_subnormal. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax5. rewrite roundUpMultGeFloatMin.
             unfold roundUp_relative. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin5. rewrite roundDownMultLtFloatMin.
             unfold roundDown_subnormal. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax5. rewrite roundUpMultLtFloatMin.
             unfold roundUp_subnormal. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin5. rewrite roundDownMultGeFloatMin.
             unfold roundDown_relative. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax5. rewrite roundUpMultGeFloatMin.
             unfold roundUp_relative. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin5. rewrite roundDownMultGeFloatMin.
             unfold roundDown_relative. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax5. rewrite roundUpMultLtFloatMin.
             unfold roundUp_subnormal. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply done.
       }
       eapply AllPredIntKeep.
       {
         eapply simpl2 with ((fun f:fstate => ub a f * ub b f >= floatMin)).
         eapply simpl2 with((fun f:fstate => ub a f * lb b f > - floatMin)).
         unfold split_All_predInt; simpl.
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin5. rewrite roundDownMultLtFloatMin.
             unfold roundDown_subnormal. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax6. rewrite roundUpMultGeFloatMin.
             unfold roundUp_relative. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin5. rewrite roundDownMultLtFloatMin.
             unfold roundDown_subnormal. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax6. rewrite roundUpMultLtFloatMin.
             unfold roundUp_subnormal. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin5. rewrite roundDownMultGeFloatMin.
             unfold roundDown_relative. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax6. rewrite roundUpMultGeFloatMin.
             unfold roundUp_relative. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin5. rewrite roundDownMultGeFloatMin.
             unfold roundDown_relative. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax6. rewrite roundUpMultLtFloatMin.
             unfold roundUp_subnormal. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply done.
       }
       eapply AllPredIntKeep.
       {
         eapply simpl2 with ((fun f:fstate => lb a f * lb b f >= floatMin)).
         eapply simpl2 with((fun f:fstate => lb a f * ub b f > - floatMin)).
         unfold split_All_predInt; simpl.
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin6. rewrite roundDownMultLtFloatMin.
             unfold roundDown_subnormal. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax5. rewrite roundUpMultGeFloatMin.
             unfold roundUp_relative. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin6. rewrite roundDownMultLtFloatMin.
             unfold roundDown_subnormal. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax5. rewrite roundUpMultLtFloatMin.
             unfold roundUp_subnormal. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin6. rewrite roundDownMultGeFloatMin.
             unfold roundDown_relative. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax5. rewrite roundUpMultGeFloatMin.
             unfold roundUp_relative. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin6. rewrite roundDownMultGeFloatMin.
             unfold roundDown_relative. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax5. rewrite roundUpMultLtFloatMin.
             unfold roundUp_subnormal. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply done.
       }
       eapply AllPredIntKeep.
       {
         eapply simpl2 with ((fun f:fstate => ub a f * ub b f >= floatMin)).
         eapply simpl2 with((fun f:fstate => lb a f * ub b f > - floatMin)).
         unfold split_All_predInt; simpl.
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin6. rewrite roundDownMultLtFloatMin.
             unfold roundDown_subnormal. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax6. rewrite roundUpMultGeFloatMin.
             unfold roundUp_relative. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin6. rewrite roundDownMultLtFloatMin.
             unfold roundDown_subnormal. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax6. rewrite roundUpMultLtFloatMin.
             unfold roundUp_subnormal. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin6. rewrite roundDownMultGeFloatMin.
             unfold roundDown_relative. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax6. rewrite roundUpMultGeFloatMin.
             unfold roundUp_relative. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H. simpl in H0. forward_reason.
           split.
           {
             rewrite multRoundMin6. rewrite roundDownMultGeFloatMin.
             unfold roundDown_relative. apply Rle_refl. 
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
           { rewrite multRoundMax6. rewrite roundUpMultLtFloatMin.
             unfold roundUp_subnormal. apply Rle_refl.
             psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
           }
         }
         eapply done.
       }
       eapply done.
     }
     eapply simpl2 with ((fun f:fstate => lb a f >= 0 /\ ub a f >= 0 /\ lb b f < 0 /\ ub b f >= 0)).
     unfold split_All_predInt; simpl.
     eapply AllPredIntKeep.
     {
       eapply simpl2 with ((fun f:fstate => ub a f * lb b f > - floatMin)).
       eapply simpl2 with((fun f:fstate => ub a f * ub b f >= floatMin)).
       unfold split_All_predInt; simpl.
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin7. rewrite roundDownMultLtFloatMin.
           unfold roundDown_subnormal. apply Rle_refl.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
         }
         { rewrite multRoundMax7. rewrite roundUpMultGeFloatMin.
           unfold roundUp_relative. apply Rle_refl.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
       }
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin7. rewrite roundDownMultGeFloatMin.
           unfold roundDown_relative. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
         { rewrite multRoundMax7. rewrite roundUpMultGeFloatMin.
           unfold roundUp_relative. apply Rle_refl.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
       }
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin7. rewrite roundDownMultLtFloatMin.
           unfold roundDown_subnormal. apply Rle_refl.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
         { rewrite multRoundMax7. rewrite roundUpMultLtFloatMin.
           unfold roundUp_subnormal. apply Rle_refl. 
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
         }
       }
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin7. rewrite roundDownMultGeFloatMin.
           unfold roundDown_relative. apply Rle_refl. 
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
         }
         { rewrite multRoundMax7. rewrite roundUpMultLtFloatMin.
           unfold roundUp_subnormal. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
         }
       }
       eapply done.
     }
     eapply simpl2 with ((fun f:fstate => lb a f < 0 /\ ub a f < 0 /\ lb b f >= 0 /\ ub b f >= 0)).
     unfold split_All_predInt; simpl.
     eapply AllPredIntKeep.
     {
       eapply simpl2 with ((fun f:fstate => lb a f * ub b f >- floatMin)).
       eapply simpl2 with((fun f:fstate => ub a f * lb b f >- floatMin)).
       unfold split_All_predInt; simpl.
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin8. rewrite roundDownMultLtFloatMin.
           unfold roundDown_subnormal. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
         }
         { rewrite multRoundMax8. rewrite roundUpMultLtFloatMin.
           unfold roundUp_subnormal. pose proof floatMinGe0. exact H35. clear -H1 H2 H6 H5 H4.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
       }
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin8. rewrite roundDownMultGeFloatMin.
           unfold roundDown_relative. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
         { rewrite multRoundMax8. rewrite roundUpMultLtFloatMin.
           unfold roundUp_subnormal.  pose proof floatMinGe0. exact H35. clear -H1 H2 H6 H5 H4.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
       }
       eapply AllPredIntKeep.
       { intros. eapply drop1. intros.
         simpl in *.  decompose [and] H. 
         clear -H1 H3 H18 H16 H4 H14 H13 H15. psatz R. eapply done.
       }
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin8. rewrite roundDownMultGeFloatMin.
           unfold roundDown_relative. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
         { rewrite multRoundMax8. rewrite roundUpMultGeFloatMin.
           unfold roundUp_relative. apply Rle_refl. 
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
         }
       }
       eapply done.
     }
      eapply simpl2 with ((fun f:fstate => lb a f < 0 /\ ub a f >= 0 /\ lb b f >= 0 /\ ub b f >= 0)).
     unfold split_All_predInt; simpl.
     eapply AllPredIntKeep.
     {
       eapply simpl2 with ((fun f:fstate => lb a f * ub b f >- floatMin)).
       eapply simpl2 with((fun f:fstate => ub a f * ub b f >= floatMin)).
       unfold split_All_predInt; simpl.
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin9. rewrite roundDownMultLtFloatMin.
           unfold roundDown_subnormal. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
         { rewrite multRoundMax9. rewrite roundUpMultGeFloatMin.
           unfold roundUp_relative. apply Rle_refl. clear -H1 H2 H6 H5 H4.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
       }
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin9. rewrite roundDownMultGeFloatMin.
           unfold roundDown_relative. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
         { rewrite multRoundMax9. rewrite roundUpMultGeFloatMin.
           unfold roundUp_relative. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
       }
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin9. rewrite roundDownMultLtFloatMin.
           unfold roundDown_relative. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
         { rewrite multRoundMax9. rewrite roundUpMultLtFloatMin.
           unfold roundUp_subnormal. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
         }
       }
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin9. rewrite roundDownMultGeFloatMin.
           unfold roundDown_relative. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
         { rewrite multRoundMax9. rewrite roundUpMultLtFloatMin.
           unfold roundUp_subnormal. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R.
         }
       }
       eapply done.
     }
     eapply simpl2 with ((fun f:fstate => lb a f >= 0 /\ ub a f >= 0 /\ lb b f >= 0 /\ ub b f >= 0)).
     unfold split_All_predInt; simpl.
     eapply AllPredIntKeep.
     {
       eapply simpl2 with ((fun f:fstate => lb a f * lb b f >= floatMin)).
       eapply simpl2 with((fun f:fstate => ub a f * ub b f >= floatMin)).
       unfold split_All_predInt; simpl.
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin10. rewrite roundDownMultGeFloatMin.
           unfold roundDown_relative. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
         { rewrite multRoundMax10. rewrite roundUpMultGeFloatMin.
           unfold roundUp_relative. apply Rle_refl. clear -H1 H2 H6 H5 H4.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
       }
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin10. rewrite roundDownMultLtFloatMin.
           unfold roundDown_subnormal. assert (-floatMin <= 0). pose proof floatMinGt0. 
           clear -H39. psatz R. exact H39.  clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
         { rewrite multRoundMax10. rewrite roundUpMultGeFloatMin.
           unfold roundUp_relative. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
       }
       eapply AllPredIntKeep.
       { intros. eapply drop1. intros.
         simpl in *.  decompose [and] H. clear -H20 H18 H4 H16 H17 H15 H1 H3. psatz R. eapply done.
       }
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H. simpl in H0. forward_reason.
         split.
         {
           rewrite multRoundMin10. rewrite roundDownMultLtFloatMin.
           unfold roundDown_subnormal. assert (-floatMin <= 0). pose proof floatMinGt0. 
           clear -H39. psatz R. exact H39.  clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
         { rewrite multRoundMax10. rewrite roundUpMultLtFloatMin.
           unfold roundUp_subnormal. apply Rle_refl. clear -H1 H2 H6 H5 H4 H3.
           psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. psatz R. 
         }
       }
       eapply done.
     }
     eapply AllPredIntKeep.
     { intros. eapply drop1. intros.
       simpl in *.  decompose [and] H. clear -H1 H3 H4 H5 H6 H7 H8 H9 H10 H13 H15. psatz R. 
       eapply done.
     }
     eapply done.
   }
Defined.   


   
Definition absFloatMinus_demo : predInt -> predInt -> All_predInt.
  refine (@optimized absFloatMinus_demo_spec _).
  econstructor.
  intros. unfold absFloatMinus_demo_spec.
  unfold split_All_predInt; simpl.
  eapply keep.
  { eapply refine_predInt_entails; simpl; intros.
    exact H.  
    simpl in H0.
    forward_reason.
    split.
    { 
      rewrite boundLbGtFloatMin.
      apply Rle_refl. assumption. }
    { rewrite boundUbGtFloatMin. apply Rle_refl. psatz R. } }
  {  eapply simpl2 with ((fun f:fstate => lb a f - ub b f >= 0)).
     eapply simpl2 with ((fun f:fstate => ub a f - lb b f >= floatMin)).
     unfold split_All_predInt; simpl.
     eapply keep.
     {
       eapply refine_predInt_entails; simpl; intros.
       exact H.
       simpl in H0.
       forward_reason.
       split.
       {
         rewrite boundLbBet0AndFloatMin. 
         pose proof floatMinGt0.
         assert (- floatMin <= 0).
         psatz R.
         exact H18.
         psatz R.
         psatz R.
       }
       {
         rewrite boundUbGtFloatMin.
         apply Rle_refl. 
         psatz R.
       }   
     }
     eapply AllPredIntKeep.
     {
       eapply simpl2 with ((fun f:fstate => lb a f - ub b f > -floatMin)).
       unfold split_All_predInt; simpl.
       eapply keep.
       {
         eapply refine_predInt_entails; simpl; intros.
         exact H.
         simpl in H0.
         forward_reason.
         split.
         {
           rewrite boundLbBetNegFloatMinAnd0.
           apply Rle_refl.
           psatz R.
           psatz R.
         }
         {
           rewrite boundUbGtFloatMin.
           apply Rle_refl.
           psatz R.
         }
       }
       {
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H.
           simpl in H0.
           forward_reason.
           split.
           {
             rewrite boundLbLessThanFloatMin.
             eapply Rle_refl.
             psatz R.
           }
           {
             rewrite boundUbGtFloatMin.
             apply Rle_refl. 
             psatz R.
           }
         }
         {
           eapply done.
         }
       }
     }
     {
       eapply AllPredIntKeep.
       {
         eapply simpl2 with ((fun f:fstate => ub a f - lb b f >= 0)).
         unfold split_All_predInt; simpl.
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H.
           simpl in H0.
           forward_reason.
           split.
           {
             rewrite boundLbBet0AndFloatMin.
             pose proof floatMinGt0.
             assert (-floatMin <= 0).
             psatz R.
             exact H20.
             psatz R.
             psatz R.
           }
           {
             rewrite boundUbBet0AndFloatMin.
             apply Rle_refl.
             psatz R.
           }
         }      
         {
           intros.
           eapply drop1.
           intros.
           simpl in *.
           psatz R.
           eapply done.
         }
       }
       {
         eapply simpl2 with ((fun f:fstate => lb a f - ub b f <= -floatMin)).
         eapply simpl2 with ((fun f:fstate => ub a f - lb b f >= R0)).
         unfold split_All_predInt; simpl.
         eapply keep.
         {
           eapply refine_predInt_entails; simpl; intros.
           exact H.
           simpl in H0.
           forward_reason.
           split.
           {
             rewrite boundLbLessThanFloatMin.
             eapply Rle_refl.
             psatz R.
           }
           {
             rewrite boundUbBet0AndFloatMin.
             unfold roundUp_subnormal.
             apply Rle_refl.
             psatz R.
           }
         }     
         {
           eapply keep.
           {
             eapply refine_predInt_entails; simpl; intros.
             exact H.
             simpl in H0.
             forward_reason.
             split.
             {
               rewrite boundLbBetNegFloatMinAnd0.
               eapply Rle_refl.
               psatz R.
               psatz R.
             }
             {
               rewrite boundUbBet0AndFloatMin.
               apply Rle_refl.
               psatz R.
             }
           }
           {
             
             eapply AllPredIntKeep.
             {
               eapply simpl2 with ((fun f:fstate => ub a f - lb b f <= -floatMin)).
               unfold split_All_predInt; simpl.
               eapply keep.
               {
                 eapply refine_predInt_entails; simpl; intros.
                 exact H.
                 simpl in H0.
                 forward_reason.
                 split.
                 {
                   rewrite boundLbLessThanFloatMin.
                   eapply Rle_refl.
                   psatz R.
                 }
                 {
                   rewrite boundUbLessThanFloatMin.
                   apply Rle_refl.
                   psatz R.
                 }
               }
               {
                 eapply keep.
                 {
                   eapply refine_predInt_entails; simpl; intros.
                   exact H.
                   simpl in H0.
                   forward_reason.
                   split.
                   {
                     rewrite boundLbLessThanFloatMin.
                     eapply Rle_refl.
                     psatz R.
                   }
                   {
                     rewrite boundUbBetNegFloatMinAnd0.
                     unfold roundUp_subnormal.
                     pose proof floatMinGt0.
                     assert (floatMin >= 0).
                     psatz R.
                     exact H24.
                     psatz R.
                   }
                 }
                 {
                   apply done.
                 }
               }
             }
             {
               eapply simpl2 with ((fun f:fstate => ub a f - lb b f <= -floatMin)).
               unfold split_All_predInt; simpl.
               eapply keep.
               {
                 eapply refine_predInt_entails; simpl; intros.
                 exact H.
                 simpl in H0.
                 forward_reason.
                 split.
                 {
                   rewrite boundLbLessThanFloatMin.
                   eapply Rle_refl.
                   psatz R.
                 }
                 {
                   rewrite boundUbLessThanFloatMin.
                   apply Rle_refl.
                   psatz R.
                 }
               }
               {
                 eapply keep. 
                 eapply refine_predInt_entails; simpl; intros.
                 exact H.
                 simpl in H0.
                 forward_reason.
                 split.
                 {
                   rewrite boundLbBetNegFloatMinAnd0.
                   eapply Rle_refl.
                   psatz R.
                   psatz R.
                 }
                 {
                   rewrite boundUbBetNegFloatMinAnd0.
                   unfold roundUp_subnormal.
                   pose proof floatMinGt0.
                   assert (floatMin >= 0).
                   psatz R.
                   exact H24.
                   psatz R.
                 }
                 
                 eapply done.
               }
             }
           }
         }
       }
  } }

Defined.



Eval cbv beta iota zeta delta [ absFloatPlus_demo optimized ] in absFloatPlus_demo.

Eval cbv beta iota zeta delta [ absFloatMinus_demo optimized ] in absFloatMinus_demo.




Print roundDown.
Print roundDown_relative.
