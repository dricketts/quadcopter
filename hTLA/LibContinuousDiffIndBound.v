Require Import Coq.Classes.Morphisms.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import ChargeTactics.Tactics.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import hTLA.DiscreteLogic.
Require Import hTLA.LibContinuous.

Section parametric.
  Variable tlaState : Type.

  (** TODO(gmalecha): Move to another file **)
  Instance Proper_starts : Proper (lentails ==> lentails) (@starts tlaState).
  Proof. Admitted.
  Instance Proper_starts_iff : Proper (lequiv ==> lequiv) (@starts tlaState).
  Proof. Admitted.
  Instance Proper_always : Proper (lentails ==> lentails) (@always tlaState).
  Proof. Admitted.
  Instance Proper_always_iff : Proper (lequiv ==> lequiv) (@always tlaState).
  Proof. Admitted.
  Instance Proper_eventually : Proper (lentails ==> lentails) (@eventually tlaState).
  Proof. Admitted.
  Instance Proper_eventually_iff : Proper (lequiv ==> lequiv) (@eventually tlaState).
  Proof. Admitted.
  Definition after (P : StateProp tlaState) : DActionProp tlaState :=
    fun _ st' => P st'.
  Lemma starts_discretely_through_now : forall (A : StateProp tlaState) B,
      through (now A) //\\ starts (discretely B) -|-
              starts (before _ A //\\ discretely (B //\\ after A)).
  Proof. unfold through, starts, discretely, before, after.
         red.
  Admitted.
  Lemma starts_discretely_through : forall C P (Q : StateProp tlaState) d,
      P |-- discretely d ->
      |-- P -->> before _ Q //\\ discretely (after Q) ->
      C |-- starts P -->> through (now Q).
  Proof.
    intros.
  Admitted.


  (** CActionProp **)
  Definition CActionVal (T : Type) : Type :=
    (R -> tlaState) -> R -> T.

  Definition CActionProp : Type := CActionVal Prop.

  Instance ILogicOps_CActionProp : ILogicOps CActionProp := @ILInsts.ILFun_Ops _ _ _.
  Instance ILogic_CActionProp : ILogic CActionProp. Admitted.

  Local Transparent ILInsts.ILFun_Ops.

  Instance Applicative_CActionVal
  : Applicative CActionVal :=
  { pure := fun _ x => fun _ _ => x
  ; ap := fun _ _ f x => fun st st' => (f st st') (x st st')
  }.

  Instance Functor_CActionVal
  : Functor CActionVal :=
  { fmap := fun _ _ f x => ap (pure f) x }.

  Global Instance EmbedOp_Prop_CActionProp : EmbedOp Prop CActionProp :=
  { embed := fun P _ _ => P }.
  Global Instance Embed_Prop_CActionProp : Embed Prop CActionProp.
  Proof. constructor; simpl; intuition. Qed.

  Global Instance EmbedOp_CActionVal_Prop_CActionProp : EmbedOp (CActionVal Prop) CActionProp :=
  { embed := fun P => P }.
  Global Instance Embed_CActionVal_Prop_CActionProp : Embed (CActionVal Prop) CActionProp.
  Proof. constructor; simpl; intuition. Qed.

  Definition throughC (P : StateProp tlaState) : CActionProp :=
    fun p t => forall t', (0 <= t' <= t)%R -> P (p t').

  Definition startsFromC (P : StateProp tlaState) : CActionProp :=
    fun p t => P (p 0)%R.

  Definition deriv_formula (G : StateProp tlaState) : CActionProp :=
    startsFromC G -->> throughC G.

  Definition ContinuousC (diffeqs : list (DiffEq tlaState))
  : CActionProp :=
    fun p t =>
      exists is_derivable,
        solves_diffeqs_range _ t p diffeqs is_derivable.

  (** Differential Induction **)
  Lemma diff_ind : forall G F (GI : StateProp tlaState) cp,
      (ContinuousC cp //\\ throughC GI |-- deriv_formula G) ->
      F |-- now G //\\ starts (discretely (Continuous_range cp GI)) -->>
            through (now G).
  Proof.
    intros.
    apply forget_prem.

    rewrite now_starts_discretely_and.
    red; red in H; simpl in *.
    unfold starts, discretely, Continuous_range, before, through. simpl.
    destruct t. destruct c; simpl.
    intros.
    Require Import ExtLib.Tactics.
    destruct H1.
    destruct H2 as [ t [ p ? ] ].
    specialize (H p t).
    unfold ContinuousC, throughC, deriv_formula in H.
    forward_reason.
    simpl in H.
    unfold startsFromC, throughC in *.
    unfold now. simpl.
    unfold pre, post in *. subst.
    forward_reason.
    eapply H.
    split.
    { red. red in H2. left; assumption. }
    { apply RIneq.Rle_refl. }
  Qed.

  Lemma deriv_formula_and
  : forall P Q,
      deriv_formula P //\\ deriv_formula Q |-- deriv_formula (P //\\ Q).
  Proof.
    unfold deriv_formula, startsFromC, throughC. simpl. intuition.
  Qed.

  Lemma deriv_formula_true
  : ltrue |-- deriv_formula ltrue.
  Proof.
    unfold deriv_formula, startsFromC, throughC. simpl. intuition.
  Qed.

  Lemma deriv_formula_false
  : lfalse |-- deriv_formula lfalse.
  Proof.
    unfold deriv_formula, startsFromC, throughC. simpl. intuition.
  Qed.

  Definition nowC (P : StateProp tlaState) : CActionProp :=
    fun p t => P (p 0)%R.

  Instance Applicative_StateVal
  : Applicative (StateVal tlaState) :=
  { pure := fun _ x => fun _ => x
  ; ap := fun _ _ f x => fun st => (f st) (x st)
  }.

  Instance Functor_StateVal
  : Functor (StateVal tlaState) :=
  { fmap := fun _ _ f x => ap (pure f) x }.

  Existing Instance AutoLift_id.
  Existing Instance AutoLift_arrow.

  Definition Dt_R {L} {IL : ILogicOps L} {E : EmbedOp Prop L} (t : R) (g : R -> R) (P : (R -> R) -> L) : L :=
    Exists is_derivable : forall (t' : R), (0 <= t' <= t)%R -> derivable_pt g t',
    Forall g' : R -> R,
      (Forall t', Forall pf : (0 <= t' <= t)%R, embed (derive_pt g t' (is_derivable t' pf) = g' t')) -->>
      P g'.

  Definition Dt (g : tlaState -> R) (P : (R -> R) -> CActionProp) : CActionProp :=
    fun p t =>
      Dt_R t (fun x => g (p x)) P p t.

  Definition CStateVal (T : Type) : Type :=
    R -> StateVal tlaState T.
  Definition CStateProp := CStateVal Prop.

  Instance ILogicOps_CStateProp : ILogicOps CStateProp := @ILInsts.ILFun_Ops _ _ _.
  Instance ILogic_CStateProp : ILogic CStateProp. Admitted.

  Instance Applicative_CStateVal
  : Applicative CStateVal :=
  { pure := fun _ x => fun _ _ => x
  ; ap := fun _ _ f x => fun st st' => (f st st') (x st st')
  }.

  Instance Functor_CStateVal
  : Functor CStateVal :=
  { fmap := fun _ _ f x => ap (pure f) x }.

  Global Instance EmbedOp_Prop_CStateProp : EmbedOp Prop CStateProp :=
    { embed := fun P _ _ => P }.
  Global Instance Embed_Prop_CStateProp : Embed Prop CStateProp.
  Proof. constructor; simpl; intuition. Qed.

  Global Instance EmbedOp_CStateVal_Prop_CStateProp : EmbedOp (CStateVal Prop) CStateProp :=
    { embed := fun P => P }.
  Global Instance Embed_CStateVal_Prop_CStateProp : Embed (CStateVal Prop) CStateProp.
  Proof. constructor; simpl; intuition. Qed.

  Definition throughCt (P : CStateProp) : CActionProp :=
    fun p t => forall t', (0 <= t' <= t)%R -> P t' (p t').

  Definition equal (f : R -> R) (r : R -> R -> Prop) (g : R -> R) : CStateVal Prop :=
    fun t st => r (f t) (g t).

  Definition range_deriv (f : R -> R) (mn mx : R)
             (is_deriv : forall t', (mn <= t' <= mx)%R -> derivable_pt f t')
    : R -> R :=
    fun t =>
      match RIneq.Rlt_le_dec t mn , RIneq.Rlt_le_dec mx t with
      | right pf , right pf' => derive_pt _ _ (is_deriv t (conj pf pf'))
      | left _ , right _ => f mn
      | _ , left _ => f mx
      end.

  Theorem range_deriv_ok : forall f mn mx is_deriv,
      forall t (pf : (mn <= t <= mx)%R),
        derive_pt f _ (is_deriv t pf) = range_deriv f mn mx is_deriv t.
  Proof.
    intros. unfold range_deriv.
    destruct pf.
    destruct (RIneq.Rlt_le_dec t mn).
    { exfalso. eapply RIneq.Rlt_not_le; eauto. }
    destruct (RIneq.Rlt_le_dec mx t).
    { exfalso. eapply RIneq.Rlt_not_le; eauto. }
    apply pr_nu.
  Qed.

  Lemma open_closed : forall a b c : R, (a < b < c -> a <= b <= c)%R.
  Proof.
    destruct 1. split; red; auto.
  Qed.

  Require Coq.Reals.MVT.

  Ltac cut_prems H :=
    try match type of H with
        | ?X -> _ => let Hf := fresh in cut X ; [ intro Hf ; specialize (H Hf) ; cut_prems H  | ]
        end.

  Lemma deriv_formula_eq
  : forall (f g : StateVal tlaState R),
      Dt f (fun f' => Dt g (fun g' => throughCt (embed (equal f' eq g'))))
      |-- deriv_formula (embed (autolift (pure (@eq R)) f g)).
  Proof.
    simpl. unfold deriv_formula, startsFromC, throughC. simpl.
    intros f g p t. intros.
    do 2 red in H; simpl in H. forward_reason.
    pose (f' := range_deriv _ _ _ x).
    specialize (H f' (range_deriv_ok _ _ _ _)).
    do 2 red in H; simpl in H. forward_reason.
    pose (g' := range_deriv _ _ _ x0).
    specialize (H g' (range_deriv_ok _ _ _ _)).
    unfold throughCt, equal in H.
    generalize (@MVT.null_derivative_loc (fun x => f (p x) - g (p x))%R 0 t).
    pose (pf := (fun x1 pf =>
                   let pf' : (0 <= x1 <= t)%R := open_closed _ _ _ pf in
                   derivable_pt_minus _ _ _ (x _ pf') (x0 _ pf'))).
    intro Hmvt.
    specialize (Hmvt pf).
    cut_prems Hmvt.
    { specialize (Hmvt t' (conj H1 H2)). simpl in Hmvt.
      clear - H0 Hmvt.
      rewrite H0 in *.
      eapply RIneq.Rminus_diag_uniq.
      rewrite Hmvt.
      apply RIneq.Rminus_diag_eq. reflexivity. }
    { intros.
      unfold pf.
      rewrite (derive_pt_minus (fun x => f (p x)) (fun x => g (p x)) x1).
      do 2 rewrite range_deriv_ok.
      rewrite H.
      - eapply RIneq.Rminus_diag_eq. reflexivity.
      - auto using open_closed. }
    { intros.
      eapply derivable_continuous_pt.
      eapply derivable_pt_minus; eauto. }
  Qed.

  Lemma deriv_formula_lt
  : forall (f g : StateVal tlaState R),
      Dt f (fun f' => Dt g (fun g' => throughCt (embed (equal f' Rle g'))))
      |-- deriv_formula (embed (autolift (pure Rlt) f g)).
  Proof.
    simpl. unfold deriv_formula, startsFromC, throughC. simpl.
    intros f g p t. intros.
    do 2 red in H; simpl in H. forward_reason.
    pose (f' := range_deriv _ _ _ x).
    specialize (H f' (range_deriv_ok _ _ _ _)).
    do 2 red in H; simpl in H. forward_reason.
    pose (g' := range_deriv _ _ _ x0).
    specialize (H g' (range_deriv_ok _ _ _ _)).
    unfold throughCt, equal in H.
    pose (pf := (fun x1 pf =>
                   let pf' : (0 <= x1 <= t)%R := open_closed _ _ _ pf in
                   derivable_pt_minus _ _ _ (x _ pf') (x0 _ pf'))).
    assert (0 = t' \/ 0 < t')%R.
    { destruct H1; try subst; eauto. }
    destruct H3.
    { subst. auto. }
    assert (0 < t)%R by admit.
    assert (0 <= 0 <= t)%R by admit.
    assert (0 <= t' <= t)%R by admit.
    (** TODO: This requires a generalization of 'derive_increasing_interv_var'
     ** that only needs to know about the derivative on an interval
     **)
(*
*)
  Admitted.

  Section any_all.
    Context {L} {LL : ILogicOps L}.

    Fixpoint AnyOf  (ls : list L) : L :=
      match ls with
      | nil => lfalse
      | cons l ls => l \\// AnyOf ls
      end.

    Fixpoint AllOf (ls : list L) : L :=
      match ls with
      | nil => ltrue
      | cons l ls => l //\\ AllOf ls
      end.
  End any_all.

(*
  Lemma Dt_permute : forall f g P,
      (forall f f' g g' a t,
          (forall t', (0 <= t' <= t)%R -> f t' = f' t') ->
          (forall t', (0 <= t' <= t)%R -> f t' = f' t') ->
          (P f g a t <-> P f' g' a t)) ->
      Dt f (fun f' => Dt g (P f')) -|- Dt g (fun g' => Dt f (fun f' => P f' g')).
  Proof.
    intros. unfold Dt. simpl.
    do 2 (apply and_forall; simpl; intro).
    intuition.
    { forward_reason.
      specialize (H _ (range_deriv_ok _ _ _ x1)).
      forward_reason.
      exists x2. intros. exists x1. intros.
      specialize (H _ H0).
      revert H.
*)

  Theorem ContinuousC_instantiate
  : forall cp,
      ContinuousC cp
      |-- AllOf (List.map (fun de => Dt de.(de_lhs _) (fun f' =>
                   throughCt (fun nowT now => de.(de_op _) (f' nowT) (de.(de_rhs _) now))))
                          cp).
  Proof.
    intros. red. simpl. unfold ContinuousC. intros.
    forward_reason.
    induction cp.
    { simpl. trivial. }
    { simpl. split.
      { clear IHcp.
        red in H.
        red. red. simpl.
        exists (x _ (or_introl _ eq_refl)).
        intros. red. intros.
        rewrite <- (H0 _ H1); clear H0.
        destruct a. simpl in *.
        eapply H. }
      { eapply IHcp.
        instantiate (1:=fun v pf => x v (or_intror _ pf)).
        clear - H. revert H.
        unfold solves_diffeqs_range. simpl.
        intros. eapply H. } }
  Qed.

  Definition is_derivative_R (f' : R -> R) (f : R -> R) (t : R) : Prop :=
    exists is_derivable : forall t', (0 <= t' <= t)%R -> derivable_pt f t',
      forall t' (pf : (0 <= t' <= t)%R),
        f' t' = derive_pt f t' (is_derivable _ pf).

  Definition is_derivative (f' : R -> R) (f : tlaState -> R) : CActionProp :=
    fun p t =>
      is_derivative_R f' (fun t => f (p t)) t.

  (** NOTE: This is not pretty! The problem stems from the
   ** fact that the type of functions does not capture the range that the
   ** properties are valid on. This means that we need to state a
   ** Properness fact about [P], but, at the same time, the properness fact
   ** is not modular.
   **)
  Lemma is_derivative_Dt : forall f f' P,
      is_derivative f' f |-- P f' ->
      is_derivative f' f |-- Dt f P.
  Proof.
    simpl. intros. specialize (H _ _ H0).
    red. red. simpl.
    red in H0. red in H0.
    forward_reason.
    exists x. intros.
    revert H.
    assert (forall t' (pf : (0 <= t' <= t0)%R),
               f' t' = x0 t').
    { intros. erewrite <- H1. eapply H0. }
    clear - H.
    admit.
    Grab Existential Variables. eassumption.
  Qed.

End parametric.
