Require Import TLA.HybridStream.
Require Import Charge.Logics.ILogic.
Require Charge.Logics.ILInsts.
Require Import Coq.Strings.String.
Require Import ExtLib.Structures.Applicative.
Require Import Coq.Reals.Rdefinitions.

Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Functor.

Existing Instance Applicative_Fun.
Existing Instance Functor_Fun.

Section localized.
  Variable tlaState : Type.
  Context {HybridState_tlaState : HybridState tlaState}.

  Definition StateVal (T : Type) : Type :=
    tlaState -> T.
  Definition DActionVal (T : Type) : Type :=
    tlaState -> tlaState -> T.
  Definition ActionVal (T : Type) : Type :=
    tlaState -> Step tlaState -> T.
  Definition TraceVal (T : Type) := trace tlaState -> T.

  Definition StateProp := StateVal Prop.

  Definition DActionProp := DActionVal Prop.
  Definition CActionProp := forall (t : R) (f : R -> tlaState), Prop.

  Definition ActionProp := ActionVal Prop.

  Definition TraceProp := TraceVal Prop.

  Global Instance ILogicOps_StateProp : ILogicOps StateProp := @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogicOps_ActionProp : ILogicOps ActionProp := @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogicOps_DActionProp : ILogicOps DActionProp := @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogicOps_CActionProp : ILogicOps CActionProp := @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogicOps_TraceProp : ILogicOps TraceProp := @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogic_StateProp : ILogic StateProp. Admitted.
  Global Instance ILogic_ActionProp : ILogic ActionProp. Admitted.
  Global Instance ILogic_DActionProp : ILogic DActionProp. Admitted.
  Global Instance ILogic_CActionProp : ILogic CActionProp. Admitted.
  Global Instance ILogic_TraceProp : ILogic TraceProp. Admitted.

  (* These are the "obvious" definitions, needed to help Coq *)
  Global Instance Applicative_Action
  : Applicative ActionVal :=
  { pure := fun _ x => fun _ _ => x
  ; ap := fun _ _ f x => fun st st' => (f st st') (x st st')
  }.

  Global Instance Functor_Action
  : Functor ActionVal :=
  { fmap := fun _ _ f x => ap (pure f) x }.

  Global Instance Applicative_DAction
  : Applicative DActionVal :=
  { pure := fun _ x => fun _ _ => x
  ; ap := fun _ _ f x => fun st st' => (f st st') (x st st')
  }.

  Global Instance Functor_DAction
  : Functor DActionVal :=
  { fmap := fun _ _ f x => ap (pure f) x }.

  Global Instance Applicative_State
  : Applicative StateVal :=
  { pure := fun _ x => fun _ => x
  ; ap := fun _ _ f x => fun st => (f st) (x st)
  }.

  Global Instance Functor_State
  : Functor StateVal :=
  { fmap := fun _ _ f x => ap (pure f) x }.


  Definition now : StateProp -> TraceProp :=
    fun P tr => P (HybridStream.hd tr).

  Definition next : StateProp -> TraceProp :=
    fun P tr => P (HybridStream.hd (HybridStream.tl tr)).

  Definition always (P : TraceProp) : TraceProp :=
    fun s =>
      forall s', HybridStream.skips_to s s' -> P s'.

  Definition eventually (P : TraceProp) : TraceProp :=
    fun s =>
      exists s', HybridStream.skips_to s s' /\ P s'.

  Definition discretely (P : DActionProp) : ActionProp :=
    fun start step =>
      match step with
      | DiscreteTo st' =>
        P start st'
      | _ => False
      end.

  Definition continuously (P : CActionProp) : ActionProp :=
    fun start step =>
      match step with
      | ContinuousBy r f => P r (fun x => hybrid_join (f x) (snd (hybrid_split start)))
      | _ => False
      end.

  Definition stutter {T} (f : tlaState -> T) : DActionProp :=
    fun st st' => f st = f st'.

  Definition starts (P : ActionProp) : TraceProp :=
    fun tr =>
      P (HybridStream.hd tr) (firstStep tr).

  Definition through (P : TraceProp) : TraceProp :=
    fun tr =>
      match firstStep tr with
      | ContinuousBy r f =>
        forall r', (0 < r' <= r)%R ->
                   forall tr', after_time r' 0 tr tr' ->
                               P tr'
      | DiscreteTo _ =>
        forall tr', after_time 0 1 tr tr' ->
                    P tr'
      end.

  Lemma always_skips_to : forall P t1 t2,
      skips_to t1 t2 ->
      always P t1 -> always P t2.
  Proof.
    unfold always. intros.
    eapply H0. etransitivity; eauto.
  Qed.

  (** This is induction over the phase changes **)
  Lemma dind_lem : forall G P,
      G |-- P -->> always (P -->> through P) -->> always P.
  Proof.
    intros. red. red. Transparent ILInsts.ILFun_Ops.
    red.
    intros. red. simpl. red.
    intros. clear H. clear G. revert H0 H1.
    eapply skips_to_skips_to' in H2.
(*
    induction H2; simpl.
    { (* Now *)
      intros. assumption. }
    { (* AfterD *)
      intros.
      eapply IHskips_to'.
      { red in H1.
        specialize (H1 _ (skip_Now _) H0).
        eapply H1. admit. }
      { eapply always_skips_to. 2: eapply H1.
        constructor. reflexivity. } }
    { (* AfterC *)
      intros.
      eapply IHskips_to.
      { red in H1.
        specialize (H1 _ (ST_Now _) H0).
        eapply H1.
        instantiate (1:=t).
        { admit. }
        { admit. } }
      { eapply always_skips_to. 2: eassumption.
        constructor. reflexivity. } }
    { (* WithinC *)
      intros.
      specialize (H1 _ (ST_Now _) H0).
      red in H1. simpl in H1.
      eapply H1 with (r' := r); clear H1.
      { admit. }
      { eapply WithinC. admit. } }
*)
  Admitted.

  Lemma always_and : forall P Q,
      always P //\\ always Q -|- always (P //\\ Q).
  Proof.
    intros. split.
    { red. red. simpl. unfold always. intuition. }
    { red. red. simpl. unfold always.
      intuition; edestruct H; eauto. }
  Qed.

  Lemma uncurry : forall P Q R,
      (P //\\ Q) -->> R -|- P -->> Q -->> R.
  Proof. compute. tauto. Qed.

  Lemma always_impl : forall P Q,
      |-- P -->> Q ->
      |-- always P -->> always Q.
  Proof. compute. intuition. Qed.

  Theorem hybrid_induction
    : forall G P T,
      G |-- always T ->
      G |-- P ->
      G |-- always (P -->> T -->> through P) ->
      G |-- always P.
  Proof.
    intros G P T.
    generalize (dind_lem G P).
    unfold lentails, ILogicOps_TraceProp. simpl.
    intros.
    eapply H; eauto.
    specialize (H2 _ H3).
    specialize (H0 _ H3).
    revert H2. revert H0.
    clear. revert t.
    cut (|-- always T -->> always (P -->> T -->> through P) -->> always (P -->> through P)).
    { intros. eapply H. exact I. auto. auto. }
    { rewrite <- uncurry.
      rewrite always_and.
      eapply always_impl.
      compute; tauto. }
  Qed.

  Lemma now_entails : forall (A B : StateProp),
      A |-- B ->
      now A |-- now B.
  Proof.
    unfold now. simpl. auto.
  Qed.

  Lemma always_tauto
    : forall G P, |-- P -> G |-- always P.
  Proof.
    compute; intuition.
  Qed.

  Lemma now_starts_discretely_and : forall P Q,
      now P //\\ starts (discretely Q) -|- starts (discretely (fun st st' => P st /\ Q st st')).
  Proof.
    intros. split.
    { red; simpl. destruct t.
      unfold starts, discretely; destruct c; simpl; tauto. }
    { red; simpl. destruct t.
      unfold starts, discretely; destruct c; simpl; tauto. }
  Qed.

  Lemma starts_next_impl : forall (P : DActionProp) (Q : StateProp),
      starts (discretely (fun st st' => P st st' -> Q st')) |-- starts (discretely P) -->> next Q.
  Proof.
    intros.
    { red; simpl. destruct t.
      unfold starts, discretely; destruct c; simpl. tauto.
      tauto. }
  Qed.

  Axiom R0_lt_R0_False : (0 < 0)%R -> False.
  Axiom R0_gt_R0_False : (0 > 0)%R -> False.

  Ltac Rarith :=
    repeat match goal with
           | H : (_ < _ <= _)%R |- _ => destruct H
           | H : (_ < _ < _)%R |- _ => destruct H
           end ;
    solve [ eauto using R0_lt_R0_False, R0_gt_R0_False ].

  Lemma starts_discretely_through : forall (P : DActionProp) (Q : StateProp),
      (forall st, P st |-- Q) ->
      |-- starts (discretely P) -->> through (now Q).
  Proof.
    intros. unfold starts, discretely, through.
    red. simpl. intros. destruct t; simpl in *.
    destruct c; simpl in *.
    - exfalso; assumption.
    - intros.
      inversion H2; clear H2; subst.
      { eapply after_time_now in H8. subst.
        unfold now. simpl. eauto. }
      { exfalso; clear - H9. Rarith. }
  Qed.

  Definition before (P : StateProp) : ActionProp :=
    fun st _ => P st.

  Definition enabled (ap : ActionProp) : StateProp :=
    Exists st', fun st => ap st st'.

  Lemma and_forall : forall {T} (F G : T -> Prop),
      ((forall x, F x) /\ (forall x, G x)) <->
      (forall x, F x /\ G x).
  Proof. firstorder. Qed.


  (** Reasoning about [through] **)
  Lemma through_and : forall P Q, through P //\\ through Q -|- through (P //\\ Q).
  Proof.
    intros. apply and_forall. intros.
    unfold through. simpl. destruct (firstStep x); intuition; firstorder.
  Qed.

  Lemma through_or : forall P Q, through P \\// through Q |-- through (P \\// Q).
  Proof.
    intros. red. simpl.
    unfold through. intro. destruct (firstStep t); intuition; firstorder.
  Qed.

  Lemma through_ex : forall T (P : T -> _),
      Exists x : T, through (P x) |-- through (lexists P).
  Proof.
    intros; red; simpl.
    unfold through. intro. intros.
    destruct H. destruct (firstStep t); eauto.
  Qed.

  Lemma through_all : forall T (P : T -> _),
      Forall x : T, through (P x) |-- through (lforall P).
  Proof.
    intros; red; simpl.
    unfold through. intro. intros.
    destruct (firstStep t); eauto.
  Qed.

  Definition throughC (P : StateProp) : CActionProp :=
    fun r f =>
      forall r', (0 < r' <= r)%R -> P (f r').

  Definition throughD (P : StateProp) : DActionProp :=
    fun _ fin => P fin.


  (** This is more continuous reasoning!
   ** - Things get a little bit more complex here.
   **)
  Require Import Coq.Reals.Ranalysis1.

  (** NOTE: It is necessary to have a topology on the continuous state **)

  Axiom is_deriv_state_pt
  : forall (f : R -> tlaState) (t : R) (val : tlaState), Prop.
(*
    exists is_derivable : forall v : tlaVar, derivable_pt (fun x => f x v) t,
      forall (v : tlaVar),
        derive_pt (fun x => f x v) t (is_derivable v) = val v.
*)
  (** NOTE: pr_nu says "forall p1 p2, derive_pt f x p1 = derive_pt f x p2" **)

  Definition deriv_on_interval (P : (R -> tlaState) -> Prop) (t : R) (f : R -> tlaState) : Prop.
(*
    exists is_derivable : forall (v : tlaVar) (t' : R), (0 <= t' < t)%R -> derivable_pt (fun x => f x v) t',
      forall f' : R -> tlaState,
        (forall v t' (pf : (0 <= t' < t)%R),
            derive_pt (fun x => f x v) t' (is_derivable v t' pf) = f' t' v) ->
        P f'.
*)
  Admitted.

  Axiom endsOn : StateProp -> ActionProp.

  Definition startsFromC (P : StateProp) : CActionProp :=
    fun t f => P (f 0)%R.

  Definition endsOnC (P : StateProp) : CActionProp :=
    fun t f => P (f t).

  Definition deriv_formula(G : StateProp) : CActionProp :=
    startsFromC G -->> throughC G.

(*
Theorem deriv_formula_and : forall H P Q,
    deriv_formula H P //\\ deriv_formula H Q |-- deriv_formula H (P //\\ Q).
Proof.
  intros. unfold deriv_formula.
  setoid_rewrite <- through_and.
  red. simpl. tauto.
Qed.

Theorem deriv_formula_or_weak : forall H P Q,
    deriv_formula H P \\// deriv_formula H Q |-- deriv_formula H (P \\// Q).
Proof.
  intros. unfold deriv_formula.
  setoid_rewrite <- through_or.
  red. simpl. tauto.
Qed.
*)

  Definition Dt_R (g : R -> R) (P : (R -> R) -> CActionProp) : CActionProp :=
    fun t f =>
      exists is_derivable : forall (t' : R), (0 <= t' < t)%R -> derivable_pt g t',
        forall g' : R -> R,
          (forall t' (pf : (0 <= t' < t)%R),
              derive_pt g t' (is_derivable t' pf) = g' t') ->
          P g' t f.

  Definition Dt (g : tlaState -> R) (P : (R -> R) -> CActionProp) : CActionProp :=
    fun t f =>
      Dt_R (fun x => g (f x)) P t f.

  Definition tlaCore : Type := (R * (R -> tlaState))%type.

  Axiom tlaState_get : tlaState -> string -> R.

  Definition get : tlaCore -> string -> R :=
    fun tlc v =>
      tlaState_get (snd tlc (fst tlc)) v.


  Definition Dt' (g : R -> (R -> tlaState) -> R)
                 (P : (R -> (R -> tlaState) -> R) -> CActionProp)
    : CActionProp.
  (*
    fun t f =>
      Dt_R (fun x => g (f x)) P t f.
   *)
  Admitted.

  Eval simpl in
      (** does the derivative of a function [R -> R * R] make sense?
       **)
      Dt_R (fun t => get (st t) "x")
         (fun f' => 

  Eval simpl in
      Dt' (fun st => get st "x")
          (fun f' => (fun t => get (f' t) "x") = fun _ => 1)%R //\\
      Dt' (fun st => get st "y") (fun dy => dy = 1)%R
      |-- Dt' (fun st => get st "x" + get st "y") (fun df => df = 2).



  Definition It_R (g : R -> R) (P : (R -> R) -> CActionProp) : CActionProp :=
    fun t f =>
      forall f_, antiderivative g f_ 0 t ->
                 P (fun x => f_ x - f_ 0)%R t f.

  Theorem Dt_It : forall f P, It_R f (fun f_ => Dt_R f_ P) -|- P f.
  Proof.
    unfold It_R, Dt_R. intros.
    red. simpl. do 2 (apply and_forall; intro).
    split.
    { intros.
      admit. }
    { intros.
      red in H0. destruct H0.
      admit. }
  Qed.

  Theorem It_Dt : forall f P, Dt_R f (fun f' => It_R f' (fun f_ => P (fun x => f_ x + f 0)%R)) -|- P f.
  Proof.
    unfold It_R, Dt_R. intros.
    do 2 (apply and_forall; intro).
    split.
    { red; simpl; intros.
      destruct H.
      unfold antiderivative in *.
      admit. }
    { admit. }
  Qed.

  Lemma Dt_plus : forall f g P,
      Dt (fun x => f x + g x)%R P -|- Dt f (fun f' => Dt g (fun g' => P (fun x => f' x + g' x))%R).
  Proof.
    intros. unfold Dt.
    red. simpl.
    apply and_forall; intro.
    apply and_forall; intro.
    split.
    { intros. admit. }
    { admit. }
  Qed.

  Definition embedC (P : Prop) : CActionProp := fun _ _ => P.

  Require Import ExtLib.Tactics.

  (** This formalism is not quite correct **)
  Theorem deriv_formula_eq : forall (H : StateProp) (f g : tlaState -> R),
      let Z : StateProp := ap (fmap (@eq R) f) g in
      Dt f (fun f' => Dt g (fun g' => embedC (f' = g'))) (* incomplete *)
      |-- deriv_formula Z.
  Proof.
    simpl. unfold deriv_formula. simpl. intros.
    unfold throughC, Dt, startsFromC, embedC in *.
    forward_reason.
    intros.
    red in H0. forward_reason.
    assert (exists g',
               (forall (t' : R) (pf : (0 <= t' < t)%R),
                   derive_pt (fun x0 : R => f (t0 x0)) t' (x t' pf) = g' t')).
    { admit. (* not provable *) }
    destruct H4.
    specialize (H0 _ H4).
    destruct H0.
    assert (exists g',
               (forall (t' : R) (pf : (0 <= t' < t)%R),
                   derive_pt (fun x0 : R => g (t0 x0)) t' (x1 t' pf) = g' t')).
    { admit. (* not provable *) }
    destruct H5.
    specialize (H0 _ H5).
    Require Coq.Reals.MVT.
    generalize (@MVT.null_derivative_loc (fun x => f (t0 x) - g (t0 x))%R 0 r').
    intro.
    assert (forall x3 : R,
               (0 < x3 < r')%R ->
               derivable_pt (fun x4 : R => (f (t0 x4) - g (t0 x4))%R) x3).
    { intros. eapply derivable_pt_minus; eauto.
      eapply x. admit.
      eapply x1. admit. }
    specialize (H6 H7).
    match goal with
    | H : ?X -> ?Y -> _ |- _ =>
      assert X by admit; assert Y by admit; forward_reason
    end.
    subst.
    clear - H6 H1. red in H6.
    assert ((0 <= r' <= r')%R) by admit.
    specialize (H6 _ H).
    rewrite H1 in *.
    admit.
  Qed.

(* TODO: Revise this formalism 
Theorem deriv_formula_eq : forall (H : StateProp) (f g : tlaState -> R),
    let Z : StateProp := ap (fmap (@eq R) f) g in
    startsFromC H -->> (** this should be in the current state **)
        Dt f (fun f' => Dt g (fun g' => f' = g'))) (* incomplete *)
    |-- deriv_formula H Z.
Proof.
  simpl. unfold deriv_formula. simpl. intros.
  specialize (H0 H1).
  unfold throughC, Dt, startsFromC, embedC in *.
  forward_reason.
  intros.
  red in H0. forward_reason.
  assert (exists g',
             (forall (t' : R) (pf : (0 <= t' < t)%R),
                 derive_pt (fun x0 : R => f (t0 x0)) t' (x t' pf) = g' t')).
  { admit. (* not provable *) }
  destruct H5.
  specialize (H0 _ H5).
  destruct H0.
  assert (exists g',
             (forall (t' : R) (pf : (0 <= t' < t)%R),
                 derive_pt (fun x0 : R => g (t0 x0)) t' (x1 t' pf) = g' t')).
  { admit. (* not provable *) }
  destruct H6.
  specialize (H0 _ H6).
  Require Coq.Reals.MVT.
  generalize (@MVT.null_derivative_loc (fun x => f (t0 x) - g (t0 x))%R 0 r').
  intro.
  assert (forall x3 : R,
           (0 < x3 < r')%R ->
           derivable_pt (fun x4 : R => (f (t0 x4) - g (t0 x4))%R) x3).
  { intros. eapply derivable_pt_minus; eauto.
    eapply x. admit.
    eapply x1. admit. }
  specialize (H7 H8).
  match goal with
  | H : ?X -> ?Y -> _ |- _ => assert X; [ | assert Y; [ | forward_reason ] ]
  end.
  admit. admit.
  clear - H7 H2 H3 H4. red in H7.
  rewrite H2 in H7.
  rewrite RIneq.Rminus_diag_eq in H7 by reflexivity.
  specialize (H7 r').
  assert ((0 <= r' <= r')%R) by admit.
  specialize (H7 H).
  admit.
Qed.
*)

(** This is the old differential induction rule **)
Theorem starts_continuously_through_now : forall G d F GI,
    startsFromC GI //\\ (deriv_on_interval d) |-- throughC GI ->
    deriv_on_interval d |-- deriv_formula GI G ->
    F |-- startsFromC GI //\\ startsFromC G //\\ (deriv_on_interval d) -->> throughC G.
Proof.
  simpl. intros.
  clear H.
  destruct H2 as [ ? [ ? ? ] ].
  specialize (H0 _ _ H3).
  red in H0.
  eapply H0; eauto.
Qed.

(*
Theorem diff_ind : forall Hyps G cp F,
  is_st_formula G ->
  is_st_formula Hyps ->
  (F |-- Continuous cp) ->
  ((Hyps //\\ Continuous cp) |-- next Hyps) ->
  (F |-- G) ->
  (F |-- Hyps) ->
  (Hyps |-- Continuous cp -->> deriv_formula G) ->
  (F |-- next G).
*)

End localized.
