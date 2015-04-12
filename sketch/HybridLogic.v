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

  Fixpoint AnyOf {L} {LL : ILogicOps L} (ls : list L) : L :=
    match ls with
    | nil => lfalse
    | cons l ls => l \\// AnyOf ls
    end.

  Fixpoint AllOf {L} {LL : ILogicOps L} (ls : list L) : L :=
    match ls with
    | nil => ltrue
    | cons l ls => l //\\ AllOf ls
    end.

End localized.
