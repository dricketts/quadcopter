Require Import TLA.HyStreamTrans.
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

  Definition StateVal (T : Type) : Type :=
    tlaState -> T.
  Definition DActionVal (T : Type) : Type :=
    tlaState -> tlaState -> T.
  Definition ActionVal (T : Type) : Type :=
    tlaState -> @Step tlaState -> T.
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
    fun P tr => P (HyStreamTrans.hd tr).

  Definition next : StateProp -> TraceProp :=
    fun P tr => P (HyStreamTrans.hd (HyStreamTrans.tl tr)).

  Definition always (P : TraceProp) : TraceProp :=
    fun s =>
      forall s', HyStreamTrans.skips_to s s' -> P s'.

  Definition eventually (P : TraceProp) : TraceProp :=
    fun s =>
      exists s', HyStreamTrans.skips_to s s' /\ P s'.

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
      | ContinuousBy r f => P r f
      | _ => False
      end.

  Definition stutter {T} (f : tlaState -> T) : DActionProp :=
    fun st st' => f st = f st'.

  Definition starts (P : ActionProp) : TraceProp :=
    fun tr =>
      P (HyStreamTrans.hd tr) (firstStep tr).

(*
  Definition get {T} : tlaVar T -> tlaState -> T := record_get.

  Definition pre {T} (v : tlaVar T) : DActionVal T :=
    fun st _ => get v st.

  Definition post {T} (v : tlaVar T) : DActionVal T :=
    fun _ st' => get v st'.
*)

  Definition lift {X T U} (f : T -> U)
    : (X -> T) -> X -> U.
    refine (ap (pure f)).
  Defined.

  Definition lift2 {X T U V} (f : T -> U -> V)
    : (X -> T) -> (X -> U) -> X -> V.
    refine (fun a b => ap (ap (pure f) a) b).
  Defined.


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
    induction H2; simpl.
    { (* Now *)
      intros. assumption. }
    { (* AfterD *)
      intros.
      eapply IHskips_to.
      { red in H1.
        specialize (H1 _ (ST_Now _) H0).
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
  Qed.

  Lemma always_and : forall P Q,
      always P //\\ always Q -|- always (P //\\ Q).
  Proof.
    intros. split.
    { red. red. simpl. unfold always. intuition. }
    { red. red. simpl. unfold always. intuition;
                                      edestruct H; eauto. }
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


(*
  Definition SSys (I : StateProp) (ls : list ActionProp) : TraceProp :=
         now I
    //\\ always (starts (     AnyOf ls
                         \\// before (AllOf (List.map (fun x => enabled x -->> lfalse) ls))
                         \\// discretely (stutter (fun x => x)))).
*)

  Definition Sys (I : StateProp) (d : DActionProp) : TraceProp :=
    now I //\\ always (starts (discretely (d \\// stutter (fun x => x)))).

  Definition HSys (I : StateProp) (w : CActionProp) (d : DActionProp) : TraceProp :=
    now I //\\ always (starts (continuously w \\// discretely (d \\// stutter (fun x => x)))).




End localized.


Section localized.
  Variable tlaState : Type.

  Definition StateProp := tlaState -> Prop.

  Definition DActionProp := tlaState -> tlaState -> Prop.
  Definition CActionProp := forall (t : R) (f : R -> tlaState), Prop.

  Definition ActionProp := tlaState -> @Step tlaState -> Prop.

  Definition TraceProp := trace tlaState -> Prop.

  Instance ILogicOps_StateProp : ILogicOps StateProp := @ILInsts.ILFun_Ops _ _ _.
  Instance ILogicOps_ActionProp : ILogicOps ActionProp := @ILInsts.ILFun_Ops _ _ _.
  Instance ILogicOps_DActionProp : ILogicOps DActionProp := @ILInsts.ILFun_Ops _ _ _.
  Instance ILogicOps_CActionProp : ILogicOps CActionProp := @ILInsts.ILFun_Ops _ _ _.
  Instance ILogicOps_TraceProp : ILogicOps TraceProp := @ILInsts.ILFun_Ops _ _ _.
  Instance ILogic_StateProp : ILogic StateProp. Admitted.
  Instance ILogic_ActionProp : ILogic ActionProp. Admitted.
  Instance ILogic_DActionProp : ILogic DActionProp. Admitted.
  Instance ILogic_CActionProp : ILogic CActionProp. Admitted.
  Instance ILogic_TraceProp : ILogic TraceProp. Admitted.

(* These are the "obvious" definitions, needed to help Coq *)
Instance Applicative_Action
: Applicative (fun x : Type => tlaState -> tlaState -> x) :=
{ pure := fun _ x => fun _ _ => x
; ap := fun _ _ f x => fun st st' => (f st st') (x st st')
}.

Instance Functor_Action
: Functor (fun x : Type => tlaState -> tlaState -> x) :=
{ fmap := fun _ _ f x => ap (pure f) x }.


Definition now : StateProp -> TraceProp :=
  fun P tr => P (HyStreamTrans.hd tr).

Definition next : StateProp -> TraceProp :=
  fun P tr => P (HyStreamTrans.hd (HyStreamTrans.tl tr)).

Definition always (P : TraceProp) : TraceProp :=
  fun s =>
    forall s', HyStreamTrans.skips_to s s' -> P s'.

Definition eventually (P : TraceProp) : TraceProp :=
  fun s =>
    exists s', HyStreamTrans.skips_to s s' /\ P s'.

Definition discretely (P : DActionProp) : ActionProp :=
  fun start step =>
    match step with
    | DiscreteTo st' =>
      P start st'
    | _ => False
    end.

Definition continuously (P : (R -> tlaState) -> R -> Prop) : ActionProp :=
  fun start step =>
    match step with
    | ContinuousBy r f => P f r
    | _ => False
    end.

Definition stutter {T} (f : tlaState -> T) : DActionProp :=
  fun st st' => f st = f st'.

Definition starts (P : ActionProp) : TraceProp :=
  fun tr =>
    P (HyStreamTrans.hd tr) (firstStep tr).

Definition Sys (I : StateProp) (d : DActionProp) : TraceProp :=
  now I //\\ always (starts (discretely (d \\// stutter (fun x => x)))).

Definition get : string -> tlaState -> R :=
  fun v st => st v.

Definition lift {X T U} (f : T -> U)
: (X -> T) -> X -> U.
refine (ap (pure f)).
Defined.

Definition lift2 {X T U V} (f : T -> U -> V)
: (X -> T) -> (X -> U) -> X -> V.
refine (fun a b => ap (ap (pure f) a) b).
Defined.

Definition init : StateProp :=
  ap (fmap eq (get "x")) (pure 0%R).

Definition pre (v : string) : tlaState -> tlaState -> R :=
  fun st _ => st v.

Definition post (v : string) : tlaState -> tlaState -> R :=
  fun _ st' => st' v.

Definition Inc : TraceProp :=
  Sys init
      (ap (T:=fun x => tlaState -> tlaState -> x)
          (fmap eq (post "x")) (ap (fmap Rplus (pre "x")) (pure 1%R))).

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
  induction H2; simpl.
  { (* Now *)
    intros. assumption. }
  { (* AfterD *)
    intros.
    eapply IHskips_to.
    { red in H1.
      specialize (H1 _ (ST_Now _) H0).
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
Qed.

Lemma always_and : forall P Q,
    always P //\\ always Q -|- always (P //\\ Q).
Proof.
  intros. split.
  { red. red. simpl. unfold always. intuition. }
  { red. red. simpl. unfold always. intuition;
    edestruct H; eauto. }
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

Theorem Inc_positive :
  |-- Inc -->> always (now (ap (fmap Rge (get "x")) (pure 0%R))).
Proof.
  intros.
  apply limplAdj.
  eapply hybrid_induction.
  { apply landL2.
    unfold Inc. unfold Sys. unfold init.
    eapply landL2.
    reflexivity. }
  { apply landL2.
    unfold Inc. unfold Sys. unfold init.
    eapply landL1.
    apply now_entails.
    simpl. intuition.
    rewrite H. admit. }
  { eapply always_tauto.
    rewrite <- uncurry.
    rewrite now_starts_discretely_and.
    eapply starts_discretely_through. simpl.
    intros. intuition.
    { unfold post, pre, get in *. 
      rewrite H. admit. }
    { unfold stutter in *. subst. assumption. } }
Qed.

Lemma and_forall : forall {T} (F G : T -> Prop),
    ((forall x, F x) /\ (forall x, G x)) <->
    (forall x, F x /\ G x).
Proof. firstorder. Qed.

(*
Definition dt_trace (P : TraceProp) : TraceProp :=
  fun tr =>
    match firstStep tr return Prop with
    | ContinuousBy r f =>
      forall r', (r' < r)%R -> forall tr', after_time r' 0 tr tr' -> P tr'
    | _ => True
    end.

Theorem deriv_and : forall P Q,
    dt_trace (P //\\ Q) -|- dt_trace P //\\ dt_trace Q.
Proof.
  red. intros.
  unfold dt_trace. simpl.
  apply and_forall. intros.
  destruct (firstStep x); firstorder.
Qed.
*)

(*
Axiom deriv_at_point_from_right : (R -> R) -> R -> R -> Prop.

Definition onDeriv (stP : TraceProp) : TraceProp :=
  fun tr =>
    match firstStep tr return Prop with
    | ContinuousBy r f =>
      exists f' : R -> tlaState,
                  (forall r', (0 < r' <= r)%R ->
                              forall v : tlaVar,
                                deriv_at_point_from_right (fun t => f' t v) r' (f' r' v)) /\
                  stP 
    | _ => True
    end.
*)

Require Import Coq.Reals.Ranalysis1.

(*
Definition solves_diffeqs (f : R -> tlaState)
           (diffeqs : list DiffEq) (r : R)
           (is_derivable : forall x, derivable (fun t => f t x)) :=
  forall x d st,
    List.In (DiffEqC x d) diffeqs ->
    forall z, (R0 <= z <= r)%R ->
              derive (fun t => f t x) (is_derivable x) z =
              eval_term d (f z) st.

(* Prop expressing that f is a solution to diffeqs in
   [0,r]. *)
Definition is_solution (f : R -> state)
           (diffeqs : list DiffEq) (r : R) :=
  exists is_derivable,
    (* f is a solution to diffeqs *)
    solves_diffeqs f diffeqs r is_derivable.
*)

Definition is_deriv_state_pt (f : R -> tlaState) (t : R) (val : tlaState) : Prop :=
  exists is_derivable : forall v : tlaVar, derivable_pt (fun x => f x v) t,
    forall (v : tlaVar),
      derive_pt (fun x => f x v) t (is_derivable v) = val v.

(** NOTE: pr_nu says "forall p1 p2, derive_pt f x p1 = derive_pt f x p2" **)

Definition deriv_on_interval (P : (R -> tlaState) -> Prop) (f : R -> tlaState) (t : R) : Prop :=
  exists is_derivable : forall (v : tlaVar) (t' : R), (0 <= t' < t)%R -> derivable_pt (fun x => f x v) t',
    forall f' : R -> tlaState,
      (forall v t' (pf : (0 <= t' < t)%R),
          derive_pt (fun x => f x v) t' (is_derivable v t' pf) = f' t' v) ->
      P f'.

Definition deriv_formula (H : StateProp) (G : StateProp) : TraceProp :=
  now H -->> through (now G).

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

Definition Dt (g : tlaState -> R) (P : (R -> R) -> CActionProp) : CActionProp :=
  fun t f =>
    exists is_derivable : forall (t' : R), (0 <= t' < t)%R -> derivable_pt (fun x => g (f x)) t',
      forall f' : R -> R,
        (forall t' (pf : (0 <= t' < t)%R),
            derive_pt (fun x => g (f x)) t' (is_derivable t' pf) = f' t') ->
        P f' t f.

Theorem deriv_formula_eq : forall (H : StateProp) (f g : tlaState -> R),
    let Z : StateProp := ap (fmap (@eq R) f) g in
    now H -->>
        starts_continuously (deriv_on_interval (fun f' : R -> tlaState => forall t, Z (f' t)%R))
    |-- now H -->> now Z -->> through (now Z). (* deriv_formula H Z. *)
Proof.
  simpl. unfold deriv_formula. simpl. intros.
  unfold through,starts_continuously in *.
  destruct t. destruct c; simpl in *; try contradiction.
  { intros.
    specialize (H0 H1).
    inversion H4; clear H4.
    { subst. exfalso; clear - H3. admit. }
    { subst. assert (c = s0) by admit.
      clear H11; subst.
      unfold now in *. simpl in *.
      clear pf1 pf3.
      red in H0.

      (** by integration **) admit. }
    { subst.
      assert (r' = r) by admit.
      subst.
      cutrewrite (r - r = 0)%R in H14; [ | admit ].
      eapply after_time_now in H14. subst.
      unfold now in *. simpl in *.
      (** by integration **) admit. } }
Qed.

(** This is the old differential induction rule **)
Theorem starts_continuously_through_now : forall G d F GI,
    now GI //\\ starts_continuously (deriv_on_interval d) |-- through (now GI) ->
    starts_continuously (deriv_on_interval d) |-- deriv_formula GI G ->
    F |-- now GI //\\ now G //\\ starts_continuously (deriv_on_interval d) -->> through (now G).
Proof.
  simpl. intros.
  clear H.
  destruct H2 as [ ? [ ? ? ] ].
  unfold starts_continuously, through in *.
  specialize (H0 t).
(*  specialize (H t). clear  *)
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

(** Thoughts
 ** 1) Stuttering invariance (ok)
 ** 2) Small footprint
 ** 3) Multiple clocks
 **)