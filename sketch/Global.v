Require Import TLA.Stream.
Require Import Charge.Logics.ILogic.
Require Charge.Logics.ILInsts.
Require Import Coq.Strings.String.
Require Import ExtLib.Structures.Applicative.
Require Import Coq.Reals.Rdefinitions.

Definition tlaState := string -> R.

Definition StateProp := tlaState -> Prop.

Definition ActionProp := tlaState -> tlaState -> Prop.

Definition TraceProp := stream tlaState -> Prop.

Instance ILogicOps_StateProp : ILogicOps StateProp := @ILInsts.ILFun_Ops _ _ _.
Instance ILogicOps_ActionProp : ILogicOps ActionProp := @ILInsts.ILFun_Ops _ _ _.
Instance ILogicOps_TraceProp : ILogicOps TraceProp := @ILInsts.ILFun_Ops _ _ _.
Instance ILogic_StateProp : ILogic StateProp. Admitted.
Instance ILogic_ActionProp : ILogic ActionProp. Admitted.
Instance ILogic_TraceProp : ILogic TraceProp. Admitted.


Definition now : StateProp -> TraceProp :=
  fun P tr => P (Stream.hd tr).

Definition next : StateProp -> TraceProp :=
  fun P tr => P (Stream.hd (Stream.tl tr)).

Definition always : TraceProp -> TraceProp :=
  fun P tr => forall n, P (nth_suf n tr).

Definition eventually : TraceProp -> TraceProp :=
  fun P tr => exists n, P (nth_suf n tr).

Definition starts : ActionProp -> TraceProp :=
  fun P tr => P (Stream.hd tr) (Stream.hd (Stream.tl tr)).

Definition stutter {T} (f : tlaState -> T) : ActionProp :=
  fun st st' => f st = f st'.

Definition Sys (I : StateProp) (d : ActionProp) : TraceProp :=
  now I //\\ always (starts (d \\// stutter (fun x => x))).

Definition get : string -> tlaState -> R :=
  fun v st => st v.

Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Functor.

Existing Instance Applicative_Fun.
Existing Instance Functor_Fun.

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

Instance Applicative_Action
: Applicative (fun x : Type => tlaState -> tlaState -> x) :=
{ pure := fun _ x => fun _ _ => x
; ap := fun _ _ f x => fun st st' => (f st st') (x st st')
}.

Instance Functor_Action
: Functor (fun x : Type => tlaState -> tlaState -> x) :=
{ fmap := fun _ _ f x => ap (pure f) x }.


Definition Inc : TraceProp :=
  Sys init
      (ap (T:=fun x => tlaState -> tlaState -> x)
          (fmap eq (post "x")) (ap (fmap Rplus (pre "x")) (pure 1%R))).

Theorem dind : forall G P T,
    G |-- now P //\\ always (starts T) ->
    G |-- always (now P //\\ starts T -->> next P) ->
    G |-- always (now P).
Proof.
  intros. red. red. Transparent ILInsts.ILFun_Ops.
  red.
  intros. red. simpl. red.
  induction n.
  { simpl. eapply H. assumption. }
  { specialize (H _ H1).
    destruct H.
    rewrite nth_suf_Sn. change (next P (nth_suf n t)).
    apply H0. auto.
    split. auto. auto. }
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
Lemma now_starts_and : forall P Q,
    now P //\\ starts Q -|- starts (fun st st' => P st /\ Q st st').
Proof.
  intros. compute; intuition.
Qed.
Lemma starts_next_impl : forall P Q,
    starts P -->> next Q -|- starts (fun st st' => P st st' -> Q st').
Proof.
  intros. compute; intuition.
Qed.
Lemma starts_tauto : forall G P,
    |-- P ->
    G |-- starts P.
Proof.
  compute; intuition.
Qed.

Theorem Inc_positive :
  |-- Inc -->> always (now (ap (fmap Rge (get "x")) (pure 0%R))).
Proof.
  intros.
  apply limplAdj.
  eapply dind.
  { apply landL2.
    unfold Inc. unfold Sys. unfold init.
    eapply landR.
    { eapply landL1.
      apply now_entails.
      simpl. intuition.
      rewrite H. admit. }
    { apply landL2.
      Require Import Setoid.
      reflexivity. } }
  { eapply always_tauto.
    rewrite now_starts_and.
    rewrite starts_next_impl.
    eapply starts_tauto. simpl. intuition.
    admit. admit. }
Qed.

Definition Continuous
           (ls : list (string * (R -> R -> Prop) * (tlaState -> R)))
: ActionProp.
Admitted.

Definition dt_state (P : StateProp) : TraceProp.
    (** This needs to be a TraceProp because only traces have derivatives
     ** the first transition is [f] and the state prop holds on the derivative
     ** of [f]
     **)
Admitted.

Definition dt_trace (P : TraceProp) : TraceProp.
Admitted.

Theorem deriv_now : forall P,
    dt_state P -|- dt_trace (now P).
Admitted.

Theorem deriv_and : forall P Q,
    dt_state (P //\\ Q) -|- dt_state P //\\ dt_state Q.
Admitted.


Theorem diff_ind : forall Hyps G cp F,
  is_st_formula G ->
  is_st_formula Hyps ->
  (F |-- Continuous cp) ->
  ((Hyps //\\ Continuous cp) |-- next Hyps) ->
  (F |-- G) ->
  (F |-- Hyps) ->
  (Hyps |-- Continuous cp -->> deriv_formula G) ->
  (F |-- next G).


(** Thoughts
 ** 1) Stuttering invariance (ok)
 ** 2) Small footprint
 ** 3) Multiple clocks
 **)