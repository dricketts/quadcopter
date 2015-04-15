Require Import Charge.Logics.ILogic.
Require Charge.Logics.ILInsts.
Require Import Coq.Strings.String.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Tactics.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.

Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Functor.

Existing Instance Applicative_Fun.
Existing Instance Functor_Fun.

Transparent ILInsts.ILFun_Ops.

Section localized.
  Variable tlaState : Type.

  Definition time : Type := R.

  Definition TemporalVal (T : Type) : Type := time -> T.

  (* These are the "obvious" definitions, needed to help Coq *)
  Global Instance Applicative_TemporalVal
  : Applicative TemporalVal :=
  { pure := fun _ x => fun _ => x
  ; ap := fun _ _ f x => fun t => (f t) (x t)
  }.

  Global Instance Functor_TemporalVal
  : Functor TemporalVal :=
  { fmap := fun _ _ f x => ap (pure f) x }.

  (** EvolveProp's are predicates about the evolution function **)
  Definition EvolveProp : Type :=
    (TemporalVal tlaState) -> Prop.

  Global Instance ILogicOps_EvolveProp : ILogicOps EvolveProp := @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogic_EvolveProp : ILogic EvolveProp. Admitted.


  Definition ContProp : Type :=
    TemporalVal EvolveProp.
  Global Instance ILogicOps_ContProp : ILogicOps ContProp := @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogic_ContProp : ILogic ContProp. Admitted.

  Definition AccessingE (P : TemporalVal tlaState -> EvolveProp) : EvolveProp :=
    fun f => (P f) f.

  Definition Accessing (P : TemporalVal tlaState -> ContProp) : ContProp :=
    fun t f => (P f) t f.

  Definition derivNow (g : TemporalVal R) (P : TemporalVal R -> ContProp) : ContProp :=
    fun t f =>
      exists is_derivable : derivable_pt g t,
        forall g' : R -> R,
          derive_pt g t is_derivable = g' t ->
          (P g') t f.

  Definition derivNowR (g : TemporalVal R) (P : R -> ContProp) : ContProp :=
    fun t f =>
      exists is_derivable : derivable_pt g t,
        forall g' : R,
          derive_pt g t is_derivable = g' ->
          (P g') t f.

  Definition deriv (g : TemporalVal R) (P : TemporalVal R -> EvolveProp) : EvolveProp :=
    fun f =>
      exists is_derivable : forall t', derivable_pt g t',
        forall g' : R -> R,
          (forall t', derive_pt g t' (is_derivable t') = g' t') ->
          (P g') f.

  (** example **)
  Variable getR : string -> tlaState -> R.

  Definition getFrom (f : TemporalVal tlaState) (s : string) : TemporalVal R :=
    fun t => getR s (f t).

  Notation "x @ now" := (getFrom now x) (at level 30).

  Definition Throughout (P : TemporalVal EvolveProp) : EvolveProp :=
    fun f => forall t, P t f.

  Definition tlift2 {A B C} (f : A -> B -> C)
             (a : TemporalVal A) (b : TemporalVal B) : TemporalVal C :=
    fun t => f (a t) (b t).

  Lemma AccessingE_entails : forall P Q,
      (forall now, P now |-- Q now) ->
      (AccessingE P |-- AccessingE Q).
  Proof.
    red. compute. intuition.
  Qed.
  Lemma Throughout_entails : forall P Q,
      (P |-- Q) -> Throughout P |-- Throughout Q.
  Proof.
    red. compute; intuition.
  Qed.

  Axiom DNow_is : TemporalVal R -> TemporalVal R -> ContProp.
  Lemma derivNow_shift_L
    : forall f P,
      derivNow f P -|- Exists f', DNow_is f f' //\\ P f'.
  Proof. Admitted.
  Lemma derivNow_use_R
    : forall C P f f',
      C |-- DNow_is f f' ->
      C |-- P f' ->
      C |-- derivNow f P.
  Proof. Admitted.
  Lemma derivNow_derivNowR : forall f P,
      derivNowR f P -|- derivNow f (fun f' t => P (f' t) t).
  Proof. Admitted.

  Goal
    AccessingE (fun now =>
                 Throughout (     derivNowR ("y" @ now) (fun y' =>
                                                           (fun _ _ => y' = 1%R))
                             //\\ derivNowR ("x" @ now) (fun x' =>
                                                          (fun _ _ => x' = 0%R))))
    |--
    AccessingE (fun now =>
                 Throughout (derivNowR (tlift2 Rplus ("x" @ now) ("y" @ now)) (fun f' =>
                                                     (fun _ _ => f' = 1%R)))).
  Proof.
    apply AccessingE_entails; intro.
    eapply Throughout_entails.
    repeat rewrite derivNow_derivNowR.
    do 3 rewrite derivNow_shift_L.
    (* break *)
    red. simpl. intuition.
    forward_reason.
    exists (fun t => x0 t + x t)%R.
    rewrite H2. rewrite H1. split.
    + admit.
    + admit.
  Qed.

  Goal
    AccessingE (fun now =>
                 Throughout (     derivNow ("y" @ now) (fun y' =>
                                                           (fun t _ => y' t = 1%R))
                             //\\ derivNow ("x" @ now) (fun x' =>
                                                          (fun t _ => x' t = 0%R))))
    |--
    AccessingE (fun now =>
                 Throughout (derivNow (tlift2 Rplus ("x" @ now) ("y" @ now)) (fun f' =>
                                                     (fun t _ => f' t = 1%R)))).
  Proof.
    apply AccessingE_entails; intro.
    eapply Throughout_entails.
    do 3 rewrite derivNow_shift_L.
    (* break *)
    red. simpl. intuition.
    forward_reason.
    exists (fun t => x0 t + x t)%R.
    rewrite H2. rewrite H1. split.
    + admit.
    + admit.
  Qed.


(*
  (** Old Version **)
  Definition deriv (g : TemporalVal R) (P : TemporalVal R -> ContProp) : ContProp :=
    fun f =>
      exists is_derivable : forall (t' : R), derivable_pt g t',
        forall g' : R -> R,
          (forall t', derive_pt g t' (is_derivable t') = g' t') ->
          P g' f.

  (** example **)
  Variable getR : string -> tlaState -> R.

  Definition getFrom (f : TemporalVal tlaState) (s : string) : TemporalVal R :=
    fun t => getR s (f t).

  Notation "x @ now" := (getFrom now x) (at level 30).

  Definition Throughout (P : TemporalVal ContProp) : ContProp :=
    fun f => forall t, P t f.

  Definition embed : Prop -> ContProp :=
    fun P _ => P.
  Definition embedT {T U} : (T -> U) -> TemporalVal T -> TemporalVal U :=
    fun f P t => f (P t).

  Goal
    Accessing (fun now =>
                 deriv ("x" @ now) (fun x' => ltrue))
    |-- Accessing (fun now =>
                 deriv ("x" @ now) (fun x' => Throughout (embedT embed (ap (fmap (F:=TemporalVal) (@eq R) x') (pure (T:=TemporalVal) 0%R))))).
*)
End localized.