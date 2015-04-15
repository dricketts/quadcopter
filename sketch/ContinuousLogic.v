Require Import Coq.Classes.Morphisms.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Strings.String.
Require Import Charge.Logics.ILogic.
Require Charge.Logics.ILInsts.
Require Import Charge.Logics.ILEmbed.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Tactics.

Require Import TLA.ChargeTactics.
Require Import hTLA.HybridLogic.

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

  (** ContProp's are predicates about a particular point in time when
   ** evolving by an evolution function
   **)
  Definition ContProp : Type :=
    TemporalVal EvolveProp.
  Global Instance ILogicOps_ContProp : ILogicOps ContProp := @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogic_ContProp : ILogic ContProp. Admitted.

  Definition AccessingE (P : TemporalVal tlaState -> EvolveProp) : EvolveProp :=
    fun f => (P f) f.

  Definition Accessing (P : TemporalVal tlaState -> ContProp) : ContProp :=
    fun t f => (P f) t f.

(* NOTE: These don't seem to have the right properties
  Definition derivNow (g : TemporalVal R) (P : TemporalVal R -> ContProp) : ContProp :=
    fun t f =>
      exists is_derivable : derivable_pt g t,
        forall g' : R -> R,
          derive_pt g t is_derivable = g' t ->
          (P g') t f.

  Definition derivNowR (g : TemporalVal R) (P : R -> ContProp) : ContProp :=
    derivNow g (fun f => Exists v, RightNow (ap (fmap (@eq _) (pure v)) f) //\\ P v).
*)

  Definition RightNow (v : TemporalVal Prop) : ContProp :=
    fun t _ => v t.

  Definition D_is (g g' : TemporalVal R) : Prop :=
    exists is_derivable : forall t', derivable_pt g t',
      (forall t', derive_pt g t' (is_derivable t') = g' t').

  Definition DNow_is (g : TemporalVal R) (g' : R) (t : time) : Prop :=
    exists is_derivable : derivable_pt g t,
      derive_pt g t is_derivable = g'.

  Instance EmbedOp_Prop_EvolveProp : EmbedOp Prop EvolveProp :=
  { embed := fun P _ => P }.
  Instance Embed_Prop_EvolveProp : Embed Prop EvolveProp. Admitted.
  Instance EmbedOp_Prop_ContProp : EmbedOp Prop ContProp :=
  { embed := fun P _ => embed P }.
  Instance Embed_Prop_ContProp : Embed Prop ContProp. Admitted.

  Definition deriv (g : TemporalVal R) (P : TemporalVal R -> EvolveProp) : EvolveProp :=
    Exists g', embed (D_is g g') //\\ P g'.

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

  Lemma deriv_shift_L
    : forall f P,
      deriv f P -|- Exists f', embed (D_is f f') //\\ P f'.
  Proof. reflexivity. Qed.

  Lemma derivNow_use_R
    : forall C P f f',
      C |-- embed (D_is f f') ->
      C |-- P f' ->
      C |-- deriv f P.
  Proof.
    intros. unfold deriv.
    eapply lexistsR. apply landR; eauto.
  Qed.

  Global Instance derivNow_proper
  : Proper ((@eq R ==> @eq R) ==> pointwise_relation _ lequiv ==> lequiv) deriv.
  Proof.
    red. red. red. intros. unfold deriv.
    setoid_rewrite H0.
    split; charge_fwd.
    { eapply lexistsR.
      charge_split; [ | charge_tauto ].
      apply landL1.
      admit. }
    { eapply lexistsR.
      charge_split; [ | charge_tauto ].
      apply landL1.
      admit. }
  Qed.

  Lemma D_is_Rplus : forall f g f' g',
      D_is f f' ->
      D_is g g' ->
      D_is (tlift2 Rplus f g) (tlift2 Rplus f' g').
  Proof.
    clear. unfold D_is.
    intros. forward_reason.
    exists (fun t => derivable_pt_plus _ _ t (x0 t) (x t)).
    intros. rewrite derive_pt_plus.
    rewrite H. rewrite H0. reflexivity.
  Qed.
  Lemma D_is_Rplus_rw : forall f g f' g',
      D_is f f' //\\ D_is g g' |--
           D_is (tlift2 Rplus f g) (tlift2 Rplus f' g').
  Proof.
    clear. unfold D_is. simpl.
    intros. forward_reason.
    exists (fun t => derivable_pt_plus _ _ t (x0 t) (x t)).
    intros. rewrite derive_pt_plus.
    rewrite H. rewrite H0. reflexivity.
  Qed.
  Lemma Throughout_land : forall P Q,
      Throughout P //\\ Throughout Q -|- Throughout (P //\\ Q).
  Proof.
    clear. unfold Throughout. red. simpl.
    intuition. firstorder. firstorder.
  Qed.
  Lemma RightNow_land : forall P Q,
      RightNow P //\\ RightNow Q -|- RightNow (P //\\ Q).
  Proof.
    unfold RightNow. simpl. red; simpl; intuition; firstorder.
  Qed.
  Lemma RightNow_lentails : forall P Q,
      P |-- Q ->
      RightNow P |-- RightNow Q.
  Proof.
    unfold RightNow; red; simpl; intuition; firstorder.
  Qed.

  Goal
    AccessingE (fun now =>
                       deriv ("y" @ now) (fun y' =>
                                            Throughout (RightNow (ap (fmap eq y') (pure 0%R))))
                  //\\ deriv ("x" @ now) (fun x' =>
                                            Throughout (RightNow (ap (fmap eq x') (pure 3%R)))))
    |--
    AccessingE (fun now =>
                  deriv (tlift2 Rplus ("x" @ now) ("y" @ now))
                        (fun f' =>
                           Throughout (RightNow (ap (fmap eq f') (pure 3%R))))).
  Proof.
    apply AccessingE_entails; intro.
    repeat rewrite deriv_shift_L.
    charge_fwd.
    apply (lexistsR (tlift2 Rplus x x0)).
    apply landR.
    { rewrite <- D_is_Rplus_rw.
      rewrite <- embedland.
      charge_tauto. }
    { rewrite landA.
      apply landL2.
      rewrite <- landA.
      rewrite landC.
      rewrite <- landA.
      apply landL1.
      rewrite Throughout_land.
      apply Throughout_entails.
      rewrite RightNow_land.
      eapply RightNow_lentails. simpl.
      intros. unfold tlift2. clear - H.
      destruct H. rewrite H. rewrite H0.
      apply RIneq.Rplus_0_r. }
  Qed.

  (** There seems to be a fundamental difference between
   ** - at all points, the function has a derivative, and
   ** - the function has a derivative at all points.
   ** This could just be a matter of [Prop] vs. [Type], but I'm not certain.
   **)
(**
  Lemma derivNow_derivNowR : forall f P,
      derivNowR f P -|- derivNow f (fun f => Exists v, RightNow (ap (fmap (@eq _) (pure v)) f) //\\ P v).
  Proof. reflexivity. Qed.

  Lemma deriv_deriveNow : forall f P,
      Proper ((eq ==> eq) ==> lequiv) P ->
      Throughout (derivNow f (fun f' t f => P f' f)) |-- deriv f P.
  Proof.
    simpl.
    intros. red in H0. red in H0.
    red. simpl.
    unfold deriv in *. simpl in H0.
    forward_reason.
    red in H0. forward_reason.
    exists (x0 t0).
    intros. rewrite H0 in H2.
    eapply H. 2: eassumption. red. intros; subst.

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
    do 3 rewrite deriv_shift_L.
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
**)

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