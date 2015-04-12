Require Import Coq.Classes.RelationClasses.
Require Coq.Lists.List.
Require Import Rdefinitions.

Set Implicit Arguments.
Set Strict Implict.

Section with_state.

  Variable ST : Type.

  (** [STc] is the continuous part of the state, [STd] is the discrete part **)
  Class HybridState : Type :=
  { STc : Type
  ; STd : Type
  ; hybrid_split : ST -> STc * STd
  ; hybrid_join  : STc -> STd -> ST
  ; hybrid_split_join : forall a b, hybrid_split (hybrid_join a b) = (a,b)
  ; hybrid_join_split : forall st, hybrid_join (fst (hybrid_split st)) (snd (hybrid_split st)) = st
  }.
  Context {HySt : HybridState}.

  (* A behavior is an infinite stream of states.
   *)
  CoInductive continue (from : ST) :=
  | Cont : forall (r : R), (r > 0)%R -> forall (f : R -> STc),
                             f 0%R = fst (hybrid_split from) ->
                             (** We could require that [f] is continuous **)
                             continue (hybrid_join (f r) (snd (hybrid_split from))) -> continue from
  | Discr : forall s : STd, continue (hybrid_join (fst (hybrid_split from)) s) -> continue from.

  Inductive trace :=
  | Trace : forall start : ST, continue start -> trace.

  (* The head of a trace *)
  Definition hd (s:trace) : ST :=
    match s with
    | Trace now _ => now
    end.

  Definition traceK (s : trace) : continue (hd s) :=
    match s as s return continue (hd s) with
    | Trace _ x => x
    end.

  Definition tl (t : trace) : trace :=
    match traceK t with
    | Discr x s => Trace s
    | Cont _ _ _ _ s => Trace s
    end.

  Axiom R_plus_minus : forall a b : R, (a + (b - a) = b)%R.
  Axiom R_minus_lt : forall a b : R, (b > 0 -> a < b -> b - a > 0)%R.

  Inductive after_time : R -> nat -> trace -> trace -> Prop :=
  | Now    : forall s, after_time 0 0 s s
  | WithinD : forall n st st' (s : continue _) s',
      after_time 0 n (Trace s) s' ->
      after_time 0 (S n) (@Trace st (@Discr st st' s)) s'
  | AfterDC : forall r n st sd (s : continue _) s',
      (r > 0)%R ->
      after_time r n (Trace s) s' ->
      after_time r n (Trace (@Discr st sd s)) s'
  | WithinC : forall n (st : ST) r t (f : R -> STc) s pf0 pf pf',
      (0 < r)%R ->
      forall pf_r_lt_t : (r < t)%R,
      after_time r n
                 (@Trace st (@Cont st t pf0 f pf s))
                 (@Trace (hybrid_join (f r) (snd (hybrid_split st)))
                         (@Cont (hybrid_join (f r) (snd (hybrid_split st))) (t - r)
                                (@R_minus_lt r t pf0 pf_r_lt_t) (fun x => f (r + x))%R pf'
                                match eq_sym (R_plus_minus r t) in _ = t
                                    , eq_sym (hybrid_split_join (f r) (snd (hybrid_split st))) in _ = X
                                      return continue (hybrid_join (f t) (snd X))
                                with
                                | eq_refl , eq_refl => s
                                end))
  | AfterC : forall st n r t f s' s'' pf0 pf,
      (r > 0)%R ->
      (r >= t)%R ->
      after_time (r - t)%R n (Trace s') s'' ->
      after_time r n (Trace (@Cont st t pf0 f pf s')) s''.

  Lemma after_time_now : forall s s',
      after_time 0 0 s s' ->
      s = s'.
  Proof.
    inversion 1; auto.
    { exfalso; clear - H0. admit. }
    { exfalso; clear - H0. admit. }
    { exfalso; clear - pf0. admit. }
  Qed.

  Definition skips_to : trace -> trace -> Prop :=
    fun s s' =>
      exists tR tN, after_time tR tN s s'.

  Inductive skips_to' : trace -> trace -> Prop :=
  | skip_Now    : forall s, skips_to' s s
  | skip_AfterD : forall st sd (s : continue _) s',
      skips_to' (Trace s) s' ->
      skips_to' (Trace (@Discr st sd s)) s'
  | skip_WithinC : forall (st : ST) r t (f : R -> STc) s pf0 pf pf',
      (0 < r)%R ->
      forall pf_r_lt_t : (r < t)%R,
      skips_to' (@Trace st (@Cont st t pf0 f pf s))
                (@Trace (hybrid_join (f r) (snd (hybrid_split st)))
                        (@Cont (hybrid_join (f r) (snd (hybrid_split st))) (t - r)
                                (@R_minus_lt r t pf0 pf_r_lt_t) (fun x => f (r + x))%R pf'
                                match eq_sym (R_plus_minus r t) in _ = t
                                    , eq_sym (hybrid_split_join (f r) (snd (hybrid_split st))) in _ = X
                                      return continue (hybrid_join (f t) (snd X))
                                with
                                | eq_refl , eq_refl => s
                                end))
  | skip_AfterC : forall st r t f s' s'' pf0 pf,
      (r > 0)%R ->
      (r >= t)%R ->
      skips_to' (Trace s') s'' ->
      skips_to' (Trace (@Cont st t pf0 f pf s')) s''.

  Theorem skips_to_skips_to' : forall a b,
      skips_to a b <-> skips_to' a b.
  Proof.
    red; split.
    { destruct 1.
      destruct H.
      induction H; try solve [ econstructor; eauto ]. }
    { induction 1.
      { solve [ do 2 eexists; econstructor; eauto ]. }
      { destruct IHskips_to'. destruct H0.
        admit. }
      { exists r. exists 0.
        constructor; eauto. }
      { destruct IHskips_to'. destruct H2.
        exists (x + t)%R. exists x0.
        eapply AfterC. admit. admit. admit. } }
  Qed.

  Inductive Step :=
  | DiscreteTo : ST -> Step
  | ContinuousBy : R -> (R -> STc) -> Step.

  Definition firstStep (s : trace)
  : Step :=
    match traceK s with
    | Discr x _ => DiscreteTo (hybrid_join (fst (hybrid_split (hd s))) x)
    | Cont r _ t _ _ => ContinuousBy r t
    end.

(*
  Definition after_dstep (s : stream) : option stream :=
    match s with
    | Cont _ _ _ => None
    | Discr _ a => Some a
    end.

  Definition next_tl (s : stream) : stream :=
    match s with
    | Cont _ _ _ => s
    | Discr _ a => a
    end.
*)

  Global Instance Transitive_skips_to : Transitive skips_to.
  Proof.
    red. 
  Admitted.

  Global Instance Reflexive_skips_to : Reflexive skips_to.
  Proof.
    red. intros. exists 0%R. exists 0. apply Now.
  Qed.

End with_state.

Arguments Step _ {_}.
Arguments trace _ {_}.
Arguments after_time {ST _} _ _ _ _.
Arguments skips_to {ST _} _ _.
Arguments hd {ST _} _.
Arguments tl {ST _} _.
Arguments firstStep {ST _} _.
Arguments Transitive_skips_to {ST _} _ _ _ _ _.
Arguments Reflexive_skips_to {ST _} _.




(* (* The tail of a stream *) *)
(* Definition tl {A} (s:stream A) : stream A := *)
(*   match s with *)
(*   | Cont  *)
(*   | Cons _ s' => s' *)
(*   end. *)

(* (* The nth suffix of a stream *) *)
(* Fixpoint nth_suf {A} (n:nat) (s:stream A) : stream A := *)
(*   match n with *)
(*     | O => s *)
(*     | S n => nth_suf n (tl s) *)
(*   end. *)

(* Lemma nth_suf_tl : forall A n (s:stream A), *)
(*   nth_suf n (tl s) = *)
(*   tl (nth_suf n s). *)
(* Proof. *)
(*   intros A n; induction n; intro s; *)
(*   firstorder. *)
(* Qed. *)

(* Lemma nth_suf_Sn : forall A n (s:Stream.stream A), *)
(*   Stream.nth_suf (S n) s = *)
(*   Stream.tl (Stream.nth_suf n s). *)
(* Proof. *)
(*   intros A n; induction n; intro s; *)
(*   firstorder. *)
(* Qed. *)


(** Two-level clock: (R * nat)
 **)
