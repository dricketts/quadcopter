Require Import Coq.Classes.RelationClasses.
Require Coq.Lists.List.
Require Import Rdefinitions.

Set Implicit Arguments.
Set Strict Implict.

Section with_state.

  Variable ST : Type.

  Definition Rpositive : Type := { x : R & x > 0 }%R.

  Definition time : Type := (R * nat)%type.

  (* A behavior is an infinite stream of states.
   * In order for differential induction to make sense, you need the solution.
   *)
  CoInductive continue (from : ST) :=
  | Cont : forall (r : R), (r > 0)%R -> forall (f : R -> ST), f 0%R = from -> continue (f r) -> continue from
  | Discr : forall s : ST, continue s -> continue from.

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
  | WithinD : forall n st st' (s : continue st') s',
      after_time 0 n (Trace s) s' ->
      after_time 0 (S n) (@Trace st (@Discr st st' s)) s'
  | AfterDC : forall r n st (s : continue st) s',
      (r > 0)%R ->
      after_time r n (Trace s) s' ->
      after_time r n (Trace (Discr st s)) s'
  | WithinC : forall n (st : ST) r t f s pf0 pf pf',
      (0 < r)%R ->
      forall pf_r_lt_t : (r < t)%R,
      after_time r n
                 (@Trace st (@Cont st t pf0 f pf s))
                 (@Trace (f r) (@Cont _ (t - r)
                                      (@R_minus_lt r t pf0 pf_r_lt_t) (fun x => f (r + x))%R pf'
                                      match eq_sym (R_plus_minus r t) in _ = t
                                            return continue (f t)
                                      with
                                      | eq_refl => s
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

  Inductive skips_to : trace -> trace -> Prop :=
  | ST_Now : forall s, skips_to s s
  | ST_AfterD : forall st st' s s',
      skips_to (@Trace st' s) s' ->
      skips_to (@Trace st (@Discr st st' s)) s'
  | ST_AfterC : forall st t f pf0 pf s s',
      skips_to (@Trace _ s) s' ->
      skips_to (@Trace st (@Cont _ t pf0 f pf s)) s'
  | ST_WithinC : forall st r t f s pf0 pf pf',
      forall pf_range : (0 <= r < t)%R,
      skips_to (@Trace st (@Cont st t pf0 f pf s))
               (@Trace (f r) (@Cont _ (t - r) (R_minus_lt pf0 (proj2 pf_range)) (fun x => f (r + x))%R pf'
                                    match eq_sym (R_plus_minus r t) in _ = t
                                          return continue (f t)
                                    with
                                    | eq_refl => s
                                    end)).


  Inductive Step :=
  | DiscreteTo : ST -> Step
  | ContinuousBy : R -> (R -> ST) -> Step.

  Definition firstStep (s : trace)
  : Step :=
    match traceK s with
    | Discr x _ => DiscreteTo x
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
    red. induction 1; intros; eauto using ST_AfterD, ST_AfterC.
  Admitted.

  Global Instance Reflexive_skips_to : Reflexive skips_to.
  Proof.
    red. intros. constructor.
  Qed.

End with_state.

Arguments after_time {ST} _ _ _ _.
Arguments skips_to {ST} _ _.
Arguments hd {ST} _.
Arguments tl {ST} _.
Arguments firstStep {ST} _.
Arguments Transitive_skips_to {ST} _ _ _ _ _.
Arguments Reflexive_skips_to {ST} _.




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
