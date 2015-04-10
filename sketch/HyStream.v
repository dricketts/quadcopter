Require Coq.Lists.List.
Require Import Rdefinitions.

Section with_state.

  Variable ST : Type.

  Definition time : Type := (R * nat)%type.

  (* A behavior is an infinite stream of states.
   * In order for differential induction to make sense, you need the solution.
   *)
  CoInductive stream :=
  | Cont : forall (r : R) (f : R -> ST), stream -> stream
  | Discr : ST -> stream -> stream.

  Inductive after_time : R -> nat -> stream -> stream -> Prop :=
  | Now    : forall s, after_time 0 0 s s
  | WithinD : forall n st s s',
      after_time 0 n s s' ->
      after_time 0 (S n) (Discr st s) s'
  | AfterDC : forall r n st s s',
      (r > 0)%R ->
      after_time r n s s' ->
      after_time r n (Discr st s) s'
  | WithinC : forall n r t f s',
      (r > 0)%R ->
      (r < t)%R ->
      after_time r n (Cont t f s') (Cont (t - r) (fun x => f (r + x)) s')%R
  | AfterC : forall n r t f s' s'',
      (r > 0)%R ->
      (r >= t)%R ->
      after_time (r - t)%R n s' s'' ->
      after_time r n (Cont t f s') s''.

  Inductive skips_to : stream -> stream -> Prop :=
  | ST_Now : forall s, skips_to s s
  | ST_AfterD : forall st s s',
      skips_to s s' -> skips_to (Discr st s) s'
  | ST_AfterC : forall t f s s',
      skips_to s s' -> skips_to (Cont t f s) s'
  | ST__WithinC : forall r t f s,
      (0 <= r < t)%R ->
      skips_to (Cont t f s) (Cont (t - r) (fun x => f (r + x))%R s).

  (* The head of a stream *)
  Definition hd (s:stream) : ST :=
    match s with
    | Cont r f _ => f 0%R
    | Discr a _ => a
    end.

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

End with_state.

Arguments after_time {ST} _ _ _ _.
Arguments skips_to {ST} _ _.
Arguments hd {ST} _.
Arguments next_tl {ST} _.



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
