Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeTactics.Tactics.

Section indexed.
  Context {L : Type}
          {ILO : ILogicOps L}
          {IL : ILogic L}.

  (* Destruct *)
  Theorem destruct_top
  : forall A B C D : L,
      A |-- B -->> C -->> D ->
      A |-- B //\\ C -->> D.
  Proof. intros. rewrite H. charge_tauto. Qed.

  (* Split *)
  Theorem split_top
  : forall A B C D : L,
      A |-- B -->> D ->
      A |-- C -->> D ->
      A |-- B \\// C -->> D.
  Proof.
    intros. charge_intros.
    charge_cases.
    - charge_apply H; charge_tauto.
    - charge_apply H0; charge_tauto.
  Qed.

  (* Move *)
  Theorem move_top
  : forall A B C D : L,
      A //\\ C |-- B -->> D ->
      (A //\\ B) //\\ C |-- D.
  Proof.
    intros. charge_apply H.
    charge_tauto.
  Qed.

  (* Copy *)
  Theorem copy_top
  : forall A B C : L,
      A |-- B -->> B -->> C ->
      A |-- B -->> C.
  Proof.
    intros. rewrite H. charge_tauto.
  Qed.

  (* Copy *)
  Theorem clear_top
  : forall A B C : L,
      A |-- C ->
      A |-- B -->> C.
  Proof.
    intros. rewrite H. charge_tauto.
  Qed.

  Theorem skip_top : forall A B C D : L,
      (A //\\ B) //\\ C |-- D ->
      A //\\ C |-- B -->> D.
  Proof.
    intros. charge_intros. charge_apply H.
    charge_tauto.
  Qed.

  Lemma apply_ctx : forall A B C : L,
      C |-- A ->
      C //\\ (A -->> B) |-- B.
  Proof.
    intros. rewrite H. charge_tauto.
  Qed.

  Lemma apply_ctx' : forall A B C D : L,
      C //\\ B |-- D ->
      C |-- A ->
      C //\\ (A -->> B) |-- D.
  Proof.
    intros. charge_apply H. rewrite <- H0 at 1.
    charge_tauto.
  Qed.
End indexed.


Ltac destruct_n n :=
  match n with
  | 0 => apply destruct_top
  | S ?n => charge_intro; destruct_n n ; charge_revert
  end.

Ltac split_n n :=
  match n with
  | 0 => apply split_top
  | S ?n => charge_intro; split_n n; charge_revert
  end.

Ltac move_n n :=
  let rec move_n n :=
      match n with
      | 0 => apply limplAdj
      | S ?n => apply limplAdj ; move_n n ; apply move_top
      end
  in
  move_n n ; charge_revert.

Ltac copy_n n :=
  match n with
  | 0 => apply copy_top
  | S ?n => charge_intro ; copy_n n ; charge_revert
  end.

Ltac clear_n n :=
  match n with
  | 0 => apply clear_top
  | S ?n => charge_intro ; copy_n n ; charge_revert
  end.

Ltac apply_n n :=
  move_n n ; apply limplAdj ;
  let rec try_apply k :=
      first [ apply apply_ctx ; k
            | apply apply_ctx'; [ try_apply k | k ] ]
  in
  let rec try_each k :=
      first [ try_apply k
            | apply skip_top ;
              let k' := (charge_revert; k) in
              try_each k' ]
  in
  try_each idtac.

Section demo.
  Context {L : Type}
          {ILO : ILogicOps L}
          {IL : ILogic L}.

  Goal forall D E F G : L,
      |-- (D -->> F) -->> E //\\ (F \\// D) -->> (E -->> F -->> G) -->> G.
  Proof. intros.
         destruct_n 1.
         split_n 2.
         { apply_n 3. charge_tauto. }
         { charge_tauto. }
  Qed.
End demo.