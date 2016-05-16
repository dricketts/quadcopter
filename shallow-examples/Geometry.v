Require Import Coq.Vectors.Vector.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rsqrt_def.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Psatz.

(* Some vector arithmetic definitions. *)

Definition Rvec : nat -> Type := Vector.t R.
Local Open Scope R_scope.
Local Open Scope vector_scope.

Definition v_zero n : Rvec n := Vector.const 0 n.

Definition v_scale {n} (r : R) (x : Rvec n) :=
  map (Rmult r) x.

Notation "r [*] x" := (v_scale r x) (at level 49) : vector_scope.
Notation "x [/] r" := (v_scale (Rinv r) x) (at level 49)
                      : vector_scope.

Definition v_add {n} (x y : Rvec n) :=
  map2 Rplus x y.

Notation "x [+] y" := (v_add x y) (at level 50) : vector_scope.
Notation "x [-] y" := (v_add x (v_scale (-1)%R y))
                        (at level 50) : vector_scope.

Definition v_dot_prod {n} (x y : Rvec n) :=
  fold_left Rplus R0 (map2 Rmult x y).

Notation "x [.] y" := (v_dot_prod x y) (at level 50)
                      : vector_scope.

Lemma x_v_dot_x_pos :
  forall n (x : Rvec n), 0 <= v_dot_prod x x.
Proof.
  intros. unfold v_dot_prod.
  rewrite fold_left_right_assoc_eq; [ | intros; psatzl R].
  induction x; simpl.
  { psatzl R. }
  { pose proof (Rle_0_sqr h). unfold Rsqr in *. psatzl R. }
Qed.

Definition v_norm_sq {n} (x : Rvec n) : nonnegreal :=
  {| nonneg := v_dot_prod x x;
     cond_nonneg := x_v_dot_x_pos _ _ |}.
Definition v_norm {n} (x : Rvec n) := Rsqrt (v_norm_sq x).

Definition normalize {n} (x : Rvec n) := x [/] (v_norm x).

(* Some useful facts and definitions about vectors. *)
Definition v_non_zero {n} (x : Rvec n) := x <> v_zero _.

Lemma v_add_nonzero_neq :
  forall n (x y : Rvec (S n)), v_non_zero y -> x <> x [+] y.
Proof.
Admitted.

Lemma v_const_nonzero :
  forall n a, a <> 0 -> Vector.const a (S n) <> v_zero (S n).
Proof.
  intros. simpl. intro. inversion H0. psatzl R.
Qed.

Lemma normalize_non_zero :
  forall n (x : Rvec n),
    0 <> v_norm x -> v_non_zero (normalize x).
Proof.
(*
  intros. destruct n.
  { revert H. eapply case0 with (v:=x). unfold v_norm, v_norm_sq.
    cbn. unfold Rsqrt. simpl.
    destruct (Rsqrt_exists 0 (x_v_dot_x_pos 0 (nil R))).
    intros. intro. apply H. unfold Rsqr in *. psatz R. }
  { einduction n,x using rectS.
    { assert (a <> 0).
      { unfold v_norm, v_norm_sq, Rsqrt in *. cbn in *.
        destruct (Rsqrt_exists (0 + a * a)).
        assert (x0 <> 0) by psatzl R. apply Rlt_0_sqr in H0.
        psatz R. }
      { unfold v_non_zero. cbn. intro. inversion H1.
        unfold v_norm, v_norm_sq, Rsqrt in H3. cbn in *.
        destruct (Rsqrt_exists (0 + a * a)). assert (x0 <> 0).
        { unfold Rsqr in *. intuition. } } } }*)
Admitted.

Lemma non_zero_scale :
  forall a n (x : Rvec n),
    a <> 0 -> v_non_zero x -> v_non_zero (a [*] x).
Admitted.

(* Some geometry definitions. *)

Record EndPoints n : Type :=
{ x : Rvec n;
  y : Rvec n;
  distinct : x <> y }.

Arguments x {_} _.
Arguments y {_} _.
Arguments distinct {_} _ _.

Require Import Ensembles.
Require Import Finite_sets.

(* A set of vectors. *)
Definition VecEnsemble n : Type := Ensemble (Rvec n).

(* We give vector definitions of points, lines, rays,
   and line segments. *)

Definition Point {n} (x : Rvec n) : VecEnsemble n :=
  fun p => x = p.

Definition Line {n} (a : EndPoints n) : VecEnsemble n :=
  fun p => exists r, p = a.(x) [+] r [*] (a.(y) [-] a.(x)).

Definition Ray {n} (a : EndPoints n) : VecEnsemble n :=
  fun p => exists r,
      0 <= r /\ p = a.(x) [+] r [*] (a.(y) [-] a.(x)).

Definition LineSegment {n} (a : EndPoints n) : VecEnsemble n :=
  fun p => exists r,
      0 <= r <= 1 /\ p = a.(x) [+] r [*] (a.(y) [-] a.(x)).

(* The boundary of a polygon in n-dimensions with m vertices.
   A boundary is well formed if no two adjacent vertices are
   equal. *)
Record Boundary (n m : nat) : Type :=
  { b : Vector.t (Rvec n) (S (S m));
    adj_distinct : forall (i : Fin.t (S m)),
        nth b (Fin.L_R (S O) i) <> nth b (Fin.FS i) }.

Arguments b {_ _} _.
Arguments adj_distinct {_ _} _ _ _.

Definition ith_Edge {n m}
           (boundary : Boundary n m) (i : Fin.t (S m))
  : VecEnsemble n :=
  LineSegment
        {| x := nth boundary.(b) (Fin.L_R (S O) i);
           y := nth boundary.(b) (Fin.FS i);
           distinct := boundary.(adj_distinct) i |}.

(* A polygon in n dimensions with m vertices. *)
Definition Polygon {n m}
           (boundary : Boundary n m) : VecEnsemble n :=
  fun p => exists (i : Fin.t (S m)) r,
      0 <= r <= 1 /\ ith_Edge boundary i p.

Definition ForallEdges {n m} (boundary : Boundary n m)
  (f : VecEnsemble n -> Prop) : Prop :=
  forall (i : Fin.t (S m)), f (ith_Edge boundary i).

(* To specify whether a point is inside a polygon, we need
   a ray originating from that point. The following constructs
   such a ray. *)
Definition A_Ray {n} (p : Rvec (S n)) : EndPoints (S n).
Proof.
  refine (
      {| x := p;
         y := p [+] (Vector.const 1 (S n));
         distinct := _ |} ).
  apply v_add_nonzero_neq. apply v_const_nonzero. psatzl R.
Qed.

(* A point is inside a polygon if a ray originating at the point
   intersects the polygon an even number of times. *)
Definition InsidePolygon {n m}
           (poly : Boundary (S n) m) (p : Rvec (S n)) : Prop :=
    exists n,
      Nat.Even n /\
      cardinal _ (Intersection _ (Polygon poly) (Ray (A_Ray p)))
               n.
