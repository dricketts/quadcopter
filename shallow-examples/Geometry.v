Require Import Coq.Vectors.Vector.
Require Import Coq.Reals.Rdefinitions.

(* Some vector arithmetic definitions. *)

Definition Rvec : nat -> Type := Vector.t R.

Definition v_scale {n} (r : R) (x : Rvec n) :=
  map (Rmult r) x.

Notation "r [*] x" := (v_scale r x) (at level 49) : vector_scope.

Definition v_add {n} (x y : Rvec n) :=
  map2 Rplus x y.

Notation "x [+] y" := (v_add x y) (at level 50) : vector_scope.
Notation "x [-] y" := (v_add x (v_scale (-1)%R y))
                        (at level 50) : vector_scope.

Definition v_dot_prod {n} (x y : Rvec n) :=
  fold_left Rplus R0 (map2 Rmult x y).

Notation "x [.] y" := (v_dot_prod x y) (at level 50)
                      : vector_scope.

(* Some geometry definitions. *)

Local Open Scope vector_scope.
Local Open Scope R_scope.

Record EndPoints n : Type :=
{ x : Rvec n;
  y : Rvec n;
  WF : x <> y }.

Arguments x {_} _.
Arguments y {_} _.
Arguments WF {_} _ _.

Require Import Ensembles.
Require Import Finite_sets.

(* A set of vectors. *)
Definition VecEnsemble n : Type := Ensemble (Rvec n).

(* We give vector definitions of lines, rays, and line segments. *)

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
    WF_b : forall (i : Fin.t (S m)),
        nth b (Fin.L_R (S O) i) <> nth b (Fin.FS i) }.

Arguments b {_ _} _.
Arguments WF_b {_ _} _ _ _.

(* A polygon in n dimensions with m vertices. *)
Definition Polygon {n m}
           (boundary : Boundary n m) : VecEnsemble n :=
  fun p => exists (i : Fin.t (S m)) r,
      0 <= r <= 1 /\
      LineSegment
        {| x := nth boundary.(b) (Fin.L_R (S O) i);
           y := nth boundary.(b) (Fin.FS i);
           WF := boundary.(WF_b) i |} p.

(* To specify whether a point is inside a polygon, we need
   a ray originating from that point. The following constructs
   such a ray. *)
Require Import Psatz.
Definition A_Ray {n} (p : Rvec (S n)) : EndPoints (S n).
Proof.
  refine (
      {| x := p;
         y := p [+] (Vector.const 1 (S n));
         WF := _ |} ).
  apply caseS with (v:=p). intros. intro. inversion H. psatzl R.
Qed.

(* A point is inside a polygon if a ray originating at the point
   intersects the polygon an even number of times. *)
Definition InsidePolygon {n m}
           (poly : Boundary (S n) m) (p : Rvec (S n)) : Prop :=
    exists n,
      Nat.Even n /\
      cardinal _ (Intersection _ (Polygon poly) (Ray (A_Ray p)))
               n.
