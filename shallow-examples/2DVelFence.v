Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.micromega.Psatz.
Require Import Coq.Reals.RIneq.
Require Import Coq.Sets.Ensembles.
Require Import ExtLib.Structures.Applicative.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILEmbed.
Require Import ChargeCore.Tactics.Tactics.
Require Import ChargeCore.Tactics.Lemmas.
Require Import SLogic.Logic.
Require Import SLogic.Instances.
Require Import SLogic.BasicProofRules.
Require Import SLogic.ContinuousNormed.
Require Import SLogic.BoundingFunctions.
Require Import SLogic.Lifting.
Require Import SLogic.LTLNotation.
Require Import SLogic.Tactics.
Require Import SLogic.Util.
Require Import SLogic.Arithmetic.
Require Import SExamples.Geometry.

Local Open Scope R_scope.
Local Open Scope LTL_scope.
Local Open Scope vector_scope.

Set SMT Solver "z3".

Section Fence.

  (* Working in 2 dimensions for the moment. *)
  Definition dim : nat := 2.

  (* Boundary of the fence. *)
  Variable nverts : nat.
  Variable boundary : Boundary dim nverts.

  (* Gives the distance required to come to a stop in one
     dimension, as a function of the current speed. *)
  Variable stop_dist : R -> R.
  Hypothesis stop_dist_non_zero :
    forall a, a <> 0 -> stop_dist a <> 0.

  (* Gives the maximum speed such that the vehicle
     can come to a stop within the input distance. *)
  Variable max_speed : R -> R.

  (* Position of the system *)
  Definition state : Type := Rvec dim.
  (* Projections of x and y components of state. *)
  Definition px : StateVal state R :=
    fun p => Vector.nth p Fin.F1.
  Definition py : StateVal state R :=
    fun p => Vector.nth p (Fin.FS Fin.F1).

  (* The main safety property, namely that we stay
     inside the fence. *)
  Definition Inside : StateProp state :=
    InsidePolygon boundary.

  (* Line segment from a position to the stopping point,
     given the current velocity. *)
  Definition StoppingSegment (v : Rvec dim)
    : StateVal state (VecEnsemble dim).
  Proof.
    refine (
        fun p =>
          let l := v_norm v in
          if Req_EM_T 0 l
          then Point p
          else LineSegment
                 {| x := p;
                    y := p [+] (stop_dist l) [*] (normalize v);
                    distinct := _ |}).
    apply v_add_nonzero_neq. apply non_zero_scale.
    { auto. }
    { apply normalize_non_zero; auto. }
  Defined.

  (* Defines what it means for the velocity to be safe
     with respect to a single edge. *)
  Definition SafeStoppingSegmentEdge
             (e : VecEnsemble dim) (v : Rvec dim)
    : StateProp state :=
    fun p => Disjoint _ (StoppingSegment v p) e.

  (* Defines what it means for the velocity to be safe with
     respect to all edges. *)
  Definition SafeStoppingSegment (v : Rvec dim)
    : StateProp state :=
    fun p =>
      ForallEdges boundary
                  (fun e => SafeStoppingSegmentEdge e v p).

  Definition SafeVelocityEdge
             (e : VecEnsemble dim) (v : Rvec dim)
    : StateProp state :=
    fun p =>
      forall q, e q -> v [.] (q [-] p) <=
                       max_speed (v_norm (q [-] p)).

  Definition SafeVelocity (v : Rvec dim)
    : StateProp state :=
    fun p =>
      ForallEdges boundary (fun e => SafeVelocityEdge e v p).

  (* Specifies a closest point in a set of points to the
     current state. *)
  Definition ClosestPoint (e : VecEnsemble dim)
    : StateVal state (VecEnsemble dim) :=
    fun p q => e q /\
               forall l, e l -> v_norm (q [-] p) <=
                                v_norm (l [-] p).

  (* Gives a set of safe velocities with respect to the
     given edge, as a function of the current state. *)
  Definition EdgeConstraint (e : VecEnsemble dim)
    : StateVal state (VecEnsemble dim) :=
    fun p v => forall q, ClosestPoint e p q ->
                         v [.] (q [-] p) <=
                         max_speed (v_norm (q [-] p)).

  (* Gives a set of safe velocities with respect to the
     boundary, as a function of the current state. *)
  Definition BoundaryConstraint
    : StateVal state (VecEnsemble dim) :=
    fun p v =>
      ForallEdges boundary (fun e => EdgeConstraint e p v).

  Require Import Coquelicot.Coquelicot.
  Definition Normed_class_of_state :
    NormedModule.class_of R_AbsRing state.
  Admitted.

  Canonical state_Normed :=
    NormedModule.Pack _ _ Normed_class_of_state state.

  Definition Next : ActionProp state :=
    ContEvolve state_Normed BoundaryConstraint.

  Definition Spec : TraceProp state :=
    (starts (!Inside)) //\\ [](starts Next).

End Fence.