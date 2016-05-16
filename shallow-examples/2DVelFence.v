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
Require Import SLogic.Continuous.
Require Import SLogic.ContinuousInstances.
Require Import SLogic.BoundingFunctions.
Require Import SLogic.RobustnessISS.
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

  (* Position of the system *)
  Definition state : Type := Rvec dim.

  (* The main safety property, namely that we stay
     inside the fence. *)
  Definition Inside : StateProp state := InsidePolygon boundary.

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
  Definition SafeVelocityEdge (e : VecEnsemble dim) (v : Rvec dim)
    : StateProp state :=
    fun p => Disjoint _ (StoppingSegment v p) e.

  (* Defines what it means for the velocity to be safe with
     respect to all edges. *)
  Definition SafeVelocity (v : Rvec dim) : StateProp state :=
    fun p =>
      ForallEdges boundary (fun e => SafeVelocityEdge e v p).

End Fence.