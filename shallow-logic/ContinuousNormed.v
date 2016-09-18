Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILEmbed.
Require Import SLogic.Logic.
Require Import SLogic.Instances.
Require Import Coquelicot.Coquelicot.

(* Definitions of continuous transitions. *)

Section Continuous.

  Variable state : NormedModule R_AbsRing.

  (* ContEvolve transitions take predicates over the state
     and its derivative - these predicates are represented
     by [ActionProp]s. By convention, the first argument is
     the state and the second is its derivative.
     ContEvolve returns predicates over pairs of states.
     Confusingly, these are also [ActionProp]s. *)
  Definition ContEvolve (dF : ActionProp state)
    : ActionProp state :=
    fun st st' =>
      exists (r : R) (F : R -> state),
        0 <= r /\ F 0 = st /\ F r = st' /\
        exists (D : R -> state),
          forall t : R, is_derive F t (D t) /\
                        0 <= t <= r -> dF (F t) (D t).

End Continuous.
