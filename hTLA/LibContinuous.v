Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.RIneq.
Require Import ExtLib.Structures.Applicative.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import hTLA.DiscreteLogic.

(* A library of useful TLA formulas, built
   from TLA primitives. *)

Class AutoLift (F : Type -> Type) (T U : Type) : Type :=
{ autolift : F T -> U }.

Instance AutoLift_id {F T} : AutoLift F T (F T) | 100 :=
{ autolift := fun x => x }.

Instance AutoLift_arrow {F} {T U V} (C : AutoLift F U V) {Ap : Applicative F}
: AutoLift F (T -> U) (F T -> V) | 10 :=
{ autolift := fun x y => autolift (ap x y) }.

Arguments autolift {_ _ _ _} _.


Section parametric.
  Variable tlaState : Type.

  (* Action formula expressing that all variables
   in xs are unchanged. *)

  Instance EmbedOp_ActionVal_ActionProp : EmbedOp (ActionVal tlaState Prop) (ActionProp tlaState) :=
    { embed := fun P => P }.
  Instance EmbedOp_DActionVal_DActionProp : EmbedOp (DActionVal tlaState Prop) (DActionProp tlaState) :=
    { embed := fun P => P }.

  (** These two definitions are the same! **)
  Definition Unchanged (xs: list { T : Type & Var tlaState T}) : DActionProp tlaState :=
    Forall p, embed (List.In p xs) -->>
              embed ( (autolift (pure eq)) (pre (projT2 p)) (post (projT2 p)) ).

  Fixpoint VarsAgree (xs:list { T : Type & Var tlaState T }) : tlaState -> StateProp tlaState :=
    match xs with
    | nil => fun _ _ => True
    | cons (existT _ x) xs => fun st st' =>
                                (x st = x st') /\ (VarsAgree xs st st')
    end.

  (* A type representing a differential equation.
   (DiffEqC x t) represents (x' = t). *)
  Record DiffEq := DiffEqC
  { de_lhs : StateVal tlaState R
  ; de_op : R -> R -> Prop
  ; de_rhs : StateVal tlaState R }.

  Section bounded.

    Variable t : R.

    (** Under all observation functions in [obs], [f'] is the derivative of [f']
     **)
    Definition deriv_state_range (obs : list (Var tlaState R))
               (f f' : R -> tlaState)
      : Prop :=
      exists is_derivable : forall o, List.In o obs ->
                                      forall t', (0 <= t' <= t)%R ->
                                                 derivable_pt (fun t => o (f t)) t',
        (forall o (pf_In_obs : List.In o obs) t' (pf_t'_range : (0 <= t' <= t)%R),
            o (f' t') = derive_pt (fun t => o (f t)) t'
                                  (@is_derivable _ pf_In_obs _ pf_t'_range)).

    (* Expresses the property that a differentiable formula
     * is a solution to a list of differential equations
     * in the range [0] to [t]. *)
    Definition solves_diffeqs_range (f : R -> tlaState)
               (diffeqs : list DiffEq)
               (is_derivable : forall x, List.In x diffeqs -> forall t', (0 <= t' <= t)%R -> derivable_pt (fun t => x.(de_lhs) (f t)) t') :=
      forall x d o (pf : List.In (DiffEqC x o d) diffeqs),
      forall z (pfr : (0 <= z <= t)%R),
        o (derive_pt (fun t => x (f t)) z (@is_derivable (DiffEqC x o d) pf z pfr))
          (d (f z)).

    (* Prop expressing that f is a solution to diffeqs in
     * [0,t]. *)
    Definition is_solution_range (f : R -> tlaState) (diffeqs : list DiffEq) :=
      exists is_derivable,
        (* f is a solution to diffeqs *)
        solves_diffeqs_range f diffeqs is_derivable.

  End bounded.

  (* Action formula expressing that a transition
   * is consistent with the system of differential
   * equations represented by cp. *)
  Definition Continuous_range (cp:list DiffEq) (P : StateProp tlaState)
    : DActionProp tlaState :=
    let xs := List.map (fun x => @existT _ (Var tlaState) R x.(de_lhs)) cp in
    Exists r : R,
    Exists f : R -> tlaState,
               (embed (r > 0)%R)
          //\\ (embed (forall t, (0 <= t <= r)%R -> P (f t)))
          //\\ (embed (is_solution_range r f cp))
          (** It is admissable that we start here **)
          //\\ (embed (pre  (eq (f 0%R))))
          //\\ (embed (post (eq (f r)))).

  Section unbounded.

    (** Under all observation functions in [obs], [f'] is the derivative of [f']
     **)
    Definition deriv_state (obs : list (Var tlaState R))
               (f f' : R -> tlaState)
      : Prop :=
      exists is_derivable : forall o, List.In o obs ->
                                      derivable (fun t => o (f t)),
        (forall o (pf_In_obs : List.In o obs) t',
            o (f' t') = derive (fun t => o (f t))
                               (@is_derivable _ pf_In_obs) t').

    (* Expresses the property that a differentiable formula
     * is a solution to a list of differential equations
     * in the range [0] to [t]. *)
    Definition solves_diffeqs (f : R -> tlaState)
               (diffeqs : list DiffEq)
               (is_derivable : forall x, List.In x diffeqs ->
                                         derivable (fun t => x.(de_lhs) (f t))) :=
      forall x d o (pf : List.In (DiffEqC x o d) diffeqs),
      forall z,
        o (derive (fun t => x (f t)) (@is_derivable (DiffEqC x o d) pf) z)
          (d (f z)).

    (* Prop expressing that f is a solution to diffeqs in
     * [0,t]. *)
    Definition is_solution (f : R -> tlaState) (diffeqs : list DiffEq) :=
      exists is_derivable,
        (* f is a solution to diffeqs *)
        solves_diffeqs f diffeqs is_derivable.

  End unbounded.

  (* Action formula expressing that a transition
   * is consistent with the system of differential
   * equations represented by cp. *)
  Definition Continuous (cp:list DiffEq) (P : StateProp tlaState)
  : DActionProp tlaState :=
    let xs := List.map (fun x => @existT _ (Var tlaState) R x.(de_lhs)) cp in
    Exists r : R,
    Exists f : R -> tlaState,
               (embed (r > 0)%R)
          //\\ (embed (forall t, P (f t)))
          //\\ (embed (is_solution f cp))
          (** It is admissable that we start here **)
          //\\ (embed (pre  (eq (f 0%R))))
          //\\ (embed (post (eq (f r)))).


End parametric.

Arguments Continuous {_} _ _ _ _.
Arguments is_solution {_} _ _.

Arguments Continuous_range {_} _ _ _ _.
Arguments is_solution_range {_} _ _ _.


(* Some notation *)
(* In a module to avoid conflicts. *)
Module LibNotations.
Notation "x ' ::= t" := (@DiffEqC _ _ x (@eq R) t) (at level 60) : HP_scope.
Notation "x ' ::< t" := (@DiffEqC _ _ x Rlt t) (at level 60) : HP_scope.
Notation "x ' ::> t" := (@DiffEqC _ _ x Rgt t) (at level 60) : HP_scope.
Notation "x ' ::<= t" := (@DiffEqC _ _ x Rle t) (at level 60) : HP_scope.
Notation "x ' ::>= t" := (@DiffEqC _ _ x Rge t) (at level 60) : HP_scope.
Notation "[ x1 , .. , xn ]" := (cons x1 .. (cons xn nil) .. )
    (at level 60) : HP_scope.
End LibNotations.
