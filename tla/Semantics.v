Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rtrigo_def.
Require Import Coq.Reals.Ranalysis1.
Require Export TLA.Syntax.
Require Import TLA.Stream.
Require Export Charge.Logics.ILogic.
Require Import Coq.Reals.R_sqrt.
Require Import Coq.Reals.Ratan.


(* The semantics of our restricted TLA *)

(* A TLA behavior, called a trace *)
Definition flow := R -> state.
Definition trace := stream (state * flow).

(* Semantics of real valued terms *)
Fixpoint eval_term (t:Term) (s1 s2:state) : R :=
  (match t with
     | VarNowT x => s1 x
     | VarNextT x => s2 x
     | NatT n => Raxioms.INR n
     | RealT r => r
     | PlusT t1 t2 =>
       (eval_term t1 s1 s2) + (eval_term t2 s1 s2)
     | MinusT t1 t2 =>
       (eval_term t1 s1 s2) - (eval_term t2 s1 s2)
     | MultT t1 t2 =>
       (eval_term t1 s1 s2) * (eval_term t2 s1 s2)
     | InvT t =>
       / (eval_term t s1 s2)
     | CosT t => cos (eval_term t s1 s2)
     | SinT t => sin (eval_term t s1 s2)
     | SqrtT t => sqrt (eval_term t s1 s2)
     | ArctanT t => atan (eval_term t s1 s2)
   end)%R.

(* Semantics of comparison operators *)
Definition eval_comp (t1 t2:Term) (op:CompOp) (s1 s2:state) :
  Prop :=
  match op with
  | Gt => Rgt
  | Ge => Rge
  | Lt => Rlt
  | Le => Rle
  | Eq => eq
  end (eval_term t1 s1 s2) (eval_term t2 s1 s2).

Fixpoint subst_state (s : list (Var * Term)) : state -> state :=
  match s with
  | nil => fun x => x
  | (v,e) :: s =>
    fun st v' => if String.string_dec v' v then
                   eval_term e st st
                 else
                   subst_state s st v'
  end.

Definition subst_flow (s : list (Var * Term)) (f : flow) : flow :=
  fun t => subst_state s (f t).

Definition subst (s : list (Var * Term))
           (stf : state * flow)
  : state * flow :=
  (subst_state s (fst stf),
   subst_flow s (snd stf)).

(* Expresses the property that a differentiable formula
   is a solution to a list of differential equations
   in the range 0 to r. *)
Definition solves_diffeqs (eval : Formula -> trace -> Prop)
           (f : R -> state) (cp : state->Formula) (r : R)
           (is_derivable : forall x, derivable (fun t => f t x)) :=
    forall z, (R0 <= z <= r)%R ->
              eval
                (cp (fun x => derive (fun t => f t x)
                                     (is_derivable x) z))
                (Stream.forever (f z, fun _ _ => R0)).

(* Prop expressing that f is a solution to diffeqs in
   [0,r]. *)
Definition is_solution (eval : Formula -> trace -> Prop)
           (f : R -> state) (cp:state->Formula) (r : R) :=
  exists is_derivable,
    (* f is a solution to diffeqs *)
    solves_diffeqs eval f cp r is_derivable.

(* Semantics of temporal formulas *)
Fixpoint eval_formula (F:Formula) (tr:trace) :=
  match F with
    | TRUE => True
    | FALSE => False
    | Comp t1 t2 op =>
      eval_comp t1 t2 op (fst (hd tr)) (fst (hd (tl tr)))
    | And F1 F2 => eval_formula F1 tr /\
                   eval_formula F2 tr
    | Or F1 F2 => eval_formula F1 tr \/
                  eval_formula F2 tr
    | Imp F1 F2 => eval_formula F1 tr ->
                   eval_formula F2 tr
    | PropF P => P
    | Continuous w =>
      match hd tr with
      | (st1, f) =>
        exists r,
        (r > 0)%R /\
        f 0%R = st1 /\
        f r = fst (hd (tl tr)) /\
        is_solution eval_formula f w r
      (*        exists is_derivable,
        forall z, (0 <= z <= r)%R ->
                  eval_formula
                    (w (fun x => derive (fun t => f t x)
                                        (is_derivable x) z))
                    (Stream.forever ((f z),
                                     {| time := R0;
                                        fl := fun _ _ => R0 |}))*)
      end
    | Syntax.Exists _ F => exists x, eval_formula (F x) tr
    | Syntax.Forall _ F => forall x, eval_formula (F x) tr
    | Enabled F => exists tr', eval_formula F (Cons (hd tr) tr')
    | Always F => forall n, eval_formula F (nth_suf n tr)
    | Eventually F => exists n, eval_formula F (nth_suf n tr)
    | Embed P =>
      P (fst (hd tr)) (fst (hd (tl tr)))
    | Rename s F =>
      eval_formula F (stream_map (subst s) tr)
  end.

(*
Notation "|- F" := (forall tr, eval_formula F tr)
                     (at level 100) : HP_scope.
*)

(** Formulas are Logics *)
Definition tlaEntails (P Q : Formula) : Prop :=
  forall tr, eval_formula P tr -> eval_formula Q tr.

Global Instance ILogicOps_Formula : ILogicOps Formula :=
{ lentails := tlaEntails
; ltrue    := TRUE
; lfalse   := FALSE
; land     := And
; lor      := Or
; limpl    := Imp
; lforall  := Syntax.Forall
; lexists  := Syntax.Exists
}.

Global Instance ILogic_Formula : ILogic Formula.
Proof.
  constructor;
  try solve [ cbv beta iota zeta delta - [ eval_formula ];
              simpl; intros; intuition eauto ].
  cbv beta iota zeta delta - [ eval_formula ];
              simpl; intros; intuition eauto.
  destruct H0. eauto.
Qed.