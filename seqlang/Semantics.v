Require Import SeqLang.Syntax.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.RIneq.
Require Import String.

(************************************************)
(* The semantics of differential dynamic logic. *)
(************************************************)
Section Semantics.
  Open Scope R_scope.

  Variable Var : Type.
  Definition Term := Term Var.
  Definition HybridProg := HybridProg Var.
  Definition Formula := Formula Var.
  Definition state := state Var.
  Definition Cond := Cond Var.
  Definition Skip := Skip Var.
  Definition Assign := Assign Var.
  Definition Continuous := Continuous Var.
  Definition Seq := Seq Var.
  Definition Ite := Ite Var.
  Definition Rep := Rep Var.

  (* Semantics of real valued terms *)
  Fixpoint eval_term (t:Term) (st:state) : R :=
    match t with
      | VarT x => st x
      | RealT r => r
      | PlusT t1 t2 => (eval_term t1 st) + (eval_term t2 st)
      | MinusT t1 t2 => (eval_term t1 st) - (eval_term t2 st)
      | MultT t1 t2 => (eval_term t1 st) * (eval_term t2 st)
    end.


  (* Semantics of comparison operators *)
  Definition eval_comp (t1 t2:Term) (st:state) (op:CompOp) :
    Prop :=
    let (e1, e2) := (eval_term t1 st, eval_term t2 st) in
    let op := match op with
                | Gt => Rgt
                | Ge => Rge
                | Lt => Rlt
                | Le => Rle
                | Eq => eq
              end in
    op e1 e2.

  (* Semantics of conditionals *)
  Fixpoint eval_cond (c:Cond) (st:state) : Prop :=
    match c with
      | CompC t1 t2 op => eval_comp t1 t2 st op
      | AndC c1 c2 => eval_cond c1 st /\ eval_cond c2 st
      | OrC c1 c2 => eval_cond c1 st \/ eval_cond c2 st
      | NegC c1 => ~eval_cond c1 st
    end.

  (* Expresses the property the a differentiable formula
   is a solution to a list of differential equations
   in the range 0 to r. *)
  Definition solves_diffeqs (f : R -> state)
             (diffeqs : list (Var * Term)) (r : R)
             (is_derivable : forall x, derivable (fun t => f t x)) :=
    forall x d,
      List.In (x, d) diffeqs ->
      forall z, R0 <= z <= r ->
                derive (fun t => f t x) (is_derivable x) z =
                eval_term d (f z).

  (* Expresses the property that f, in the range 0 to r,
   does not change any variables without differential
   equations in diffeqs. *)
  Definition vars_unchanged (f : R -> state)
             (diffeqs : list (Var * Term)) (r : R)
             (is_derivable : forall x, derivable (fun t => f t x)) :=
    forall x,
      ~(exists d, List.In (x, d) diffeqs) ->
      forall z, R0 <= z <= r ->
                derive (fun t => f t x) (is_derivable x) z = R0.
  (* Is this equivalent to the following? I think not. *)
  (*        f z x = s x.*)

  (* Prop expressing that f is a solution to diffeqs in
   [0,r]. *)
  Definition is_solution (f : R -> state)
             (diffeqs : list (Var * Term)) (r : R) :=
    exists is_derivable,
      (* (2) f is a solution to diffeqs *)
      solves_diffeqs f diffeqs r is_derivable /\
      (* (3) f does not change other variables *)
      vars_unchanged f diffeqs r is_derivable.

  (* Updates state s by setting x to the value of t. *)
  Definition updated_st (s:state) (x:Var) (t:Term) (s' : state)
  : Prop :=
    s' x = eval_term t s /\
    (forall y, x <> y -> s x = s' x).

  Inductive Event : Type :=
  | Finish : state -> Event
  | Evolve : (time -> state) -> time -> Event -> Event.

  Fixpoint Event_app (e1 e2 : Event) : Event :=
    match e1 with
      | Finish _ => e2
      | Evolve f t e1' => Evolve f t (Event_app e1' e2)
    end.

  Fixpoint Event_end (e : Event) : state :=
    match e with
      | Finish st => st
      | Evolve _ _ e => Event_end e
    end.

  Inductive Behavior :
    HybridProg -> state -> Event -> Prop :=
  | C_Skip : forall s, Behavior Skip s (Finish s)
  | C_Assign : forall x t st st',
                 updated_st st x t st' ->
                 Behavior (Assign x t) st (Finish st')
  (* Semantics of continuous evolution. The system can
   transition continuously from state s1 to state s2
   according to differential equations diffeqs if
   there exists some function (f : R -> state) which
     1) is equal to s1 at time 0 and equal to s2 at
        some later time
     2) is a solution to diffeqs
     3) only changes values of variables whose
        derivative is specified in diffeqs
  The system evolves for at most b time units.
   *)
  | C_Cont : forall cp f b r st,
               is_solution f cp r ->
               f R0 = st ->
               Behavior (Continuous cp b) st
                        (Evolve f b (Finish (f b)))

  (* Semantics of sequencing. Nothing special here. *)
  | C_Seq : forall p1 p2 l1 l2 st,
              Behavior p1 st l1 ->
              Behavior p2 (Event_end l1) l2 ->
              Behavior (Seq p1 p2) st (Event_app l1 l2)

  (* Branching semantics when first branch is taken. *)
  | C_IteTrue : forall c p1 p2 tr st,
                  eval_cond c st ->
                  Behavior p1 st tr ->
                  Behavior (Ite c p1 p2) st tr

  (* Branching semantics when second branch is taken. *)
  | C_IteFalse : forall c p1 p2 tr st,
                  ~eval_cond c st ->
                  Behavior p2 st tr ->
                  Behavior (Ite c p1 p2) st tr

  (* Repetition semantics with 0 repetitions. *)
  | Rep0 : forall p s l,
             Behavior (Rep p) s l

  (* Repetition semantics with at least 1 repetition. *)
  | RepN : forall p s tr tr',
             Behavior p s tr ->
             Behavior (Rep p) (Event_end tr) tr' ->
             Behavior (Rep p) s (Event_app tr tr').

  (** None -> x < y
   ** Some t -> x = y + t
   **)
  Axiom time_left : forall x y : time, option time.
  Axiom time_0 : time.
  Axiom add_time : time -> time -> time.

  Definition trace := time -> state.

  (** This extends the final state forever.
   ** This constructs a complete trace by compressing consecutive
   ** instantaneous changes into a single instantaneous change.
   **)
  Fixpoint toFunction (e : Event) : trace :=
    match e with
      | Finish s => fun _ => s
      | Evolve f t e' =>
        let nxt := toFunction e' in
        fun t' => match time_left t' t with
                    | None => f t'
                    | Some rem => nxt rem
                  end
    end.

  (* Semantics of formulas. A formula valid with respect
     to a given behavior. When we state correctness
     properties of programs, we will quantify over the
     behavior.  *)
  Fixpoint eval_formula (f:Formula) (tr:trace) : Prop :=
    match f with
      | CompF t1 t2 op => eval_comp t1 t2 (tr time_0) op
      | AndF f1 f2 => eval_formula f1 tr /\ eval_formula f2 tr
      | OrF f1 f2 => eval_formula f1 tr \/ eval_formula f2 tr
      | Imp f1 f2 => eval_formula f1 tr -> eval_formula f2 tr
      | Prog p => exists e, Behavior p (tr time_0) e /\
                            toFunction e = tr
      | Always f' =>
        forall t, eval_formula f' (fun r => tr (add_time r t))
      | Eventually f' =>
        exists t, eval_formula f' (fun r => tr (add_time r t))
    end.

  Close Scope R_scope.

End Semantics.

(* Adding some notation for evaluation of formulas. *)
Notation "|- f" := (forall tr, eval_formula string f tr)
                     (at level 100) : HP_scope.