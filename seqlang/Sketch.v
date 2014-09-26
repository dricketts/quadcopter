Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.RIneq.

(************************************************)
(* The semantics of differential dynamic logic. *)
(************************************************)
Open Scope R_scope.


Section with_stuff.
  Variable Var : Type.

  Definition state := Var -> R.

  Definition time := nonnegreal.

  Inductive Term :=
  | VarT : Var -> Term
  | RealT : R -> Term
  | PlusT : Term -> Term -> Term
  | MinusT : Term -> Term -> Term
  | MultT : Term -> Term -> Term.

  Inductive CompOp :=
  | Gt : CompOp
  | Ge : CompOp
  | Lt : CompOp
  | Le : CompOp
  | Eq : CompOp.

  (* Conditionals *)
  Inductive Cond :=
  | CompC : Term -> Term -> CompOp -> Cond
  | AndC : Cond -> Cond -> Cond
  | OrC : Cond -> Cond -> Cond
  | NegC : Cond -> Cond.

  Definition DiffEq := (Var * Term)%type.

  (* Programs containing discrete and continuous parts. *)
  Inductive HybridProg :=
  (* No-op *)
  | Skip : HybridProg
  (* A discrete progam constructor for assignment *)
  | Assign : Var -> Term -> HybridProg
  (* A continuous program constructor that takes a list
   of differential equations and a time bound. Each
   differential equation is a pair of a variable and
   a real valued term. For example, if variables are
   strings, then the system of differential equations

    x' = 4
    y' = x

   would be represented as

    DiffEq [ ("x", RealT 4); ("y", VarT "x") ]

   The time bound specifies the maximum time for which
   the system evolves according to the differential
   equations.
   *)
  | Continuous : list DiffEq -> time -> HybridProg
  (* Sequencing programs *)
  | Seq : HybridProg -> HybridProg -> HybridProg
  (* Branching *)
  | Ite : Cond -> HybridProg -> HybridProg -> HybridProg
  (* Non-deterministic repetition *)
  | Rep : HybridProg -> HybridProg.

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
  Definition updated_st (s:state) (x:Var) (t:Term) (s' : state) : Prop :=
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
               Behavior (Continuous cp b) st (Evolve f b (Finish (f b)))

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

  (** Sanity Check **)
  Goal forall s,
       exists tr, Behavior (Seq Skip Skip) s tr
                  /\ forall t, toFunction tr t = s.
  Proof.
    intros.
    eexists. split.
    - repeat econstructor.
    - simpl. reflexivity.
  Qed.

  (** The Logic **)
  Definition sprop := state -> Prop.
  Definition tprop := trace -> Prop.

  Axiom time_add : time -> time -> time.
  Axiom T0 : time.

  Definition Always (P : tprop) : tprop :=
    fun tr => forall r, P (fun x => tr (time_add x r)).

  Definition Eventually (P : tprop) : tprop :=
    fun tr => exists r, P (fun x => tr (time_add x r)).

  Definition Now (P : sprop) : tprop :=
    fun tr => P (tr T0).

  (** Note:
   ** The difficulty here comes from the need to give a
   ** reasoning principle for sequences of instantaneous transitions.
   ** - We could solve this by writing propositions over [Event]s,
   **   rather than the streams that they induce.
   **   - This has odd semantics because some things are true about [Event]s
   **     but not about the induced trace, e.g.
   **       Eventually (Now (fun st => st "x" = 0))
   **     is provable on the [Event] for:
   **       (x = 0) ; (x = 1)
   **     but it is not true for the trace that it induces.
   ** - Something else to note, however, is that as long as discrete events
   **   do not modify "continuous" variables, all of the temporal properties
   **   that mention only continuous variables are true on an [Event] if and
   **   only if it is true on the induced [trace].
   **)


  (** Proof Rules **)



End with_stuff.