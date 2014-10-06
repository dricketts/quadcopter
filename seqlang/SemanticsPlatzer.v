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
             (diffeqs : list DiffEq) (r : R)
             (is_derivable : forall x, derivable (fun t => f t x)) :=
    forall x d,
      List.In (DiffEqC x d) diffeqs ->
      forall z, R0 <= z <= r ->
                derive (fun t => f t x) (is_derivable x) z =
                eval_term d (f z).

  (* Expresses the property that f, in the range 0 to r,
   does not change any variables without differential
   equations in diffeqs. *)
  Definition vars_unchanged (f : R -> state)
             (diffeqs : list DiffEq) (r : R)
             (is_derivable : forall x, derivable (fun t => f t x)) :=
    forall x,
      ~(exists d, List.In (DiffEqC x d) diffeqs) ->
      forall z, R0 <= z <= r ->
                derive (fun t => f t x) (is_derivable x) z = R0.
  (* Is this equivalent to the following? I think not. *)
  (*        f z x = s x.*)

  (* Prop expressing that f is a solution to diffeqs in
   [0,r]. *)
  Definition is_solution (f : R -> state)
             (diffeqs : list DiffEq) (r : R) :=
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

  Definition partial := ((time->state) * time)%type.

  Inductive trace :=
  | one : partial -> trace
  | next : partial -> trace -> trace.

  Fixpoint last (tr:trace) :=
    match tr with
      | one f => f
      | next _ tr' => last tr'
    end.

  Definition start (tr:trace) :=
    match tr with
      | one f => f
      | next f _ => f
    end.

  Fixpoint append (tr1 tr2:trace) :=
    match tr1 with
      | one f => next f tr2
      | next f tr1' => next f (append tr1' tr2)
    end.

  Definition time_0 : time :=
    mknonnegreal R0 (Rle_refl _).

  Definition st_fun (s:state) : partial :=
    (fun _ => s, time_0).

  Definition Now (tr:trace) :=
    fst (start tr) time_0.

  Definition connected (tr1 tr2:trace) :=
    let (f1, t1) := last tr1 in
    let (f2, _) := start tr2 in
    f1 t1 = f2 time_0.

  Inductive Behavior :
    HybridProg -> trace -> Prop :=
  | C_Skip : forall s, Behavior Skip (next (st_fun s) (one (st_fun s)))
  | C_Assign : forall x t st st',
                 updated_st st x t st' ->
                 Behavior (Assign x t)
                          (next (st_fun st) (one (st_fun st')))
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
  | C_Cont : forall cp f (b r:time),
               r <= b ->
               is_solution f cp r ->
               Behavior (Continuous cp b)
                        (one (fun (t:time) => f t, r))

  (* Semantics of sequencing. Nothing special here. *)
  | C_Seq : forall p1 p2 tr1 tr2,
              Behavior p1 tr1 ->
              Behavior p2 tr2 ->
              connected tr1 tr2 ->
              Behavior (Seq p1 p2) (append tr1 tr2)

  (* Branching semantics when first branch is taken. *)
  | C_IteTrue : forall c p1 p2 tr,
                  eval_cond c (Now tr) ->
                  Behavior p1 tr ->
                  Behavior (Ite c p1 p2) tr

  (* Branching semantics when second branch is taken. *)
  | C_IteFalse : forall c p1 p2 tr,
                  ~eval_cond c (Now tr) ->
                  Behavior p2 tr ->
                  Behavior (Ite c p1 p2) tr

  (* Repetition semantics with 0 repetitions. *)
  | Rep0 : forall p s,
             Behavior (Rep p) (one (st_fun s))

  (* Repetition semantics with at least 1 repetition. *)
  | RepN : forall p tr tr',
             Behavior p tr ->
             Behavior (Rep p) tr' ->
             connected tr tr' ->
             Behavior (Rep p) (append tr tr').

  

  (* Semantics of formulas. A formula valid with respect
     to a given behavior. When we state correctness
     properties of programs, we will quantify over the
     behavior.  *)
  Fixpoint eval_formula (f:Formula) (tr:trace) : Prop :=
    match f with
      | CompF t1 t2 op => eval_comp t1 t2 (Now tr) op
      | AndF f1 f2 => eval_formula f1 tr /\ eval_formula f2 tr
      | OrF f1 f2 => eval_formula f1 tr \/ eval_formula f2 tr
      | Imp f1 f2 => eval_formula f1 tr -> eval_formula f2 tr
      | Prog p => Behavior p tr
      | Always f' =>
        eval_formula f' tr /\
        let (b, t) := start tr in
        
        forall t, eval_formula f' (fun r => tr (add_time r t))
      | Eventually f' =>
        exists t, eval_formula f' (fun r => tr (add_time r t))
    end.

  Close Scope R_scope.

End Semantics.

(* Adding some notation for evaluation of formulas. *)
Notation "|- f" := (forall tr, eval_formula f tr)
                     (at level 100) : HP_scope.