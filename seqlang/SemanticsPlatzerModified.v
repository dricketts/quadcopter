Require Import SeqLang.Syntax.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.RIneq.
Require Import String.

(************************************************)
(* The semantics of differential dynamic logic. *)
(* Based on Andre Platzer's formulation, but    *)
(* uses functions into lists of states.         *)
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

  Close Scope HP_scope.

  Record nelist (A : Type) : Type :=
    mkNelist { nel : list A; cond_nel : nel <> nil}.
  
  Arguments mkNelist [A] _ _.
  Arguments nel [A] _.
  Arguments cond_nel [A] _ _.


  Definition nefirst {A : Type} (nl : nelist A) : A.
    inversion nl as [l nemp].
    destruct l as [| h t].
    - contradict nemp. reflexivity.
    - exact h.
  Defined.

  Definition nelast {A : Type} (nl : nelist A) : A.
    inversion nl as [l nemp].
    destruct l as [| h t].
    - contradict nemp. reflexivity.
    - destruct t as [| h' t'].
      + exact h. 
      + exact (List.last (h' :: t') h').
  (* this might become awful to reason about *)
  Defined.

  (* function from time to states, and time bound *)
  Definition trace := ((time -> nelist state) * time)%type.

  (*
  Definition partial := ((time->state) * time)%type.

  Inductive trace :=
  | one : partial -> trace
  | next : partial -> trace -> trace.
   *)
  (*
  Fixpoint last (tr:trace) :=
    match tr with
      | one f => f
      | Next _ tr' => last tr'
    end.

  Definition start (tr:trace) :=
    match tr with
      | one f => f
      | next f _ => f
    end.
   *)

  (* May introduce a discontinuity *)
  Definition tr_append (tr1 tr2:trace) : trace.
  refine(
    let (f1, b1) := tr1 in
    let (f2, b2) := tr2 in
    let newf :=
        fun t =>
          if (Rlt_dec (nonneg t) (nonneg b1)) then f1 t
          else f2 (mknonnegreal (t - b1) _)
          
    in
    (newf, mknonnegreal (b1 + b2) _)).
  (* first hole - t - b1 *)
  - apply Rnot_lt_ge in _H.
    apply Rge_le.
    apply Rge_minus. assumption.

  (* second hole - b1 + b2 *)
  - apply Rplus_le_le_0_compat;
    apply cond_nonneg.
  Defined.

  Definition time_0 : time :=
    mknonnegreal R0 (Rle_refl _).

  Definition st_fun (s:state) : trace.
    refine (fun _ => (mkNelist (s :: nil) _), time_0).
    intro H; inversion H.
  Defined.

  Definition Now (tr:trace) :=
    nefirst ((fst tr) time_0).

  Definition connected (tr1 tr2:trace) :=
    let (f1, t1) := tr1 in
    let (f2, _) := tr2 in
    nelast (f1 t1) = nefirst (f2 time_0).

  Local Open Scope list_scope.

  (* Helper functions for inductive behavior defn *)
  Definition discHelp1 (s1 : state) : trace.
    refine (fun _ => mkNelist (s1 :: nil) _, time_0).
    intro H; inversion H.
  Defined.

  Definition discHelp2 (s1 s2 : state) : trace.
    refine (fun _ => mkNelist (s1 :: s2 :: nil) _, time_0).
    intro H; inversion H.
  Defined.

  Definition contHelp (f : time -> state) (b : time) : trace.
    refine (fun t => mkNelist (f t :: nil) _, b).
    intro H; inversion H.
  Defined.

  Inductive Behavior :
    HybridProg -> trace -> Prop :=
  | C_Skip : forall s,
               Behavior Skip (discHelp2 s s)
  | C_Assign : forall x t st st',
                 updated_st st x t st' ->
                 Behavior (Assign x t) (discHelp2 st st')
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
               Behavior (Continuous cp b) (contHelp f r)

  (* Semantics of sequencing. Nothing special here. *)
  | C_Seq : forall p1 p2 tr1 tr2,
              Behavior p1 tr1 ->
              Behavior p2 tr2 ->
              connected tr1 tr2 ->
              Behavior (Seq p1 p2) (tr_append tr1 tr2)

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
             Behavior (Rep p) (discHelp1 s)

  (* Repetition semantics with at least 1 repetition. *)
  | RepN : forall p tr tr',
             Behavior p tr ->
             Behavior (Rep p) tr' ->
             connected tr tr' ->
             Behavior (Rep p) (tr_append tr tr').

  (* Useful functions for working with time *)
  Ltac inv H := inversion H; subst; clear H.

  Definition add_time (t1 t2 : time) : time.
    destruct t1 as [nnr1 p1]; destruct t2 as [nnr2 p2].
    refine (mknonnegreal (nnr1 + nnr2) _).
    apply Rplus_le_le_0_compat; auto.
  Defined.

  Definition time_left (x y : time) : option time.
    refine (
        match Rlt_dec x y with
          | left _ => None
          | right LT => Some (mknonnegreal (x-y) _)
        end).
    apply Rnot_lt_le. intro.
    apply Rminus_lt in H. auto.
  Defined.

  (* Semantics of formulas. A formula valid with respect
     to a given behavior. When we state correctness
     properties of programs, we will quantify over the
     behavior.  *)
Print trace.

  Fixpoint eval_formula (f:Formula) (tr:trace) : Prop :=
    match f with
        (* is Now the right moment for the first case? *)
      | CompF t1 t2 op => eval_comp t1 t2 (Now tr) op
      | AndF f1 f2 => eval_formula f1 tr /\ eval_formula f2 tr
      | OrF f1 f2 => eval_formula f1 tr \/ eval_formula f2 tr
      | Imp f1 f2 => eval_formula f1 tr -> eval_formula f2 tr
      | Prog p => Behavior p tr
      | Always f' => 
        let (fn, bd) := tr in
        eval_formula f' tr /\
        forall t, eval_formula f'
          (fun r => fn (add_time r t), bd)
      | Eventually f' =>
        let (fn, bd) := tr in
        exists t, eval_formula f'
          (fun r => fn (add_time r t), bd)
    end.
      
  Close Scope R_scope.

End Semantics.

(* Adding some notation for evaluation of formulas. *)
Notation "|- f" := (forall tr, eval_formula f tr)
                     (at level 100) : HP_scope.
