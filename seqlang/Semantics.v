Require Import Syntax.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.RIneq.
Require Import String.

(************************************************)
(* The semantics of differential dynamic logic. *)
(************************************************)
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
  | NegC c' => ~eval_cond c' st
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
Definition update_st (s:state) (x:Var) (t:Term) :=
  fun y => if string_dec x y
           then eval_term t s
           else s y.

CoInductive stream (A : Type) :=
| Cons : A -> stream A -> stream A.

Arguments Cons {A} [_] [_].

Notation "a :: s" := (Cons a s)
                       (at level 60, right associativity).

CoFixpoint append {A} (s1 s2 : stream A) :=
  match s1 with
  | Cons a s1' => a :: append s1' s2
  end.

Notation "s1 ++ s2" := (append s1 s2)
                         (at level 60, right associativity).

Definition hd {A} (s : stream A) :=
  match s with Cons a _ => a end.

(* Semantics of hybrid programs. Intuitively,
   Behavior p f b should hold if p terminates in
   time b and f describes its behavior. *)
Inductive Behavior :
  HybridProg -> stream state -> Prop :=
| C_Skip : forall st s, Behavior Skip (st :: st :: s)
| C_Assign : forall x t st s,
    Behavior (Assign x t) (st :: update_st st x t :: s)
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
| C_Cont : forall cp f b r s,
   r <= (nonneg b) ->
   is_solution f cp r ->
   Behavior (DiffEqHP cp b) (f R0 :: f r :: s)

(* Semantics of sequencing. Nothing special here. *)
| C_Seq : forall p1 p2 l1 l2,
   Behavior p1 l1 ->
   Behavior p2 l2 ->
   Behavior (Seq p1 p2) (l2 ++ l1)

(* Branching semantics when first branch is taken. *)
| C_IteTrue : forall c p1 p2 st s1 s2,
   eval_cond c st ->
   Behavior p1 s1 ->
   Behavior (Ite c p1 p2) (st :: s1 ++ s2)

(* Branching semantics when second branch is taken. *)
| C_IteFalse : forall c p1 p2 st s1 s2,
   ~eval_cond c st ->
   Behavior p2 s1 ->
   Behavior (Ite c p1 p2) (st :: s1 ++ s2)

(* Repetition semantics with 0 repetitions. *)
| Rep0 : forall p s,
   Behavior (Rep p) s

(* Repetition semantics with at least 1 repetition. *)
| RepN : forall p s1 sN,
   Behavior p s1 ->
   Behavior (Rep p) sN ->
   Behavior (Rep p) (sN ++ s1).

(* Semantics of formulas. A formula valid with respect
   to a given behavior. When we state correctness
   properties of programs, we will quantify over the
   behavior.  *)
Fixpoint eval_formula (f:Formula) (beh:stream state) : Prop :=
  match f with
  | CompF t1 t2 op => eval_comp t1 t2 (hd beh) op
  | AndF f1 f2 => eval_formula f1 beh /\ eval_formula f2 beh
  | OrF f1 f2 => eval_formula f1 beh \/ eval_formula f2 beh
  | Imp f1 f2 => eval_formula f1 beh -> eval_formula f2 beh
  | Prog p => Behavior p beh
  | Always f' => forall t, eval_formula f' (fun r => beh (r+t))
  | Eventually f' => exists t, eval_formula f' (fun r => beh (r+t))
  end.

(* Adding some notation for evaluation of formulas. *)
Notation "|- f" := (forall beh, eval_formula f beh)
                     (at level 100) : HP_scope.

Close Scope R_scope.