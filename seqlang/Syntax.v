Require Import String.
Require Import List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

(************************************************)
(* The syntax of differential dynamic logic.    *)
(************************************************)
Section Syntax.
  Variable Var : Type.

  (* All variables are real-valued. *)
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

(* Formulas expressing correctness properties of hybrid
   programs. *)
Inductive Formula :=
| CompF : Term -> Term -> CompOp -> Formula
| AndF : Formula -> Formula -> Formula
| OrF : Formula -> Formula -> Formula
| Imp : Formula -> Formula -> Formula
| Prog : HybridProg -> Formula
| Always : Formula -> Formula
| Eventually : Formula -> Formula.

End Syntax.

(************************************************)
(* Some notation for the logic.                 *)
(************************************************)
Delimit Scope HP_scope with HP.

(*Term notation *)
Notation " # a " := (RealT string a) (at level 0) : HP_scope.
Notation " ` a " := (VarT string a) (at level 0) : HP_scope.
Definition T0 := RealT string 0.
Definition T1 := RealT string 1.
Infix "+" := (PlusT string) : HP_scope.
Infix "-" := (MinusT string) : HP_scope.
Notation "-- x" := (MinusT string (RealT string R0) x)
                     (at level 0) : HP_scope.
Infix "*" := (MultT string) : HP_scope.
Fixpoint pow Var (t : Term Var) (n : nat) :=
  match n with
  | O => RealT Var 1
  | S n => MultT Var t (pow Var t n)
  end.
Notation "t ^^ n" := (pow string t n) (at level 10) : HP_scope.

(* This type class allows us to define a single notation
   for comparison operators and logical connectives in
   the context of a formula and conditionals. *)
Class Comparison (V : Type) (T : Type -> Type) : Type :=
{ Comp : Term V -> Term V -> CompOp -> T V }.

Definition Gt' {V T I} x y := @Comp V T I x y Gt.
Infix ">" := (Gt') : HP_scope.
Definition Eq' {V T I} x y := @Comp V T I x y Eq.
Infix "=" := (Eq') : HP_scope.
Definition Ge' {V T I} x y := @Comp V T I x y Ge.
Infix ">=" := (Ge') : HP_scope.
Definition Le' {V T I} x y := @Comp V T I x y Le.
Infix "<=" := (Le') : HP_scope.
Definition Lt' {V T I} x y := @Comp V T I x y Lt.
Infix "<" := (Lt') : HP_scope.

Class PropLogic (V : Type) (T : Type -> Type) : Type :=
{ And : T V -> T V -> T V;
  Or : T V -> T V -> T V }.

Infix "/\" := (And) : HP_scope.
Infix "\/" := (Or) : HP_scope.

Instance FormulaComparison Var : Comparison Var Formula :=
{ Comp := CompF Var }.

Instance CondComparison Var : Comparison Var Cond :=
{ Comp := CompC Var }.

Instance FormulaPropLogic Var : PropLogic Var Formula :=
{ And := AndF Var;
  Or := OrF Var }.

Instance CondPropLogic Var : PropLogic Var Cond :=
{ And := AndC Var;
  Or := OrC Var }.

(* HybridProg notation *)
Notation "x ::= t" := (Assign string x t)
                        (at level 60) : HP_scope.
Notation "x ' ::= t" := (x, t) (at level 60) : HP_scope.
Notation "[ x1 , .. , xn ]" := (cons x1 .. (cons xn nil) .. )
    (at level 70) : HP_scope.
Notation "diffeqs @ b" := (Continuous string diffeqs b)
                            (at level 75) : HP_scope.
Notation "p1 ; p2" := (Seq string p1 p2)
  (at level 80, right associativity) : HP_scope.
Notation "'IFF' c 'THEN' p1 'ELSE' p2" :=
  (Ite string c p1 p2) (at level 90) : HP_scope.
Notation "p **" := (Rep string p)
                     (at level 90) : HP_scope.

(* Formula notation *)
Notation "f1 --> f2" := (Imp string f1 f2)
                          (at level 97) : HP_scope.
Notation "| p |" := (Prog string p)
                      (at level 95) : HP_scope.
Notation "[] f" := (Always string f)
                     (at level 95) : HP_scope.
Notation "<> f" := (Eventually string f)
                     (at level 95) : HP_scope.