(*
 * FloatLang.v
 * An imperative programming language with floating point numbers.
 *)

Require Import Coq.Reals.Rbase.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Tactics.Consider.
Require Import Abstractor.FloatOps.
Require Import Abstractor.Embed.

Definition Var := string.

Definition fstate := list (Var * (float)).

(*
Fixpoint fstate_lookup (f : fstate) (v : Var) : option (float) :=
  match f with
  | List.nil          => None
  | (v',b) :: fs =>
    if v ?[ eq ] v' then
     Some b
    else fstate_lookup fs v
 end.

Definition fstate_set (f : fstate) (v : Var) (val : float) : fstate :=
  (v, val) :: f.
*)

Inductive fexpr :=
| FVar   : Var -> fexpr
| FConst : float -> fexpr
| FPlus  : fexpr -> fexpr -> fexpr
| FMinus : fexpr -> fexpr -> fexpr
| FMult  : fexpr -> fexpr -> fexpr
| FMax   : fexpr -> fexpr -> fexpr
.

(* We use this for NaN values representing failed lookups *)
Definition fnan := Eval compute in float_plus (Fappli_IEEE.B754_infinity _ _ true) (Fappli_IEEE.B754_infinity _ _ false).

(*
Fixpoint fexprD (fx : fexpr) (sf : fstate) : option float :=
  match fx with
  | FVar s         => fm_lookup sf s
  | FConst f       => Some f
  | FPlus fx1 fx2  => lift2 float_plus  (fexprD fx1 sf) (fexprD fx2 sf)
  | FMinus fx1 fx2 => lift2 float_minus (fexprD fx1 sf) (fexprD fx2 sf)
  | FMult fx1 fx2  => lift2 float_mult  (fexprD fx1 sf) (fexprD fx2 sf)
  | FMax l r       => lift2 float_max (fexprD l sf) (fexprD r sf)
  end.
 *)
(* fexprD need no longer be optional; we can have NaNs! *)
(* do fm lookup; return nan if lookup fails *)
Definition fstate_lookup_nan (fs : list (string * float)) (s : string) : float :=
  match fm_lookup fs s with
  | Some f => f
  | None => fnan
  end.
  
Fixpoint fexprD (fx : fexpr) (sf : fstate) : float :=
  match fx with
  | FVar s         => fstate_lookup_nan sf s
  | FConst f       => f
  | FPlus fx1 fx2  => float_plus  (fexprD fx1 sf) (fexprD fx2 sf)
  | FMinus fx1 fx2 => float_minus (fexprD fx1 sf) (fexprD fx2 sf)
  | FMult fx1 fx2  => float_mult  (fexprD fx1 sf) (fexprD fx2 sf)
  | FMax l r       => float_max (fexprD l sf) (fexprD r sf)
  end.

Inductive fcmd : Type :=
| FSeq   : fcmd -> fcmd -> fcmd
| FSkip  : fcmd
| FAsn   : Var -> fexpr -> fcmd
| FIte   : fexpr -> fcmd -> fcmd -> fcmd
(*| FIFin  : fexpr -> fcmd -> fcmd -> fcmd*)
| FFail  : fcmd
.

Definition fzero : float := Fappli_IEEE.B754_zero 24 128 false.
Definition fnegzero : float := Fappli_IEEE.B754_zero 24 128 true.

Definition float_lt (f1 f2 : float)  : Prop :=
  (float_compare f1 f2 = Some Lt)%R.

Definition float_ge_or_nan (f1 f2 : float) : Prop :=
  ~ (float_compare f1 f2 = Some Lt)%R.

Inductive feval : fstate -> fcmd -> fstate -> Prop :=
| FESkip : forall s, feval s FSkip s
| FESeqS : forall s s' os'' a b,
    feval s a s' ->
    feval s' b os'' ->
    feval s (FSeq a b) os''
| FEAsnS : forall s v e,
    feval s (FAsn v e) ((fm_update s v (fexprD e s)))
| FEIteT :
    forall s os' ex c1 c2,
      float_lt (fexprD ex s) fzero ->
      feval s c1 os' ->
      feval s (FIte ex c1 c2) os'
| FEIteF:
    forall s os' ex c1 c2,
      float_ge_or_nan (fexprD ex s) fzero ->
      feval s c2 os' ->
      feval s (FIte ex c1 c2) os'
(*| FEIFinT:
    forall s os' ex c1 c2 f,
      fexprD ex s = Some f ->
      Fappli_IEEE.is_finite _ _ f = true ->
      feval s c1 os' ->
      feval s (FIFin ex c1 c2) os'
| FEIFinF :
    forall s os' ex c1 c2 f,
      fexprD ex s = Some f ->
      Fappli_IEEE.is_finite _ _ f = false ->
      feval s c2 os' ->
      feval s (FIFin ex c1 c2) os'*)
.

Lemma fm_update_match :
  forall {T} fst v val,
    Some val = @fm_lookup T (fm_update fst v val) v.
Proof.
  intros.
  simpl.
  consider (Strings.String.string_dec v v); subst; congruence.
Qed.

Lemma fstate_lookup_irrelevant_update :
  forall {T} fst v v' val,
    v <> v' ->
    @fm_lookup T fst v = @fm_lookup T (@fm_update T fst v' val) v.
Proof.
  intros.
  simpl.
  consider (Strings.String.string_dec v v'); subst; congruence.
Qed.
