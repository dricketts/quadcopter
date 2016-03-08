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

Definition Var := string.

Definition fstate := list (Var * (float)).

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

Inductive fexpr :=
| FVar   : Var -> fexpr
| FConst : float -> fexpr
| FPlus  : fexpr -> fexpr -> fexpr
| FMinus : fexpr -> fexpr -> fexpr
| FMult  : fexpr -> fexpr -> fexpr
| FMax   : fexpr -> fexpr -> fexpr
.

Fixpoint fexprD (fx : fexpr) (sf : fstate) : option float :=
  match fx with
  | FVar s         => fstate_lookup sf s
  | FConst f       => Some f
  | FPlus fx1 fx2  => lift2 float_plus  (fexprD fx1 sf) (fexprD fx2 sf)
  | FMinus fx1 fx2 => lift2 float_minus (fexprD fx1 sf) (fexprD fx2 sf)
  | FMult fx1 fx2  => lift2 float_mult  (fexprD fx1 sf) (fexprD fx2 sf)
  | FMax l r       => lift2 float_max (fexprD l sf) (fexprD r sf)
  end.

Inductive fcmd : Type :=
| FSeq   : fcmd -> fcmd -> fcmd
| FSkip  : fcmd
| FAsn   : Var -> fexpr -> fcmd
| FIte   : fexpr -> fcmd -> fcmd -> fcmd
| FFail  : fcmd
.

Definition fzero : float := Fappli_IEEE.B754_zero 24 128 false.
Definition fnegzero : float := Fappli_IEEE.B754_zero 24 128 true.

(** NOTE: These are not quite kosher because they are not the meaning
 ** of equality on floating point numbers.
 **)
Definition float_lt (f1 f2 : float)  : Prop :=
  (FloatToR f1 < FloatToR f2)%R.

Definition float_ge (f1 f2 : float) : Prop :=
  (FloatToR f1 >= FloatToR f2)%R.

Inductive feval : fstate -> fcmd -> fstate -> Prop :=
| FESkip : forall s, feval s FSkip s
| FESeqS : forall s s' os'' a b,
    feval s a s' ->
    feval s' b os'' ->
    feval s (FSeq a b) os''
| FEAsnS : forall s v e val,
    fexprD e s = Some val ->
    feval s (FAsn v e) ((fstate_set s v val))
| FEIteT :
    forall s os' ex c1 c2 f,
      fexprD ex s = Some f ->
      float_lt f fzero ->
      feval s c1 os' ->
      feval s (FIte ex c1 c2) os'
| FEIteF:
    forall s os' ex c1 c2 f,
      fexprD ex s = Some f ->
      float_ge f fzero ->
      feval s c2 os' ->
      feval s (FIte ex c1 c2) os'
.

Lemma fstate_lookup_update_match :
  forall fst v val,
    Some val = fstate_lookup (fstate_set fst v val) v.
Proof.
  intros.
  simpl.
  consider (v ?[eq] v); intro; subst; congruence.
Qed.

Lemma fstate_lookup_irrelevant_update :
  forall fst v v' val,
    v <> v' ->
    fstate_lookup fst v = fstate_lookup (fstate_set fst v' val) v.
Proof.
  intros.
  simpl.
  consider (v ?[eq] v'); intro; subst; congruence.
Qed.
