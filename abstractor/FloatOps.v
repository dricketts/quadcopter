(*
 * FloatLib.v
 * Contains various additional floating-point definitions
 *)

Require Import Coq.micromega.Psatz.
Require Import Coq.Reals.Rdefinitions.
Require Import List.
Import ListNotations.
Require Import Flocq.Appli.Fappli_IEEE.
Require Import Flocq.Appli.Fappli_IEEE_bits.
Require Abstractor.Floats.

Require Import ExtLib.Programming.Extras.
Import FunNotation.

Delimit Scope SrcLang_scope with SL.
Local Open Scope SrcLang_scope.

(** [prec] is the number of bits of the mantissa including the implicit one.
    [emax] is the exponent of the infinities.
    Typically p=24 and emax = 128 in single precision. *)

Definition prec:Z := 24%Z.
Definition emax := 128%Z.

(*Definition emin:Z := (3 - emax - prec)%Z.*)
Definition emin:Z := (-126)%Z.
Definition emaxGtEmin : (emax > emin)%Z.
Proof. compute. reflexivity.
Defined.

Definition precGe1: (prec >= 1)%Z.
Proof. compute. inversion 1.
Defined.

(* these last two may not end up being useful *)
Lemma eminMinValue : (emin >= 3 - emax - prec)%Z.
Proof. compute. inversion 1. Qed.

Definition precLtEmax : (prec < emax)%Z.
Proof. compute. reflexivity.
Defined.

(* Lemma nan : binary_float prec emax -> binary_float prec emax -> bool * nan_pl prec. *)
Lemma precThm : forall k : Z,
    (emin < k)%Z ->
    (prec <=
     k - Fcore_FLT.FLT_exp (3 - emax - prec) prec k)%Z.
Proof.
  intros.
  unfold Fcore_FLT.FLT_exp.
  unfold Z.max.
  destruct (k -prec ?= 3 - emax - prec)%Z eqn:Hk; try lia.
  - rewrite Z.compare_lt_iff in Hk.
    unfold emin, emax, prec in *.
    simpl in *.
    psatz Z.
Qed.

Definition custom_prec := prec.
Definition custom_emax:= emax.
Definition custom_float_zero := B754_zero custom_prec custom_emax false.
Definition custom_emin := emin.
Definition float := binary_float custom_prec custom_emax.
Lemma customEminMinValue : (custom_emin >= 3 - custom_emax - custom_prec)%Z.
unfold custom_emin, custom_emax, custom_prec.
apply eminMinValue.
Qed.
Lemma custom_precGe1: (custom_prec >= 1)%Z.
unfold custom_prec.
apply precGe1.
Qed.
Lemma custom_emaxGtCustom_emin : (custom_emax > custom_emin)%Z.
Proof.
unfold custom_emax,custom_emin.
apply emaxGtEmin.
Qed.

Lemma custom_precGt0 : Fcore_FLX.Prec_gt_0 custom_prec.
unfold Fcore_FLX.Prec_gt_0.
unfold custom_prec.
pose proof precGe1.
lia.
Qed.

Lemma custom_precLtEmax : (custom_prec < custom_emax)%Z.
unfold custom_emax, custom_prec.
apply precLtEmax.
Qed.

Definition custom_nan:float -> float -> bool * nan_pl custom_prec :=
  Floats.Float32.binop_pl.


Definition nat_to_float (n : nat) : float :=
  Fappli_IEEE_extra.BofZ custom_prec custom_emax
                         custom_precGt0 custom_precLtEmax (Z.of_nat n).

Definition FloatToR : (float) -> R := B2R custom_prec custom_emax.

Coercion Pos.of_nat : nat >-> positive.

(* Semantics *)
Definition lift2 {T U V : Type} (f : T -> U -> V) (a : option T) (b : option U) : option V :=
  match a , b with
  | Some a , Some b => Some (f a b)
  | _ , _ => None
  end.

(* Useful floating-point operations for our format *)
Definition float_plus (a b : float) : float :=
  Bplus custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_ZR a b.

Definition float_minus (a b : float) : float :=
  Bminus custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_ZR a b.

Definition float_mult (a b : float) : float :=
  Bmult custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_ZR a b.

Definition float_max (a b : float) : float :=
    match a, b with
    | B754_nan _ _ _ _, _ => a
    | _, B754_nan _ _ _ _ => b
    | B754_infinity _ _ _, _ => a
    | _, B754_infinity _ _ _ => b
    | _, _ =>
      match Fappli_IEEE_extra.Bcompare custom_prec custom_emax a b with
      | Some Datatypes.Eq => a
      | Some Datatypes.Lt => b
      | Some Datatypes.Gt => a
      | None => a
      end
    end.

Definition float_compare :=
  Fappli_IEEE.Bcompare custom_prec custom_emax.


(* This replaces a validity proof in the floating-point representation and replaces it with
   eq_refl (this is possible since boolean equality is decidable). Doing this optimization
   allows us to compute floating-point operations in Coq, (including constructing
   floating-point numbers) though we must do so using lazy. *)
Definition concretize_float (f : float) :=
  match f with
  | B754_finite _ _ sig m e pf =>
    @B754_finite _ _ sig m e
                (match bounded prec emax m e as X return (X = true -> X = true) with
                 | true => fun p => eq_refl
                 | false => fun p => p
                 end pf)
  | _ => f
  end.

Lemma concretize_float_correct :
  forall (f : float), concretize_float f = f.
Proof.
  intros.
  unfold concretize_float.
  destruct f; try reflexivity.
  assert (((if bounded prec emax m e as X return (X = true -> X = true)
       then fun _ : true = true => eq_refl
            else fun p : false = true => p) e0) = e0).
  { unfold custom_prec, custom_emax in e0.
    rewrite e0. reflexivity. }
  rewrite H. reflexivity.
Qed.

(* here is how we define new floating-point constants. *)
Definition new_float_one := Eval lazy in (concretize_float (nat_to_float 1)).

(* Nice tactics for reducing floating-point expressions. Automatically apply concretization *)
Ltac fcompute_in X :=
  rewrite <- concretize_float_correct in X; lazy in X.

Ltac fcompute :=
  rewrite <- concretize_float_correct; lazy.

(* raw representaion of float 1 as bits (obtained from simple C program) *)
Lemma test : new_float_one = concretize_float (b32_of_bits 1065353216).
Proof.
  fcompute.
  reflexivity.
Qed.

(* and here is how we add them *)
Definition new_float_one' := Eval lazy in (concretize_float (float_plus custom_float_zero (nat_to_float 1))).


(* Floating-point comparisons *)
(* NB: sign bit is true if negative *)

(*
Definition float_lt (a b : float) : option bool :=
  Fappli_IEEE_extra.Bcompare _ _ a b.
  | Some
  | B754_zero _ _ _ => false
  | B754_infinity _ _ is_neg => is_neg
  | B754_nan _ _ is_neg _ => is_neg (* should never happen for non-exceptional operands... *)
  | B754_finite _ _ is_neg _ _ _ => is_neg
  end.

Definition float_le (a b : float) : bool :=
  match float_minus a b with
  | B754_zero _ _ _ => true
  | B754_infinity _ _ is_neg => is_neg
  | B754_nan _ _ is_neg _ => is_neg (* should never happen for non-exceptional operands... *)
  | B754_finite _ _ is_neg _ _ _ => is_neg
  end.
 *)

Definition fzero : float := Fappli_IEEE.B754_zero 24 128 false.
Definition fnegzero : float := Fappli_IEEE.B754_zero 24 128 true.


Definition F2OR (f : float) : option R :=
  match f with
  | Fappli_IEEE.B754_zero   _ _ _       => Some (FloatToR f)
  | Fappli_IEEE.B754_finite _ _ _ _ _ _ => Some (FloatToR f)
  | _                                   => None
  end.

