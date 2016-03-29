Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
Require Import ExtLib.Tactics.
Require Import SMT.Tactic.
Require Import Flocq.Appli.Fappli_IEEE.
Require Import Flocq.Core.Fcore_Raux.
Require Import Flocq.Prop.Fprop_relative.
Require Import Flocq.Core.Fcore_FLT.
Require Import Flocq.Core.Fcore_generic_fmt.
Require Import Flocq.Core.Fcore_defs.
Require Import Abstractor.FloatOps.
Require Import Abstractor.FloatLang.

Import ListNotations.

Definition error    : R := bpow radix2 (- (custom_prec) + 1).
Definition floatMax : R := bpow radix2 custom_emax.
Definition floatMin : R := bpow radix2 custom_emin%Z.

(* Real numbers, with +/- infinity but not NaN *)
Inductive Rinf :=
| RinfR : R -> Rinf
| RinfInf : Rinf
| RinfNInf : Rinf      
.

Inductive Rinf_lt : Rinf -> Rinf -> Prop :=
| Rinf_ltR : forall r1 r2, Rlt r1 r2 -> Rinf_lt (RinfR r1) (RinfR r2)
| Rinf_ltInf : forall r, Rinf_lt (RinfR r) RinfInf
| Rinf_ltNInf : forall r, Rinf_lt RinfNInf (RinfR r)
| Rinf_ltInfs : Rinf_lt RinfNInf RinfInf
.

Inductive Rinf_eq : Rinf -> Rinf -> Prop :=
| Rinf_eqR : forall r1 r2, r1 = r2 -> Rinf_eq (RinfR r1) (RinfR r2)
| Rinf_eqInf : Rinf_eq RinfInf RinfInf
| Rnf_eqNInf : Rinf_eq RinfNInf RinfNInf
.
               
Definition Rinf_gt (r1 r2 : Rinf) : Prop :=
  Rinf_lt r2 r1.

(* TODO: is native equality what we want here?
   No; we want 

 *)
Definition Rinf_le (r1 r2 : Rinf) : Prop :=
  Rinf_lt r1 r2 \/ Rinf_eq r1 r2.

Definition Rinf_ge (r1 r2 : Rinf) : Prop :=
  Rinf_lt r2 r1 \/ Rinf_eq r1 r2.

(* TODO: make sure this really is the abstraction we want by pushing through
   the velocity shim. *)
(* TODO: should this be predicated? (i.e. should it take an fstate) *)
(* nan is a flag saying whether it might be NaN. *)
Record interval : Type :=
  mkI { lb : Rinf;
        ub : Rinf;
        nan : bool}.

Definition B2Rinf (f : float) : option Rinf :=
  match f with
  | B754_infinity _ _ true => Some RinfInf
  | B754_infinity _ _ false => Some RinfNInf
  | B754_nan _ _ _ _ => None
  | _ => Some (RinfR (B2R _ _ f))
  end.

(* TODO: don't check nan bit. this needs to take a real
   instead of a float *)
Definition intervalD (i : interval) (f : float) : Prop :=
  let '(mkI ilb iub isnan) := i in
  (is_nan _ _ f = true /\ isnan = true) \/
   match B2Rinf f with
   | Some ri => Rinf_le i.(lb) ri /\ Rinf_le ri i.(ub)
   | None => False
   end. 

(*
Definition intervalD (i : option interval) (f : float) : Prop :=
  match i with
  | None => is_nan _ _ f = true
  | Some (mkI lb ub) =>
    match (B2Rinf f) with
    | None => False
    | Some ri => Rinf_le lb ri /\ Rinf_le ri ub
    end
  end.
 *)

(** * Intersections of Predicated Intervals **)
(*
Definition All_interval : Type := list (option interval).

Definition All_intervalD (p : All_interval) (f : float) (fs : fstate) : Prop :=
  Forall (fun x => intervalD x f) p.

Definition All_predInt_entails (a b : All_interval) : Prop :=
  forall f fs, All_intervalD a f fs -> All_intervalD b f fs.

Section cross_product.
  Context {T U V : Type}.
  Variable f : T -> U -> V.
  Fixpoint cross (x : list T) (y : list U) : list V :=
    match x with
    | List.nil => List.nil
    | x :: xs => map (f x) y ++ cross xs y
    end.

  Theorem cross_In : forall xs ys z,
      List.In z (cross xs ys) <->
      exists x y, z = f x y /\ List.In x xs /\ List.In y ys.
  Proof.
    induction xs; simpl; intros.
    { split; destruct 1. destruct H; tauto. }
    { rewrite in_app_iff.
      rewrite IHxs.
      rewrite in_map_iff.
      split.
      { destruct 1; forward_reason;
        do 2 eexists; eauto. }
      { destruct 1; forward_reason.
        destruct H0; subst; eauto.
        right. do 2 eexists; eauto. } }
  Qed.
End cross_product.

Definition lift (abs : option interval -> option interval -> option interval) (l r : All_interval)
  : All_interval :=
  cross abs l r.

Fixpoint flatten {T} (ls : list (list T)) : list T :=
  match ls with
  | List.nil => List.nil
  | l :: ls => l ++ flatten ls
  end.

Definition lift_flatten (abs : option interval -> option interval -> All_interval) (l r : All_interval)
  : All_interval :=
  flatten (cross abs l r).
*)
(* Rounding stuff... *)
Definition the_round : R -> R :=
  round radix2 (FLT_exp (3 - custom_emax - custom_prec) custom_prec)
        (round_mode mode_ZR).

Definition Rsign (r : R) : R :=
  if Rlt_dec r 0 then -1%R
  else if Rlt_dec 0 r then 1%R
       else R0.

Definition oRinf := option Rinf.

(*TODO need *)
Definition Rinf_sign (ri : Rinf) : R :=
  match ri with
  | RinfR r => Rsign r
  | RinfInf => 1%R
  | RinfNInf => -1%R
  end.
               
Definition Rinf_plus (ril rir : Rinf) : option Rinf :=
  match ril, rir with
  (* nan cases *)
  | RinfInf, RinfNInf => None
  | RinfNInf, RinfInf => None
  (* inf *)
  | RinfInf, _ => Some RinfInf
  | _, RinfInf => Some RinfInf
  (* -inf *)
  | RinfNInf, _ => Some RinfNInf
  | _, RinfNInf => Some RinfNInf
  (* reals. NB the result will be unrounded. *)
  | RinfR l, RinfR r => Some (RinfR (l + r))%R
  end.

Definition Rinf_max (ril rir : Rinf) : Rinf :=
  match ril, rir with
  | RinfNInf, _ => rir
  | _, RinfNInf => ril
  | RinfInf, _ => RinfInf
  | _, RinfInf => RinfInf
  | RinfR l, RinfR r => RinfR (Rmax l r)
  end.

(* NB these ORinf things are all dead code... *)
Definition oRinf_minus (oril orir : oRinf) : oRinf :=
  match oril, orir with
  | None, _ => None
  | _, None => None
  | Some ril, Some rir =>
    match ril, rir with
    | RinfInf, RinfInf => None
    | RinfNInf, RinfNInf => None
    (* inf *)
    | RinfInf, _ => Some RinfInf
    | _, RinfInf => Some RinfInf
    (* -inf *)
    | RinfNInf, _ => Some RinfNInf
    | _, RinfNInf => Some RinfNInf
    (* reals. NB the result will be unrounded. *)
    | RinfR l, RinfR r => Some (RinfR (l - r))%R
    end
  end.

Print Rle_lt_or_eq_dec.

Axiom Req_dec' : forall (a1 a2 : R), {a1 = a2} + {a1 <> a2}.

Definition oRinf_times (oril orir : oRinf) : oRinf :=
  match oril, orir with
  | None, _ => None
  | _, None => None
  | Some ril, Some rir =>
    match ril, rir with
    | RinfInf, RinfInf => Some RinfInf
    | RinfInf, RinfNInf => Some RinfNInf
    | RinfNInf, RinfNInf => Some RinfInf
    | RinfNInf, RinfInf => Some RinfNInf
    (* inf, check for zero *)
    | RinfInf, RinfR r => if Req_dec' r 0 then None
                         else Some (if Rlt_dec r 0 then RinfNInf
                                    else RinfInf)
    | RinfR r, RinfInf => if Req_dec' r 0 then None
                         else Some (if Rlt_dec r 0 then RinfNInf
                                    else RinfInf)
    (* -inf, check for zero *)
    | RinfNInf, RinfR r => if Req_dec' r 0 then None
                         else Some (if Rlt_dec r 0 then RinfInf
                                    else RinfNInf)
    | RinfR r, RinfNInf => if Req_dec' r 0 then None
                         else Some (if Rlt_dec r 0 then RinfInf
                                    else RinfNInf)
    (* reals. NB the result will be unrounded. *)
    | RinfR l, RinfR r => Some (RinfR (l * r))%R
    end
  end.

Definition roundDown_relative (r : R) : R :=
  r * (R1 - (Rsign r) * error).

Definition roundDown_subnormal (a : R) : R := -floatMin.

Definition roundDown (r : R) : R :=
  if Rlt_dec (Rabs r) floatMin then
    roundDown_subnormal r
  else
    roundDown_relative r.

Definition roundDown_Rinf (ri : Rinf) : Rinf :=
  match ri with
  | RinfR r =>
    if Rlt_dec r (-floatMax)
    then RinfNInf
    else if Rgt_dec r floatMax
         then RinfInf
         else RinfR (roundDown r)
  | _ => ri
  end.

(* TODO: what is rounding behavior of infinities *)
Definition roundDown_oRinf (ori : oRinf) : oRinf :=
  match ori with
  | None => None
  | Some ri =>
    Some (roundDown_Rinf ri)
  end.

Definition roundUp_relative (r : R) : R :=
  r * (1 + (Rsign r) * error).

Definition roundUp_subnormal (a : R) : R := floatMin.

Definition roundUp (r : R) : R :=
  if Rlt_dec (Rabs r) floatMin then
    roundUp_subnormal r
  else
    roundUp_relative r.

Definition roundUp_Rinf (ri : Rinf) : Rinf :=
  match ri with
  | RinfR r =>
    if Rlt_dec r (-floatMax)
    then RinfNInf
    else if Rgt_dec r floatMax
         then RinfInf
         else RinfR (roundUp r)
  | _ => ri
  end.

Definition roundUp_oRinf (ori : oRinf) : oRinf :=
  match ori with
  | None => None
  | Some ri =>
    Some (roundUp_Rinf ri)
  end.

(* Used to represent constant nan value *)
Definition nan_const : interval :=
  {| lb := RinfInf; ub := RinfNInf; nan := true |}.

(* used to represent an inconsistent value (Bottom) *)
Definition bot_const : interval :=
  {| lb := RinfInf; ub := RinfNInf; nan := false |}.

(* used to represent a trivial value (Top) *)
Definition top_const : interval :=
  {| lb := RinfNInf; ub := RinfInf; nan := true |}.

(* abstraction functions *)
Definition absFloatConst (f : float) : interval :=
  match (B2Rinf f) with
  | None => nan_const
  | Some ri => {| lb := ri ; ub := ri; nan := false|}
  end.

(* lift a binary function on reals to one on Rinfs *)
(* how do we keep track of what type of float to return? *)
Definition absFloatPlus' (l r : interval) : interval :=
  (* if the extremes result in NaN, then we can't really say anything
     i think nan_const is what we should return in this case
 *)
  match Rinf_plus l.(lb) r.(lb), Rinf_plus l.(ub) r.(ub) with
  | Some ll, Some uu =>
    (* these check for -inf + inf *)
    let flag1 := match Rinf_plus l.(lb) r.(ub) with
                 | Some _ => false
                 | None => true end in
    let flag2 := match Rinf_plus l.(ub) r.(lb) with
                 | Some _ => false
                 | None => true end in
    {| lb := roundDown_Rinf ll; ub := roundUp_Rinf uu; nan := orb (orb l.(nan) r.(nan)) (orb flag1 flag2) |}
  | _, _ => nan_const
  end.

(* floating point max semantics:
 *)
Definition absFloatMax' (l r : interval) : interval :=
  let res_lb := Rinf_max l.(lb) r.(lb) in
  let res_ub := Rinf_max l.(ub) r.(ub) in
  {| lb := Rinf_max l.(lb) r.(lb);
     ub := Rinf_max l.(ub) r.(ub);
     (* max(x, NaN) = x; max(NaN, x) = x.*)
     nan := andb l.(nan) r.(nan) |}.
(*
    , Rinf_plus l.(lb) r.(ub), Rinf_plus l.(ub) r.(lb), Rinf_plus l.(ub) r.(ub) with
  | 
  | Some l =>
    (* lower bound *)
    match Rinf_plus (l.(ub) r.(ub)) with
    | None =>
    | Some u =>
      match Rinf_plus (l.
  let min := roundDown_Rinf (Rinf_plus l.(lb) r.(lb))%R in
  let max := roundUp_Rinf   (Rinf_plus l.(ub) + r.(ub)) in
  let bad := 
    Some {| lb := min; ub := max |}
    None
  end.
    let min := 
    match l, r with
    | {| lb := 
    (* inf, inf
       inf, -inf
       -inf, inf
       -inf, -inf *)
    let min fst := roundDown (l.(lb) fst + r.(lb) fst) in
    let max fst := roundUp   (l.(ub) fst + r.(ub) fst) in
    Some {| (*premise := fun fst => l.(premise) fst /\ r.(premise) fst
                          /\ float_bounded (min fst) /\ float_bounded (max fst)
                          /\ min fst <= max fst; *)
        lb := min
        ; ub := max |}%R
  end.
*)
