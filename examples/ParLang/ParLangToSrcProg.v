Require Import Examples.ParLang.ParLang.
Require Import Abstractor.Source.

Print Source.

(*
Parallel -> SrcProg
Cond     -> FlatFormula
ParTerm  -> NowTerm
*)
Print eval_SrcProg.

(* How to relate fstates and par states?? *)
(* Definition Par_Abstracts_SrcProg
 *   {ins outs} (p : Parallel ins outs) (sp : SrcProg)
 *   : Prop :=
 *   forall st1 st2 fst1 fst2,
 *     (eval_SrcProg sp fst1) = Some fst2 ->
 *     (forall x, In x outs -> fst1 x = st2 x) ->
 *     eval_Parallel p st1 = st2.
 *)

Definition Cond_Abstracts_FlatFormula
  {ins} (c : Cond ins) (ff : FlatFormula)
  : Prop :=
  forall st fst b,
    (progr_cond_holds fst ff) = Some b ->
    eq (eval_Cond c st) b.

Print fstate.
Print eval_ParTerm.

Definition ParTerm_Abstracts_NowTerm
  {ins} (pt : ParTerm ins) (nt : NowTerm)
  : Prop :=
  forall st fst f,
    eval_NowTerm fst nt = Some f ->
    eval_ParTerm pt st = FloatToR f.

Print NowTerm.
Require Import ExtLib.Structures.Monad.

Fixpoint Par_To_Now {xs} (pt: ParTerm xs) {struct pt} : option NowTerm :=
  match pt with
  | VarPT v => Some (VarNowN v)
  | NatPT n => Some (NatN n)
  | RealPT r => None
  | PlusPT _ _ a b =>
    bind (Par_To_Now a)
         (fun a1 =>
            bind (Par_To_Now b)
                 (fun b1 => ret (PlusN a1 b1)))
  | MinusPT _ _ a b =>
    bind (Par_To_Now a)
         (fun a1 =>
            bind (Par_To_Now b)
                 (fun b1 => ret (MinusN a1 b1)))
  | MultPT _ _ a b =>
      bind (Par_To_Now a)
         (fun a1 =>
            bind (Par_To_Now b)
                 (fun b1 => ret (MultN a1 b1)))
  | _ => None
  end.

Lemma Par_To_Now_sound :
  forall xs pt nt,
  @Par_To_Now xs pt = Some nt ->
  ParTerm_Abstracts_NowTerm pt nt.
Proof.
  induction pt; simpl; try solve [intros; congruence].
  { intros. inversion H. subst. red. simpl. intros.
Abort.
