Require Import Examples.ParLang.ParLang.
Require Import Abstractor.Source.

Print Source.

(*
Parallel -> SrcProg
Cond     -> FlatFormula
ParTerm  -> NowTerm (missing a lot of math operators...)
 *)

Definition Par_Abstracts_SrcProg
  {ins outs} (par : Parallel ins outs) (sp : SrcProg)
  : Prop :=
  forall st1 st2 fst1 fst2,
    (eval_SrcProg sp fst1) = Some fst2 ->
    eval_Parallel par st1 = st2.

Definition Cond_Abstracts_FlatFormula
  {ins} (c : Cond ins) (ff : FlatFormula)
  : Prop :=
  forall st fst b,
    (progr_cond_holds fst ff) = Some b ->
    eq (eval_Cond c st) b.

Definition ParTerm_Abstracts_NowTerm
           {ins} (pt : ParTerm ins) (nt : NowTerm)
  : Prop :=
  forall st fst f,
    eval_NowTerm fst nt = Some f ->
    eval_ParTerm pt st = FloatToR f.
