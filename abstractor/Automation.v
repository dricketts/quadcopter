(* this is where the automation that currently sits at the
   beginning of Postprocess_velshim.v will go. *)
Require Import Logic.Syntax.
Require Import Logic.Semantics.
Require Import Logic.ProofRules.
Require Import String.
Local Open Scope HP_scope.
Local Open Scope string_scope.
Require Import List.
Require Import Strings.String.
Import ListNotations.
Require Import Rdefinitions.
Require Import ExtLib.Core.RelDec.
Require Import Coq.Reals.Rbase.
Require Import SMT.Tactic.
Require Import Abstractor.Embed.
Require Import Abstractor.FloatEmbed.
Require Import Logic.Automation.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Tactics.
Require Import Abstractor.FloatOps.
Require Import Abstractor.FloatLang.

Import FloatEmbed.

(* "Pushing" Embed through connectives *)
Lemma lequiv_formula_iff :
  forall (P Q : Formula),
    (forall tr, eval_formula P tr <-> eval_formula Q tr) <->
    (P -|- Q).
Proof.
  intros.
  split.
  - intros. split; breakAbstraction; intros; apply H; assumption.
  - intros. unfold lequiv in H. destruct H.
    breakAbstraction.
    split; intros; [apply H | apply H0]; assumption.
Qed.

Ltac shatterAbstraction :=
  try apply lequiv_formula_iff; unfold lequiv in *; breakAbstraction.

Lemma embed_push_TRUE :
  Embed (fun _ _ => True) -|- TRUE.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma embed_push_FALSE :
  Embed (fun _ _ => False) -|- FALSE.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma embed_push_And :
  forall (P1 P2 : _ -> _ -> Prop) (F1 F2 : Formula),
    Embed P1 -|- F1 -> Embed P2 -|- F2 ->
    Embed (fun x y => P1 x y /\ P2 x y) -|- F1 //\\ F2.
Proof.
  shatterAbstraction. intuition.
Qed.

Lemma embed_push_Or :
  forall (P1 P2 : _ -> _ -> Prop) (F1 F2 : Formula),
    Embed P1 -|- F1 -> Embed P2 -|- F2 ->
    Embed (fun x y => P1 x y \/ P2 x y) -|- F1 \\// F2.
Proof.
  shatterAbstraction. intuition.
Qed.

Lemma embed_push_Imp :
  forall (P1 P2 : _ -> _ -> Prop) (F1 F2 : Formula),
    Embed P1 -|- F1 -> Embed P2 -|- F2 ->
    Embed (fun x y => P1 x y -> P2 x y) -|- F1 -->> F2.
Proof.
  shatterAbstraction. intuition.
Qed.

Ltac fwd := forward_reason.

Lemma embed_push_Exists :
  forall (T : Type) (P : T -> state -> state -> Prop) (F : T -> Formula),
    (forall (t : T), Embed (P t) -|- F t) ->
    Embed (fun x y => exists (t : T), (P t x y)) -|- lexists F.
Proof.
  shatterAbstraction.
  intuition.
  fwd. specialize (H x). fwd.
  eexists. eauto.
  fwd. specialize (H x). fwd.
  eexists. eauto.
Qed.

Lemma embed_push_Forall :
  forall (T : Type) (P : T -> state -> state -> Prop) (F : T -> Formula),
    (forall (t : T), Embed (P t) -|- F t) ->
    Embed (fun x y => forall (t : T), (P t x y)) -|- lforall F.
Proof.
  intros.
  shatterAbstraction. intuition.
  eapply H. apply H0.
  eapply H. apply H0.
Qed.

Lemma embed_push_Const : forall P, Embed (fun _ _ => P) -|- PropF P.
Proof.
  shatterAbstraction; tlaIntuition.
Qed.

(* Relation expressing a side-condition that must be used to push embed through arithmetic facts *)
Definition evals_to (f : Term) (f' : state -> state -> R) : Prop :=
  (eval_term f = f')%type.

Notation "f =|> g" := (evals_to f g) (at level 60).

(* comparison pushing *)
Lemma embed_push_Eq :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => l' x y = r' x y)%type -|-
          Comp l r Eq.
Proof.
  intros.
  unfold evals_to in *.
  shatterAbstraction. subst. reflexivity.
Qed.

Lemma embed_push_Gt :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => Rgt (l' x y) (r' x y))%type -|-
          Comp l r Gt.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma embed_push_Ge :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => Rge (l' x y) (r' x y))%type -|-
          Comp l r Ge.
Proof.
  intros.
  unfold evals_to in *.
  shatterAbstraction. subst. reflexivity.
Qed.

Lemma embed_push_Lt :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => Rlt (l' x y) (r' x y))%type -|-
          Comp l r Lt.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma embed_push_Le :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => Rle (l' x y) (r' x y))%type -|-
          Comp l r Le.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

(* arithmetic pushing *)
Lemma arith_push_plus :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    PlusT l r =|> (fun x y => l' x y + r' x y)%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_minus :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    MinusT l r =|> (fun x y => l' x y - r' x y)%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_mult :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    MultT l r =|> (fun x y => l' x y * r' x y)%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_inv :
  forall l l',
    l =|> l' ->
    InvT l =|> (fun x y => / (l' x y))%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_cos :
  forall l l',
    l =|> l' ->
    CosT l =|> (fun x y => Rtrigo_def.cos (l' x y))%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_max :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    MaxT l r =|> (fun x y => Rbasic_fun.Rmax (l' x y) (r' x y))%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction.
  subst. reflexivity.
Qed.

Lemma arith_push_sin :
  forall l l',
    l =|> l' ->
    SinT l =|> (fun x y => Rtrigo_def.sin (l' x y))%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

(* var, real *)
Lemma arith_push_VarNow :
  forall (x : Var),
    VarNowT x =|> fun st _ => st x.
Proof.
  reflexivity.
Qed.

Lemma arith_push_VarNext :
  forall (x : Var),
    VarNextT x =|> fun _ st' => st' x.
Proof.
  reflexivity.
Qed.

(* special cases for 0 and 1: want to compile these into nats,
   since nat are easier to work with *)
Lemma arith_push_Nat_zero :
    NatT 0 =|> fun _ _ => 0%R.
Proof. reflexivity. Qed.

Lemma arith_push_Nat_one :
    NatT 1 =|> fun _ _ => 1%R.
Proof. reflexivity. Qed.

Lemma arith_push_Nat :
  forall (n : nat),
    NatT n =|> fun _ _ => INR n.
Proof. reflexivity. Qed.

Lemma arith_push_Real :
  forall (r : R),
    RealT r =|> fun _ _ => r.
Proof. reflexivity. Qed.

(* for solving goals containing fupdate *)
(*
Lemma arith_push_fm_update_eq :
  forall (t: state -> state -> R) (v : Var) (X : Term) (f : state -> state -> state),
    X =|> t ->
    X =|> (fun x y : state => fupdate (f x y) v (t x y) v).
Proof.
  intros. unfold evals_to in *.
  rewrite H. unfold fupdate.
  rewrite rel_dec_eq_true; eauto with typeclass_instances.
Qed.

Lemma arith_push_fupdate_neq :
  forall (t: state -> state -> R) (v v' : Var) (X : Term) (f : state -> state -> istate),
    v <> v' ->
    X =|> (fun x y : state => f x y v') ->
    X =|> (fun x y : state => fupdate (f x y) v (t x y) v').
Proof.
  intros.
  unfold fupdate, evals_to in *. rewrite H0.
  rewrite rel_dec_neq_false; eauto with typeclass_instances.
Qed.
*)


Create HintDb embed_push discriminated.
Create HintDb arith_push discriminated.

Hint Rewrite
     embed_push_TRUE embed_push_FALSE
     embed_push_And embed_push_Or embed_push_Imp
     embed_push_Exists embed_push_Forall
     embed_push_Const
  : embed_push.

Hint Rewrite
     embed_push_Eq embed_push_Gt embed_push_Ge embed_push_Lt embed_push_Le
     using solve [eauto 20 with arith_push]
                         : embed_push.

(* for the "<>" goals created by arith_push_fupdate_neq *)
Hint Extern
     0 (_ <> _) => congruence : arith_push.

(* Other miscellaneous rewriting lemmas *)
Lemma AnyOf_singleton :
  forall (P : Prop), AnyOf [P] -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma AnyOf_weaken :
  forall (P : Prop) (Ps : list Prop),
    AnyOf Ps |-- AnyOf (P :: Ps).
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma and_True_snip1 :
  forall (P : Prop),
    True //\\ P -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma and_True_snip2 :
  forall (P : Prop),
    P //\\ True -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma or_False_snip1 :
  forall (P : Prop),
    P \\// False -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma or_False_snip2 :
  forall (P : Prop),
    False \\// P -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

Definition nat_to_float (n : nat) : float :=
Fappli_IEEE_extra.BofZ custom_prec custom_emax custom_precGt0 custom_precLtEmax (Z.of_nat n).

Lemma PropF_revert :
  forall (P : Prop) (G Q : Syntax.Formula),
    (P -> G |-- Q) ->
    (G |-- PropF P -->> Q).
Proof.
  tlaIntuition.
Qed.

Lemma PropF_pull :
  forall (P : Prop) (G Q : Syntax.Formula),
    P ->
    (G |-- Q) ->
    (PropF P -->> G |-- Q).
Proof.
  tlaIntuition.
Qed.

(* Used to begin rewriting in our goal. *)
Lemma lequiv_rewrite_left :
  forall (A B C : Formula),
    A -|- C -> C |-- B -> A |-- B.
Proof.
  shatterAbstraction. intuition.
Qed.

(* Automation for rewriting Embeds *)
Hint Extern
     0 (_ =|> (fun _ _ => ?X)) => first [ apply arith_push_Nat_zero | apply arith_push_Nat_one
                                          | apply arith_push_Nat | apply arith_push_Real]
                                  : arith_push.

Hint Resolve
     arith_push_plus arith_push_minus arith_push_mult arith_push_inv
     arith_push_sin arith_push_cos
     arith_push_VarNow arith_push_VarNext
     (*arith_push_fupdate_eq arith_push_fupdate_neq*)
  : arith_push.

(* Automation for pushing through embed rewriting *)
Ltac crunch_embeds :=
  progress repeat
           match goal with
           | |- Embed (fun x y => models _ _ _ _) -|- _ => reflexivity
           | |- Embed (fun x y => _ -> _) -|- _ => eapply embed_push_Imp
           | |- Embed (fun x y => _ \/ _) -|- _ => eapply embed_push_Or
           | |- Embed (fun x y => _ /\ _) -|- _ => eapply embed_push_And
           | |- Embed (fun x y => exists z, _) -|- _ => eapply embed_push_Exists; intro
           | |- Embed (fun x y => forall z, _) -|- _ => eapply embed_push_Forall; intro
           | |- Embed (fun x y => _ = _) -|- _ => eapply embed_push_Eq; eauto with arith_push
           | |- Embed (fun x y => (_ < _)%R) -|- _ => eapply embed_push_Lt; eauto with arith_push
           | |- Embed (fun x y => (_ <= _)%R) -|- _ => eapply embed_push_Le; eauto with arith_push
           | |- Embed (fun x y => (_ > _)%R) -|- _ => eapply embed_push_Gt; eauto with arith_push
           | |- Embed (fun x y => (_ >= _)%R) -|- _ => eapply embed_push_Ge; eauto with arith_push
           | |- Embed (fun x y => ?X) -|- _ => eapply embed_push_Const
           end.

(* Small logic lemmas for the subsequent theorem *)
Lemma lentail_cut1 :
  forall (A B C : Formula),
    C |-- A ->
    A -->> B |-- C -->> B.
Proof.
  intros. breakAbstraction. intuition.
Qed.

Lemma lentail_cut2 :
  forall (A B C D : Formula),
    C |-- A ->
    B |-- D ->
    (A -->> B |-- C -->> D).
Proof.
  intros. tlaIntuition.
Qed.

Lemma land_comm_left :
  forall (A B C : Formula),
    A //\\ B |-- C ->
    B //\\ A |-- C.
Proof.
  tlaIntuition.
Qed.

Lemma limpl_comm1 :
  forall (A B C D : Formula),
    A |-- B -->> C -->> D ->
    A |-- C -->> B -->> D.
Proof.
  tlaIntuition.
Qed.


(* Predicate capturing that the given variable is a float in the pre-state *)
(* todo, possibly: lift to variable maps? *)

Lemma F2OR_FloatToR :
  forall (f : float) (r r' : R),
    F2OR f = Some r ->
    FloatToR f = r' ->
    r = r'.
Proof.
  intros.
  unfold F2OR, FloatToR in *.
  destruct f; try congruence.
Qed.

(* generalized version of Enabled_action, needed to prove
   enabledness goals *)
Lemma Enabled_action_gen
  : forall P Q : Syntax.Formula,
    (forall (st : state) (tr : trace),
        Semantics.eval_formula Q (Stream.Cons st tr) ->
        exists st' : state,
          Semantics.eval_formula P (Stream.Cons st (Stream.forever st'))) ->
    Q |-- Enabled P.
Proof.
  tlaIntuition.
  destruct tr.
  eapply H in H0.
  simpl.
  fwd.
  eauto.
Qed.

Lemma PropF_tauto :
  forall (P : Prop) F,
    P -> F |-- PropF P.
Proof.
  tlaIntuition.
Qed.

Lemma app_cons_last :
  forall (T : Type) (l l' : list T) (a : T),
    l ++ (a :: l') =
    (l ++ [a]) ++ l'.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl. reflexivity.
Qed.

Lemma limpl_limpl_land :
  forall (A B C : Syntax.Formula),
    |-- A //\\ B -->> C ->
    |-- A -->> B -->> C.
Proof.
  tlaIntuition.
Qed.

(* Used to expose post-states, since fwp by default does not let us talk about both
   pre- and post-states *)
Definition fstate_get_rval (v : Var) (P : R -> fstate -> Prop) (fs : fstate) : Prop :=
  match fm_lookup fs v with
  | None => False
  | Some vf =>
    match F2OR vf with
    | None => False
    | Some vr => P vr fs
    end
  end.

(* Used to get pre-state variable values *)
Lemma inject_var :
  forall (s : Var) G P,
    (G |-- Forall x : R, (RealT x = VarNowT s)%HP -->> P) ->
    (G |-- P).
Proof.
  tlaIntuition.
  eapply H. eassumption.
  reflexivity.
Qed.

Ltac show_value val :=
  let x := eval compute in val in
      assert (val = x) by reflexivity.

Lemma land_curry1 :
  forall (A B C D : Syntax.Formula),
    A |-- (B //\\ C) -->> D ->
    A |-- B -->> C -->> D.
Proof.
  tlaIntuition.
Qed.

(*
Ltac proveVarValid :=
  match goal with
  | |- isVarValid ?s ?v =>
    match goal with
    | H1: eq (fstate_lookup v s) (Some ?x) |- _ =>
      match goal with
      | H2: FloatEmbed.asReal x ?r |- _ =>
        unfold isVarValid, F2OR; rewrite H1; unfold FloatEmbed.asReal in H2 ;
        consider x; simpl; auto; try congruence
      | H2: F2OR x = Some ?r |- _ =>
        unfold isVarValid, F2OR; rewrite H1;
        consider x; simpl; auto; try congruence
      end
    end
  end.
*)

Require Import Coq.micromega.Psatz.
(*
Lemma fstate_lookup_fstate_lookup_force :
  forall (s : fstate) (v : Var) (f : float) (r : R),
    fstate_lookup s v = Some f ->
    FloatEmbed.asReal_in f r ->
    (Bound.roundDown r <= fstate_lookup_force s v <= Bound.roundUp r)%R.
Proof.
  unfold fstate_lookup_force. intros.
  rewrite H.
  unfold FloatToR.
  red in H0.
  generalize (Bound.roundUp_round r); intros.
  generalize (Bound.roundDown_round r); intros.
  destruct f; simpl in *; try congruence.
  { inversion H0; subst; clear H0.
    lra. }
  { inversion H0; subst; clear H0.
    lra. }
Qed.
*)

(* use firstN, skipN *)
Lemma hide_tail :
  forall {T : Type} (ls : list T),
    ls = match ls with
         | h :: t => h :: tl ls
         | nil => nil
         end.
Proof.
  induction ls; reflexivity.
Qed.

(* used for evaluating vc gen a bit at a time... *)
(*
Ltac peel_bound_hyp H :=
  rewrite hide_tail in H;
  change bound_fexpr with bound_fexpr2 in H at 2;
  simpl in H;
  destruct H.
*)

Lemma F2OR_FloatToR' :
  forall (f : float) (r : R),
    F2OR f = Some r ->
    FloatToR f = r.
Proof.
  destruct f; simpl; congruence.
Qed.

Lemma F2OR_weaken :
  forall f r, F2OR f = Some r -> FloatToR f = r.
Proof.
  destruct f; simpl; intros; congruence.
Qed.

(* used instead of admit for the goals we solve by Z3 *)
Axiom z3_says : forall (A : Prop), A.

Ltac z3_solve_discharge :=
  z3 solve; apply z3_says.

Tactic Notation "z3" "solve!" := z3_solve_discharge.

Lemma AnyOf_app :
  forall (l1 l2 : list Prop),
    AnyOf (l1 ++ l2) <-> AnyOf l1 \/ AnyOf l2.
Proof.
  split.
  { induction l1; intros.
    - auto.
    - simpl in *.
      destruct H; auto.
      rewrite or_assoc. auto. }
  { induction l1; intros.
    - simpl in *. destruct H; auto; contradiction.
    - simpl in *. rewrite or_assoc in H.
      destruct H; auto. }
Qed.

(*
Ltac peel_bounds_hyp H n :=
  rewrite <- (firstn_skipn n) in H;
  apply AnyOf_app in H;
  change bound_fexpr with bound_fexpr2 in H at 2;
  simpl in H; (* simpl bound_fexpr? *)
  destruct H; [|change bound_fexpr2 with bound_fexpr in H].
*)

(* used for tagging abstractor outputs *)
Definition dummy (r1 r2 : R) : Prop :=
  True.

Definition preVarPred (pred : R -> Prop) (v : Var) : Formula :=
  Syntax.Exists float
                (fun f : float =>
                   Embed (fun st _ => FloatToR f = Bound.the_round (st v) /\
                                     pred (st v))).

(* find F2R's; remember them; pull them; compute them *)
Ltac do_F2Rs :=
  match goal with
  | H: context[Fcore_defs.F2R ?X] |- _ =>
    let FR := fresh "FR" in
    let FRE := fresh "FRE" in
    remember (Fcore_defs.F2R X) as FR eqn: FRE;
      compute in FRE
  | |- context[Fcore_defs.F2R ?X] =>
    let FR := fresh "FR" in
    let FRE := fresh "FRE" in
    remember (Fcore_defs.F2R X) as FR eqn: FRE;
      compute in FRE
  end.

(* TODO is an analog of this necessary *)
(*
Lemma models_fstate_has_vars :
  forall ar vs vs' fst st,
    models ar (vs' ++ vs) fst st ->
    fstate_has_vars_b fst vs = true.
Proof.
  induction vs; simpl; intros; auto.
  apply Bool.andb_true_iff.
  split.
  {
    unfold models in H.
    specialize (H a).
    fwd.
    generalize (Coqlib.in_app); intros.
    specialize (H0 _ a vs' (a :: vs)).
    simpl in H0. destruct H0.
    specialize (H1 (or_intror (or_introl eq_refl))).
    fwd.
    idtac.
    rewrite <- fstate_lookup_fm_lookup in H.
    rewrite H.
    reflexivity.
  }      
  {
    rewrite app_cons_last in H.
    eapply IHvs; eauto.
  }
Qed.
*)


Lemma F2OR_is_finite :
  forall f r,
    F2OR f = Some r -> Fappli_IEEE.is_finite _ _ f = true.
Proof.
  intros; consider f; intros; simpl in *; congruence.
Qed.

(*
Lemma isVarValid_fstate_set :
  forall fst v,
    isVarValid v fst ->
    forall v' f,
      Fappli_IEEE.is_finite f = true ->
      isVarValid v (fstate_set fst v' f).
Proof.
  unfold isVarValid; simpl; intros.
  fwd.
  consider (v ?[eq] v'); intros; subst;
  eexists; split; eauto.
Qed.
*)


Fixpoint AllOf
         (Ps : list Prop) : Prop :=
  match Ps with
  | nil => True
  (*        | P :: nil => P*)
  | P :: Ps' => P /\ AllOf Ps'
  end.

(* used to get more useful information out of models *)
Lemma models_exploit :
  forall ar vs fs ss,
    models ar vs fs ss ->
    AllOf (map (fun v => (exists d : float, fm_lookup fs v = Some d /\ ar d (ss v))) vs).
Proof.
  intros.
  unfold models in H.
  assert (forall s : string, In s vs -> exists d : M.pl_data, fm_lookup fs s = Some d /\ ar d (ss s)).
  { intros. specialize (H s). fwd. eexists; split; eauto. }
  clear H.
  revert H0; revert ss; revert fs.
  induction vs; simpl; intros; auto.
Qed.

Require Import Coq.Reals.Rbasic_fun.

(* another z3 hint *)
Lemma Rmax_z3_fact :
  forall r1 r2,
    (Rmax r1 r2 = r2 /\ r1 < r2)%R \/
    (Rmax r1 r2 = r1 /\ r1 >= r2)%R.
Proof.
  intros.
  consider (Rlt_dec r1 r2); intros.
  { left. split; auto.
    apply Rmax_right. lra. }
  { right. split.
    { apply Rmax_left. lra. }
    { lra. } }
Qed.

(* one more z3 hint, this one about the_round *)
Lemma the_round_z3_fact :
  forall r,
    (Bound.roundDown r <= Bound.the_round r <= Bound.roundUp r)%R.
Proof.
Admitted.
(*
  intros.
  generalize (Bound.roundUp_round r).
  generalize (Bound.roundDown_round r).
  lra.
Qed.
 *)
Locate floatMin.
Lemma roundDown_fact :
  forall (r : R),
    (r <= -Bound.floatMin /\ Bound.roundDown r = r * (1 + Bound.error))%R \/
    (r >= Bound.floatMin /\ Bound.roundDown r = r * (1 - Bound.error))%R \/
    (r > -Bound.floatMin /\ r < Bound.floatMin /\ Bound.roundDown r = -Bound.floatMin)%R.
Proof.
  intros.
  generalize (Rle_dec r 0); intros.
  destruct H.
  { generalize (Rle_dec r (-Bound.floatMin)); intros.
    destruct H.
    { left. unfold Bound.roundDown.
      split; try lra.
      consider (Rlt_dec (Rbasic_fun.Rabs r) Bound.floatMin); intros.
      { apply Fcore_Raux.Rabs_lt_inv in r2. lra. }
      { unfold Bound.roundDown_relative. unfold Bound.Rsign.
        consider (Rlt_dec r 0); intros; try lra.
        consider (Rlt_dec 0 r); intros; try lra.
        assert (eq r 0)%R by lra. subst. lra. } }
    { assert (r >= -Bound.floatMin)%R by lra.
      right. right.
      split; try lra. split; try lra.
      unfold Bound.roundDown.
      consider (Rlt_dec (Rbasic_fun.Rabs r) Bound.floatMin); intros.
      { reflexivity. }
      { assert (Bound.floatMin <= Rbasic_fun.Rabs r)%R by lra.
        apply Fcore_Raux.Rabs_ge_inv in H0.
        destruct H0; lra. } } }
  { assert (r > 0)%R by lra.
    right.
    generalize (Rlt_dec r Bound.floatMin); intros.
    destruct H0.
    { right. split; try lra. split; try lra.
      unfold Bound.roundDown.
      consider (Rlt_dec (Rbasic_fun.Rabs r) Bound.floatMin).
      { reflexivity. }
      { unfold Bound.roundDown_relative.
        assert (Bound.floatMin <= Rbasic_fun.Rabs r)%R by lra.
        apply Fcore_Raux.Rabs_ge_inv in H0.
        destruct H0; lra. } }
    { assert (r >= Bound.floatMin)%R by lra.
      left.
      split; try lra.
      unfold Bound.roundDown.
      consider (Rlt_dec (Rbasic_fun.Rabs r) Bound.floatMin); intros.
      { apply Fcore_Raux.Rabs_lt_inv in r0. lra. }
      { unfold Bound.roundDown_relative. unfold Bound.Rsign.
        consider (Rlt_dec r 0); try lra.
        consider (Rlt_dec 0 r); lra. } } }
Qed.

Local Ltac considif := match goal with | |- context[if ?X then _ else _] => consider X end.

Lemma roundUp_fact :
  forall (r : R),
    (r <= -Bound.floatMin /\ Bound.roundUp r = r * (1 - Bound.error))%R \/
    (r >= Bound.floatMin /\ Bound.roundUp r = r * (1 + Bound.error))%R \/
    (r > -Bound.floatMin /\ r < Bound.floatMin /\ Bound.roundUp r = Bound.floatMin)%R.
Proof.
  intros.
  generalize (Rle_dec r 0); intros.
  destruct H.
  { generalize (Rle_dec r (-Bound.floatMin)); intros.
    destruct H.
    { left. split; try lra.
      unfold Bound.roundUp.
      considif.
      { apply Fcore_Raux.Rabs_lt_inv in r2. lra. }
      { unfold Bound.roundUp_relative.
        unfold Bound.Rsign.
        consider (Rlt_dec r 0); try lra.
        consider (Rlt_dec 0 r); try lra.
        assert (eq r 0)%R by lra. subst. lra. } }
    { assert (r > -Bound.floatMin)%R by lra.
      right. right.
      split; try lra. split; try lra.
      unfold Bound.roundUp.
      considif.
      { reflexivity. }
      { assert (Bound.floatMin <= Rbasic_fun.Rabs r)%R by lra.
        apply Fcore_Raux.Rabs_ge_inv in H0.
        destruct H0; lra. } } }
  { assert (r > 0)%R by lra.
    right.
    generalize (Rlt_dec r Bound.floatMin); intros.
    destruct H0.
    { right.
      split; try lra.
      split; try lra.
      unfold Bound.roundUp.
      consider (Rlt_dec (Rbasic_fun.Rabs r) Bound.floatMin).
      { reflexivity. }
      { assert (Bound.floatMin <= Rbasic_fun.Rabs r)%R by lra.
        apply Fcore_Raux.Rabs_ge_inv in H0.
        destruct H0; lra. } }
    { assert (r >= Bound.floatMin)%R by lra.
      left.
      split; try lra.
      unfold Bound.roundUp.
      considif.
      { apply Fcore_Raux.Rabs_lt_inv in r0. lra. }
      { unfold Bound.roundUp_relative.
        unfold Bound.Rsign.
        considif; try lra.
        considif; lra. } } }
Qed.


Ltac show_roundDown_z3_hint r :=
  let H := fresh "H" in
  generalize (roundDown_fact r); intro H;
  generalize dependent (Bound.roundDown r); intros.

Ltac show_roundUp_z3_hint r :=
  let H := fresh "H" in
  generalize (roundUp_fact r); intro H;
  generalize dependent (Bound.roundUp r); intros.

Ltac show_Rmax_z3_hint r1 r2 :=
  let H := fresh "H" in
  generalize (Rmax_z3_fact r1 r2); intro H;
  generalize dependent (Rmax r1 r2); intros.

Ltac show_the_round_z3_hint r :=
  let H := fresh "H" in
  generalize (the_round_z3_fact r); intro H;
  generalize dependent (Bound.the_round r); intros.

(* new and improved version, goes bottom-up *)
Ltac show_z3_hints :=
  let ensure_deepest T' :=
      lazymatch T' with
      | context[Bound.roundUp ?r] => fail
      | context[Bound.roundDown ?r] => fail
      | context[Rmax ?r1 ?r2] => fail
      | _ => idtac
      end
    in
      repeat match goal with
             | H : context[Bound.the_round ?r] |- _ =>
               ensure_deepest r;
               show_the_round_z3_hint r
             | |- context[Bound.the_round ?r] =>
               ensure_deepest r;
               show_the_round_z3_hint r
             | H : context[Bound.roundDown ?r] |- _ =>
               ensure_deepest r;
               show_roundDown_z3_hint r
             | |- context[Bound.roundDown ?r] =>
               ensure_deepest r;
               show_roundDown_z3_hint r
             | H : context[Bound.roundUp ?r] |- _ =>
               ensure_deepest r;
               show_roundUp_z3_hint r
             | |- context[Bound.roundUp ?r] =>
               ensure_deepest r;
               show_roundUp_z3_hint r
             | H : context[Rmax ?r1 ?r2] |- _ =>
               ensure_deepest r1;
                 ensure_deepest r2;
                 show_Rmax_z3_hint r1 r2
             | |- context[Rmax ?r1 ?r2] =>
               ensure_deepest r1;
                 ensure_deepest r2;
                 show_Rmax_z3_hint r1 r2
             end.

Ltac show_values :=
  show_value Bound.floatMax;
  show_value Bound.floatMin;
  show_value Bound.error.

Ltac weaken_F2ORs :=
  repeat match goal with
         | H : F2OR ?f = Some ?r |- _ =>
           apply F2OR_weaken in H
         end.

(* used to embed a program and assert that all vars
   other than outputs are unchanged *)
Fixpoint list_minus {T : Type} (dec : forall (x y : T), ({x = y} + {x <> y})) (l1 l2 : list T) : list T :=
  match l1 with
  | nil => nil
  | h :: l1t => if in_dec dec h l2 then list_minus dec l1t l2
               else h :: list_minus dec l1t l2
  end.

Definition embed_ex_seal
           (vis vos : list string) (prg : fcmd) : Formula :=
  embed_ex vis vos prg //\\ Lib.Unchanged (list_minus Coq.Strings.String.string_dec vis vos).

Check Hoare__embed_rw.

(* rewriting rule for using "sealed" embed *)
Lemma Hoare__embed_seal_rw :
  forall (c : fcmd) (vis vos : list string),
    embed_ex_seal vis vos c |--
                  Forall P : state -> fstate -> Prop,
   Embed
     (fun st st' : state =>
        exists fst : fstate,
          models M.asReal_in vis fst st /\
          (P st fst ->
           exists fst' : fstate,
             models M.asReal_out vos fst' st' /\ fpig_vcgen c (P st) fst')) //\\
                                                          Lib.Unchanged (list_minus string_dec vis vos
                                                                        ).
Proof.
  intros.
  generalize (Hoare__embed_rw); intros.
  unfold embed_ex_seal.
  rewrite H.
  tlaIntuition.
Qed.
