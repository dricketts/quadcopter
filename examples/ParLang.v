Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import ChargeTactics.Lemmas.

(* Terms in the parallel language. The type parameter
   that is a list of vars captures the variables
   appearing in the term. *)
Inductive ParTerm : list Var -> Type :=
| VarPT    : forall x, ParTerm (x::nil)
| NatPT    : nat -> ParTerm nil
| RealPT   : R -> ParTerm nil
| PlusPT   : forall {xs ys},
    ParTerm xs -> ParTerm ys -> ParTerm (xs ++ ys)
| MinusPT  : forall {xs ys},
    ParTerm xs -> ParTerm ys -> ParTerm (xs ++ ys)
| MultPT   : forall {xs ys},
    ParTerm xs -> ParTerm ys -> ParTerm (xs ++ ys)
| InvPT    : forall {xs}, ParTerm xs -> ParTerm xs
| CosPT    : forall {xs}, ParTerm xs -> ParTerm xs
| SinPT    : forall {xs}, ParTerm xs -> ParTerm xs
| SqrtPT   : forall {xs}, ParTerm xs -> ParTerm xs
| ArctanPT : forall {xs}, ParTerm xs -> ParTerm xs
| ExpPT    : forall {xs}, ParTerm xs -> ParTerm xs
| MaxPT    : forall {xs ys},
    ParTerm xs -> ParTerm ys -> ParTerm (xs ++ ys)
.

Print CompOp.
Print state.
Print Formula.
Print state. Print trace.
Print eval_formula.
SearchAbout Formula.
(* Conditionals in the parallel language. The type parameter
   that is a list of vars captures the variables
   appearing in the conditional. *)
Inductive Cond : list Var -> Type :=
| TRUEP  : Cond nil
| FALSEP : Cond nil
| CompP  : forall {xs ys},
    ParTerm xs -> ParTerm ys -> CompOp -> Cond (xs ++ ys)
| AndP   : forall {xs ys},
    Cond xs -> Cond ys -> Cond (xs ++ ys)
| OrP    : forall {xs ys},
    Cond xs -> Cond ys -> Cond (xs ++ ys)
| NegP   : forall {xs}, Cond xs -> Cond xs.

Definition sets_disjoint {T} (a b : list T) : Prop :=
    forall x,
      List.In x b -> ~List.In x a.

(* A language with parallel semantics.
   An instance of (Parallel in out) is a program
   with input variables in and output variables out. *)
Inductive Parallel : list Var -> list Var -> Type :=
| Assign : forall x ins, ParTerm ins ->
                         Parallel ins (x::nil)
| Par : forall {ins1 ins2 outs1 outs2},
    sets_disjoint outs1 outs2 ->
    Parallel ins1 outs1 -> Parallel ins2 outs2 ->
    Parallel (ins1 ++ ins2) (outs1 ++ outs2)
| Ite : forall {insc ins1 ins2 outs1 outs2},
    Cond insc -> Parallel ins1 outs1 -> Parallel ins2 outs2 ->
    Parallel (insc ++ ins1 ++ ins2) (outs1 ++ outs2).

(* Evaluation for terms in the language. *)
Fixpoint eval_ParTerm {xs} (t : ParTerm xs) (st : state)
  : Value :=
  match t with
  | VarPT x => st x
  | NatPT n => Coq.Reals.Raxioms.INR n
  | RealPT r => r
  | PlusPT _ _ t1 t2 =>
    eval_ParTerm t1 st + eval_ParTerm t2 st
  | MinusPT _ _ t1 t2 =>
    eval_ParTerm t1 st - eval_ParTerm t2 st
  | MultPT _ _ t1 t2 =>
    eval_ParTerm t1 st * eval_ParTerm t2 st
  | InvPT _ t => / (eval_ParTerm t st)
  | CosPT _ t => Rtrigo_def.cos (eval_ParTerm t st)
  | SinPT _ t => Rtrigo_def.sin (eval_ParTerm t st)
  | SqrtPT _ t => R_sqrt.sqrt (eval_ParTerm t st)
  | ArctanPT _ t => Ratan.atan (eval_ParTerm t st)
  | ExpPT _ t => Rtrigo_def.exp (eval_ParTerm t st)
  | MaxPT _ _ t1 t2 =>
    Rbasic_fun.Rmax (eval_ParTerm t1 st) (eval_ParTerm t2 st)
  end%R.

Definition eval_ParComp {xs ys} (t1:ParTerm xs)
           (t2:ParTerm ys) (op:CompOp)
           (st:state) : bool :=
  if match op as _op return
           forall r1 r2:R,
             let _op := match _op with
                        | Gt => Rgt
                        | Ge => Rge
                        | Lt => Rlt
                        | Le => Rle
                        | Eq => eq
                        end in
             {_op r1 r2} + {~_op r1 r2}
     with
     | Gt => RIneq.Rgt_dec
     | Ge => RIneq.Rge_dec
     | Lt => RIneq.Rlt_dec
     | Le => RIneq.Rle_dec
     | Eq => RiemannInt.Req_EM_T
     end (eval_ParTerm t1 st) (eval_ParTerm t2 st)
  then true else false.

Fixpoint eval_Cond {xs} (c : Cond xs) (st : state) : bool :=
  match c with
  | TRUEP => true
  | FALSEP => false
  | CompP _ _ t1 t2 op => eval_ParComp t1 t2 op st
  | AndP _ _ c1 c2 => andb (eval_Cond c1 st) (eval_Cond c2 st)
  | OrP _ _ c1 c2 => orb (eval_Cond c1 st) (eval_Cond c2 st)
  | NegP _ c => negb (eval_Cond c st)
  end.

Definition merge_states (xs1 xs2 : list Var)
           (st1 st2 : state) : state :=
  fun x =>
    if (* List.in_dec String.string_dec x xs1 *)
    List.existsb (fun y => if String.string_dec x y
                              then true else false) xs1
    then st1 x
    else st2 x.

Fixpoint eval_Parallel {ins outs} (p : Parallel ins outs)
         (st : state) : state :=
  match p with
  | Assign x _ t => fun y => if String.string_dec x y
                           then eval_ParTerm t st
                           else st y
  | Par _ _ outs1 outs2 _ p1 p2 =>
    let st1 := eval_Parallel p1 st in
    let st2 := eval_Parallel p2 st in
    merge_states outs1 outs2 st1 st2
  | Ite _ _ _ _ _ c p1 p2 =>
    if eval_Cond c st
    then eval_Parallel p1 st
    else eval_Parallel p2 st
  end.

Definition tlaParD {ins outs} (p : Parallel ins outs) :=
  Embed (fun st1 st2 =>
           forall x, List.In x outs ->
                     eval_Parallel p st1 x = st2 x).

(* Language definition complete. *)

(* TODO TODO TODO *)
(* This is the goal for next week *)
(* if f abstracts p, then f s1 s2 <- eval p s1 = s2*)
(* Formula :: state -> state -> prop *)

Definition Abstracts {ins outs} (f : Formula) (p : Parallel ins outs) : Prop :=
  forall st1 st2 st3 sts,
    eq (eval_Parallel p st1) st2 ->
    (forall x, In x outs -> st2 x = st3 x) ->
    eval_formula f (Stream.Cons st1 (Stream.Cons st3 sts)).

Print eval_ParTerm.
Definition Abstracts_term {ins} (t: TLA.Syntax.Term) (p: ParTerm ins) : Prop :=
  forall st1 st2, eq (eval_term t st1 st2) (eval_ParTerm p st1).

Lemma sets_disjoint_cons : forall {T} (a: T) b c,
    sets_disjoint (a :: b) c <->
    sets_disjoint b c /\ ~In a c.
Proof.
  intros. unfold sets_disjoint. split.
  { intro. split.
    { intros. intro. eapply H. eassumption. simpl. tauto. }
    { intro. simpl in H. apply H in H0. tauto. } }
  { intros. simpl; intro.
    destruct H1; subst.
    { tauto. }
    { destruct H. clear H2.
      eapply H; eassumption. } }
Qed.

Lemma sets_disjoint_commut : forall {T} (a : list T) b,
    sets_disjoint a b <-> sets_disjoint b a.
Proof.
  intros. unfold sets_disjoint, not.
  split; intros; firstorder.
Qed.

Lemma sets_disjoint_concat : forall {T} (a : list T) b c,
    sets_disjoint (a ++ b) c ->
    sets_disjoint a c /\ sets_disjoint b c.
Proof.
  intros. split; firstorder.
Qed.

(* intros. unfold sets_disjoint. split.
 *   { intros. eapply H. destruct a.
 *     { eapply in_or_app. tauto. }
 *     { eapply in_or_app. tauto. } }
 *   { destruct a.
 *     { simpl in H. unfold sets_disjoint in H. assumption. }
 *     { unfold sets_disjoint in H.
 *       intros. apply H. apply in_or_app. right. assumption. } }
 * Qed. *)


Lemma And_synth_Par
: forall {ins1 ins2 outs1 outs2}
         A (A' : Parallel ins1 outs1)
         B (B' : Parallel ins2 outs2),
    Abstracts A A' ->
    Abstracts B B' ->
    forall sd : sets_disjoint outs1 outs2,
      Abstracts (A //\\ B) (Par sd A' B').
Proof.
  intros. unfold Abstracts. intros. breakAbstraction.
  unfold Abstracts in *.
  split.
  { eapply H.
    { reflexivity. }
    { clear H H0.
      subst.
      intros.
      rewrite <- H2; [ | eapply in_app_iff; tauto ].
      clear H2.
      unfold merge_states.      (* rewrite for in_dec *)
Check in_dec.
      cutrewrite (eq (existsb
                    (fun y : String.string =>
                       if String.string_dec x y then true else false) outs1) true).
      { reflexivity. }
      { clear - H.
        induction outs1; simpl.
        { red in H. destruct H. }
        { destruct (String.string_dec x a).
          { simpl. reflexivity. }
          { simpl. eapply IHouts1.
            destruct H. congruence. assumption. } } } } }
  { eapply H0.
    { reflexivity. }
    { clear H H0.
      subst.
      intros.
      rewrite <- H2 ; [ | eapply in_app_iff; tauto ].
      clear H2.
      unfold merge_states.  (* rewrite for in_dec *)
      cutrewrite (eq (existsb
         (fun y : String.string =>
            if String.string_dec x y then true else false) outs1) false).
      { reflexivity. }
      { clear - sd H.
        induction outs1.
        { simpl. reflexivity. }
        { simpl. rewrite IHouts1.
          { destruct (String.string_dec x a).
            2: reflexivity.
            simpl. subst.
            apply sets_disjoint_cons in sd.
            exfalso; tauto. }
          { apply sets_disjoint_cons in sd. tauto. } } } } }
Qed.
Print Assign.
Print ParTerm.

Arguments Assign v {_} t : rename.
Theorem Next_assign_synth
  : forall {ins} (v : Var) (t : TLA.Syntax.Term) (t' : ParTerm ins),
    Abstracts_term t t' ->
    Abstracts (v! = t) (Assign v t').
Proof.
  intros.
  unfold Abstracts. simpl. intros. subst. rewrite <- H1; [| tauto].
  destruct String.string_dec.
  red in H.
  auto.
  congruence.
Qed.

Theorem Real_term_synth
  : forall (r : R),
    Abstracts_term r (RealPT r).
Proof. compute. reflexivity. Qed.

Theorem Var_term_synth
  : forall (v : Var),
    Abstracts_term v (VarPT v).
Proof. compute. reflexivity. Qed.

Theorem Plus_term_synth
  : forall {ins1 ins2}
           A (A' : ParTerm ins1)
           B (B' : ParTerm ins2),
    Abstracts_term A A' ->
    Abstracts_term B B' ->
    Abstracts_term (A + B) (PlusPT A' B').
Proof.
  unfold Abstracts_term. simpl. intros.
  rewrite H. rewrite H0.
  reflexivity.
Qed.

(* Theorem Next_assign_synth_real
 *   : forall (v : Var) (e : R),
 *     Abstracts (v! = e) (Assign v (RealPT e)).
 * Proof.
 *   intros.
 *   unfold Abstracts. simpl. intros. subst. specialize (H0 v). rewrite <- H0.
 *   { destruct String.string_dec.
 *     { reflexivity. }
 *     { congruence. } }
 *   { tauto. }
 * Qed. *)

Ltac synthTerm :=
  repeat first [ eapply And_synth_Par
               | eapply Next_assign_synth
               | eapply Plus_term_synth
               | eapply Var_term_synth
               | eapply Real_term_synth ].

Local Open Scope string_scope.
Goal exists ins outs, exists prog : Parallel ins outs,
      Abstracts ("x"! = "y" + 2 + 1 + 1+ 1+ 1+ 1+ 1+ 1)%HP prog.
Proof.
  do 3 eexists.
  synthTerm.
Qed.
Print Unnamed_thm.


Goal exists ins outs, exists prog : Parallel ins outs,
      Abstracts ("x"! = 2 //\\ "y"! = 3)%HP prog.
Proof.
  do 3 eexists.
  synthTerm.
  (* eapply And_synth_Par; apply Next_assign_synth_real. *)
  Grab Existential Variables.
  unfold sets_disjoint. intros. intro. red in H. destruct H.
  Focus 2. assumption.
  destruct H0. congruence.
  assumption.
Qed.

Print Unnamed_thm.

Print BasicProofRules.
SearchAbout option.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.OptionMonad.
SearchAbout option Monad.

Import MonadNotation.

Fixpoint Term_to_ParTerm (t : Syntax.Term) :
  option { xs : list Var & ParTerm xs } :=
  match t with
  | VarNowT x => Some (existT _ _ (VarPT x))
  | NatT n    => Some (existT _ _ (NatPT n))
  | RealT r   => Some (existT _ _ (RealPT r))
  | PlusT t1 t2 =>
    t1 <- Term_to_ParTerm t1 ;;
    t2 <- Term_to_ParTerm t2 ;;
    ret (existT _ _
           (PlusPT (projT2 t1)
                   (projT2 t2)))
  | MinusT t1 t2 =>
    t1 <- Term_to_ParTerm t1 ;;
    t2 <- Term_to_ParTerm t2 ;;
    ret (existT _ _
           (MinusPT (projT2 t1)
                   (projT2 t2)))
  | MultT t1 t2 =>
    t1 <- Term_to_ParTerm t1 ;;
    t2 <- Term_to_ParTerm t2 ;;
    ret (existT _ _
           (MultPT (projT2 t1)
                   (projT2 t2)))
  | InvT t =>
    t <- Term_to_ParTerm t ;;
      ret (existT _ _ (InvPT (projT2 t)))
  | CosT t =>
    t <- Term_to_ParTerm t ;;
      ret (existT _ _ (CosPT (projT2 t)))
  | SinT t =>
    t <- Term_to_ParTerm t ;;
      ret (existT _ _ (SinPT (projT2 t)))
  | SqrtT t =>
    t <- Term_to_ParTerm t ;;
      ret (existT _ _ (SqrtPT (projT2 t)))
  | ArctanT t =>
    t <- Term_to_ParTerm t ;;
      ret (existT _ _ (ArctanPT (projT2 t)))
  | ExpT t =>
    t <- Term_to_ParTerm t ;;
      ret (existT _ _ (ExpPT (projT2 t)))
  | MaxT t1 t2 =>
    t1 <- Term_to_ParTerm t1 ;;
    t2 <- Term_to_ParTerm t2 ;;
    ret (existT _ _
           (MaxPT (projT2 t1)
                   (projT2 t2)))
  | _ => None
  end%monad.

Theorem Term_to_ParTerm_sound
  : forall t x,
    Term_to_ParTerm t = Some x ->
    Abstracts_term t (projT2 x).
Proof.
  induction t; simpl.
  { inversion 1. subst. simpl. eapply Var_term_synth. }
  { inversion 1. }
  { admit. }
  { admit. }
  { destruct (Term_to_ParTerm t1); try congruence.
    destruct (Term_to_ParTerm t2); try congruence.
    inversion 1; simpl.
    eapply Plus_term_synth. eapply IHt1. reflexivity. eapply IHt2; reflexivity. }
Admitted.

Goal exists ins outs, exists prog : Parallel ins outs,
      Abstracts ("x"! = "y" + 2 + 1 + 1 + 1 + 1 + 1)%HP prog.
Proof.
  do 3 eexists.
  eapply Next_assign_synth.
  eapply Term_to_ParTerm_sound.
  compute. reflexivity.
Defined.
Print Unnamed_thm0.
Print Unnamed_thm1.


(* TODO TODO TODO *)
Fixpoint Formula_to_Cond (F : Formula) :
  { xs : list Var & Cond xs } :=
  match F with
  | TRUE => existT _ _ TRUEP
  | FALSE => existT _ _ FALSEP
  | Comp t1 t2 op =>
    existT _ _
           (CompP (projT2 (Term_to_ParTerm t1))
                  (projT2 (Term_to_ParTerm t2)) op)
  | And F1 F2 =>
    existT _ _
           (AndP (projT2 (Formula_to_Cond F1))
                 (projT2 (Formula_to_Cond F2)))
  | Or F1 F2 =>
    existT _ _
           (OrP (projT2 (Formula_to_Cond F1))
                 (projT2 (Formula_to_Cond F2)))
  | Syntax.Imp F1 F2 =>
    existT _ _
           (OrP (NegP (projT2 (Formula_to_Cond F1)))
                (projT2 (Formula_to_Cond F2)))
  | _ => existT _ _ TRUEP
  end.

Lemma Term_to_ParTerm_sound :
  forall t tr,
    is_st_term t = true ->
    eval_ParTerm (projT2 (Term_to_ParTerm t)) (Stream.hd tr) =
    eval_term t (Stream.hd tr) (Stream.hd (Stream.tl tr)).
Proof.
  induction t; simpl;
  try solve [ reflexivity |
              discriminate |
              intros; rewrite Bool.andb_true_iff in *;
              rewrite IHt2; try tauto; rewrite IHt1;
              try tauto |
              intros; rewrite IHt; tauto ].
Qed.

(* true if the formula can be decided on the current state. *)
Fixpoint is_decidable_st_formula (F:Formula) : bool :=
  match F with
    | TRUE => true
    | FALSE => true
    | Comp t1 t2 _ =>
      andb (is_st_term t1) (is_st_term t2)
    | And F1 F2 | Or F1 F2 | Syntax.Imp F1 F2 =>
      andb (is_decidable_st_formula F1)
           (is_decidable_st_formula F2)
    | _ => false
  end.

Lemma excluded_middle :
  forall A,
    is_decidable_st_formula A = true ->
    |-- A \\// (A -->> lfalse).
Proof.
  induction A; breakAbstraction; auto; intros;
  try solve [ apply andb_prop in H; destruct H as [HA1 HA2];
              specialize (IHA1 HA1 tr I);
              specialize (IHA2 HA2 tr I);
              intuition | discriminate ].
  destruct c; solve_linear.
Qed.

Lemma Formula_to_Cond_true :
  forall A tr,
    is_decidable_st_formula A = true ->
    (eval_Cond (projT2 (Formula_to_Cond A))
               (Stream.hd tr) = true <->
     eval_formula A tr).
Proof.
  induction A;
  try solve [ simpl; intuition |
              simpl; intros;
              repeat rewrite Bool.andb_true_iff in *;
              repeat rewrite Bool.orb_true_iff in *;
              rewrite IHA1; try tauto;
              rewrite IHA2; tauto ].
  - simpl; unfold eval_comp; simpl; intros;
    rewrite Bool.andb_true_iff in H;
    destruct c; unfold eval_ParComp; simpl;
    match goal with
    | [ |- context [ if ?e then _ else _ ] ]
      => destruct e
    end; repeat rewrite <- Term_to_ParTerm_sound;
    intuition.
  - pose proof (excluded_middle A1) as Hexcluded;
    breakAbstraction.
    simpl; intros;
    repeat rewrite Bool.andb_true_iff in *;
    repeat rewrite Bool.orb_true_iff in *;
    repeat rewrite Bool.negb_true_iff in *.
    rewrite IHA2; try tauto.
    specialize (Hexcluded (proj1 H) tr I).
    intuition.
    { rewrite <- IHA1 in *; try tauto; congruence. }
    { left. rewrite <- IHA1 in *; try tauto;
            apply Bool.not_true_is_false; auto. }
Qed.

Lemma ite_refine_aux :
  forall A B C,
    is_decidable_st_formula A = true ->
    (A -->> B) //\\ ((A-->>lfalse) -->> C)  |--
    (A //\\ B) \\// C.
Proof.
  intros.
  tlaAssert (A \\// (A -->> lfalse));
    [ rewrite <- excluded_middle; auto; charge_tauto |
      charge_intros ].
  repeat rewrite land_lor_distr_L;
  repeat apply lorL; charge_tauto.
Qed.

Lemma ite_refine :
  forall A B C ins1 ins2 outs1 outs2
         (b:Parallel ins1 outs1) (c:Parallel ins2 outs2),
    is_decidable_st_formula A = true ->
    tlaParD b |-- B ->
    tlaParD c |-- C ->
    tlaParD (Ite (projT2 (Formula_to_Cond A)) b c) |--
            (A //\\ B) \\// C.
Proof.
  intros.
  rewrite <- ite_refine_aux; auto.
  rewrite <- H0. rewrite <- H1. clear H0 H1.
  breakAbstraction. intros.
  rewrite <- Formula_to_Cond_true; auto.
  split; intros; rewrite <- H0 by (apply in_or_app; tauto).
  { intros. rewrite H1; auto. }
  { intros.
    match goal with
    | [ |- context [ if ?e then _ else _ ] ]
      => destruct e
    end; intuition. }
Qed.

Lemma Assign_refine :
  forall x t,
    is_st_term t = true ->
    tlaParD (Assign x _ (projT2 (Term_to_ParTerm t))) |--
    (x! = t)%HP.
Proof.
  intros; breakAbstraction; intros;
  rewrite <- Term_to_ParTerm_sound; auto;
  rewrite <- H0; destruct (String.string_dec x x);
  intuition.
Qed.

Lemma ite_refine_and_impl :
  forall A B C D ins1 ins2 outs1 outs2
         (b:Parallel ins1 outs1) (d:Parallel ins2 outs2),
    is_decidable_st_formula A = true ->
    A //\\ C |-- lfalse ->
    tlaParD b |-- B ->
    tlaParD d |-- D ->
    tlaParD (Ite (projT2 (Formula_to_Cond A)) b d) |--
            (A -->> B) //\\ (C -->> D).
Proof.
  intros. rewrite <- H1. rewrite <- H2. clear H1 H2.
  breakAbstraction. intros.
  split; intros; rewrite <- H1 by (apply in_or_app; tauto);
  clear H1; specialize (H0 tr);
  rewrite <- (Formula_to_Cond_true A) in *; auto;
  match goal with
  | [ |- context [ if ?e then _ else _ ] ]
    => destruct e eqn:?
  end; intuition.
Qed.

Lemma par_disjoint_refine :
  forall A B ins1 ins2 outs1 outs2
         (a:Parallel ins1 outs1) (b:Parallel ins2 outs2),
    tlaParD a |-- A ->
    tlaParD b |-- B ->
    forall (pf:sets_disjoint outs1 outs2),
      tlaParD (Par pf a b) |-- A //\\ B.
Proof.
  intros. breakAbstraction. intros.
  split.
  { apply H; intros;
    rewrite <- H1 by (apply List.in_or_app; tauto).
    unfold merge_states, sets_disjoint in *.
    repeat match goal with
           | [ |- context [ if ?e then _ else _ ] ]
               => destruct e eqn:?
           end; try reflexivity.
    rewrite existsb_exists in *.
    destruct Heqb1 as [y [Hy ?]].
    destruct (String.string_dec x y); try discriminate.
    subst; specialize (pf y); intuition. }
  { apply H0; intros;
    rewrite <- H1 by (apply List.in_or_app; tauto).
    unfold merge_states, sets_disjoint in *.
    repeat match goal with
           | [ |- context [ if ?e then _ else _ ] ]
               => destruct e eqn:?
           end; try reflexivity.
    { rewrite existsb_exists in *.
      destruct Heqb0 as [y [Hy ?]].
      destruct (String.string_dec x y); try discriminate.
      subst; specialize (pf y); intuition. }
    { rewrite <- Bool.not_true_iff_false in *.
      rewrite existsb_exists in *.
      contradict Heqb1. exists x.
      destruct (String.string_dec x x); auto. } }
Qed.