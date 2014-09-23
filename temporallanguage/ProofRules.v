Require Import TempLang.Syntax.
Require Import TempLang.Semantics.
Require Import Rbase.
Require Import Ranalysis1.
Require Import MVT.
Require Import Equality.

Open Scope HP_scope.
Open Scope string_scope.

Fixpoint is_st_formula (F:Formula) : bool :=
  match F with
    | TT => true
    | FF => true
    | CompF _ _ _ => true
    | AndF F1 F2 => andb (is_st_formula F1)
                         (is_st_formula F2)
    | OrF F1 F2 => andb (is_st_formula F1)
                        (is_st_formula F2)
    | Imp F1 F2 => andb (is_st_formula F1)
                        (is_st_formula F2)
    | _ => false
  end.

Lemma st_formula : forall F beh1 beh2,
  is_st_formula F = true ->
  eval_formula F beh1 ->
  beh1 R0 = beh2 R0 ->
  eval_formula F beh2.
Proof.
  induction F; simpl in *; intros; auto;
  try discriminate.
  - rewrite <- H1. auto.
  - apply Bool.andb_true_iff in H.
    split; try apply (IHF1 beh1);
    try apply (IHF2 beh1); tauto.
  - apply Bool.andb_true_iff in H.
    destruct H0; [left; apply (IHF1 beh1) |
    right; apply (IHF2 beh1)]; tauto.
  - apply Bool.andb_true_iff in H. firstorder.
Qed.

Lemma branch_rule : forall p1 p2 I,
  (|- (I /\ |p1|) --> []I) ->
  (|- (I /\ |p2|) --> []I) ->
  (|- (I /\ |Branch p1 p2|) --> []I).
Proof.
  simpl; intros.
  destruct H1. destruct H3.
  inversion_clear H3; firstorder.
Qed.

Ltac solve_ineq :=
  repeat match goal with
           | [ H : (_ < _ < _)%R |- _ ] => destruct H
           | [ |- (_ <= _ <= _)%R ] => split
           | [ |- _ ] => solve [eapply RIneq.Rlt_le; eauto]
           | [ |- _ ] => solve [apply RIneq.Rle_refl]
         end.

Lemma rep_rule : forall p I,
  is_st_formula I = true ->
  (|- (I /\ |p|) --> []I) ->
  (|- (I /\ |p**|) --> []I).
Proof.
  simpl. intros. destruct H1. destruct H3.
  dependent induction H3; auto.
  clear IHBehavior1. unfold merge_fun in *.
  assert (eval_formula I f1).
  eapply st_formula. auto. apply H1.
  apply H4. solve_ineq; auto.
  pose proof (Rle_dec t b1).
  destruct H7.
  - specialize (H0 f1). eapply st_formula; auto. apply H0.
    split; eauto.
    + eauto.
    + simpl. symmetry. apply H4. rewrite Rplus_0_l.
      solve_ineq. apply Rge_le; auto. auto.
  - specialize (IHBehavior2 p H).
    apply (st_formula _ (fun r:R => fN (r+(t-b1))%R)); auto.
    apply IHBehavior2; auto.
    + eapply st_formula. apply H. eapply (H0 f1).
      split; eauto. apply Rle_ge. apply H2.
      simpl. rewrite Rplus_0_l. transitivity (f b1).
      symmetry. apply H4. solve_ineq; auto.
      destruct H4. specialize (H7 R0 (Rle_refl _)).
      rewrite Rplus_0_l in H7. auto.
    + apply Rge_minus. unfold not in n. unfold Rle in n.
      apply Rle_ge. apply Rnot_lt_le. intro. auto.
    + repeat rewrite Rplus_0_l. symmetry.
      destruct H4. specialize (H7 (t-b1)%R).
      assert ((t-b1+b1)%R = t).
      field_simplify. rewrite (Fdiv_def Rfield).
      rewrite Rinv_1. rewrite Rmult_1_r. reflexivity.
      rewrite H8 in H7. apply H7.
      apply Rge_le. apply Rge_minus. unfold not in n.
      unfold Rle in n. apply Rle_ge. apply Rnot_lt_le.
      intro. auto.
Qed.

(*Lemma is_derivable_eq : forall f1 f2 b,
  (forall x : Var, Ranalysis1.derivable (fun t : R => f1 t x)) ->
  (forall r, (0 <= r <= b)%R -> f1 r = f2 r) ->
  (forall x : Var, Ranalysis1.derivable (fun t : R => f2 t x)).
Proof.
  intros f1 f2 b Hderiv Heq x.
  unfold Ranalysis1.derivable, Ranalysis1.derivable_pt in *.
  intro r. specialize (Hderiv x r). destruct Hderiv.
  apply (exist _ x0).
  unfold Ranalysis1.derivable_pt_abs,
  Ranalysis1.derivable_pt_lim in *.
  intros eps Heps. specialize (d eps Heps). destruct d.
  exists x1. intros h Hh1 Hh2. specialize (H h Hh1 Hh2).
  

Lemma is_solution_eq : forall f1 f2 b diffeqs,
  is_solution f1 diffeqs b ->
  (forall r, (0 <= r <= b)%R -> f1 r = f2 r) ->
  is_solution f2 diffeqs b.
Proof.
  intros f1 f2 b diffeqs Hsol Heq.
  unfold is_solution in *.
  eexists. split.
  - unfold solves_diffeqs.*)
  

(*Lemma beh_equiv : forall p f1 f2 b,
  (0 <= b)%R ->
  Behavior p f1 b ->
  (forall r, (0 <= r <= b) f1 r = f2 r) ->
  Behavior p f2 b.
Proof.
  intros p f1 f2 b Hb Hbeh Hfeq.
  induction Hbeh.
  - econstructor; eauto. rewrite <- (Hfeq b).
    rewrite <- (Hfeq R0). auto.
    split; try apply Rle_refl; auto.
    split; try apply Rle_refl; auto.
    intros r Hr. rewrite <- (Hfeq r); auto.
    destruct Hr; split; auto.
    apply Rlt_le; auto.
  - econstructor; eauto. unfold is_solution in *.
    destruct H0. unfold Ranalysis1.derivable in *.
    unfold Ranalysis1.derivable_pt in *.

Lemma seq_rule : forall p1 p2 F,
  (|- (F /\ |p1|) --> [](|p2| --> []F)) ->
  (|- (F /\ |Seq p1 p2|) --> []F).
Proof.
  simpl; intros p1 p2 F H beh Hbeh t.
  destruct Hbeh as [HF Hbeh]. destruct Hbeh as [b Hbeh].
  inversion_clear Hbeh.
  eapply H.

Lemma seq_rule : forall p1 p2 F,
  (|- (F /\ |p1|) --> []F) ->
  (|- (F /\ |p2|) --> []F) ->
  (|- (F /\ |Seq p1 p2|) --> []F).
Proof.
  simpl; intros.
  destruct H1. destruct H2.
  inversion_clear H2; unfold merge_fun in *.
  apply H. split; auto.
Qed.*)

Fixpoint lift_cond (c:Cond) : Formula :=
  match c with
    | T => TT
    | F => FF
    | CompC t1 t2 op => CompF t1 t2 op
    | AndC c1 c2 => AndF (lift_cond c1) (lift_cond c2)
    | OrC c1 c2 => OrF (lift_cond c1) (lift_cond c2)
  end.

(* Substitutes t2 for x in t1 *)
Fixpoint subst_var_term' (t1 t2:Term) (x:Var) : Term :=
  match t1 with
  | VarT y => if String.string_dec x y then t2 else t1
  | RealT r => t1
  | PlusT t3 t4 =>
     (subst_var_term' t3 t2 x) + (subst_var_term' t4 t2 x)
  | MinusT t3 t4 =>
     (subst_var_term' t3 t2 x) - (subst_var_term' t4 t2 x)
  | MultT t3 t4 =>
     (subst_var_term' t3 t2 x) * (subst_var_term' t4 t2 x)
  end.

Definition subst_var_term (t:Term) (p:list Assign) : Term :=
  List.fold_right
    (fun a t => subst_var_term' t (snd a) (fst a)) t p.

Fixpoint subst_var_cond (c:Cond) (p:list Assign) :=
  match c with
    | CompC t1 t2 op => CompC (subst_var_term t1 p)
                              (subst_var_term t2 p)
                              op
    | AndC c1 c2 => AndC (subst_var_cond c1 p)
                         (subst_var_cond c2 p)
    | OrC c1 c2 => OrC (subst_var_cond c1 p)
                       (subst_var_cond c2 p)
    | _ => c
  end.

Fixpoint subst_var_discr_prog (p:DiscreteProg) (a:list Assign) :=
  match p with
    | ((c, p), b) =>
      (subst_var_cond c a,
       List.map (fun d => (fst d, subst_var_term (snd d) a)) p,
       b)
  end.

Fixpoint subst_var_prog (hp:HybridProg) (a:list Assign) :=
  match hp with
    | DiffEqHP eqs p =>
       DiffEqHP (List.map
                   (fun d =>
                      (fst d, subst_var_term (snd d) a)) eqs)
                (subst_var_discr_prog p a)
    | Branch hp1 hp2 => Branch (subst_var_prog hp1 a)
                               (subst_var_prog hp2 a)
    | Rep hp' => Rep (subst_var_prog hp' a)
  end.

(* Substitutes t for x in f *)
Fixpoint subst_assign (F:Formula) (a:list Assign) : Formula :=
  match F with
    | CompF t1 t2 op =>
      CompF (subst_var_term t1 a) (subst_var_term t2 a) op
    | AndF f1 f2 => AndF (subst_assign f1 a) (subst_assign f2 a)
    | OrF f1 f2 => OrF (subst_assign f1 a) (subst_assign f2 a)
    | Imp f1 f2 => Imp (subst_assign f1 a) (subst_assign f2 a)
    | Prog p => Prog (subst_var_prog p a)
    | Always F' => Always (subst_assign F' a)
    | Eventually F' => Eventually (subst_assign F' a)
    | _ => F
  end.

(* The following three functions will be used to state
   the differential induction rule (diff_ind) below.
   Essentially, an invariant inv is a differential
   invariant of a system of differential equations
   diffeqs at some state st if
     1) inv holds at st
     2) if one takes the "derivative" of inv
        and substitutes the right hand sides of diffeqs
        into this derivative to form inv', then inv'
        holds on any state st'
   The derivative of a formula and substitution of
   differential equations right hand sides is implemented
   in the following three functions. *)
(* Takes a var x and list of differential equations
   and returns Some t if (x' := t) is in the list of
   differential equations. Returns None otherwise. *)
Definition get_deriv (x:Var) (eqs:list (Var * Term))
  : option Term :=
  option_map (@snd Var Term)
    (List.find (fun p : Var * Term => let (y, t) := p in
          proj1_sig (Sumbool.bool_of_sumbool (String.string_dec x y))) eqs).

(* Takes the derivative of a term and substitutes in
   the right hand side of differential equations. If
   a variable has no corresponding differential equation
   then 0 is substituted. This is because variables
   without specified derivatives have a derivative of 0. *)
Fixpoint deriv_term (t:Term) (eqs:list (Var * Term))
  : Term :=
  match t with
  | VarT x =>
    match get_deriv x eqs with
      | Some t => t
      | None   => RealT R0
    end
  | RealT r => RealT R0
  | PlusT t1 t2 =>
     (deriv_term t1 eqs) + (deriv_term t2 eqs)
  | MinusT t1 t2 =>
     (deriv_term t1 eqs) - (deriv_term t2 eqs)
  | MultT t1 t2 =>
     ((deriv_term t1 eqs) * t2) + (t1 * (deriv_term t2 eqs))
  end.

(* For some formulas, differential induction does not work,
   so we use the following unprovable formula in those
   cases. *)
Definition FalseFormula : Formula := #0 > #1.

Lemma FalseFormulaFalse : forall st,
  ~eval_formula FalseFormula st.
Proof.
  intros. simpl. apply RIneq.Rle_not_gt.
  apply RIneq.Rle_0_1.
Qed.

(* When you take the synthetic derivative of a formula
   with a comparison operator, the operator does not
   necessarily stay the same. For example x < y becomes
   x' <= y' *)
Fixpoint deriv_comp_op (op:CompOp) : CompOp :=
  match op with
    | Gt => Ge
    | Ge => Ge
    | Lt => Le
    | Le => Le
    | Eq => Eq
    | Neq => Eq
  end.

(* The derivative of a formula is essentially the derivative
   of each of its terms (with some exceptions). *)
Fixpoint deriv_formula (f:Formula) (eqs:list (Var * Term))
  : Formula :=
  match f with
  | TT => TT
  | FF => FF
  | CompF t1 t2 op =>
     CompF (deriv_term t1 eqs) (deriv_term t2 eqs)
           (deriv_comp_op op)
  | AndF f1 f2 => AndF (deriv_formula f1 eqs)
                      (deriv_formula f2 eqs)
  | OrF f1 f2 => AndF (deriv_formula f1 eqs)
                      (deriv_formula f2 eqs)
  | _ => FalseFormula
  end.

(* Now we have a bunch of messy lemmas that we'll use
   to prove the differential induction (diff_ind) rule. *)
Lemma term_is_derivable : forall (f : R -> state) (e : Term),
  (forall x, derivable (fun t => f t x)) ->
  derivable (fun t => eval_term e (f t)).
Proof.
  intros f e.
  induction e; simpl; intro is_derivable.
    - auto.
    - apply derivable_const.
    - apply derivable_plus; auto.
    - apply derivable_minus; auto.
    - apply derivable_mult; auto.
(*    - apply derivable_div; auto.*)
Qed.

Lemma get_deriv_in : forall x eqs t,
  get_deriv x eqs = Some t ->
  List.In (x, t) eqs.
Proof.
  intros x eqs t Hderiv.
  induction eqs.
    - unfold get_deriv in *. simpl in *. discriminate.
    - unfold get_deriv in *. simpl in *. destruct a.
      destruct (String.string_dec x v) eqn:?; simpl in *;
        intuition congruence.
Qed.

Lemma get_deriv_not_in : forall x eqs,
  get_deriv x eqs = None ->
  ~exists t, List.In (x, t) eqs.
Proof.
  intros x eqs Hderiv.
  induction eqs.
    - intro H. destruct H. auto.
    - intro H. destruct H. simpl in *.
      destruct H.
      + subst a. unfold get_deriv in *. simpl in *.
        destruct (String.string_dec x x); simpl in *;
        intuition discriminate.
      + unfold get_deriv in *. simpl in *. destruct a.
        destruct (String.string_dec x v); simpl in *.
        * discriminate.
        * intuition. eauto.
Qed.

Lemma term_deriv : forall (f : R -> state) (e : Term)
  (r : R) (diffeqs : list (Var * Term)) is_derivable s,
  solves_diffeqs f diffeqs r is_derivable ->
  vars_unchanged f diffeqs r s ->
  forall z, 
    (R0 <= z <= r)%R ->
    derive (fun t => eval_term e (f t))
           (term_is_derivable f e is_derivable) z =
    eval_term (deriv_term e diffeqs) (f z).
Proof.
  intros. unfold derive.
  apply (derive_pt_D_in
           (fun t : R => eval_term e (f t))
           (fun t : R => eval_term (deriv_term e diffeqs)
                                   (f t))).
  induction e; intros; simpl in *.
    - destruct (get_deriv v diffeqs) eqn:?.
      + unfold solves_diffeqs in *.
        unfold derive in *.
        specialize (H v t (get_deriv_in _ _ _ Heqo) z H1).
        apply (derive_pt_D_in
                 (fun t0 : R => f t0 v)
                 (fun t0 : R => eval_term t (f t0))) in H.
        auto.
      + apply (derive_pt_D_in _ _ _
         (term_is_derivable _ (VarT v) is_derivable z)).
        simpl. unfold vars_unchanged, derive in *.
        specialize (H0 v (get_deriv_not_in v diffeqs Heqo)
                       z H1).
        transitivity (derive_pt (fun t : R => f t v) z
                                (s v z)).
        apply pr_nu.
        apply H0.
    - apply Dconst.
    - apply Dadd; auto.
    - apply Dminus; auto.
    - apply Dmult; auto.
Qed.

Lemma deriv_neg : forall f t1 t2 r diffeqs is_derivable,
  solves_diffeqs f diffeqs r is_derivable ->
  vars_unchanged f diffeqs r is_derivable ->
  (forall st,
     (R0 <= eval_term (deriv_term t1 diffeqs) st -
      eval_term (deriv_term t2 diffeqs) st)%R) ->
  forall t,
    (R0 <= t <= r)%R ->
    (R0 <=
    derive_pt
      (fun z : R => eval_term t1 (f z) - eval_term t2 (f z))
      t (derivable_pt_minus _ _ t
           (term_is_derivable _ _ is_derivable t)
           (term_is_derivable _ _ is_derivable t)))%R.
Proof.
  intros f t1 t2 r diffeqs is_derivable Hdiff1 Hdiff2 Hineq
         t Ht.
  specialize (Hineq (f t)).
  erewrite <- term_deriv in Hineq; eauto.
  erewrite <- term_deriv in Hineq; eauto.
  unfold derive in Hineq.
  rewrite <- derive_pt_minus in Hineq.
  apply Hineq.
Qed.

Ltac normalize_ineq_goal :=
  match goal with
    | [ |- Rgt _ _ ]
      => apply RIneq.Rminus_gt; apply RIneq.Rlt_gt
    | [ |- Rge _ _ ]
      => apply RIneq.Rminus_ge; apply RIneq.Rle_ge
    | [ |- Rlt _ _ ]
      => apply RIneq.Rminus_lt; apply RIneq.Ropp_lt_cancel;
         rewrite RIneq.Ropp_minus_distr; rewrite RIneq.Ropp_0
    | [ |- Rle _ _ ]
      => apply RIneq.Rminus_le; apply RIneq.Ropp_le_cancel;
         rewrite RIneq.Ropp_minus_distr; rewrite RIneq.Ropp_0
    | [ |- eq _ _ ]
      => apply RIneq.Rminus_diag_uniq
    | [ |- _ <> _ ]
      => apply Rminus_not_eq
  end.

Ltac normalize_ineq_hyp H :=
  match type of H with
    | context [Rgt _ _] => eapply RIneq.Rgt_minus in H;
                          eapply RIneq.Rgt_lt in H
    | context [Rge _ _] => eapply RIneq.Rge_minus in H;
                          eapply RIneq.Rge_le in H
    | context [Rlt _ _] => eapply RIneq.Rlt_minus in H;
       eapply RIneq.Ropp_lt_contravar in H;
       rewrite RIneq.Ropp_minus_distr in H;
       rewrite RIneq.Ropp_0 in H
    | context [Rle _ _] => eapply RIneq.Rle_minus in H;
       eapply RIneq.Ropp_le_contravar in H;
       rewrite RIneq.Ropp_minus_distr in H;
       rewrite RIneq.Ropp_0 in H
    | context [ eq _ _ ] => apply RIneq.Rminus_diag_eq in H
    | context [ _ <> _ ] => apply Rminus_eq_contra in H
  end.

Ltac ineq_trans Hbase :=
  let r1 :=
      match type of Hbase with
        | Rlt ?r1 _ => r1
        | Rle ?r1 _ => r1
        | eq ?r1 _ => r1
      end in
  let r2 :=
      match type of Hbase with
        | Rlt _ ?r2 => r2
        | Rle _ ?r2 => r2
        | eq _ ?r2 => r2
      end in
  match goal with
    | [ |- Rlt r1 ?r3 ]
        => apply (RIneq.Rlt_le_trans r1 r2 r3)
    | [ |- Rle r1 ?r3 ]
        => apply (RIneq.Rle_trans r1 r2 r3)
    | [ |- Rlt ?r3 r2 ]
        => apply (RIneq.Rlt_le_trans r3 r1 r2)
    | [ |- Rle ?r3 r2 ]
        => apply (RIneq.Rle_trans r3 r1 r2)
    | [ |- eq _ r2 ]
        => transitivity r1
  end.

Ltac deriv_ineq :=
  match goal with
    | [ _ : solves_diffeqs _ _ ?r2 _
        |- Rle (eval_term ?t1 (?f ?r1) - eval_term ?t2 (?f _))
               (eval_term ?t1 (?f _) - eval_term ?t2 (?f _)) ]
        => eapply (derive_increasing_interv_var r1 r2
                     (fun z => eval_term t1 (f z) -
                               eval_term t2 (f z))%R); eauto
    | [ |- @eq R
               (Rminus (eval_term ?t1 (?f _))
                       (eval_term ?t2 (?f _)))
               (Rminus (eval_term ?t1 (?f _))
                       (eval_term ?t2 (?f _)))]
        => eapply (null_derivative_loc
                 (fun z => (eval_term t1 (f z) -
                            eval_term t2 (f z))%R)); eauto
  end.

Lemma eval_comp_ind : forall f r diffeqs is_derivable
                             t1 t2 op,
  Rle R0 r ->
  solves_diffeqs f diffeqs r is_derivable ->
  vars_unchanged f diffeqs r is_derivable ->
  eval_comp t1 t2 (f R0) op ->
  (forall st, eval_comp (deriv_term t1 diffeqs)
                        (deriv_term t2 diffeqs)
                        st
                        (deriv_comp_op op)) ->
  forall z, (0 <= z <= r)%R -> eval_comp t1 t2 (f z) op.
Proof.
  intros f r diffeqs is_derivable t1 t2 op Hr Hdiff1 Hdiff2
         Hbase Hind z Hz.
  destruct Hz. destruct H. destruct Hr.
  destruct op; unfold eval_comp in *; simpl in *;
  try solve [normalize_ineq_goal; normalize_ineq_hyp Hbase;
       ineq_trans Hbase; auto; deriv_ineq; intros;
       match goal with
         | [ |- context [ derive_pt _ _ _ ] ]
           => eapply deriv_neg; eauto; intros;
         normalize_ineq_hyp Hind; try eapply Hind
         | [ |- _ ]
           => idtac
       end; solve_ineq; auto].

normalize_ineq_goal; normalize_ineq_hyp Hbase;
ineq_trans Hbase; auto; deriv_ineq; intros.
apply continuity_pt_minus; apply derivable_continuous_pt;
apply term_is_derivable; auto.
eapply RIneq.Rminus_diag_eq in Hind.
erewrite <- term_deriv in Hind; eauto.
erewrite <- term_deriv in Hind; eauto.
unfold derive in *.
rewrite <- derive_pt_minus in Hind.
apply Hind.
solve_ineq.
solve_ineq.
solve_ineq; auto.

normalize_ineq_goal; normalize_ineq_hyp Hbase.
cut ((eval_term t1 (f z) - eval_term t2 (f z))%R =
     (eval_term t1 (f 0) - eval_term t2 (f 0))%R).
intro HH; rewrite HH; auto.
deriv_ineq; intros.
apply continuity_pt_minus; apply derivable_continuous_pt;
apply term_is_derivable; auto.
eapply RIneq.Rminus_diag_eq in Hind.
erewrite <- term_deriv in Hind; eauto.
erewrite <- term_deriv in Hind; eauto.
unfold derive in *.
rewrite <- derive_pt_minus in Hind.
apply Hind.
solve_ineq.
solve_ineq.
solve_ineq; auto.
subst r. destruct H0.
apply Rlt_not_le in H0.
contradict H0.
apply Rlt_le; auto.
subst z.
apply Rlt_irrefl in H. auto.
subst z. auto.
Grab Existential Variables.
exact (f r).
exact (f r).
exact (f r).
exact (f r).
Qed.

Lemma diffeq_rule : forall I c p d D,
  (|- (I /\ |DiffEqHP nil (c, p, R0)|) --> []I) ->
  (|- (I /\ |DiffEqHP D (c, nil, d)|) --> []I) ->
  (|- (I /\ |DiffEqHP D (c, p, d)|) --> []I).
Proof.
  simpl. intros I c p d D Hassign Hdiffeq
    beh H t Ht. destruct H as [HI Hbeh].
  destruct Hbeh as [b Hbeh].
  dependent destruction Hbeh. inversion_clear H.
  destruct (Rlt_le_dec t d) as [Hd | Hd].
  - apply Hdiffeq; auto. split.
    + auto.
    + exists d. econstructor; eauto.
      constructor; auto. repeat constructor.
      intros. 

Lemma diffeq_rule : forall I c p d D,
  (|- (I /\ (lift_cond c)) --> (subst_assign I p)) ->
  (|- (lift_cond c) --> deriv_formula I D) ->
  (|- (I /\ |DiffEqHP D (c, p, d)|) --> []I).
Proof.
  intros I c p d D Hassign Hderiv.
  induction I; simpl in *; intros; auto.
  - tauto.
  - (*destruct H. destruct H1. inversion_clear H1.
    unfold is_solution in *. destruct H3.
    destruct H1. rewrite Rplus_0_l. apply Rge_le in H0.
    eapply (eval_comp_ind fcp x); auto.*)
    admit.
  - split.
    + apply IHI1; auto. intros. apply Hassign; auto.
      intuition.