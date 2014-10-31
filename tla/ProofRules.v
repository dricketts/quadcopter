Require Import Coq.micromega.Psatz.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import Rdefinitions.
Require Import Ranalysis1.
Require Import MVT.

Open Scope HP_scope.

Fixpoint next_term (t:TermNext) :=
  match t with
    | VarT (VarNow x) => VarT _ (VarNext x)
    | PlusT t1 t2 => PlusT _ (next_term t1)
                           (next_term t2)
    | MinusT t1 t2 => MinusT _ (next_term t1)
                             (next_term t2)
    | MultT t1 t2 => MultT _ (next_term t1)
                           (next_term t2)
    | _ => t
  end.

Fixpoint next (F:Formula) :=
  match F with
    | Comp t1 t2 op => Comp (next_term t1) (next_term t2) op
    | And F1 F2 => And (next F1) (next F2)
    | Or F1 F2 => Or (next F1) (next F2)
    | Imp F1 F2 => Imp (next F1) (next F2)
    | Exists _ f => Exists _ (fun x => next (f x))
    | Always F => Always (next F)
    | Eventually F => Eventually (next F)
    | _ => F
  end.

Fixpoint is_st_term (t:TermNext) : bool :=
  match t with
    | VarT (VarNext x) => false
    | PlusT t1 t2 => andb (is_st_term t1)
                          (is_st_term t2)
    | MinusT t1 t2 => andb (is_st_term t1)
                           (is_st_term t2)
    | MultT t1 t2 => andb (is_st_term t1)
                          (is_st_term t2)
    | _ => true
  end.

Fixpoint is_st_formula (F:Formula) : bool :=
  match F with
    | TRUE => true
    | FALSE => true
    | Comp t1 t2 _ => andb (is_st_term t1)
                           (is_st_term t2)
    | And F1 F2 => andb (is_st_formula F1)
                         (is_st_formula F2)
    | Or F1 F2 => andb (is_st_formula F1)
                        (is_st_formula F2)
    | Imp F1 F2 => andb (is_st_formula F1)
                        (is_st_formula F2)
    | _ => false
  end.

Lemma next_term_tl : forall t tr,
  is_st_term t = true ->
  eval_termnext (next_term t) tr =
  eval_termnext t (tl tr).
Proof.
  intros t tr Hst.
  induction t; auto; simpl in *;
  try solve [
        destruct v; try discriminate; auto |
        apply andb_prop in Hst; intuition;
        unfold eval_termnext in *; simpl in *;
        rewrite H1; rewrite H2; auto].
Qed.

Lemma next_formula_tl : forall F tr,
  is_st_formula F = true ->
  (eval_formula (next F) tr <->
   eval_formula F (tl tr)).
Proof.
  intros F tr Hst; induction F; simpl in *;
  try tauto; try discriminate.
  - unfold eval_comp in *. simpl in *.
    apply andb_prop in Hst.
    repeat rewrite <- next_term_tl;
      intuition.
   - apply andb_prop in Hst; intuition.
   - apply andb_prop in Hst; intuition.
   - apply andb_prop in Hst; intuition.
Qed.

Lemma st_term_hd : forall t tr1 tr2,
  is_st_term t = true ->
  hd tr1 = hd tr2 ->
  eval_termnext t tr1 =
  eval_termnext t tr2.
Proof.
  induction t; intros tr1 tr2 Hst Hhd;
  simpl in *; auto;
  try solve [
        apply andb_prop in Hst;
        unfold eval_termnext; simpl;
        erewrite IHt1; intuition].
  - destruct v; try discriminate;
    unfold eval_termnext; simpl;
    rewrite Hhd; auto.
Qed.

Lemma st_formula_hd : forall F tr1 tr2,
  is_st_formula F = true ->
  eval_formula F tr1 ->
  hd tr1 = hd tr2 ->
  eval_formula F tr2.
Proof.
  induction F; intros; simpl in *; auto;
  try tauto; try discriminate;
  try solve [apply andb_prop in H; intuition; firstorder].
  - unfold eval_comp in *. simpl in *.
    apply andb_prop in H.
    rewrite st_term_hd with (t:=t) (tr2:=tr1); intuition.
    rewrite st_term_hd with (t:=t0) (tr2:=tr1); intuition.
Qed.

Lemma st_formula_varsagree : forall xs s,
  is_st_formula (VarsAgree xs s) = true.
Proof.
  induction xs; auto.
Qed.

Lemma avarsagree_next : forall xs s1 s2 tr,
  eval_formula (AVarsAgree xs s2)
               (Cons _ s1 (Cons _ s2 tr)).
Proof.
  induction xs; intros; simpl in *; auto;
  unfold eval_comp; auto.
Qed.

Lemma nth_suf_tl : forall A n (s:stream A),
  nth_suf n (tl s) =
  tl (nth_suf n s).
Proof.
  intros A n; induction n; intro s;
  firstorder.
Qed.

Lemma inv_discr_ind : forall I N,
  is_st_formula I = true ->
  (|- (I /\ N) --> (next I)) ->
  (|- (I /\ []N) --> []I).
Proof.
  intros I N Hst Hind. simpl in *.
  intros tr [HI HAN] n.
  induction n; auto.
  simpl. rewrite nth_suf_tl.
  apply next_formula_tl; intuition.
Qed.

Lemma imp_trans : forall F1 F2 F3,
  (|- F1 --> F2) ->
  (|- F2 --> F3) ->
  (|- F1 --> F3).
Proof. firstorder. Qed.

Lemma always_imp : forall F1 F2,
  (|- F1 --> F2) ->
  (|- []F1 --> []F2).
Proof. firstorder. Qed.

Lemma and_right : forall F1 F2 F3,
  (|- F1 --> F2) ->
  (|- F1 --> F3) ->
  (|- F1 --> (F2 /\ F3)).
Proof. firstorder. Qed.

Lemma and_left1 : forall F1 F2 F3,
  (|- F1 --> F3) ->
  (|- (F1 /\ F2) --> F3).
Proof. firstorder. Qed.

Lemma and_left2 : forall F1 F2 F3,
  (|- F2 --> F3) ->
  (|- (F1 /\ F2) --> F3).
Proof. firstorder. Qed.

Lemma imp_id : forall F,
  |- F --> F.
Proof. firstorder. Qed.

Lemma or_next : forall F1 F2 N1 N2,
  (|- (F1 /\ N1) --> F2) ->
  (|- (F1 /\ N2) --> F2) ->
  (|- (F1 /\ (N1 \/ N2)) --> F2).
Proof. firstorder. Qed.

Lemma imp_right : forall F1 F2 F3,
  (|- (F1 /\ F2) --> F3) ->
  (|- F1 --> (F2 --> F3)).
Proof. firstorder. Qed.

Lemma and_assoc_left : forall F1 F2 F3 F4,
  (|- (F1 /\ (F2 /\ F3)) --> F4) ->
  (|- ((F1 /\ F2) /\ F3) --> F4).
Proof. firstorder. Qed.

Lemma and_comm_left : forall F1 F2 F3,
  (|- (F2 /\ F1) --> F3) ->
  (|- (F1 /\ F2) --> F3).
Proof. firstorder. Qed.

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
Definition get_deriv (x:Var) (eqs:list DiffEq)
  : option TermNow :=
  option_map get_term
    (List.find (fun p : DiffEq => let (y, t) := p in
          proj1_sig (Sumbool.bool_of_sumbool
                       (String.string_dec x y))) eqs).

Definition option_map2 {A B C} (f:A->B->C) 
  (a:option A) (b:option B) : option C :=
  match a, b with
    | Some a, Some b => Some (f a b)
    | _, _ => None
  end.

Fixpoint lift_termnow (t:TermNow) : TermNext :=
  match t with
    | VarT x => VarT _ (VarNow x)
    | NatT n => NatT _ n
    | RealT r => RealT _ r
    | PlusT t1 t2 => PlusT _ (lift_termnow t1)
                           (lift_termnow t2)
    | MinusT t1 t2 => MinusT _ (lift_termnow t1)
                             (lift_termnow t2)
    | MultT t1 t2 => MultT _ (lift_termnow t1)
                           (lift_termnow t2)
  end.

Fixpoint lower_termnext (t:TermNext) :
  option TermNow :=
  match t with
    | VarT (VarNow x) => Some (VarT _ x)
    | VarT (VarNext x) => None
    | NatT n => Some (NatT _ n)
    | RealT r => Some (RealT _ r)
    | PlusT t1 t2 =>
      option_map2 (PlusT _) (lower_termnext t1)
                  (lower_termnext t2)
    | MinusT t1 t2 =>
      option_map2 (MinusT _) (lower_termnext t1)
                  (lower_termnext t2)
    | MultT t1 t2 =>
      option_map2 (MultT _) (lower_termnext t1)
                  (lower_termnext t2)
  end.

(* Takes the derivative of a term and substitutes in
   the right hand side of differential equations. If
   a variable has no corresponding differential equation
   then 0 is substituted. This is because variables
   without specified derivatives have a derivative of 0. *)
Fixpoint deriv_term (t:TermNow) (eqs:list DiffEq)
  : option TermNow :=
  match t with
  | VarT x =>
    get_deriv x eqs
  | NatT _ => Some (RealT _ R0)
  | RealT _ => Some (RealT _ R0)
  | PlusT t1 t2 =>
     option_map2 (PlusT _) (deriv_term t1 eqs) (deriv_term t2 eqs)
  | MinusT t1 t2 =>
     option_map2 (MinusT _) (deriv_term t1 eqs) (deriv_term t2 eqs)
  | MultT t1 t2 =>
     option_map2 (PlusT _)
                 (option_map (fun t => MultT _ t t2)
                             (deriv_term t1 eqs))
                 (option_map (MultT _ t1) (deriv_term t2 eqs))
  end.

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
  end.

Fixpoint deriv_formula (F:Formula) (eqs:list DiffEq) :=
  match F with
    | TRUE => TRUE
    | FALSE => FALSE
    | Comp t1 t2 op =>
      match lower_termnext t1, lower_termnext t2 with
        | Some t1, Some t2 =>
          match deriv_term t1 eqs, deriv_term t2 eqs with
            | Some t1, Some t2 =>
              Comp (lift_termnow t1) (lift_termnow t2)
                   (deriv_comp_op op)
            | _, _ => FALSE
          end
        | _, _ => FALSE
      end
    | And F1 F2 => And (deriv_formula F1 eqs)
                       (deriv_formula F2 eqs)
    | _ => FALSE
  end.

(* Now we have a bunch of messy lemmas that we'll use
   to prove the differential induction (diff_ind) rule. *)
Lemma term_is_derivable : forall (f : R -> state) (e : TermNow),
  (forall x, derivable (fun t => f t x)) ->
  derivable (fun t => eval_termnow e (f t)).
Proof.
  intros f e.
  induction e; unfold eval_termnow;
  simpl; intro is_derivable.
    - auto.
    - apply derivable_const.
    - apply derivable_const.
    - apply derivable_plus; auto.
    - apply derivable_minus; auto.
    - apply derivable_mult; auto.
Qed.

Lemma get_deriv_in : forall x eqs t,
  get_deriv x eqs = Some t ->
  List.In (DiffEqC x t) eqs.
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
  ~exists t, List.In (DiffEqC x t) eqs.
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

Lemma term_deriv : forall (f : R -> state) (e e' : TermNow)
  (r : R) (eqs : list DiffEq) is_derivable,
  solves_diffeqs f eqs r is_derivable ->
  deriv_term e eqs = Some e' ->
  forall z, 
    (R0 <= z <= r)%R ->
    derive (fun t => eval_termnow e (f t))
           (term_is_derivable f e is_derivable) z =
    eval_termnow e' (f z).
Proof.
  intros. unfold derive.
  apply (derive_pt_D_in
           (fun t : R => eval_termnow e (f t))
           (fun t : R => eval_termnow e' (f t))).
  generalize dependent e'.
  induction e; intros; simpl in *.
    - destruct (get_deriv v eqs) eqn:?.
      + unfold solves_diffeqs in *.
        unfold derive in *.
        specialize (H v t (get_deriv_in _ _ _ Heqo) z H1).
        apply (derive_pt_D_in
                 (fun t0 : R => f t0 v)
                 (fun t0 : R => eval_termnow t (f t0))) in H.
        inversion H0; subst e'; auto.
      + discriminate.
    - inversion H0; subst e'.
      unfold eval_termnow. simpl. apply Dconst.
    - inversion H0; subst e'.
      unfold eval_termnow. simpl. apply Dconst.
    - destruct (deriv_term e1 eqs); destruct (deriv_term e2 eqs);
      simpl in *; try discriminate. inversion H0; subst e'.
      apply Dadd; auto.
    - destruct (deriv_term e1 eqs); destruct (deriv_term e2 eqs);
      simpl in *; try discriminate. inversion H0; subst e'.
      apply Dminus; auto.
    - destruct (deriv_term e1 eqs); destruct (deriv_term e2 eqs);
      simpl in *; try discriminate. inversion H0; subst e'.
      apply Dmult; auto.
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
  end.

Ltac ineq_trans :=
  match goal with
    | [ H : Rlt ?r1 ?r2 |- Rlt ?r1 ?r3 ]
        => apply (RIneq.Rlt_le_trans r1 r2 r3)
    | [ H : Rle ?r1 ?r2 |- Rle ?r1 ?r3 ]
        => apply (RIneq.Rle_trans r1 r2 r3)
    | [ H : Rlt ?r2 ?r3 |- Rlt ?r1 ?r3 ]
        => apply (RIneq.Rlt_le_trans r1 r2 r3)
    | [ H : Rle ?r2 ?r3 |- Rle ?r1 ?r3 ]
        => apply (RIneq.Rle_trans r1 r2 r3)
    | [ H : eq (Rminus (eval_term _ ?t1 _) (eval_term _ ?t2 _)) ?r3
        |- Rle ?r3 (Rminus (eval_term _ ?t1 _) (eval_term _ ?t2 _)) ]
        => rewrite <- H
    | [ H : eq (Rminus (eval_term _ ?t2 _) (eval_term _ ?t1 _)) ?r3
        |- Rle ?r3 (Rminus (eval_term _ ?t1 _) (eval_term _ ?t2 _)) ]
        => apply RIneq.Rminus_diag_uniq in H;
           symmetry in H; apply RIneq.Rminus_diag_eq in H;
           rewrite <- H
  end.

Ltac deriv_ineq :=
  match goal with
    | [ |- Rle (eval_term _ ?t1 (?f ?r1) - eval_term _ ?t2 (?f _))
            (eval_term _ ?t1 (?f ?r2) - eval_term _ ?t2 (?f _)) ]
        => eapply (derive_increasing_interv_var r1 r2
                     (fun z => eval_term _ t1 (f z) -
                               eval_term _ t2 (f z))%R); eauto
    | [ |- @eq R
               (Rminus (eval_term _ ?t1 (?f _))
                       (eval_term _ ?t2 (?f _)))
               (Rminus (eval_term _ ?t1 (?f _))
                       (eval_term _ ?t2 (?f _)))]
        => eapply (null_derivative_loc
                 (fun z => (eval_term _ t1 (f z) -
                            eval_term _ t2 (f z))%R)); eauto
  end.

Ltac solve_ineq := psatzl R.

Lemma deriv_trace_now : forall f eqs t t' tr,
  eval_formula (VarsAgree (List.map get_var eqs) (f R0)) tr ->
  deriv_term t eqs = Some t' ->
  eval_termnow t (hd tr) = eval_termnow t (f R0).
Proof.
  induction t; simpl; intros; auto.
  - induction eqs.
    + unfold get_deriv in *.
      simpl in *. discriminate.
    + unfold get_deriv in *. simpl in *.
      destruct H. destruct a.
      destruct (String.string_dec v v0); simpl in *.
      * subst v0; unfold eval_comp in *; simpl in *; auto.
      * apply IHeqs; auto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    unfold eval_termnow in *; simpl in *;
      erewrite IHt1; eauto;
      erewrite IHt2; eauto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    unfold eval_termnow in *; simpl in *;
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    unfold eval_termnow in *; simpl in *;
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
Qed.

Lemma deriv_trace_next : forall f eqs (r:R) t t' tr,
  eval_formula (AVarsAgree (List.map get_var eqs) (f r)) tr ->
  deriv_term t eqs = Some t' ->
  eval_termnow t (hd (tl tr)) = eval_termnow t (f r).
Proof.
  induction t; simpl; intros; auto.
  - induction eqs.
    + unfold get_deriv in *.
      simpl in *. discriminate.
    + unfold get_deriv in *. simpl in *.
      destruct H. destruct a.
      destruct (String.string_dec v v0); simpl in *.
      * subst v0; unfold eval_comp in *; simpl in *; auto.
      * apply IHeqs; auto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    unfold eval_termnow in *; simpl in *;
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    unfold eval_termnow in *; simpl in *;
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
  - destruct (deriv_term t1 eqs) eqn:?;
             destruct (deriv_term t2 eqs) eqn:?;
             try discriminate.
    unfold eval_termnow in *; simpl in *;
    erewrite IHt1; eauto;
    erewrite IHt2; eauto.
Qed.

Lemma eval_lift_termnow : forall t tr,
  eval_termnext (lift_termnow t) tr =
  eval_termnow t (hd tr).
Proof.
  induction t; intro tr; auto;
  unfold eval_termnow, eval_termnext;
  simpl; rewrite IHt1; rewrite IHt2;
  auto.
Qed.

Lemma eval_next_lift_termnow : forall t tr,
  eval_termnext (next_term (lift_termnow t)) tr =
  eval_termnow t (hd (tl tr)).
Proof.
  induction t; intro tr; auto;
  unfold eval_termnow, eval_termnext;
  simpl; rewrite IHt1; rewrite IHt2;
  auto.
Qed.

Lemma is_solution_sub : forall f eqs r1 r2,
  (r1 <= r2)%R ->
  is_solution f eqs r2 ->
  is_solution f eqs r1.
Proof.
  intros f eqs r1 r2 Hr Hsol.
  unfold is_solution in *.
  destruct Hsol as [pf Hsol].
  exists pf. unfold solves_diffeqs in *.
  intros x d Hin z Hz.
  apply Hsol; auto.
  psatzl R.
Qed.

Lemma deriv_neg : forall f t1 t2 t1' t2' r eqs is_derivable,
  solves_diffeqs f eqs r is_derivable ->
  deriv_term t1 eqs = Some t1' ->
  deriv_term t2 eqs = Some t2' ->
  (forall st,
     (R0 <= eval_termnow t1' st -
      eval_termnow t2' st)%R) ->
  forall t,
    (R0 <= t <= r)%R ->
    (R0 <=
    derive_pt
      (fun z : R => eval_termnow t1 (f z) - eval_termnow t2 (f z))
      t (derivable_pt_minus _ _ t
           (term_is_derivable _ _ is_derivable t)
           (term_is_derivable _ _ is_derivable t)))%R.
Proof.
  intros f t1 t2 t1' t2' r diffeqs is_derivable Hsol Ht1 Ht2 Hineq
         t Ht.
  specialize (Hineq (f t)).
  erewrite <- term_deriv in Hineq; eauto.
  erewrite <- term_deriv in Hineq; eauto.
  unfold derive in Hineq.
  rewrite <- derive_pt_minus in Hineq.
  apply Hineq.
Qed.

Lemma eval_comp_ind : forall Hyps eqs
                             t1 t2 t1' t2' op,
  deriv_term t1 eqs = Some t1' ->
  deriv_term t2 eqs = Some t2' ->
  is_st_formula Hyps = true ->
  (|- (Hyps /\ Continuous eqs) --> next Hyps) ->
  (|- Hyps --> (Comp (lift_termnow t1') (lift_termnow t2') (deriv_comp_op op))) ->
  (|- (Comp (lift_termnow t1) (lift_termnow t2) op /\ Hyps /\
       Continuous eqs) -->
                              Comp (next_term (lift_termnow t1))
                                   (next_term (lift_termnow t2)) op).
Proof.
  intros Hyps eqs t1 t2 t1' t2' op Ht1 Ht2 Hst Hhyps Hind.
  simpl in *; unfold eval_comp in *; simpl in *.
  intros tr H; destruct H as [Hbase [HhypsI Hcont] ].

  destruct Hcont as [r [f Hcont] ];
    destruct Hcont as [Hr [Hsol [? ?] ] ].
  do 2 rewrite eval_lift_termnow in Hbase; auto.
  do 2 erewrite deriv_trace_now with (tr:=tr) in Hbase; eauto.
  repeat rewrite eval_next_lift_termnow.
  erewrite deriv_trace_next with (tr:=tr); eauto.
  erewrite deriv_trace_next with (tr:=tr); eauto.
  unfold is_solution in *. destruct Hsol as [pf Hsol].
  simpl in *. simpl in *. unfold eval_termnow, eval_termnext in *.
  destruct op; simpl in *; try (apply RIneq.Rle_le_eq; split);
  normalize_ineq_goal; normalize_ineq_hyp Hbase;
  ineq_trans; auto;
  deriv_ineq; intros; try solve_ineq;
  try (pose proof (term_deriv f (t1 - t2) (t1' - t2')
                              r eqs pf Hsol)
        as Hterm;
       instantiate (1:=term_is_derivable f (t1 - t2) pf));
  try (pose proof (term_deriv f (t2 - t1) (t2' - t1')
                              r eqs pf Hsol)
        as Hterm;
       instantiate (1:=term_is_derivable f (t2 - t1) pf));
  simpl in *; try rewrite Ht1 in Hterm; try rewrite Ht2 in Hterm;
  try specialize (Hterm (eq_refl _));
  try unfold derive in Hterm;
  try rewrite Hterm; try solve_ineq;
  try specialize (Hhyps (Cons _ (hd tr)
                              (Cons _ (f t) (tl (tl tr)))));
  simpl in *; try apply next_formula_tl in Hhyps; auto;
  try specialize (Hind (Cons _ (f t) tr)); simpl in *;
  try apply st_formula_hd
    with (tr2:=Cons _ (f t) tr) (F:=Hyps)
    in Hhyps; auto;
  try specialize (Hind Hhyps);
  repeat rewrite eval_lift_termnow in Hind; auto;
  unfold eval_termnow in *; simpl in *; try solve_ineq;
  try (split;
        [ eapply st_formula_hd; eauto |
          exists t; exists f; repeat split; try solve_ineq;
          solve [apply is_solution_sub with (r2:=r);
                  try solve_ineq; unfold is_solution; eauto |
                 apply st_formula_hd with (tr1:=tr); auto;
                 apply st_formula_varsagree |
                 apply avarsagree_next]
      ]).
Qed.

Lemma lower_st_term : forall t,
  is_st_term t = true ->
  exists t',
    eq (lower_termnext t) (Some t').
Proof.
  induction t; intro Hst; simpl in *.
  - destruct v; try discriminate.
    exists (VarT _ v); auto.
  - exists (NatT _ n); auto.
  - exists (RealT _ r); auto.
  - apply andb_prop in Hst; intuition.
    destruct H1; destruct H2.
    exists (x + x0); rewrite H1;
    rewrite H2; auto.
  - apply andb_prop in Hst; intuition.
    destruct H1; destruct H2.
    exists (x - x0); rewrite H1;
    rewrite H2; auto.
  - apply andb_prop in Hst; intuition.
    destruct H1; destruct H2.
    exists (x * x0); rewrite H1;
    rewrite H2; auto.
Qed.

Lemma lift_lower_term : forall t t',
  lower_termnext t = Some t' ->
  lift_termnow t' = t.
Proof.
  induction t; intros t Hlower;
  simpl in *;
  try solve [inversion Hlower; auto |
             destruct (lower_termnext t1);
               destruct (lower_termnext t2);
               try discriminate;
               simpl in *; inversion Hlower;
               simpl; erewrite <- IHt1; eauto;
               erewrite <- IHt2; eauto |
             destruct v; try discriminate;
             inversion Hlower; auto].
Qed.

Lemma diff_ind : forall Hyps G cp F,
  is_st_formula G = true ->
  is_st_formula Hyps = true ->
  (|- (Hyps /\ Continuous cp) --> next Hyps) ->
  (|- F --> Continuous cp) ->
  (|- F --> G) ->
  (|- F --> Hyps) ->
  (|- Hyps --> deriv_formula G cp) ->
  (|- F --> next G).
Proof.
  intros Hyps G; generalize dependent Hyps;
  induction G;
    intros Hyps cp F HstG HstH Hhyps Hcont Hbase HhypsF Hind;
  simpl in *; intros; eauto;
  try discriminate; try solve [exfalso; eapply Hind; eauto].
  apply andb_prop in HstG; destruct HstG as [HstG1 HstG2].
  destruct (lower_st_term t HstG1) as [t' Ht'].
  destruct (lower_st_term t0 HstG2) as [t0' Ht0'].
  rewrite Ht' in Hind; rewrite Ht0' in Hind.
  destruct (deriv_term t' cp) eqn:?;
           destruct (deriv_term t0' cp) eqn:?;
  try solve [simpl in *; exfalso; eapply Hind; eauto].
  simpl in *. pose proof (Hcont tr H).
  destruct H0 as [r [f Hf] ].
  decompose [and] Hf.
  pose proof (eval_comp_ind Hyps cp t' t0'
                            t1 t2 c Heqo Heqo0 HstH) as Hcomp.
  rewrite lift_lower_term with (t:=t) (t':=t') in Hcomp; auto.
  rewrite lift_lower_term with (t:=t0) (t':=t0') in Hcomp; auto.
  apply Hcomp; auto.
  repeat split; intuition.
  - apply HhypsF; auto.
  - apply Hcont; auto.
  - split.
    + eapply IHG1; eauto.
      * apply andb_prop in HstG; intuition.
      * apply Hbase; auto.
      * apply Hind; auto.
    + eapply IHG2; eauto.
      * apply andb_prop in HstG; intuition.
      * apply Hbase; auto.
      * apply Hind; auto.
Qed.

Lemma zero_deriv : forall G cp F x,
  List.In (DiffEqC x 0) cp ->
  (|- F --> Continuous cp) ->
  (|- (F /\ x! = x) --> G) ->
  (|- F --> G).
Proof.
induction cp.  intros F x Hin Hcont Hsuf.
- simpl in *. contradiction.
-  intros F x Hin Hcont Hsuf. simpl in Hin. destruct Hin.
+ simpl in *. intros. apply Hsuf.
split. auto. specialize (Hcont tr H0).
destruct Hcont as [r [f Hf] ].
decompose [and] Hf.
unfold eval_comp in *. simpl in *.
destruct a. simpl in *. inversion H.
subst x. subst t. unfold is_solution in *.
unfold solves_diffeqs in *.
destruct H3 as [H10]. specialize (H3 v 0).
simpl in *. rewrite H2. rewrite H4.
rewrite (null_derivative_loc (fun t => f t v) R0 r).
auto.
* intros.  unfold derivable in H10. apply derivable_continuous_pt.
apply H10.
* unfold derive in H2. firstorder. apply H3. auto. psatzl R.
* intuition. 
+ apply IHcp with (x:=x).
apply H. 
simpl in *. intros. specialize (Hcont tr H0).
destruct Hcont as [r [f Hf]]. decompose [and] Hf.
exists r. exists f. intuition.
unfold is_solution in *.
destruct H9.
unfold solves_diffeqs in *.
simpl in *.
exists x0. intros. apply H9; auto.
apply Hsuf. Qed.

Fixpoint extract_vars_term (t:TermNext) : list Var :=
  match t with
    | NatT _ => nil
    | RealT _ => nil
    | VarT (VarNow x) => cons x nil
    | VarT (VarNext x) => cons x nil
    | PlusT t1 t2 => List.app
                       (extract_vars_term t1)
                       (extract_vars_term t2)
    | MinusT t1 t2 => List.app
                        (extract_vars_term t1)
                        (extract_vars_term t2)
    | MultT t1 t2 => List.app
                       (extract_vars_term t1)
                       (extract_vars_term t2)
  end.

Fixpoint extract_vars (F:Formula) : list Var :=
  match F with
    | Comp t1 t2 _ =>
      List.app (extract_vars_term t1) (extract_vars_term t2)
    | And F1 F2 =>
      List.app (extract_vars F1) (extract_vars F2)
    | Or F1 F2 =>
      List.app (extract_vars F1) (extract_vars F2)
    | Imp F1 F2 =>
      List.app (extract_vars F1) (extract_vars F2)
    | _ => nil
  end.

Lemma extract_vars_term_0 : forall t eqs tr,
  is_st_term t = true ->
  (forall x, List.In x (extract_vars_term t) ->
             List.In (DiffEqC x 0) eqs) ->
  eval_formula (Continuous eqs) tr ->
  eval_termnext (next_term t) tr = eval_termnext t tr.
Proof.
  induction t; simpl;
  intros eqs tr Hst Hin Heval; auto;
  try solve [
        simpl in *; unfold eval_termnext; simpl;
    apply andb_prop in Hst; destruct Hst;
    erewrite IHt1; eauto; try (erewrite IHt2; eauto);
    intros; apply Hin; apply List.in_or_app; auto;
    intros; apply Hin; apply List.in_or_app; auto].
  - destruct v; try discriminate.
    specialize (Hin v (or_introl (Logic.eq_refl _))).
    pose proof (zero_deriv (v!=v) eqs (Continuous eqs) v Hin (imp_id _)).
    apply H; auto; simpl; intros; intuition.
Qed.

Lemma extract_vars_0 : forall F H eqs,
  is_st_formula H = true ->
  (forall x, List.In x (extract_vars H) ->
             List.In (DiffEqC x 0) eqs) ->
  (|- F --> Continuous eqs) ->
  (|- (F /\ next H) --> H) /\ (|- (F /\ H) --> next H).
Proof.
  induction H; intros eqs Hst Hin Hcont;
  simpl in *; intros; intuition; try discriminate.
  - unfold eval_comp in *; simpl.
    apply andb_prop in Hst; destruct Hst.
    rewrite <- extract_vars_term_0 with (eqs:=eqs) (t:=t); auto;
    try rewrite <- extract_vars_term_0 with (eqs:=eqs) (t:=t0); auto;
      auto; try apply Hcont; auto; intros; apply Hin;
      apply List.in_or_app; auto.
  - unfold eval_comp in *; simpl.
    apply andb_prop in Hst; destruct Hst.
    rewrite extract_vars_term_0 with (eqs:=eqs) (t:=t); auto;
    try rewrite extract_vars_term_0 with (eqs:=eqs) (t:=t0); auto.
    intros; apply Hin; apply List.in_or_app; auto.
    apply Hcont; auto.
    intros; apply Hin; apply List.in_or_app; auto.
    apply Hcont; auto.
  - eapply IHFormula1; eauto.
    apply andb_prop in Hst; intuition.
    intros; apply Hin; apply List.in_or_app; auto.
  - eapply IHFormula2; eauto.
    apply andb_prop in Hst; intuition.
    intros; apply Hin; apply List.in_or_app; auto.
  - eapply IHFormula1; eauto.
    apply andb_prop in Hst; intuition.
    intros; apply Hin; apply List.in_or_app; auto.
  - eapply IHFormula2; eauto.
    apply andb_prop in Hst; intuition.
    intros; apply Hin; apply List.in_or_app; auto.
  - left. eapply IHFormula1; eauto.
    apply andb_prop in Hst; intuition.
    intros; apply Hin; apply List.in_or_app; auto.
  - right. eapply IHFormula2; eauto.
    apply andb_prop in Hst; intuition.
    intros; apply Hin; apply List.in_or_app; auto.
  - left. eapply IHFormula1; eauto.
    apply andb_prop in Hst; intuition.
    intros; apply Hin; apply List.in_or_app; auto.
  - right. eapply IHFormula2; eauto.
    apply andb_prop in Hst; intuition.
    intros; apply Hin; apply List.in_or_app; auto.
  - eapply IHFormula2; eauto; intuition.
    apply andb_prop in Hst; intuition.
    apply H4. eapply IHFormula1; eauto.
    apply andb_prop in Hst; intuition.
    intros; apply Hin; apply List.in_or_app; auto.
  - eapply IHFormula2; eauto; intuition.
    apply andb_prop in Hst; intuition.
    apply H4. eapply IHFormula1; eauto.
    apply andb_prop in Hst; intuition.
    intros; apply Hin; apply List.in_or_app; auto.
Qed.

Definition var_eqb (s1 s2:Var) : bool :=
  proj1_sig (Sumbool.bool_of_sumbool
               (String.string_dec s1 s2)).

Lemma var_eqb_ok : forall s1 s2,
  var_eqb s1 s2 = true ->
  s1 = s2.
Proof.
  unfold var_eqb; simpl; intros.
  destruct (String.string_dec s1 s2);
    try discriminate; auto.
Qed.  

Definition diffeq_eqb (x:Var) (n:nat) (d:DiffEq) : bool :=
  andb (var_eqb (get_var d) x)
       (match get_term d with
          | NatT n' => beq_nat n n'
          | _ => false
        end).

Fixpoint term_unchanged (t:TermNext) (eqs:list DiffEq) : bool :=
  match t with
    | VarT (VarNow x) =>
      List.existsb (diffeq_eqb x 0) eqs
    | VarT (VarNext _) => false
    | RealT _ => true
    | NatT _ => true
    | PlusT t1 t2 =>
      andb (term_unchanged t1 eqs) (term_unchanged t2 eqs)
    | MinusT t1 t2 =>
      andb (term_unchanged t1 eqs) (term_unchanged t2 eqs)
    | MultT t1 t2 =>
      andb (term_unchanged t1 eqs) (term_unchanged t2 eqs)
  end.

Fixpoint formula_unchanged (F:Formula) (eqs:list DiffEq) : bool :=
  match F with
    | Comp t1 t2 _ =>
      andb (term_unchanged t1 eqs) (term_unchanged t2 eqs)
    | And F1 F2 =>
      andb (formula_unchanged F1 eqs) (formula_unchanged F2 eqs)
    | Or F1 F2 =>
      andb (formula_unchanged F1 eqs) (formula_unchanged F2 eqs)
    | Imp F1 F2 =>
      andb (formula_unchanged F1 eqs) (formula_unchanged F2 eqs)
    | _ => false
  end.

Lemma diffeq_eqb_ok : forall v e d,
  diffeq_eqb v e d = true ->
  d = DiffEqC v e.
Proof.
  intros v e d Heq.
  unfold diffeq_eqb in *. simpl in *.
  apply andb_prop in Heq; destruct Heq.
  apply var_eqb_ok in H.
  destruct d as [v' t]; simpl in *.
  destruct t; try discriminate.
  apply beq_nat_true in H0.
  subst e; subst v; auto.
Qed.

Lemma term_unchanged_list_in : forall t eqs,
  term_unchanged t eqs = true ->
  forall x, List.In x (extract_vars_term t) ->
            List.In (DiffEqC x 0) eqs.
Proof.
  induction t; simpl; intros eqs Hsame x Hin;
  try contradiction;
  try solve [apply List.in_app_or in Hin;
              apply andb_prop in Hsame;
              intuition].
  - destruct v; try discriminate.
    apply List.existsb_exists in Hsame.
    destruct Hsame as [d [Hd1 Hd2] ].
    apply diffeq_eqb_ok in Hd2.
    subst d. simpl in *. intuition.
    subst v; auto.
Qed.

Lemma formula_unchanged_list_in : forall F eqs,
  formula_unchanged F eqs = true ->
  forall x, List.In x (extract_vars F) ->
            List.In (DiffEqC x 0) eqs.
Proof.
  induction F; simpl; intros eqs Hsame x Hin;
  try discriminate;
  try solve [apply List.in_app_or in Hin;
              apply andb_prop in Hsame;
              intuition].
  - apply List.in_app_or in Hin.
    apply andb_prop in Hsame. destruct Hsame.
    destruct Hin.
    + apply term_unchanged_list_in with (t:=t); auto.
    + apply term_unchanged_list_in with (t:=t0); auto.
Qed.

Lemma list_in_fold_right : forall A B (eqs:list A) (l:list B) e,
  List.fold_right and True
                  (List.map (fun x => List.In e eqs)
                            l) ->
  (forall x, List.In x l ->
             List.In e eqs).
Proof.
  intros A B eqs l e Hfold x Hin.
  induction l; simpl in *; try contradiction.
  firstorder.
Qed.

Lemma diff_ind_imp : forall F H G eqs,
  is_st_formula G = true ->
  is_st_formula H = true ->
  formula_unchanged H eqs = true ->
  (|- (F /\ H) --> G) ->
  (|- F --> Continuous eqs) ->
  (|- H --> deriv_formula G eqs) ->
  (|- F --> (next H --> next G)).
Proof.
  intros F H G eqs HstG HstH Hin Hinit Hcont Hind.
  apply imp_right.
  assert (|- (F /\ next H) --> H) by
      (eapply extract_vars_0; auto;
       apply formula_unchanged_list_in; auto).
  apply diff_ind with (Hyps:=H) (cp:=eqs); auto.
  - apply and_comm_left. eapply extract_vars_0; auto.
    + apply formula_unchanged_list_in; eauto.
    + apply imp_id.      
  - apply and_left1; auto.
  - apply imp_trans with (F2:=F/\H); auto.
    apply and_right; auto. apply and_left1.
    apply imp_id.
Qed.

Fixpoint zero_deriv_term (t:TermNext) (eqs:list DiffEq) :=
  match t with
    | VarT (VarNext x) =>
      if List.existsb (diffeq_eqb x 0) eqs
      then VarT _ (VarNow x)
      else t
    | PlusT t1 t2 =>
      PlusT _ (zero_deriv_term t1 eqs)
            (zero_deriv_term t2 eqs)
    | MinusT t1 t2 =>
      MinusT _ (zero_deriv_term t1 eqs)
             (zero_deriv_term t2 eqs)
    | MultT t1 t2 =>
      MultT _ (zero_deriv_term t1 eqs)
            (zero_deriv_term t2 eqs)
    | _ => t
  end.

Fixpoint zero_deriv_formula (F:Formula) (eqs:list DiffEq) :=
  match F with
    | Comp t1 t2 op => Comp (zero_deriv_term t1 eqs)
                            (zero_deriv_term t2 eqs) op
    | And F1 F2 => And (zero_deriv_formula F1 eqs)
                       (zero_deriv_formula F2 eqs)
    | Or F1 F2 => Or (zero_deriv_formula F1 eqs)
                       (zero_deriv_formula F2 eqs)
    | _ => F
  end.

Lemma zero_deriv_term_ok : forall t eqs F,
  (|- F --> Continuous eqs) ->
  (|- F --> (zero_deriv_term t eqs) = t).
Proof.
  intros t eqs.
  induction t; intros F Hcont;
  try solve [simpl; unfold eval_comp; simpl; intuition |
            simpl in *; unfold eval_comp,
                        eval_termnext in *; simpl;
            simpl; intros tr HF;
            erewrite IHt1; eauto; erewrite IHt2; eauto].
  - destruct v.
    + simpl; unfold eval_comp; auto.
    + unfold zero_deriv_term.
      destruct (List.existsb (diffeq_eqb v 0) eqs) eqn:?.
      * apply List.existsb_exists in Heqb.
        destruct Heqb as [d [Hd1 Hd2] ].
        apply diffeq_eqb_ok in Hd2. subst d.
        apply zero_deriv with (x:=v) (cp:=eqs); auto.
        simpl; unfold eval_comp; simpl;
        intuition.
      * simpl; unfold eval_comp; simpl; intuition.
Qed.

Lemma zero_deriv_formula_ok : forall F G eqs,
  (|- F --> Continuous eqs) ->
  (|- F --> zero_deriv_formula G eqs) ->
  (|- F --> G).
Proof.
  simpl; intros F G eqs Hcont Hzero tr HF.
  specialize (Hzero tr HF).
  induction G; simpl in *; auto.
  - pose proof (zero_deriv_term_ok t eqs).
    pose proof (zero_deriv_term_ok t0 eqs).
    specialize (H F Hcont). specialize (H0 F Hcont).
    simpl in *. unfold eval_comp in *. simpl in *.
    rewrite <- H; auto. rewrite <- H0; auto.
  - split; try apply IHG1;
    try apply IHG2; intuition.
  - destruct Hzero.
    + left; apply IHG1; auto.
    + right; apply IHG2; auto.
Qed.

Close Scope HP_scope.