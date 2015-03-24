Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Classes.RelationClasses.
Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import TLA.ArithFacts.
Import LibNotations.
Require Import Coq.Lists.ListSet.

Open Scope HP_scope.
Open Scope string_scope.

Definition World (dvars : list Var)
           (world : list DiffEq) : Formula :=
  Continuous (("t"'::=--1)::world ++
                          (List.map
                             (fun x => x ' ::= 0) dvars))%list.

Definition Discr (cvars : list Var)
           (Prog : Formula) (d : R) : Formula :=
  Prog //\\ "t"! <= d //\\ Unchanged cvars.

Definition list_union (a b : list Var) : list Var :=
  set_union String.string_dec a b.

Definition Next (dvars cvars : list Var)
           (Prog: Formula) (world : list DiffEq)
           (WConstraint : Formula) (d : R) :=
       ((World dvars world //\\ WConstraint) \\//
         Discr cvars Prog d)
  \\// Unchanged ("t"::list_union dvars cvars)%list.

Definition sysD (dvars cvars : list Var)
           (Init Prog: Formula) (world : list DiffEq)
           (WConstraint : Formula) (d : R) : Formula :=
  ("t" <= d //\\ Init) //\\
     [](Next dvars cvars Prog world WConstraint d //\\ 0 <= "t").

Record SysRec (cvars : list Var) (world : list DiffEq)
       (maxTime : R)
: Type := Sys
{ dvars : list Var
; Init : Formula
; Prog: Formula
; WConstraint : Formula }.

Arguments dvars {_ _ _} _.
Arguments Init {_ _ _} _.
Arguments Prog {_ _ _} _.
Arguments WConstraint {_ _ _} _.

Definition SysD {cvars world maxTime}
           (s : SysRec cvars world maxTime)
: Formula :=
  sysD s.(dvars) cvars s.(Init) s.(Prog) world s.(WConstraint)
                                                   maxTime.

Definition SysCompose {c w m} (a b : SysRec c w m) :
  SysRec c w m :=
{| dvars := list_union a.(dvars) b.(dvars)
 ; Init  := a.(Init) //\\ b.(Init)
 ; Prog  := a.(Prog) //\\ b.(Prog)
 ; WConstraint := a.(WConstraint) //\\ b.(WConstraint)
 |}.

Ltac tlaRevert := first [ apply landAdj | apply lrevert ].

Lemma discr_indX : forall P A IndInv,
    is_st_formula IndInv ->
    P |-- [] A ->
    P |-- IndInv ->
    A //\\ IndInv |-- next IndInv ->
    P |-- []IndInv.
Proof.
  intros.
  intro. simpl; intros.
  specialize (H0 _ H3).
  induction n.
  { simpl. intros; eapply H1. auto. }
  { simpl. rewrite Stream.nth_suf_tl.
    apply next_formula_tl; auto.
    apply H2; auto.
    split; auto. }
Qed.

Lemma Always_now : forall P I,
  P |-- []I ->
  P |-- I.
Proof.
  breakAbstraction.
  intros P I H tr HP.
  apply (H tr HP 0).
Qed.

Ltac decompose_hyps :=
  repeat rewrite land_lor_distr_R;
  repeat rewrite land_lor_distr_L;
  repeat apply lorL.

Definition TimeBound d : Formula := 0 <= "t" <= d.

Lemma Sys_bound_t : forall P cvars w d (a : SysRec cvars w d),
    P |-- SysD a ->
    P |-- []TimeBound d.
Proof.
  intros. unfold SysD in *.
  rewrite <- Always_and with (P:=0 <= "t") (Q:="t" <= d). tlaSplit.
  - rewrite H. unfold sysD. rewrite <- Always_and. tlaAssume.
  - apply discr_indX
    with (A:=Next a.(dvars) cvars a.(Prog) w a.(WConstraint) d).
    + tlaIntuition.
    + rewrite H. unfold sysD. rewrite <- Always_and. tlaAssume.
    + rewrite H. unfold sysD. tlaAssume.
    + unfold Next. decompose_hyps.
      * eapply diff_ind with (Hyps:=TRUE);
        try solve [tlaIntuition].
        { unfold World. tlaAssume. }
        { solve_linear. }
      * solve_linear.
      * solve_linear.
Qed.

Definition InvariantUnder (vars : list Var) (F : Formula) : Prop :=
  F //\\ Unchanged vars |-- next F.

Definition all_in {T} (l1 l2 : list T) :=
  forall x, List.In x l1 -> List.In x l2.

Theorem all_in_dec_ok : forall (l1 l2 : list Var),
  List.forallb
    (fun x => if List.in_dec String.string_dec x l2
              then true else false) l1 = true ->
  all_in l1 l2.
Proof.
  red. intros.
  rewrite List.forallb_forall in H.
  apply H in H0.
  destruct (List.in_dec String.string_dec x l2);
    auto; discriminate.
Qed.

Instance Reflexive_all_in {T} : Reflexive (@all_in T).
Proof. red; red; tauto. Qed.

Instance Transitive_all_in {T} : Transitive (@all_in T).
Proof. unfold all_in; red; intros. eauto. Qed.

Lemma VarsAgree_val : forall x xs s,
  List.In x xs ->
  VarsAgree xs s |-- x = (s x).
Proof.
  induction xs.
  - tlaIntuition.
  - intros. simpl in H. destruct H.
    + subst a. charge_assumption.
    + rewrite <- IHxs.
      * charge_assumption.
      * auto.
Qed.

Lemma VarsAgree_weaken : forall xs xs' s,
  all_in xs xs' ->
  VarsAgree xs' s |-- VarsAgree xs s.
Proof.
  induction xs.
  - tlaIntuition.
  - intros. simpl VarsAgree. restoreAbstraction.
    rewrite <- VarsAgree_val with (x:=a) (xs:=xs').
    + charge_split.
      * charge_tauto.
      * rewrite IHxs; try charge_tauto.
        unfold all_in in *. intuition.
    + intuition.
Qed.

Lemma VarsAgree_app : forall xs1 xs2 s,
  VarsAgree (xs1 ++ xs2) s -|- VarsAgree xs1 s //\\ VarsAgree xs2 s.
Proof.
  induction xs1; intros.
  - tlaIntuition. split; charge_tauto.
  - simpl VarsAgree. restoreAbstraction.
    rewrite IHxs1. split; charge_tauto.
Qed.

Lemma AVarsAgree_val : forall x xs s,
  List.In x xs ->
  AVarsAgree xs s |-- x! = (s x).
Proof.
  induction xs.
  - tlaIntuition.
  - intros. simpl in H. destruct H.
    + subst a. charge_assumption.
    + rewrite <- IHxs.
      * charge_assumption.
      * auto.
Qed.

Lemma AVarsAgree_weaken : forall xs xs' s,
  all_in xs xs' ->
  AVarsAgree xs' s |-- AVarsAgree xs s.
Proof.
  induction xs.
  - tlaIntuition.
  - intros. simpl AVarsAgree. restoreAbstraction.
    rewrite <- AVarsAgree_val with (x:=a) (xs:=xs').
    + charge_split.
      * charge_tauto.
      * rewrite IHxs; try charge_tauto.
        unfold all_in in *. intuition.
    + intuition.
Qed.

Lemma AVarsAgree_app : forall xs1 xs2 s,
  AVarsAgree (xs1 ++ xs2) s -|- AVarsAgree xs1 s //\\ AVarsAgree xs2 s.
Proof.
  induction xs1; intros.
  - tlaIntuition. split; charge_tauto.
  - simpl AVarsAgree. restoreAbstraction.
    rewrite IHxs1. split; charge_tauto.
Qed.

Lemma exists_entails : forall T F1 F2,
  (forall x, F1 x |-- F2 x) ->
  Exists x : T, F1 x |-- Exists x : T, F2 x.
Proof.
  tlaIntuition.  destruct H0.
  exists x. intuition.
Qed.

Lemma all_in_map : forall A B (l l':list A) (f:A->B),
  all_in l l' ->
  all_in (List.map f l) (List.map f l').
Proof.
  unfold all_in; simpl; intros.
  apply List.in_map_iff.
  apply List.in_map_iff in H0. destruct H0.
  exists x0. intuition.
Qed.

Lemma World_weaken : forall dvars dvars' w w',
    all_in dvars dvars' ->
    all_in w w' ->
    World dvars' w' |-- World dvars w.
Proof.
  intros. unfold World, Continuous.
  repeat (apply exists_entails; intros).
  repeat charge_split; try solve [tlaAssume].
  - breakAbstraction; unfold is_solution; intros;
    intuition.
    match goal with
    | [ H : context[solves_diffeqs] |- _ ]
        => let pf := fresh "pf" in
           let Hcont := fresh "Hcont" in
           destruct H as [pf Hcont]; exists pf
    end.
    unfold solves_diffeqs in *; intros.
    erewrite Hcont; eauto.
    simpl in *; intuition. right.
    apply List.in_or_app.
    match goal with
    | [ H : _ |- _ ]
      => apply List.in_app_or in H
    end; intuition. right.
    apply List.in_map_iff.
    match goal with
    | [ H : _ |- _ ]
      => let x := fresh "x" in
         apply List.in_map_iff in H;
           destruct H as [x ?]; exists x
    end; intuition.
  - fold VarsAgree. simpl VarsAgree.
    repeat rewrite List.map_app with (f:=get_var).
    repeat rewrite VarsAgree_app. charge_split.
    + erewrite VarsAgree_weaken with (xs:=List.map get_var w).
      * tlaIntuition.
      * apply all_in_map; auto.
    + erewrite VarsAgree_weaken with
      (xs:=List.map get_var
                    (List.map (fun x1 : Var => x1 '  ::= 0)
                              dvars0))
        (xs':=List.map get_var
                       (List.map (fun x1 : Var => x1 '  ::= 0)
                                 dvars')).
      * tlaIntuition.
      * repeat apply all_in_map; auto.
  - fold AVarsAgree. simpl AVarsAgree.
    repeat rewrite List.map_app with (f:=get_var).
    repeat rewrite AVarsAgree_app. charge_split.
    + erewrite AVarsAgree_weaken with (xs:=List.map get_var w).
      * tlaIntuition.
      * apply all_in_map; auto.
    + erewrite AVarsAgree_weaken with
      (xs:=List.map get_var
                    (List.map (fun x1 : Var => x1 '  ::= 0)
                              dvars0))
        (xs':=List.map get_var
                       (List.map (fun x1 : Var => x1 '  ::= 0)
                                 dvars')).
      * tlaIntuition.
      * repeat apply all_in_map; auto.
Qed.

Lemma Unchanged_In : forall ls l,
    List.In l ls ->
    Unchanged ls |-- l! = l.
Proof.
  induction ls; simpl.
  { inversion 1. }
  { intros. destruct H; restoreAbstraction.
    { subst. charge_tauto. }
    { rewrite IHls; eauto. charge_tauto. } }
Qed.

Lemma Unchanged_weaken : forall vars' vars,
    all_in vars' vars ->
    Unchanged vars |-- Unchanged vars'.
Proof.
  induction vars'.
  { intros. tlaIntuition. }
  { intros. red in H.
    simpl. restoreAbstraction.
    tlaSplit.
    { apply Unchanged_In. apply H. left. reflexivity. }
    { eapply IHvars'. red. intros. eapply H. right. assumption. } }
Qed.

Lemma Discr_weaken : forall cvars cvars' P P' d d',
    all_in cvars cvars' ->
    P' |-- P ->
    (d >= d')%R ->
    Discr cvars' P' d' |-- Discr cvars P d.
Proof.
  unfold Discr. intros.
  rewrite Unchanged_weaken; eauto. solve_linear.
Qed.
Print Sys.
Theorem Sys_weaken : forall dvars dvars' cvars cvars'
                            I I' P P' w w' WC WC' d d',
  all_in dvars dvars' ->
  all_in cvars cvars' ->
  I' |-- I ->
  P' |-- P ->
  all_in w w' ->
  WC' |-- WC ->
  (d >= d')%R ->
  SysD (Sys cvars' w' d' dvars' I' P' WC') |--
  SysD (Sys cvars w d dvars I P WC).
Proof.
  do 14 intro.
  intros Hdvars Hcvars HI HP Hw HWC Hd.
  unfold SysD, sysD, Init, Next.
  simpl. restoreAbstraction.
  apply lrevert.
  rewrite HI; clear HI.
  tlaIntro.
  repeat tlaSplit; try tlaAssume.
  { do 2 apply landL1. clear - Hd. solve_linear. }
  { tlaRevert.
    apply always_imp. tlaIntro.
    repeat tlaSplit; try tlaAssume.
    rewrite landC. tlaRevert. apply forget_prem.
    tlaIntro. unfold Next.
    erewrite World_weaken by eauto.
    rewrite HWC.
    erewrite Discr_weaken by eauto.
    erewrite Unchanged_weaken. tlaAssume.
    revert Hdvars Hcvars.
    clear.
    unfold all_in. intros. specialize (Hdvars x).
    specialize (Hcvars x).
    revert H. simpl. intro Hin.
    unfold list_union in *. apply set_union_elim in Hin.
    destruct Hin.
    - apply set_union_intro1. intuition.
    - apply set_union_intro2. intuition. }
Qed.

Ltac sys_apply_with_weaken H :=
  eapply imp_trans; [ | apply H ];
  eapply Sys_weaken;
  try solve [ apply all_in_dec_ok ; reflexivity
            | apply imp_id
            | reflexivity ].

Theorem Sys_by_induction :
  forall P A dvars cvars Init Prog Inv IndInv w WC (d:R),
  is_st_formula IndInv ->
  P |-- SysD (Sys cvars w d dvars Init Prog WC) ->
  P //\\ Init |-- IndInv ->
  P |-- [] A ->
  A //\\ IndInv //\\ TimeBound d |-- Inv ->
  InvariantUnder ("t"::list_union dvars cvars)%list IndInv ->
  A //\\ IndInv //\\ World dvars w //\\ WC |-- next IndInv ->
  A //\\ IndInv //\\ TimeBound d //\\ next (TimeBound d)
          //\\ Discr cvars Prog d |-- next IndInv ->
  P |-- [] Inv.
Proof.
  intros P A dvars cvars Init Prog Inv IndInv w WC d
         Hst Hsys Hinit Ha Hinv InvUnder Hw Hdiscr.
  tlaAssert ([]TimeBound d).
  - eapply Sys_bound_t. rewrite Hsys. tlaAssume.
  - tlaIntro. tlaAssert ([]IndInv).
    + tlaAssert ([]A); [rewrite Ha; tlaAssume | tlaIntro ].
      tlaAssert (SysD (Sys cvars w d dvars Init Prog WC));
        [ rewrite Hsys; tlaAssume | tlaIntro ].
      apply discr_indX with
      (A:=Next dvars cvars Prog w WC d //\\
               TimeBound d //\\ next (TimeBound d) //\\ A).
        { assumption. }
        { unfold SysD, sysD, Next. simpl.
          restoreAbstraction.
          repeat rewrite <- Always_and.
          repeat tlaSplit.
          - tlaAssume.
          - tlaAssume.
          - rewrite always_st with (Q:=TimeBound d);
            (unfold TimeBound; simpl next;
            repeat rewrite <- Always_and; charge_tauto)
            || tlaIntuition.
          - rewrite always_st with (Q:=TimeBound d);
            (unfold TimeBound; simpl next;
            repeat rewrite <- Always_and; charge_tauto)
            || tlaIntuition.
          - tlaAssume. }
        { rewrite <- Hinit. unfold SysD. charge_tauto. }
        { unfold Next. decompose_hyps.
          - rewrite <- Hw. charge_tauto.
          - rewrite <- Hdiscr. charge_tauto.
          - unfold InvariantUnder in *. rewrite <- InvUnder.
            charge_tauto. }
    + rewrite Ha. tlaRevert. tlaRevert.
      repeat rewrite <- uncurry. repeat rewrite Always_and.
      apply always_imp. charge_intros. rewrite <- Hinv.
      charge_tauto.
Qed.

(** TODO: move this **)
Lemma charge_and_use : forall P Q C,
    C |-- P ->
    C //\\ P |-- Q ->
    C |-- P //\\ Q.
Proof.
  intros. charge_tauto.
Qed.

Section ComposeDiscrete.

  Variable Is : Formula.
  Variable Ic : Formula.
  Variable dvars : list Var.
  Variable cvars : list Var.
  Variable w : list DiffEq.
  Variable WC : Formula.
  Variable d : R.
  Variable S : Formula.
  Variable C : Formula.
  Variable P : Formula.
  Variable E : Formula.

  Theorem compose_discrete :
        |-- SysD (Sys cvars w d dvars Is S WC) -->> []E ->
    []E |-- SysD (Sys cvars w d dvars Ic C WC) -->> []P ->
    |-- SysD (Sys cvars w d dvars (Is //\\ Ic) (S //\\ C) WC) -->>
        [](P //\\ E).
  Proof.
    intros.
    rewrite <- Always_and.
    tlaIntro. rewrite (landC ([]P) ([]E)). apply charge_and_use.
    { charge_apply H.
      eapply Sys_weaken; try reflexivity.
      charge_tauto. charge_tauto. }
    { charge_apply H0. charge_split; try charge_tauto.
      erewrite Sys_weaken;
        try first [ charge_assumption |
                    reflexivity |
                    charge_tauto ]. }
  Qed.

End ComposeDiscrete.

Section ComposeWorld.

  Variable Iw : Formula.
  Variable Id : Formula.
  Variable dvars : list Var.
  Variable cvars : list Var.
  Variable w : list DiffEq.
  Variable WC : Formula.
  Variable d : R.
  Variable D : Formula.
  Variable P : Formula.
  Variable E : Formula.


  Theorem compose_world :
        |-- SysD (Sys cvars w d dvars Iw ltrue WC) -->> []E ->
    []E |-- SysD (Sys cvars w d dvars Id D ltrue) -->> []P ->
    |-- SysD (Sys cvars w d dvars (Iw //\\ Id) D WC) -->>
        [](P //\\ E).
  Proof.
    intros.
    rewrite <- Always_and.
    tlaIntro. rewrite (landC ([]P) ([]E)). apply charge_and_use.
    { charge_apply H.
      eapply Sys_weaken; try reflexivity.
      charge_tauto. charge_tauto. }
    { charge_apply H0. charge_split; try charge_tauto.
      erewrite Sys_weaken;
        try first [ charge_assumption |
                    reflexivity |
                    charge_tauto ]. }
  Qed.

End ComposeWorld.

Theorem ComposeRefine c w m (a b : SysRec c w m) :
  SysD (SysCompose a b) |-- SysD a.
Proof.
  unfold SysCompose, SysD, sysD, Next.
  simpl. restoreAbstraction.
  repeat rewrite <- Always_and.
  repeat charge_split; try charge_tauto.
  tlaRevert. apply forget_prem.
  charge_intros.
  rewrite Always_and.
  tlaRevert. apply always_imp.
  charge_intros. decompose_hyps.
  - apply lorR1. apply lorR1.
    charge_split; try charge_tauto.
    rewrite (World_weaken (dvars a)).
    + charge_tauto.
    + unfold all_in. intros. apply set_union_intro1. auto.
    + reflexivity.
  - apply lorR1. apply lorR2.
    charge_tauto.
  - apply lorR2. charge_split; try charge_tauto.
    rewrite (Unchanged_weaken (list_union (dvars a) c)).
    + charge_tauto.
    + unfold all_in. intros. unfold list_union in *.
      apply set_union_elim in H. destruct H.
      * apply set_union_intro1. apply set_union_intro1. auto.
      * apply set_union_intro2. auto.
Qed.

Theorem ComposeComm c w m (a b : SysRec c w m) :
  SysD (SysCompose a b) |-- SysD (SysCompose b a).
Proof.
  intros. unfold SysCompose, SysD, sysD, Next.
  simpl. restoreAbstraction.
  repeat rewrite <- Always_and.
  repeat charge_split; try charge_tauto.
  tlaRevert. apply forget_prem.
  charge_intros.
  rewrite Always_and.
  tlaRevert. apply always_imp.
  charge_intros. decompose_hyps.
  - apply lorR1. apply lorR1.
    charge_split; try charge_tauto.
    rewrite (World_weaken (list_union (dvars b) (dvars a))).
    + charge_tauto.
    + unfold all_in, list_union. intros.
      apply set_union_elim in H. apply set_union_intro.
      intuition.
    + reflexivity.
  - apply lorR1. apply lorR2.
    charge_tauto.
  - apply lorR2. charge_split; try charge_tauto.
    rewrite (Unchanged_weaken
               (list_union (list_union (dvars b) (dvars a)) c)).
    + charge_tauto.
    + unfold all_in, list_union. intros.
      apply set_union_intro.
      apply set_union_elim in H. destruct H.
      * left. apply set_union_elim in H.
        apply set_union_intro. intuition.
      * right. auto.
Qed.

Theorem Compose c w m (a b : SysRec c w m) P Q :
  |-- SysD a -->> [] P ->
  [] P |-- SysD b -->> [] Q ->
  |-- SysD (SysCompose a b) -->> [](P //\\ Q).
Proof.
  intros Ha Hb.
  rewrite <- Always_and.
  tlaIntro. tlaAssert ([]P).
  - charge_apply Ha. apply ComposeRefine.
  - tlaAssert (SysD b).
    + rewrite ComposeComm. apply ComposeRefine.
    + charge_tauto.
  Qed.