Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import ChargeTactics.Tactics.
Require Import ExtLib.Structures.Applicative.
Require Import hTLA.DiscreteLogic.
Require Import hTLA.LibContinuous.

Section parametric.
  Variable tlaState : Type.

  Definition CActionProp : Type :=
    (R -> tlaState) -> R -> Prop.

  Definition deriv_formula (G : StateProp tlaState) (st : tlaState) : Prop :=
    G st.

(*
  Definition solves_diffeqs (f : R -> tlaState)
             (diffeqs : list DiffEq) (r : R)
             (is_derivable : forall x, List.In x diffeqs -> derivable (fun t => x.(de_lhs) (f t))) :=
    forall x d o (pf : List.In (DiffEqC x o d) diffeqs),
    forall z, (0 <= z <= r)%R ->
              o (derive (fun t => x (f t)) (@is_derivable (DiffEqC x o d) pf) z)
                (d (f z)).
*)



  Definition deriv_formula (f f' : tlaState -> R) (diffeqs : list (DiffEq tlaState))
    : Prop :=
    forall (p : R -> tlaState) t,
      forall is_derive,
        solves_diffeqs _ p diffeqs t is_derive ->
(*        exists (is_derivable : forall x, List.In x (List.map (de_lhs) diffeqs) -> derivable (fun t => x (f (p t)))),
          True. *)
        derive (fun t => f (p t)) = (fun t => f' (p t)).
        forall x d o (pf : List.In (DiffEqC x o d) obs),
        forall z,
          (derive (fun t => x (f t)) (@is_derivable (DiffEqC x o d) pf) z) = (d (f z)).



  Definition deriv_formula (f f' : tlaState -> R) (obs : list (tlaState -> R))
    : Prop :=
    exists (is_derivable : forall x, List.In x obs -> derivable (fun t => x (f t))),
    forall x d o (pf : List.In (DiffEqC x o d) obs),
    forall z,
      (derive (fun t => x (f t)) (@is_derivable (DiffEqC x o d) pf) z) = (d (f z)).

    G st.
Definition solves_diffeqs (f : R -> tlaState)
             (diffeqs : list DiffEq) (r : R)
             (is_derivable : forall x, List.In x diffeqs -> derivable (fun t => x.(de_lhs) (f t))) :=
    forall x d o (pf : List.In (DiffEqC x o d) diffeqs),
    forall z, (0 <= z <= r)%R ->
              o (derive (fun t => x (f t)) (@is_derivable (DiffEqC x o d) pf) z)
                (d (f z)).

  (** These should move! **)
  Definition after (P : StateProp tlaState) : DActionProp tlaState :=
    fun _ st' => P st'.
  Lemma starts_discretely_through_now : forall (A : StateProp tlaState) B,
      through (now A) //\\ starts (discretely B) -|-
              starts (before _ A //\\ discretely (B //\\ after A)).
  Proof. unfold through, starts, discretely, before, after.
         red.
  Admitted.
  Require Import Morphisms.
  Instance Proper_starts : Proper (lentails ==> lentails) (@starts tlaState).
  Proof. Admitted.
  Instance Proper_starts_iff : Proper (lequiv ==> lequiv) (@starts tlaState).
  Proof. Admitted.
  Instance Proper_always : Proper (lentails ==> lentails) (@always tlaState).
  Proof. Admitted.
  Instance Proper_always_iff : Proper (lequiv ==> lequiv) (@always tlaState).
  Proof. Admitted.
  Instance Proper_eventually : Proper (lentails ==> lentails) (@eventually tlaState).
  Proof. Admitted.
  Instance Proper_eventually_iff : Proper (lequiv ==> lequiv) (@eventually tlaState).
  Proof. Admitted.
  Lemma starts_discretely_through : forall C P (Q : StateProp tlaState) d,
      P |-- discretely d ->
      |-- P -->> before _ Q //\\ discretely (after Q) ->
      C |-- starts P -->> through (now Q).
  Proof.
    intros.
  Admitted.

  (** Differential Induction **)
  Lemma diff_ind : forall G F (GI : StateProp tlaState) cp,
      (forall f : R -> tlaState,
          forall t : R,
            forall f',
              forall t',
                let st := f t' in
                let st' := f' t' in
                  Forall (fun de => de.(de_rel)
                                         (de.(de_lhs) st')
                                         (de.(de_rhs) st)) cp ->
                  GI st -> deriv_formula f' G (f t)) ->

(* ) ->
            forall f', deriv_state _ (List.map (@de_lhs _) cp) t f f' ->
                       is_solution f cp t ->
                       deriv_formula f' G f t) ->
      
      GI -->> deriv_formula f' G
*)

      (* , through (now GI) //\\ deriv_on_interval d |-- deriv_formula GI G -> *)
      F |-- now G //\\ starts (discretely (Continuous cp GI)) -->> through (now G).



  Lemma core_diff_ind : forall G F (GI : StateProp tlaState) cp,
      (forall f : R -> tlaState,
          forall t : R,
            (forall t', (0 <= t' <= t)%R -> GI (f t')) ->
            forall f', deriv_state _ (List.map (@de_lhs _) cp) t f f' ->
                       is_solution f cp t ->
                       deriv_formula f' G f t) ->
      
      GI -->> deriv_formula f' G

      (* , through (now GI) //\\ deriv_on_interval d |-- deriv_formula GI G -> *)
      F |-- now G //\\ starts (discretely (Continuous cp GI)) -->> through (now G).
  Print DiffEq.
  Proof.
    simpl. intros.
    unfold Continuous.
    charge_intros.
    repeat rewrite now_starts_discretely_and.
    rewrite starts_discretely_through_now.
    rewrite now_starts_discretely_and.
    apply landAdj.
    apply forget_prem.
    eapply starts_discretely_through.
    charge_tauto. charge_intros.
    charge_split; try charge_tauto.
    


  Abort.

  Lemma core_diff_ind : forall G F (GI : StateProp tlaState) cp,
      F |-- now GI -->> starts (discretely (Continuous (tlaState:=tlaState) cp)) -->> through (now GI) ->
      (forall f : R -> tlaState,
          forall t : R,
            (forall t', (0 <= t' <= t)%R -> GI (f t')) ->
            forall f', deriv_state _ (List.map (@de_lhs _) cp) t f f' ->
                       deriv_formula f' G f t) ->
      (* , through (now GI) //\\ deriv_on_interval d |-- deriv_formula GI G -> *)
      F |-- now G //\\ through (now GI) //\\ starts (discretely (Continuous cp)) -->> through (now G).
  Proof.
    simpl. intros.
    unfold Continuous.
    charge_intros.
    repeat rewrite now_starts_discretely_and.
    rewrite starts_discretely_through_now.
    rewrite now_starts_discretely_and.
    apply landAdj.
    apply forget_prem.
    eapply starts_discretely_through.
    charge_tauto. charge_intros.
    charge_split; try charge_tauto.
  (** NOTE: The premise here is too weak, it requires that [GI] holds
   ** at all points along the path. This is *not* expressible in a
   ** discrete logic.
   **)
  Abort.



  Theorem starts_continuously_through_now : forall G F GI cp,
    F |-- now GI -->> starts (Continuous (tlaState:=tlaState) cp) -->> through (now GI) ->
    (forall f : R -> tlaState,
        forall t : R,
          (forall t', (0 <= t' <= t)%R -> GI (f t')) ->
          forall f', True (* f' is the derivative of f on [0,t] *) ->
                     is_solution _ f cp t (* f' satisfies cp on [0,t] *) ->
                     deriv_formula f' (GI -->> G) f t) ->
  (* , through (now GI) //\\ deriv_on_interval d |-- deriv_formula GI G -> *)
    F |-- now G //\\ now GI //\\ starts (Continuous cp) -->> through (now G).
  Proof.
    simpl. intros.
    clear H.
    destruct H2 as [ ? [ ? ? ] ].
    specialize (H0 _ _ H3).
    red in H0.
    eapply H0; eauto.
  Qed.




End parametric.

Ltac charge_fwd :=
  let rec search_it fin :=
   (match goal with
    | |- ?A //\\ _ //\\ ?B |-- ?G => idtac "mid" ; first
      [ simple apply (land_limpl_specialize_ap _ _ A B G);
         [ charge_tauto | search_it ltac:idtac ]
      | simple apply land_lexists_ap; [ idtac "a" ; intro ; search_it ltac:idtac ]
      | simple apply (landA_ap A _ B G); search_it fin ]
    | |- ?A //\\ ?B |-- ?G => idtac "start_end" ; first
      [ simple eapply (land_limpl_specializeR_ap _ _ _ G);
         [ charge_tauto | search_it ltac:idtac ]
      | simple eapply (land_limpl_specializeL_ap _ _ _ G);
         [ charge_tauto | search_it ltac:idtac ]
      | apply land_lexistsR_ap; [ idtac "A" ; intro ; search_it ltac:idtac ]
      | apply land_lexistsL_ap; [ idtac "B" ; intro ; search_it ltac:idtac ]
      | fin ]
    | |- _ => fin
    end) in
  repeat rewrite landA; search_it ltac:idtac.
