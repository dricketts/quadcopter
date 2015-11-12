Require Import Coq.Reals.Reals.
Require Import ExtLib.Tactics.
Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import Examples.System2.

Set Implicit Arguments.
Set Strict Implicit.

Local Open Scope string_scope.

Section quadcopter.
  Variable D : ActionFormula.
  Variable delta : R.

  Definition roll  : Var := "theta".
  Definition pitch : Var := "phi".
  Definition gravity : R := (- 98 / 10)%R.

  Definition max_angle : R := Rdiv PI 6.

  Local Open Scope HP_scope.

  Definition small_angle_constraint : StateFormula :=
           -- max_angle <= pitch <= max_angle
      //\\ -- max_angle <= roll <= max_angle.

  Definition W_quadcopter : Evolution :=
    fun st' =>
      small_angle_constraint -->>
      (     st' "x" = "vx" //\\ st' "y" = "vy" //\\ st' "z" = "vz"
       //\\ st' "vx" = "a" * cos( pitch ) * sin( roll )
       //\\ st' "vy" = "a" * sin( pitch )
       //\\ st' "vz" = "a" * cos( pitch ) * cos( roll ) + gravity
       //\\ st' pitch = 0 //\\ st' roll = 0 //\\ st' "a" = 0).

  Definition W_quadcopter_plane : Evolution :=
    fun st' =>
           st' "x" = "vx" //\\ st' "y" = "vy"
      //\\ st' "vx" = "a" * cos( "theta" )
      //\\ st' "vy" = "a" * sin( "theta" )
      //\\ st' "theta" = 0 //\\ st' "a" = 0.

  Definition W_quadcopter_vplane : Evolution :=
    fun st' =>
      -- max_angle <= pitch <= max_angle //\\
      -- max_angle <= "theta" <= max_angle -->>
           st' "x" = "vx" //\\ st' "z" = "vz"
      //\\ st' "vx" = "a" * sin( "theta" )
      //\\ st' "vz" = "a" * cos( "theta" ) + gravity
      //\\ st' "theta" = 0 //\\ st' "a" = 0.


  Theorem W_quadcopter_vplane_refinement
  : let A : Term := "a" * cos( pitch ) in
    let theta : Term := roll in
        Continuous W_quadcopter
    |-- Rename ({{ "a" ~> A
                 ; "theta" ~> theta }})%rn
               (Continuous W_quadcopter_vplane).
  Proof.
    cbv zeta.
    intros.
    rewrite <- Rename_Continuous_deriv_term'.
    2: eapply deriv_term_list; reflexivity.
    eapply Proper_Continuous_entails.
    red. intros.
    charge_intros.
    rewrite <- Rename_ok by eauto with rw_rename.
    simpl. restoreAbstraction.
    unfold W_quadcopter.
    unfold small_angle_constraint.
    charge_intros.
    unfold roll.
    breakAbstraction. intros.
    forward_reason.
    repeat rewrite H4. simpl.
    repeat split; auto.
    rewrite H12.
    rewrite H10.
    rewrite_real_zeros. reflexivity.
  Qed.

  Theorem W_quadcopter_plane_refinement
  : let ax : Term := "a" * cos( pitch ) * sin( roll ) in
    let ay : Term := "a" * sin( pitch ) in
    let az : Term := "a" * cos( pitch ) * cos( roll ) in
    let A : Term := SqrtT (ax * ax + ay * ay) in
    let theta : Term := ArctanT (ay / ax) in
        Continuous W_quadcopter
    |-- Rename ({{ "a" ~> A
                 ; "theta" ~> theta }})%rn
               (Continuous W_quadcopter_plane).
  Proof.
    intros.
    rewrite <- Rename_Continuous'.
    Require Import Coq.Reals.Ratan.
    instantiate (1 := fun st' x =>
                        let ax' := st' "a" * cos(pitch) * sin(roll) +
                                   "a" * (0 - sin(pitch)) * sin(roll) +
                                   "a" * cos(pitch) * cos(roll) in
                        let ay' := st' "a" * sin(pitch) + "a" * cos(pitch) in
                        if String.string_dec x "a" then
                          / (2 * SqrtT (ax * ax + ay * ay)) * (2 * ax * ax' + 2 * ay * ay')
                        else if String.string_dec x "theta" then
                               let u' := 2 * ay / ax * (ax * ay' - ay * ax') / (ax * ax) in
                                / (1 + (ay / ax) * (ay / ax)) * u'
                             else
                               st' x).
    { eapply Proper_Continuous_entails.
      red; intros.
      charge_intros.
      rewrite <- Rename_ok by eauto with rw_rename.
      simpl; restoreAbstraction.
      unfold W_quadcopter.
      unfold small_angle_constraint.
      breakAbstraction. intros.
      forward_reason.
      repeat rewrite H0; simpl; clear H0.
      destruct H.
      { admit. }
      forward_reason.
      Cases.rewrite_all_goal.
      rewrite_real_zeros.
      pose (cos (Stream.hd tr pitch)) as cpitch; fold cpitch.
      pose (sin (Stream.hd tr pitch)) as spitch; fold spitch.
      pose (cos (Stream.hd tr roll)) as croll; fold croll.
      pose (sin (Stream.hd tr roll)) as sroll; fold sroll.
      generalize dependent (Stream.hd tr "a"). intro a_; intros.
      cutrewrite (eq (sqrt (a_ * cpitch * sroll *
                        (a_ * cpitch * sroll) +
                        a_ * spitch * (a_ * spitch)))
                     (a_ * sqrt (cpitch * cpitch * sroll * sroll + spitch * spitch)))%R.
      { repeat split; auto.
        { rewrite ArithFacts.cos_atan.
          cutrewrite (eq (1 +
                          a_ * spitch * / (a_ * cpitch * sroll) *
                          (a_ * spitch * / (a_ * cpitch * sroll)))
                         (1 + (spitch / (cpitch * sroll) * (spitch / (cpitch * sroll)))))%R.
          { repeat rewrite Rmult_assoc.
            admit. }
          { admit. } }
        { rewrite ArithFacts.sin_atan.
          admit. }
        { cutrewrite (eq (a_ * cpitch * sroll * (a_ * cpitch) -
                          a_ * spitch * (a_ * (0 - spitch) * sroll + a_ * cpitch * croll))
                         0)%R.
          { rewrite_real_zeros. reflexivity. }
          { ring_simplify. (* NOT WORKING *)
    (* This is a quite complex proof. *)
  Abort.

  Definition quadcopter : ActionFormula :=
    Sys D W_quadcopter delta.

  Definition Quadcopter : ActionFormula :=
    System D W_quadcopter delta.

End quadcopter.