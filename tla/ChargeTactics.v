Require Export Charge.Logics.ILogic.
Require Import TLA.LogicLemmas.

Ltac charge_split := apply landR.

Ltac charge_search_prems found :=
  match goal with
  | |- ?X |-- ?Y =>
    solve [ found
          | apply landL1 ; charge_search_prems found
          | apply landL2 ; charge_search_prems found ]
  end.

Ltac charge_assumption :=
  charge_search_prems reflexivity.

Ltac charge_intro :=
  first [ apply lforallR; intro
        | apply limplAdj_true
        | apply limplAdj ].

Ltac charge_intros :=
  repeat match goal with
         | |- _ |-- _ -->> _ =>
           charge_intro
         end.

Ltac charge_trivial := apply ltrueR.

Ltac charge_use :=
  eapply lapply; [ charge_assumption | ].

Ltac ends_with H ABC C :=
  let rec go k ABC :=
      match ABC with
      | C => k
      | _ -->> ?BC =>
        let k' := (k; first [ apply landAdj_true in H | apply landAdj in H ]) in
        go k' BC
      end
  in
  go ltac:(idtac) ABC.

Ltac charge_apply H :=
  match type of H with
  | _ |-- ?X =>
    match goal with
    | |- _ |-- ?Y =>
      ends_with H X Y ; etransitivity ; [ | eapply H ]
    end
  end.

Ltac charge_tauto :=
  repeat charge_split ;
  solve [ charge_assumption
        | charge_trivial
        | charge_intro; repeat charge_intro; charge_tauto
        | charge_split; solve [ charge_tauto ]
        | match goal with
          | H : _ |-- _ |- _ =>
            charge_apply H ; charge_tauto
          end
        | charge_use ; charge_tauto ].

Create HintDb pull_quant.

Lemma landexistsD_right:
  forall (A : Frm) (ILOps : ILogicOps A),
  ILogic A ->
  forall (T : Type) (f : T -> A) (P : A),
   P //\\ (Exists a : T, f a) -|- Exists a : T, f a //\\ P.
Proof.
  intros.
  rewrite landC. apply landexistsD.
Qed.

Hint Rewrite @landexistsD landexistsD_right using solve [ eauto with typeclass_instances ] : pull_quant.

Ltac charge_fwd :=
  repeat progress ( autorewrite with pull_quant;
                    repeat (simple apply lexistsL; intro) ).

Notation "x <<-->> y" := (liff x y) (at level 78).