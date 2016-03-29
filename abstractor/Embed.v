(*
 * Embed.v
 * General embedding framework
 *)

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

Require Import ExtLib.Data.Option.

Require Import micromega.Psatz.
Require Import ExtLib.Tactics.
Require Import FunctionalExtensionality.
Require Import ExtLib.Data.Option.


(* We need to add an (axiomatized) decider for the reals, since the one in
   the standard library returns a value that cannot be matched on *)
Definition my_req_dec : forall (a b : R),
                     {a = b} + {a <> b}.
intros.
destruct (Rle_dec a b).
{ destruct (Rge_dec a b).
  { left. eapply Rle_antisym; eauto using Rge_le. }
  { right. red. intro. subst. apply n.
    eapply Rge_refl. } }
{ right. red; intro. subst. apply n.
  apply Rle_refl. }
Qed.

(* state utility functions *)
(* finite map lookup *)
Section lookup.
  Context {T :Type}.

  Fixpoint fm_lookup  (l : list (string * T)) (s : string): option T :=
    match l with
    | nil => None
    | (var, val) :: l' =>
      if string_dec s var
      then Some val
      else fm_lookup l' s
    end.

  (* finite map update *)
  (*
  Fixpoint fm_update (l : list (string * T)) (s : string) (t : T) : list (string * T) :=
    match l with
    | nil => [(s,t)]
    | (var, val) :: l' =>
      if string_dec s var
      then (var, t) :: l'
      else (var, val) :: fm_update l' s t
    end.
   *)
  Definition fm_update (l : list (string * T)) (s : string) (t : T) : list (string * T) :=
    (s, t) :: l.

  (* removes last binding put into finite map; convenient for
     strongest-postcondition semantics *)
  Definition fm_unset (l : list (string * T)) : list (string * T) :=
    match l with
    | nil => nil
    | _ :: l' => l'
    end.
End lookup.

Module Type EmbeddedLang.
  Parameter ast : Type.
  Parameter pl_data : Type.

  Parameter pl_equ : pl_data -> pl_data -> Prop.

  Axiom pl_equ_refl : forall (p : pl_data), pl_equ p p.
  Axiom pl_equ_trans : forall (p p' p'' : pl_data),
      pl_equ p p' -> pl_equ p' p'' -> pl_equ p p''.
  Axiom pl_equ_symm : forall (p p' : pl_data),
      pl_equ p p' -> pl_equ p' p.

  Definition istate : Type := list (string * pl_data).

  Parameter eval : istate -> ast -> istate -> Prop.

  (* Embedding deterministic functions that fail by
   "getting stuck" *)

  Definition states_iso (st st' : istate) : Prop :=
    forall (s : string),
      match fm_lookup st s , fm_lookup st' s with
      | None, None => True
      | Some f1, Some f2 => pl_equ f1 f2
      | _, _ => False
      end.

  Notation "a ~~ b" := (states_iso a b) (at level 70).

  (* we may want to require these but they don't seem to be necessary for
   * our purposes *)
  Axiom eval_det :
    forall prg isti isti' istf,
      (isti ~~ isti') ->
      eval isti prg istf ->
      exists istf', istf ~~ istf' /\ eval isti' prg istf'.

  (* relate concrete to abstract variables on inputs.
     e.g. in floating point inputs will be the rounding of real-world values *)
  Parameter asReal_in : pl_data -> R -> Prop.

  (* relate concrete to abstract variables on outputs.
     e.g. *)
  Parameter asReal_out : pl_data -> R -> Prop.

  Axiom asReal_in_det :
    forall (p p' : pl_data) (r : R),
      asReal_in p r ->
      asReal_in p' r ->
      pl_equ p p'. (* was p = p' *)

  Axiom asReal_in_equ :
    forall (p p' : pl_data),
      pl_equ p p' -> forall (r : R), asReal_in p r -> asReal_in p' r.

  Axiom asReal_out_det :
    forall (p : pl_data) (r r' : R),
      asReal_out p r ->
      asReal_out p r' ->
      r = r'.

  (* we get this one for free I think *)
  (*
  Axiom asReal_out_equ :
    forall (p : pl_data) (r r' : R),
      r = r' ->
      asReal_out p r ->
      asReal_out p r'.
   *)

End EmbeddedLang.

Module Type EMBEDDING_THEOREMS.
  Declare Module M : EmbeddedLang.
  Import M.

   (* Here is a correct embedding function.
     As we'll see below though, we depend on certain determinism properties *)
  Parameter embed_ex : list string -> list string -> ast -> Syntax.Formula.

  (* relate concrete to abstract states *)
  (* should all variables not in the list must be None? *)
  Definition models (asReal : pl_data -> R -> Prop) (vars : list string) (ist : istate) (sst : Syntax.state)
  : Prop :=
    forall (s : string),
      (In s vars ->
      exists (d : pl_data),
        fm_lookup ist s = Some d /\
        asReal d (sst s)).

  (** This ensures that all possible runs of the program are included
   ** in the final trace.
   **
   ** It is a soundness property.
   **)
  Axiom embed_ex_sound :
    forall (v v' : list string) (prg : ast) (is is' : istate)
           (ls ls' : Syntax.state) (tr : Stream.stream Syntax.state),
      models asReal_in v is ls ->
      models asReal_out v' is' ls' ->
      eval is prg is' ->
      Semantics.eval_formula
        (embed_ex v v' prg)
        (Stream.Cons ls (Stream.Cons ls' tr)).

  (** This ensures that only possible runs of the program are included in
   ** the final trace.
   **
   ** This is a partial completeness property.
   **)
  Axiom embed_ex_complete :
    forall (v v' : list string) (prg : ast) (ls : Syntax.state)
           (tr : Stream.stream Syntax.state),
      Semantics.eval_formula (embed_ex v v' prg) (Stream.Cons ls tr) ->
      exists is is', models asReal_in v is ls
                  /\ models asReal_out v' is' (Stream.hd tr)
                  /\ eval is prg is'.

  (** Next, some definitions for Hoare-style reasoning about programs.
   ** We use this to implement weakest-precondition.
   **)
  Section Hoare.
    Variables (P : istate -> Prop) (c : ast) (Q : istate -> Prop).

    Definition Hoare : Prop :=
      (forall s, P s ->
            (exists s', eval s c s') /\
            (forall s', eval s c s' -> Q s'))%type.

  End Hoare.
    Axiom Hoare__embed :
    forall vs vs' c,
      (|-- embed_ex vs vs' c -->>
           Embed (fun st st' =>
                    forall (P Q : istate -> Prop),
                      Hoare P c Q ->
                      exists fst,
                        models asReal_in vs fst st /\
                        (P fst ->
                         exists fst',
                           models asReal_out vs' fst' st' /\
                           Q fst'))).

End EMBEDDING_THEOREMS.

Module Embedding (M : EmbeddedLang) : EMBEDDING_THEOREMS with Module M := M.
  Module M := M.
  Import M.

  Definition models (asReal : pl_data -> R -> Prop) (vars : list string) (ist : istate) (sst : Syntax.state)
  : Prop :=
    forall (s : string),
      (In s vars ->
      exists (d : pl_data),
        fm_lookup ist s = Some d /\
        asReal d (sst s)).


  Definition embed_ex (v v' : list string) (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun lpre lpost =>
                    exists cpre cpost,
                      models asReal_in v cpre lpre /\
                      models asReal_out v' cpost lpost /\
                      eval cpre prg cpost).

  Lemma states_iso_symm :
    forall (st st' : istate),
      st ~~ st' -> st' ~~ st.
  Proof.
    induction st.
    - unfold states_iso. simpl. intros.
      specialize (H s).
      consider (fm_lookup st' s); try congruence.
    - unfold states_iso. simpl. intros.
      destruct a.
      consider (string_dec s s0); intros.
      + subst. specialize (H s0).
        consider (string_dec s0 s0); intros; try congruence.
        consider (fm_lookup st' s0); try contradiction.
        intros. apply pl_equ_symm. auto.
      + specialize (H s).
        consider (string_dec s s0); intros; try congruence.
        consider (fm_lookup st s); intros; try congruence.
        consider (fm_lookup st' s); intros; try congruence.
        apply pl_equ_symm. auto.
  Qed.

  Theorem embed_ex_sound
  : forall (v v' : list string) (prg : ast) (is is' : istate)
           (ls ls' : Syntax.state) (tr : Stream.stream Syntax.state),
      models asReal_in v is ls ->
      models asReal_out v' is' ls' ->
      eval is prg is' ->
      Semantics.eval_formula
        (embed_ex v v' prg)
        (Stream.Cons ls (Stream.Cons ls' tr)).
  Proof.
    red.
    simpl. intros.
    exists is. exists is'.
    intuition.
  Qed.

  Theorem embed_ex_complete
  : forall (v v' : list string) (prg : ast) (ls : Syntax.state)
           (tr : Stream.stream Syntax.state),
      Semantics.eval_formula (embed_ex v v' prg) (Stream.Cons ls tr) ->
         (exists is is', models asReal_in v is ls
                      /\ models asReal_out v' is' (Stream.hd tr)
                      /\ eval is prg is').
  Proof.
    simpl; intros.
    forward_reason.
    do 2 eexists; eauto.
  Qed.

(*
  Lemma embed_ex_correct2 :
    forall (v v' : list string) (prg : ast) (is : istate) (ls : Syntax.state)
           (tr : Stream.stream Syntax.state),
      models v is ls ->
      ~(exists is', eval is prg is') ->
      ~(Semantics.eval_formula
        (Enabled (embed_ex v v' prg))
        (Stream.Cons ls tr)).
  Proof.
    red.
    intros.
    simpl in H1.
    apply H0; clear H0.
    Printi
    forward_reason.
    generalize (models_det v ls is x0 H H1); intro Hmf.
    apply states_iso_symm in Hmf.
    eapply eval_det in Hmf; eauto.
    forward_reason; eauto.
  Qed.
*)

  Section Hoare.
    Variables (P : istate -> Prop) (c : ast) (Q : istate -> Prop).

    Definition Hoare : Prop :=
      (forall s, P s ->
            (exists s', eval s c s') /\
            (forall s', eval s c s' -> Q s'))%type.
    End Hoare.

  Theorem Hoare__embed :
    forall vs vs' c,
      (|-- embed_ex vs vs' c -->>
           Embed (fun st st' =>
                    forall (P Q : istate -> Prop),
                      Hoare P c Q ->
                      exists fst,
                        models asReal_in vs fst st /\
                        (P fst ->
                         exists fst',
                           models asReal_out vs' fst' st' /\
                           Q fst'))).
  Proof.
    simpl. intros. unfold tlaEntails. simpl.
    intros.
    forward_reason.
    unfold Hoare in H1.
    exists x. unfold models. split; auto.
    intros.
    exists x0.
    split; auto.
    specialize (H1 _ H4). forward_reason.
    auto.
  Qed.

  (** NOTE(gmalecha): This should probably go into FloatEmbed.
   ** This seems generic to Hoare, not specific to fpig_vcgen_correct
   ** This suggests that this should be in Embed.v?
   **)
  (* TODO: do i need a single varmap or two? *)
  (*
    Lemma float_embed_ex_enabled :
      forall (vs : list Var) (prg : ast) (st st' : state) (P Q : istate -> Prop),
        Hoare (fun fst => models vs fst st) prg (fun fst' => models vs fst' st') ->
(*        Hoare (fun fst => P fst /\ models vs fst st) prg (fun fst' => Q fst' /\ models vs fst' st') ->*)
        forall (tr : trace),
          Semantics.eval_formula (Enabled (embed_ex vs prg)) (Stream.Cons st tr).
    Proof.
      intros.
      unfold Hoare in *.
      Require Import Logic.Automation.
      breakAbstraction.
      unfold Hoare in H.

  (* fstate version *)
  Lemma float_embed_ex_enabled :
    forall (vs : list Var) (prg : ast) (fst fst' : fstate) (st' : state),
      let (_, P) := fpig_vcgen prg vs in
      P (fun fst' => models vs fst' st') fst ->
      forall (st : state) (tr : trace),
        models vs fst st ->
        Semantics.eval_formula (Enabled (embed_ex vs prg)) (Stream.Cons st tr).
  Proof.
    breakAbstraction.
    intros.
    generalize (fpig_vcgen_correct prg vs (fun fst'0 : fstate => models vs fst'0 st')); intros.
    destruct (fpig_vcgen prg vs); intros.
    unfold Hoare in *.
    specialize (H fst).
    generalize (models_fstate_has_vars vs nil fst st); intros. simpl in H2. fwd.
    rewrite H2 in H. fwd.
    specialize (H3 _ H).
    exists (Stream.Cons st' (Stream.forever st')).
    eapply embed_ex_correct1; [| | eapply H]; auto.
  Qed.
*)

End Embedding.
