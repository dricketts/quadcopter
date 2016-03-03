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
  Fixpoint fm_update (l : list (string * T)) (s : string) (t : T) : list (string * T) :=
    match l with
    | nil => [(s,t)]
    | (var, val) :: l' =>
      if string_dec s var
      then (var, t) :: l'
      else (var, val) :: fm_update l' s t
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

  (* relate concrete to abstract variables *)
  Parameter asReal : pl_data -> R -> Prop.

  Axiom asReal_det :
    forall (p p' : pl_data) (r : R),
      asReal p r ->
      asReal p' r ->
      pl_equ p p'. (* was p = p' *)

  Axiom pl_eq_asReal :
    forall (p1 p2 : pl_data) (r : R),
      pl_equ p1 p2 -> asReal p1 r -> asReal p2 r.

End EmbeddedLang.

(** NOTE(gmalecha): Do we ever use this? **)
Module Type EMBEDDING_THEOREMS.
  Declare Module M : EmbeddedLang.
  Import M.

   (* Here is a correct embedding function.
     As we'll see below though, we depend on certain determinism properties *)
  Parameter embed_ex : list string -> ast -> Syntax.Formula.

  (* relate concrete to abstract states *)
  (* should all variables not in the list must be None *)
  Definition models (vars : list string) (ist : istate) (sst : Syntax.state)
  : Prop :=
    forall (s : string),
      (In s vars ->
      exists (d : pl_data),
        fm_lookup ist s = Some d /\
        asReal d (sst s)) /\
      (~In s vars -> fm_lookup ist s = None).

  Axiom states_iso_symm :
    forall (st st' : M.istate),
      M.states_iso st st' -> M.states_iso st' st.

  Axiom models_det :
    forall (v : list string) (sst : Syntax.state) (ist ist' : M.istate),
      models v ist sst -> models v ist' sst ->
      M.states_iso ist ist'.

  Axiom embed_ex_correct1 :
    forall (v : list string) (prg : ast) (is is' : istate)
           (ls ls' : Syntax.state) (tr : Stream.stream Syntax.state),
      models v is ls ->
      models v is' ls' ->
      eval is prg is' ->
      Semantics.eval_formula
        (embed_ex v prg)
        (Stream.Cons ls (Stream.Cons ls' tr)).

  Axiom embed_ex_correct2 :
    forall (v : list string) (prg : ast) (is : istate) (ls : Syntax.state)
           (tr : Stream.stream Syntax.state),
      models v is ls ->
      ~(exists is', eval is prg is') ->
      ~(Semantics.eval_formula
        (Enabled (embed_ex v prg))
        (Stream.Cons ls tr)).

  (** Next, some definitions for Hoare-style reasoning about programs.
      We use this to implement weakest-precondition.
   **)
  Section Hoare.
    Variables (P : istate -> Prop) (c : ast) (Q : istate -> Prop).

    Definition Hoare : Prop :=
      (forall s, P s ->
            (exists s', eval s c s') /\
            (forall s', eval s c s' -> Q s'))%type.

  (* End Hoare. *)


  (* Axiom Hoare_Hoare' : forall (P : M.istate -> Prop) (c : M.ast) *)
  (*                             (Q : M.istate -> Prop), *)
  (*     Hoare P c Q <-> M.Hoare' P c Q. *)

  Axiom Hoare__embed :
    forall vs,
      Hoare ->
      (|-- embed_ex vs c -->>
           Embed (fun st st' =>
                    exists fst,
                      models vs fst st /\
                      (P fst ->
                       exists fst',
                         models vs fst' st' /\
                         Q fst'))).


  (* (* type of embeddings *) *)
  (* Definition embedding : Type := list string -> ast -> Syntax.Formula. *)

  (* (* "Preservation" - loosely *) *)
  (* (* this one doesn't consider terminating programs. *) *)
  (* Definition embedding_correct1 (embed : embedding) : Prop := *)

  (* (* correctness in the case of crashing programs *) *)
  (* Definition embedding_correct2 (embed : embedding) : Prop := *)
  (*   . *)

  End Hoare.


End EMBEDDING_THEOREMS.

(** NOTE(gmalecha): Do we ever use this? **)
Module Embedding (M : EmbeddedLang) <: EMBEDDING_THEOREMS with Module M := M.
  Module M := M.
  Import M.

  Definition models (vars : list string) (ist : istate) (sst : Syntax.state)
  : Prop :=
    forall (s : string),
      (In s vars ->
      exists (d : pl_data),
        fm_lookup ist s = Some d /\
        asReal d (sst s)) /\
      (~In s vars -> fm_lookup ist s = None).


  Definition embed_ex (v : list string) (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun lpre lpost =>
                    exists cpre cpost,
                      models v cpre lpre /\
                      models v cpost lpost /\
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

  Lemma models_det :
    forall (v : list string) (sst : Syntax.state) (ist ist' : istate),
      models v ist sst -> models v ist' sst ->
      ist ~~ ist'.
  Proof.
    unfold models, states_iso.
    intros.
    specialize (H s). specialize (H0 s).
    consider (In_dec string_dec s v).
    - forward_reason.
      specialize (asReal_det _ _ _ H3 H4).
      intro; subst. rewrite H. rewrite H0. apply pl_equ_symm. auto.
    - forward_reason.
      rewrite H2. rewrite H1. auto.
  Qed.

  (* "progress" in the sense of taking into account the possibility of failure to progress *)
  Lemma embed_ex_correct1 :
    forall (v : list string) (prg : ast) (is is' : istate)
           (ls ls' : Syntax.state) (tr : Stream.stream Syntax.state),
      models v is ls ->
      models v is' ls' ->
      eval is prg is' ->
      Semantics.eval_formula
        (embed_ex v prg)
        (Stream.Cons ls (Stream.Cons ls' tr)).
  Proof.
    red.
    simpl. intros.
    exists is. exists is'.
    intuition.
  Qed.

  Lemma embed_ex_correct2 :
    forall (v : list string) (prg : ast) (is : istate) (ls : Syntax.state)
           (tr : Stream.stream Syntax.state),
      models v is ls ->
      ~(exists is', eval is prg is') ->
      ~(Semantics.eval_formula
        (Enabled (embed_ex v prg))
        (Stream.Cons ls tr)).
  Proof.
    red.
    intros.
    simpl in H1.
    apply H0.
    forward_reason.
    generalize (models_det v ls is x0 H H1); intro Hmf.
    apply states_iso_symm in Hmf.
    eapply eval_det in Hmf; eauto.
    forward_reason; eauto.
  Qed.

  Section Hoare.
    Variables (P : istate -> Prop) (c : ast) (Q : istate -> Prop).


    Definition Hoare : Prop :=
      (forall s, P s ->
                 (exists s', eval s c s') /\
                 (forall s', eval s c s' -> Q s'))%type.


    Theorem Hoare__embed :
      forall vs,
        Hoare ->
        (|-- embed_ex vs c -->>
             Embed (fun st st' =>
                      exists fst,
                        models vs fst st /\
                        (P fst ->
                         exists fst',
                           models vs fst' st' /\
                           Q fst'))).
    Proof.
      simpl. intros. unfold tlaEntails. simpl.
      intros.
      forward_reason.
      unfold Hoare in H.
      exists x. unfold models. split; auto.
      intros.
      exists x0.
      split; auto.
      specialize (H _ H4). forward_reason.
      auto.
    Qed.
  End Hoare.

End Embedding.

