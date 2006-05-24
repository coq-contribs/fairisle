(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                Solange Coupet-Grimal & Line Jakubiec-Jamet               *)
(*                                                                          *)
(*                                                                          *)
(*             Laboratoire d'Informatique Fondamentale de Marseille         *)
(*                   CMI et Faculté des Sciences de Luminy                  *)
(*                                                                          *)
(*           e-mail:{Solange.Coupet,Line.Jakubiec}@lif.univ-mrs.fr          *)
(*                                                                          *)
(*                                                                          *)
(*                            Developped in Coq v6                          *)
(*                            Ported to Coq v7                              *)
(*                            Translated to Coq v8                          *)
(*                                                                          *)
(*                             July 12nd 2005                               *)
(*                                                                          *)
(****************************************************************************)
(*                                Identity.v                                *)
(****************************************************************************)
 

Require Import Mealy.


Set Implicit Arguments.
Unset Strict Implicit.


(** We specify here a tool in order to express some connections. **)
(** This tool represents the Identity function. It is described **) 
(** as a Mealy automaton. No proof is done. **)


Section Identity.

  Variable Input_type : Set.

  Inductive state_id : Set :=
      IDENTITY : state_id.


(** Automaton describing the transitions from a state to another **)

  Definition Trans_id (i : Input_type) (s : state_id) : state_id := s.



(** Each state corresponds to a result **)

  Definition Out_id (i : Input_type) (s : state_id) : Input_type := i.


(** States stream **)

  Definition States_IDENTITY := States_Mealy Trans_id.


(** Intented behaviour **)

  Definition Behaviour_IDENTITY := Mealy Trans_id Out_id.

End Identity.


Lemma S_tail_Behaviour_IDENTITY :
 forall (Input_type : Set) (i : Stream Input_type) (si : state_id),
 S_tail (Behaviour_IDENTITY i si) = Behaviour_IDENTITY (S_tail i) si.
auto.
Qed.


Lemma EqS_IDENTITY :
 forall (Input_type : Set) (i : Stream Input_type) (si : state_id),
 EqS (Behaviour_IDENTITY i si) i.
cofix.
intros Input_type i si.
apply eqS.
simpl in |- *; auto.
rewrite S_tail_Behaviour_IDENTITY; auto.
Qed.