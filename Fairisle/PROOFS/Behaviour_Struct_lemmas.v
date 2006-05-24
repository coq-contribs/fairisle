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
(*                        Behaviour_Struct_lemmas.v                         *)
(****************************************************************************)
 

Require Export Arbitration.
Require Export Arbiter4_Proof.
Require Export Timing_Proof.
Require Export PriorityDecode_Proof.

Set Implicit Arguments.
Unset Strict Implicit.


(* Some tools for proofs *)

Lemma S_tail_Behaviour_TIMING :
 forall (s : Stream (bool * d_list bool 4)) (st : label_t),
 S_tail (Behaviour_TIMING s st) =
 Behaviour_TIMING (S_tail s) (Trans_Timing (S_head s) st).
unfold Behaviour_TIMING in |- *.
unfold Moore in |- *; simpl in |- *; auto.
Qed.

Lemma S_head_Behaviour_TIMING :
 forall (s : Stream (bool * d_list bool 4)) (st : label_t),
 S_head (Behaviour_TIMING s st) = Out_Timing st.
auto.
Qed.


Lemma S_head_Behaviour_PDECODE :
 forall
   (s : Stream (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4)))
   (sp : STATE_p),
 S_head (Behaviour_PRIORITY_DECODE s sp) = Out_PriorityDecode sp.
auto.
Qed.

Lemma S_tail_Behaviour_PDECODE :
 forall
   (s : Stream (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4)))
   (sp : STATE_p),
 S_tail (Behaviour_PRIORITY_DECODE s sp) =
 Behaviour_PRIORITY_DECODE (S_tail s) (Trans_PriorityDecode (S_head s) sp).
auto.
Qed.


Lemma S_tail_States_TIMING :
 forall (s : Stream (bool * d_list bool 4)) (st : label_t),
 S_tail (States_TIMING s st) =
 States_TIMING (S_tail s) (Trans_Timing (S_head s) st).
auto.
Qed.


Lemma S_head_States_TIMING :
 forall (s : Stream (bool * d_list bool 4)) (st : label_t),
 S_head (States_TIMING s st) = st.
auto.
Qed.


Lemma S_tail_States_Structure_TIMING :
 forall (i : Stream (bool * d_list bool 4)) (x : d_list bool 2),
 S_tail (States_Structure_TIMING i x) =
 States_Structure_TIMING (S_tail i) (Timing_Aux (S_head i) x).
auto.
Qed.


Lemma S_head_States_Structure_TIMING :
 forall (i : Stream (bool * d_list bool 4)) (x : d_list bool 2),
 S_head (States_Structure_TIMING i x) = x.
auto.
Qed.


Lemma S_tail_States_FOUR_ARBITERS :
 forall (i : Stream (bool * (bool * d_list (d_list bool 4) 4)))
   (s : STATE_a4),
 S_tail (States_FOUR_ARBITERS i s) =
 States_FOUR_ARBITERS (S_tail i) (Trans_Four_Arbiters (S_head i) s).
auto.
Qed.


Lemma S_tail_Structure_States_FOUR_ARBITERS :
 forall (i : Stream (bool * (bool * d_list (d_list bool 4) 4)))
   (olds : d_list bool 2 * bool * (d_list bool 2 * bool) *
           (d_list bool 2 * bool * (d_list bool 2 * bool))),
 S_tail (Structure_States_FOUR_ARBITERS i olds) =
 Structure_States_FOUR_ARBITERS (S_tail i)
   (Trans_Struct_four_arbiters (S_head i) olds).
auto.
Qed.
