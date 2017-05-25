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
(*                           Arbitration_Specif.v                           *)
(****************************************************************************)
 

Require Export Arbiter4_Specif.
Require Export Arbitration.
Require Export PriorityDecode_Proof.
Require Export Timing_Proof.
Require Import Timing_Arbiter.

Set Implicit Arguments.
Unset Strict Implicit.


Section Arbitration_Specification.

  Let Input_type :=
    (bool * (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4)))%type.

  Let Output_type :=
    (d_list bool 3 * d_list bool 3 * (d_list bool 3 * d_list bool 3))%type.


(** The automaton describing the behaviour of ARBITER has 5 states **)

  Inductive label_A : Set :=
    | WAIT_BEGIN_A : label_A
    | TRIGGER_A : label_A
    | START_A : label_A
    | ACTIVE_A : label_A
    | NOT_TRIGGER_A : label_A. 

  Definition STATE_A : Set :=
    (label_A *
     (d_list (bool * bool) 4 * (d_list bool 4 * d_list (d_list bool 4) 4)))%type.



(** Automaton describing the transitions from a state to another **)


  Definition Trans_Arbitration (i : Input_type) (s : STATE_A) : STATE_A :=
    let (fs, t) := i in
    let (act, p') := t in
    let (pri, route) := p' in
    let (s', t) := s in
    let (g, p) := t in
    let (d, l) := p in
    match s' with
    | WAIT_BEGIN_A =>
        match fs with
        | true =>
            (START_A, (g, (l4_tttt, Convert_and_filter (act, (pri, route)))))
        | false =>
            (WAIT_BEGIN_A, (g, (d, Convert_and_filter (act, (pri, route)))))
        end
    | TRIGGER_A =>
        match fs with
        | true =>
            (START_A, (g, (l4_tttt, Convert_and_filter (act, (pri, route)))))
        | false =>
            (WAIT_BEGIN_A, (g, (d, Convert_and_filter (act, (pri, route)))))
        end
    | START_A =>
        match fs with
        | true =>
            (START_A, (g, (l4_tttt, Convert_and_filter (act, (pri, route)))))
        | false =>
            match Ackor act with
            | true =>
                (ACTIVE_A, (g, (d, Convert_and_filter (act, (pri, route)))))
            | false =>
                (START_A,
                (g, (l4_tttt, Convert_and_filter (act, (pri, route)))))
            end
        end
    | ACTIVE_A =>
        match fs with
        | true =>
            (START_A, (g, (l4_tttt, Convert_and_filter (act, (pri, route)))))
        | false =>
            match Ackor (d_map (Ackor (n:=3)) l) with
            | true =>
                (TRIGGER_A,
                (d_Map_List4_pdt_Grant l g,
                (Output_requested l, Convert_and_filter (act, (pri, route)))))
            | false =>
                (NOT_TRIGGER_A,
                (g, (d, Convert_and_filter (act, (pri, route)))))
            end
        end
    | NOT_TRIGGER_A =>
        match fs with
        | true =>
            (START_A, (g, (l4_tttt, Convert_and_filter (act, (pri, route)))))
        | false =>
            (NOT_TRIGGER_A, (g, (d, Convert_and_filter (act, (pri, route)))))
        end
    end.


(** The output function returns the result of ARBITRATION **)

  Definition Out_Arbitration (s : STATE_A) : Output_type :=
    let (_, t) := s in
    let (g, p) := t in
    let (d, _) := p in
    (List3 (fst (Fst_of_l4 g)) (snd (Fst_of_l4 g)) (Fst_of_l4 d),
    List3 (fst (Scd_of_l4 g)) (snd (Scd_of_l4 g)) (Scd_of_l4 d),
    (List3 (fst (Thd_of_l4 g)) (snd (Thd_of_l4 g)) (Thd_of_l4 d),
    List3 (fst (Fth_of_l4 g)) (snd (Fth_of_l4 g)) (Fth_of_l4 d))). 


(** States stream **)

  Definition States_ARBITRATION :
    Stream Input_type -> STATE_A -> Stream STATE_A :=
    States_Mealy Trans_Arbitration.



(** Intented behaviour **)

  Definition Behaviour_ARBITRATION := Moore Trans_Arbitration Out_Arbitration.


(** Transformation of Behaviour_ARBITRATION to a Mealy automaton **)

  Definition Out_Arbitration_Mealy :=
    Out_Mealy (Input_type:=Input_type) Out_Arbitration.

  Lemma equiv_out_Arbitration_Moore_Mealy :
   forall (i : Input_type) (s : STATE_A),
   Out_Arbitration s = Out_Arbitration_Mealy i s.
  auto.
  Qed.


  Lemma Equiv_Arbitration_Moore_Mealy :
   forall (s : STATE_A) (i : Stream Input_type),
   EqS (Behaviour_ARBITRATION i s)
     (Mealy Trans_Arbitration Out_Arbitration_Mealy i s).
  intros s i.
  unfold Behaviour_ARBITRATION in |- *; unfold Out_Arbitration_Mealy in |- *;
   apply Equiv_Moore_Mealy.
  Qed.



(** Invariant definition **)

  Definition R_A (s_A : STATE_A)
    (s : state_id * (label_t * STATE_p) * STATE_a4) : Prop :=
    let (s_tpi, s_a4) := s in
    let (sA, t) := s_A in
    let (_, stp) := s_tpi in
    let (st, s_p) := stp in
    let (sp, l) := s_p in
    let (sa4, p) := s_a4 in
    let (G, p') := t in
    let (D, L) := p' in
    let (g, d) := p in
    (sA = WAIT_BEGIN_A /\ st = START_t /\ sa4 = WAIT_a4 /\ sp = START_p \/
     sA = WAIT_BEGIN_A /\ st = START_t /\ sa4 = WAIT_a4 /\ sp = DECODE_p \/
     sA = START_A /\
     st = WAIT_t /\ sa4 = START_a4 /\ sp = DECODE_p /\ D = l4_tttt \/
     sA = ACTIVE_A /\
     st = ROUTE_t /\ sa4 = START_a4 /\ sp = DECODE_p /\ D = l4_tttt \/
     sA = NOT_TRIGGER_A /\
     st = START_t /\ sa4 = START_a4 /\ sp = DECODE_p /\ D = l4_tttt \/
     sA = TRIGGER_A /\
     st = START_t /\ sa4 = AT_LEAST_ONE_IS_ACTIVE_a4 /\ sp = DECODE_p) /\
    G = g /\ D = d /\ L = l.



(** There is an hypothesis on input signals here **)

  Definition P_A (i : Input_type) (sA : STATE_A)
    (s : state_id * (label_t * STATE_p) * STATE_a4) :=
    let (s_tpi, _) := s in
    let (_, stp) := s_tpi in
    let (st, _) := stp in let (fs, _) := i in P_Timing fs st.


End Arbitration_Specification.