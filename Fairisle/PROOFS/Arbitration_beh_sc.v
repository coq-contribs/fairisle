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
(*                          Arbitration_beh_sc.v                            *)
(****************************************************************************)
 

Require Export Basic_composition_rules.
Require Export Identity.
Require Export PriorityDecode_Proof.
Require Export Timing_Proof.
Require Export Arbiter4_Specif.

Set Implicit Arguments.
Unset Strict Implicit.


  (** Comportement reel (composition des comportements) **)


(* Parallel composition of Behaviour_TIMING and Behaviour_PRIORITY_DECODE *)

Section Timing_and_PDecode_beh.

 Let Input_type :=
   (bool * (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4)))%type.

 Let f_tp (i : Input_type) :=
   let (fs, t) := i in
   let (act, p) := t in
   let (pri, route) := p in (fs, act, (act, (pri, route))).


 Let output_tp (out : bool * d_list (d_list bool 4) 4) := out.

 Definition Trans_Timing_PDecode :=
   Trans_PC Trans_Timing Trans_PriorityDecode f_tp.

 Definition Out_Timing_PDecode :=
   Out_PC Out_Timing_Mealy Out_PriorityDecode_Mealy f_tp output_tp.

 Definition Behaviour_TIMING_PDECODE (i : Stream Input_type) :=
   PC Trans_Timing Trans_PriorityDecode Out_Timing_Mealy
     Out_PriorityDecode_Mealy f_tp output_tp i.

 Definition States_Beh_TIMING_PDECODE (i : Stream Input_type) :=
   States_PC Trans_Timing Trans_PriorityDecode f_tp i.

End Timing_and_PDecode_beh.



(* Parallel composition of IDENTITY and TIMING_PDECODE *)

Section Identity_and_TimingPDecode_beh.

 Let Input_type :=
   (bool * (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4)))%type.

 Let f_tpi (i : Input_type) :=
   let (fs, t) := i in
   let (act, p) := t in
   let (pri, route) := p in (fs, (fs, (act, (pri, route)))).

 Let output_tpi (out : bool * (bool * d_list (d_list bool 4) 4)) := out.


 Definition Trans_TimingPDecode_Id :=
   Trans_PC (Trans_id (Input_type:=bool)) Trans_Timing_PDecode f_tpi.

 Definition Out_TimingPDecode_Id :=
   Out_PC (Out_id (Input_type:=bool)) Out_Timing_PDecode f_tpi output_tpi.


 Definition Behaviour_TIMINGPDECODE_ID (i : Stream Input_type) :=
   PC (Trans_id (Input_type:=bool)) Trans_Timing_PDecode
     (Out_id (Input_type:=bool)) Out_Timing_PDecode f_tpi output_tpi i.


 Definition States_Beh_TIMINGPDECODE_ID (i : Stream Input_type) :=
   States_PC (Trans_id (Input_type:=bool)) Trans_Timing_PDecode f_tpi i.

End Identity_and_TimingPDecode_beh.


(* Series composition of Behaviour_TIMINGPDECODE_ID and Behaviour_FOUR_ARBITERS *)

Section Arbitration_beh.

  Let Input_type :=
    (bool * (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4)))%type.


  Definition TransSC_Arbitration_beh :=
    Trans_SC Trans_TimingPDecode_Id Trans_Four_Arbiters Out_TimingPDecode_Id.

  Definition OutSC_Arbitration_beh :=
    Out_SC Out_TimingPDecode_Id Out_Four_Arbiters_Mealy.



  Definition BehaviourSC_ARBITRATION (i : Stream Input_type)
    (stpia4 : state_id * (label_t * STATE_p) * STATE_a4) :=
    SC Trans_TimingPDecode_Id Trans_Four_Arbiters Out_TimingPDecode_Id
      Out_Four_Arbiters_Mealy i stpia4.


  Definition States_Beh_SC_ARBITRATION (i : Stream Input_type)
    (stpia4 : state_id * (label_t * STATE_p) * STATE_a4) :=
    States_SC Trans_TimingPDecode_Id Trans_Four_Arbiters Out_TimingPDecode_Id
      i stpia4.


End Arbitration_beh.
