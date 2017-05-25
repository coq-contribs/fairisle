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
(*                              Arbitration.v                               *)
(****************************************************************************)
 

Require Export ElementComb.
Require Import Basic_composition_rules.
Require Export Identity.


Set Implicit Arguments.
Unset Strict Implicit.


 (** Describes the components of the ARBITRATION unit and the unit itself **)


(** The structure of TIMING is exactly a Moore automaton **)

Definition Timing_Aux (e : bool * d_list bool 4) (l : d_list bool 2) :=
  let (fs, act) := e in Timing fs act l.

Definition Out_Struct_Timing (_ : bool * d_list bool 4)
  (l : d_list bool 2) := d_Head l. 

Definition Structure_TIMING := Mealy Timing_Aux Out_Struct_Timing.



(** The structure of OUTDIS is a Mealy automaton **)

Definition Trans_outdis (i : d_list bool 4 * (bool * bool))
  (old_jk : bool) :=
  let (req, p) := i in
  let (fs, routeEnable) := p in Jk fs (outdis req routeEnable) old_jk.


Definition Out_outdis (_ : d_list bool 4 * (bool * bool)) 
  (old_jk : bool) := old_jk.

Definition Structure_Outdis := Mealy Trans_outdis Out_outdis.



(** The structure of ARBITER_XY is a Mealy automaton **)

Definition Trans_ArbiterXY (i : d_list bool 4 * bool)
  (old_xy : d_list bool 2) :=
  let (req, routeEnable) := i in
  List2
    (JkE (Fst_of_l2 (Arbx (Scd_of_l2 old_xy) req))
       (Scd_of_l2 (Arbx (Scd_of_l2 old_xy) req)) (Fst_of_l2 old_xy)
       routeEnable)
    (JkE (Fst_of_l2 (Arby (Fst_of_l2 old_xy) req))
       (Scd_of_l2 (Arby (Fst_of_l2 old_xy) req)) (Scd_of_l2 old_xy)
       routeEnable).

Definition Out_ArbiterXY (_ : d_list bool 4 * bool)
  (old_xy : d_list bool 2) := old_xy.

Definition Structure_ArbiterXY := Mealy Trans_ArbiterXY Out_ArbiterXY.


(** The structure of ARBITER is a PC of Structure_Outdis and Structure_ArbiterXY **)

Definition f_arbiter (i : bool * (bool * d_list bool 4)) :=
  let (fs, p) := i in
  let (routeEnable, req) := p in (req, routeEnable, (req, (fs, routeEnable))).

Definition output_arbiter (l : d_list bool 2 * bool) :=
  let (o1, o2) := l in List3 (Fst_of_l2 o1) (Scd_of_l2 o1) o2.

Definition TransPC_arbiter := Trans_PC Trans_ArbiterXY Trans_outdis f_arbiter.

Definition OutPC_arbiter :=
  Out_PC Out_ArbiterXY Out_outdis f_arbiter output_arbiter.

Definition Structure_ARBITER :=
  PC Trans_ArbiterXY Trans_outdis Out_ArbiterXY Out_outdis f_arbiter
    output_arbiter.


(** Parallel composition of two arbiters with the PC rule **)

Definition f_two_arbiters (i : bool * (bool * d_list (d_list bool 4) 2)) :=
  let (fs, p) := i in
  let (routeEnable, req2) := p in
  (fs, (routeEnable, Fst_of_l2 req2), (fs, (routeEnable, Scd_of_l2 req2))).

Definition output_two_arbiters (o : d_list bool 3 * d_list bool 3) := o.

Definition Trans_Struct_two_arbiters :=
  Trans_PC TransPC_arbiter TransPC_arbiter f_two_arbiters.

Definition Out_Struct_two_arbiters :=
  Out_PC OutPC_arbiter OutPC_arbiter f_two_arbiters output_two_arbiters.

Definition Structure_TWO_ARBITERS :=
  PC TransPC_arbiter TransPC_arbiter OutPC_arbiter OutPC_arbiter
    f_two_arbiters output_two_arbiters.



(** Parallel composition of four arbiters with the PC rule **)

Definition f_four_arbiters (i : bool * (bool * d_list (d_list bool 4) 4)) :=
  let (fs, p) := i in
  let (routeEnable, req) := p in
  (fs, (routeEnable, Two_Fst_of_l4' req),
  (fs, (routeEnable, Two_last_of_l4' req))).

Definition output_four_arbiters
  (o : d_list bool 3 * d_list bool 3 * (d_list bool 3 * d_list bool 3)) := o.

Definition Trans_Struct_four_arbiters :=
  Trans_PC Trans_Struct_two_arbiters Trans_Struct_two_arbiters
    f_four_arbiters.

Definition Out_Struct_four_arbiters :=
  Out_PC Out_Struct_two_arbiters Out_Struct_two_arbiters f_four_arbiters
    output_four_arbiters.

Definition Structure_FOUR_ARBITERS :=
  PC Trans_Struct_two_arbiters Trans_Struct_two_arbiters
    Out_Struct_two_arbiters Out_Struct_two_arbiters f_four_arbiters
    output_four_arbiters.


(** PRIORITY_DECODE is a Mealy automaton too **)

Definition Trans_priority_decode
  (e : d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4))
  (_ : d_list (d_list bool 4) 4) :=
  let (act, p) := e in
  let (pri, route) := p in Priority_Decode_Less_Pause act pri route.


Definition Out_priority_decode
  (_ : d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4))
  (reg : d_list (d_list bool 4) 4) := reg.


Definition Structure_PRIORITY_DECODE :=
  Mealy Trans_priority_decode Out_priority_decode.


(* Parallel composition of TIMING and PRIORITY_DECODE *)

Section Timing_and_PDecode.

 Let Input_vector_type :=
   (bool * (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4)))%type.

 Let f_tp (i : Input_vector_type) :=
   let (fs, t) := i in
   let (act, p) := t in
   let (pri, route) := p in (fs, act, (act, (pri, route))).


 Let output_tp (out : bool * d_list (d_list bool 4) 4) := out.

 Definition TransPC_Timing_PDecode :=
   Trans_PC Timing_Aux Trans_priority_decode f_tp.

 Definition OutPC_Timing_PDecode :=
   Out_PC Out_Struct_Timing Out_priority_decode f_tp output_tp.

 Definition Structure_TIMING_PDECODE (i : Stream Input_vector_type) :=
   PC Timing_Aux Trans_priority_decode Out_Struct_Timing Out_priority_decode
     f_tp output_tp i.

 Definition States_TIMING_PDECODE (i : Stream Input_vector_type) :=
   States_PC Timing_Aux Trans_priority_decode f_tp i.

End Timing_and_PDecode.



(* Parallel composition of IDENTITY and TIMING_PDECODE *)

Section Identity_and_TimingPDecode.

 Let Input_vector_type :=
   (bool * (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4)))%type.

 Let f_tpi (i : Input_vector_type) :=
   let (fs, t) := i in
   let (act, p) := t in
   let (pri, route) := p in (fs, (fs, (act, (pri, route)))).

 Let output_tpi (out : bool * (bool * d_list (d_list bool 4) 4)) := out.


 Definition TransPC_TimingPDecode_Id :=
   Trans_PC (Trans_id (Input_type:=bool)) TransPC_Timing_PDecode f_tpi.

 Definition OutPC_TimingPDecode_Id :=
   Out_PC (Out_id (Input_type:=bool)) OutPC_Timing_PDecode f_tpi output_tpi.


 Definition Structure_TIMINGPDECODE_ID (i : Stream Input_vector_type) :=
   PC (Trans_id (Input_type:=bool)) TransPC_Timing_PDecode
     (Out_id (Input_type:=bool)) OutPC_Timing_PDecode f_tpi output_tpi i.


 Definition States_TIMINGPDECODE_ID (i : Stream Input_vector_type) :=
   States_PC (Trans_id (Input_type:=bool)) TransPC_Timing_PDecode f_tpi i.

End Identity_and_TimingPDecode.


(* Series composition of TIMINGPDECODE_ID and FOUR_ARBITERS *)

Section Arbitration_Structure.

  Let Input_vector_type :=
    (bool * (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4)))%type.


  Definition TransSC_Arbitration :=
    Trans_SC TransPC_TimingPDecode_Id Trans_Struct_four_arbiters
      OutPC_TimingPDecode_Id.

  Definition OutSC_Arbitration :=
    Out_SC OutPC_TimingPDecode_Id Out_Struct_four_arbiters.


  Definition Structure_ARBITRATION (i : Stream Input_vector_type) :=
    SC TransPC_TimingPDecode_Id Trans_Struct_four_arbiters
      OutPC_TimingPDecode_Id Out_Struct_four_arbiters i.


  Definition StatesSC_ARBITRATION (i : Stream Input_vector_type) :=
    States_SC TransPC_TimingPDecode_Id Trans_Struct_four_arbiters
      OutPC_TimingPDecode_Id i.


End Arbitration_Structure.
