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
(*                              ElementTemp.v                               *)
(****************************************************************************)
 

Require Export ElementComb.
Require Export Basic_composition_rules.
Require Import Identity.

Set Implicit Arguments.
Unset Strict Implicit.


(** Describing the temporal parts of the circuit using co-induction **)


Definition RLATCH2 (rd : Stream bool) := RLATCH rd (n:=2).


Definition DMUX4T2FFC_AUX := S_map2 dmux4t2ffc.

Definition DMUX4T2FFC (d : Stream (d_list bool 4))
  (y outputDisable : Stream bool) (old : d_list bool 2) :=
  RLATCH2 outputDisable (Stream_to_dlist (DMUX4T2FFC_AUX y d)) old.


Definition DMUX4T2 := S_map2 Dmux4t2.


Definition DMUX2B4CA11_AUX (y outputDisable : Stream bool)
  (d : Stream (d_list (d_list bool 4) 2))
  (old_mux : d_list (d_list bool 2) 2) :=
  List2
    (dlist_to_Stream
       (DMUX4T2FFC (S_Fst_of_l2 d) y outputDisable (Fst_of_l2 old_mux)))
    (dlist_to_Stream
       (DMUX4T2FFC (S_Scd_of_l2 d) y outputDisable (Scd_of_l2 old_mux))).


Definition DMUX2B4CA11 (old_mux : d_list (d_list bool 2) 2)
  (outputDisable : Stream bool) (grant : Stream (d_list bool 2))
  (d : Stream (d_list (d_list bool 4) 2)) :=
  DMUX4T2 (S_Fst_of_l2 grant)
    (dlist_to_Stream
       (DMUX2B4CA11_AUX (S_Scd_of_l2 grant) outputDisable d old_mux)).



Definition DATASWITCHC_AUX (i : nat) (H : 0 < i) (H' : i <= 7)
  (outputDisable : Stream bool) (grant : Stream (d_list bool 2))
  (d : Stream (d_list (d_list bool 8) 4))
  (old_mux : d_list (d_list bool 2) 2) :=
  DMUX2B4CA11 old_mux outputDisable grant
    (dlist_to_Stream
       (List2 (S_map (list_of_nth (i:=i) (n:=8) H (le_leS H') (n0:=4)) d)
          (S_map
             (list_of_nth (i:=S i) (n:=8) (lt_O_Sn i) (le_n_S i 7 H') (n0:=4))
             d))).
 



Definition DATASWITCHC (outputDisable : Stream bool)
  (grant : Stream (d_list bool 2)) (d : Stream (d_list (d_list bool 8) 4))
  (old_mux : d_list (d_list (d_list bool 2) 2) 4) :=
  dlist_to_Stream
    (List4
       (DATASWITCHC_AUX lt_O_1 le_1_7 outputDisable grant d
          (Fst_of_l4 old_mux))
       (DATASWITCHC_AUX lt_O_3 le_3_7 outputDisable grant d
          (Scd_of_l4 old_mux))
       (DATASWITCHC_AUX lt_O_5 le_5_7 outputDisable grant d
          (Thd_of_l4 old_mux))
       (DATASWITCHC_AUX lt_O_7 le_7_7 outputDisable grant d
          (Fth_of_l4 old_mux))).


Definition DATASWITCH_N_AUX (i : nat) (H : 0 < i) (H' : i <= 4)
  (outputDisable : Stream (d_list bool 4))
  (grant : Stream (d_list (d_list bool 2) 4))
  (d : Stream (d_list (d_list bool 8) 4))
  (old_mux : d_list (d_list bool 2) 8) :=
  DATASWITCHC (S_Nth (i:=i) H H' outputDisable) (S_Nth (i:=i) H H' grant) d
    (Fold_List (n:=2) (m:=4) old_mux).


Definition DATASWITCH_N (outputDisable : Stream (d_list bool 4))
  (grant : Stream (d_list (d_list bool 2) 4))
  (d : Stream (d_list (d_list bool 8) 4))
  (old_mux : d_list (d_list (d_list bool 2) 8) 4) :=
  S_map (d_map (Unfold_List (n:=2) (m:=4)) (n:=4))
    (dlist_to_Stream
       (List4
          (DATASWITCH_N_AUX lt_O_1 le_1_4 outputDisable grant d
             (Fst_of_l4 old_mux))
          (DATASWITCH_N_AUX lt_O_2 le_2_4 outputDisable grant d
             (Scd_of_l4 old_mux))
          (DATASWITCH_N_AUX lt_O_3 le_3_4 outputDisable grant d
             (Thd_of_l4 old_mux))
          (DATASWITCH_N_AUX lt_O_4 le_4_4 outputDisable grant d
             (Fth_of_l4 old_mux)))).



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
  (fs, (routeEnable, Two_Fst_of_l4 req),
  (fs, (routeEnable, Two_last_of_l4 req))).

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


(** PRIORITY_DECODE should be a Mealy automaton too **)

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

 Definition Structure_TIMING_PDECODE (i : Stream Input_vector_type)
   (l : d_list bool 2) (reg : d_list (d_list bool 4) 4) :=
   PC Timing_Aux Trans_priority_decode Out_Struct_Timing Out_priority_decode
     f_tp output_tp i (l, reg).

 Definition States_TIMING_PDECODE (i : Stream Input_vector_type)
   (l : d_list bool 2) (reg : d_list (d_list bool 4) 4) :=
   States_PC Timing_Aux Trans_priority_decode f_tp i (l, reg).

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


 Definition Structure_TIMINGPDECODE_ID (i : Stream Input_vector_type)
   (id : state_id) (old : d_list bool 2 * d_list (d_list bool 4) 4) :=
   PC (Trans_id (Input_type:=bool)) TransPC_Timing_PDecode
     (Out_id (Input_type:=bool)) OutPC_Timing_PDecode f_tpi output_tpi i
     (id, old).


 Definition States_TIMINGPDECODE_ID (i : Stream Input_vector_type)
   (id : state_id) (old : d_list bool 2 * d_list (d_list bool 4) 4) :=
   States_PC (Trans_id (Input_type:=bool)) TransPC_Timing_PDecode f_tpi i
     (id, old).

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


  Definition Structure_ARBITRATION (i : Stream Input_vector_type)
    (old_tpi : state_id * (d_list bool 2 * d_list (d_list bool 4) 4))
    (old_arbiters : d_list bool 2 * bool * (d_list bool 2 * bool) *
                    (d_list bool 2 * bool * (d_list bool 2 * bool))) :=
    SC TransPC_TimingPDecode_Id Trans_Struct_four_arbiters
      OutPC_TimingPDecode_Id Out_Struct_four_arbiters i
      (old_tpi, old_arbiters).


  Definition StatesSC_ARBITRATION (i : Stream Input_vector_type)
    (old_tpi : state_id * (d_list bool 2 * d_list (d_list bool 4) 4))
    (old_arbiters : d_list bool 2 * bool * (d_list bool 2 * bool) *
                    (d_list bool 2 * bool * (d_list bool 2 * bool))) :=
    States_SC TransPC_TimingPDecode_Id Trans_Struct_four_arbiters
      OutPC_TimingPDecode_Id i (old_tpi, old_arbiters).


End Arbitration_Structure.
