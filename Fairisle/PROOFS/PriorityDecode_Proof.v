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
(*                          PriorityDecode_Proof.v                          *)
(****************************************************************************)


Require Export PickSuccessfulInput.
Require Export Arbitration.
Require Export Moore_Mealy.


Set Implicit Arguments.
Unset Strict Implicit.

Section PriorityDecode_Correctness.

  Let Input_type :=
    (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4))%type.

  Let Output_type := d_list (d_list bool 4) 4.

  Inductive label_p : Set :=
    | START_p : label_p
    | DECODE_p : label_p.

  Definition STATE_p : Set := (label_p * d_list (d_list bool 4) 4)%type.


(** Automaton describing the transitions from a state to another **)

  Definition Convert_and_filter (i : Input_type) : Output_type :=
    let (act, p) := i in
    let (pri, route) := p in
    d_map (PriorityRequests act pri) (merge (d_map Convert_list2 route)).


  Definition Trans_PriorityDecode (i : Input_type) 
    (s : STATE_p) : STATE_p := (DECODE_p, Convert_and_filter i).



(** Each state corresponds to a result **)

  Definition Out_PriorityDecode (s : STATE_p) : Output_type :=
    let (s', old) := s in old.


(** States stream **)

  Definition States_PRIORITY_DECODE := States_Mealy Trans_PriorityDecode.


(** Intented behaviour **)

  Definition Behaviour_PRIORITY_DECODE :=
    Moore Trans_PriorityDecode Out_PriorityDecode.


(** Transformation of Behaviour_PRIORITY_DECODE to a Mealy automaton **)

  Definition Out_PriorityDecode_Mealy :=
    Out_Mealy (Input_type:=Input_type) Out_PriorityDecode.

  Lemma equiv_out_PriorityDecode :
   forall (i : Input_type) (s : STATE_p),
   Out_PriorityDecode s = Out_PriorityDecode_Mealy i s.
  Proof.
  auto.
  Qed.


  Lemma Equiv_PriorityDecode_Moore_Mealy :
   forall (s : STATE_p) (i : Stream Input_type),
   EqS (Behaviour_PRIORITY_DECODE i s)
     (Mealy Trans_PriorityDecode Out_PriorityDecode_Mealy i s).
  Proof.
  intros s i.
  unfold Behaviour_PRIORITY_DECODE in |- *;
   unfold Out_PriorityDecode_Mealy in |- *; apply Equiv_Moore_Mealy.
  Qed.


  Definition States_Structure_PRIORITY_DECODE :=
    States_Mealy Trans_priority_decode.


 (** No invariant property *)

  Let Reg_type := d_list (d_list bool 4) 4. (* Type of the registers of PRIORITY_DECODE *)


  Let Cst_True (i : Input_type) (s : STATE_p) (reg : Reg_type) := True.


  Definition R_Priority_Decode (s : STATE_p) (reg : Reg_type) :=
    reg = Out_PriorityDecode s.


 (* Cst_True is an invariant *)

  Lemma Cst_True_inv_pdecode :
   forall (i : Stream Input_type) (s : STATE_p) (reg : Reg_type),
   Inv Cst_True i (States_PRIORITY_DECODE i s)
     (States_Structure_PRIORITY_DECODE i reg).

  Proof.
  cofix Cst_True_inv_pdecode.
  intros i s reg.
  apply Inv_Ok.
  unfold Cst_True in |- *; auto.
  Qed.


(** Because the unit is essentially combinational, we assume its correctness **)

  Axiom
    Invariant_relation_p :
      Inv_under_P Trans_PriorityDecode Trans_priority_decode Cst_True
        R_Priority_Decode.



  Lemma Output_relation_p :
   Output_rel Out_PriorityDecode_Mealy Out_priority_decode R_Priority_Decode.

  Proof.
  unfold Output_rel in |- *; auto.
  Qed.


(** Correctness lemma  **)

  Lemma Correct_PRIORITY_DECODE :
   forall (i : Stream Input_type) (reg : Reg_type) (s : STATE_p),
   R_Priority_Decode s reg ->
   EqS (Behaviour_PRIORITY_DECODE i s) (Structure_PRIORITY_DECODE i reg).

  Proof.
  intros i reg s HR.
  unfold Structure_PRIORITY_DECODE in |- *;
   unfold Behaviour_PRIORITY_DECODE in |- *.
  apply
   (Equiv_2_Mealy Invariant_relation_p Output_relation_p
      (Cst_True_inv_pdecode i s reg) HR).

  Qed.


End PriorityDecode_Correctness.
