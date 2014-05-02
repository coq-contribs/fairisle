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
(*                       Equiv_Struct_Beh_Arbitration.v                     *)
(****************************************************************************)
 
Require Import Timing_Arbiter.
Require Import Arbitration_beh_sc.
Require Import Arbitration.
Require Import Arbiter4_Proof.
Require Import Arbitration_Proof.
Require Import Lemmas_for_Arbitration.

Set Implicit Arguments.
Unset Strict Implicit.


Section Struct_Beh_Arbitration.

  Let Input_type :=
    (bool * (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4)))%type.


  Lemma Equiv_tpi :
   forall i i' : Stream Input_type,
   EqS i i' ->
   forall (sa1 : state_id * (d_list bool 2 * d_list (d_list bool 4) 4))
     (sb1 : state_id * (label_t * STATE_p)),
   fst sa1 = fst sb1 ->
   R_Timing (fst (snd sb1)) (fst (snd sa1)) ->
   R_Priority_Decode (snd (snd sb1)) (snd (snd sa1)) ->
   EqS (Mealy TransPC_TimingPDecode_Id OutPC_TimingPDecode_Id i sa1)
     (Mealy Trans_TimingPDecode_Id Out_TimingPDecode_Id i' sb1).

  intros i i' H sa1 sb1.
  elim sa1; clear sa1; intros ri olds; elim olds; clear olds; intros rt rp.
  elim sb1; clear sb1; intros si olds; elim olds; clear olds; intros st sp.
  simpl in |- *.
  intros H0 Ht Hp; elim H0.
  unfold TransPC_TimingPDecode_Id in |- *;
   unfold Trans_TimingPDecode_Id in |- *.
  unfold OutPC_TimingPDecode_Id in |- *; unfold Out_TimingPDecode_Id in |- *.

  apply PC_Mealy.
  try trivial.

  apply equiv_PC.
  try trivial.

  apply EqS_Mealy.
  try trivial.

  apply S_map_f.
  apply S_map_f.
  apply EqS_reflex.

  unfold TransPC_Timing_PDecode in |- *; unfold Trans_Timing_PDecode in |- *.
  unfold OutPC_Timing_PDecode in |- *; unfold Out_Timing_PDecode in |- *.
  apply PC_Mealy.
  apply S_map_f.
  apply S_map_f.
  apply EqS_reflex.

  apply equiv_PC.
  apply S_map_f.
  apply S_map_f.
  apply EqS_reflex.

  apply EqS_sym; apply Correct_TIMING.
  try trivial.

  apply EqS_sym; apply Correct_PRIORITY_DECODE.
  try trivial.
  Qed.



  Lemma Equiv_a4 :
   forall i i' : Stream (bool * (bool * d_list (d_list bool 4) 4)),
   EqS i i' ->
   forall
     (sa2 : d_list bool 2 * bool * (d_list bool 2 * bool) *
            (d_list bool 2 * bool * (d_list bool 2 * bool))) 
     (sb2 : STATE_a4),
   R_a4 sb2 sa2 ->
   Inv P_a4 i (States_FOUR_ARBITERS i sb2)
     (Structure_States_FOUR_ARBITERS i sa2) ->
   EqS (Mealy Trans_Struct_four_arbiters Out_Struct_four_arbiters i sa2)
     (Mealy Trans_Four_Arbiters Out_Four_Arbiters_Mealy i' sb2).
  intros.
  apply Equiv_2_Mealy_tool; try trivial.
  apply EqS_sym; apply Correct_FOUR_ARBITERS; try trivial.
  Qed.




(** Hypotheses sur les signaux d'entree fs at act **)


  Variable i : Stream Input_type.

  Let Fs := S_map fstS i.

  Let Act := S_map fstS (S_map sndS i).

  Hypothesis fs_0 : S_head Fs = false.

  Hypothesis
    fs_act_signals : EqS sig_false (S_map2 andb (S_tail Fs) (S_Ackor Act)).   
  


  Lemma Equiv_Struct_Beh_Arbitration :
   forall (stpia4 : state_id * (label_t * STATE_p) * STATE_a4)
     (regs : state_id * (d_list bool 2 * d_list (d_list bool 4) 4) *
             (d_list bool 2 * bool * (d_list bool 2 * bool) *
              (d_list bool 2 * bool * (d_list bool 2 * bool)))),
   fst (fst stpia4) = fst (fst regs) ->
   R_a4 (snd stpia4) (snd regs) ->
   R_Timing (fst (snd (fst stpia4))) (fst (snd (fst regs))) ->
   R_Priority_Decode (snd (snd (fst stpia4))) (snd (snd (fst regs))) ->
   Inv_t_a4 (snd stpia4) (fst (snd (fst stpia4))) ->
   EqS (Structure_ARBITRATION i regs) (BehaviourSC_ARBITRATION i stpia4).

  unfold Structure_ARBITRATION in |- *;
   unfold BehaviourSC_ARBITRATION in |- *.
  intros stpia4 regs.
  elim regs; clear regs; intros ritp ra4.
  elim stpia4; clear stpia4; intros sitp sa4.
   elim ritp; clear ritp; intros ri rtp; elim rtp; clear rtp; intros rt rp.
 elim sitp; clear sitp; intros si stp; elim stp; clear stp; simpl in |- *;
  intros st sp H HRa4 Ht Hp HI.
  apply equiv_SC.
  apply Equiv_a4.
  apply Equiv_tpi; auto.
  apply EqS_reflex.
  auto.
  apply
   eqS_about_P
    with
      (i' := Behaviour_TIMINGPDECODE_ID i (si, (st, sp)))
      (s1' := States_FOUR_ARBITERS
                (Behaviour_TIMINGPDECODE_ID i (si, (st, sp))) sa4)
      (s2' := Structure_States_FOUR_ARBITERS
                (Behaviour_TIMINGPDECODE_ID i (si, (st, sp))) ra4).

  change
    (EqS
       (Mealy TransPC_TimingPDecode_Id OutPC_TimingPDecode_Id i
          (ri, (rt, rp)))
       (Mealy Trans_TimingPDecode_Id Out_TimingPDecode_Id i (si, (st, sp))))
   in |- *.
  apply Equiv_tpi; auto.
  apply EqS_reflex.
  unfold States_FOUR_ARBITERS in |- *.
  apply EqS_States_Mealy.
  auto.
  change
    (EqS
       (Mealy TransPC_TimingPDecode_Id OutPC_TimingPDecode_Id i
          (ri, (rt, rp)))
       (Mealy Trans_TimingPDecode_Id Out_TimingPDecode_Id i (si, (st, sp))))
   in |- *.
  apply Equiv_tpi; auto.
  apply EqS_reflex.
  unfold Structure_States_FOUR_ARBITERS in |- *.
  unfold States_PC in |- *.
  apply EqS_States_Mealy.
  auto.
  change
    (EqS
       (Mealy TransPC_TimingPDecode_Id OutPC_TimingPDecode_Id i
          (ri, (rt, rp)))
       (Mealy Trans_TimingPDecode_Id Out_TimingPDecode_Id i (si, (st, sp))))
   in |- *.
  apply Equiv_tpi; auto.
  apply EqS_reflex.
  apply Inv_a4'; auto.
  Qed.



 (** Correction a partir de l'etat initial **)

 (** Don't care values of registers **)

  Variable g11_0 g12_0 g21_0 g22_0 : bool * bool.      (* lasts *)
  Variable p_0 : d_list (d_list bool 4) 4.    (* ltReq *)


  Lemma Correct_ARBITRATION_end :
   EqS
     (Behaviour_ARBITRATION i
        (WAIT_BEGIN_A, (List4 g11_0 g12_0 g21_0 g22_0, (l4_ffff, p_0))))
     (Structure_ARBITRATION i
        (IDENTITY, (l2_ff, p_0),
        (pdt_List2 g11_0, false, (pdt_List2 g12_0, false),
        (pdt_List2 g21_0, false, (pdt_List2 g22_0, false))))).

  apply
   EqS_trans
    with
      (BehaviourSC_ARBITRATION i
         (IDENTITY, (START_t, (START_p, p_0)),
         (WAIT_a4, (List4 g11_0 g12_0 g21_0 g22_0, l4_ffff)))).

  apply Correct_ARBITRATION.

  apply Inv_P_Timing_Inv_A.
  apply
   eqS_Inv_P_Timing
    with
      (S_map fstS i)
      (States_TIMING
         (Compact (S_map fstS i)
            (S_map fstS (S_map sndS i))) START_t).
  apply EqS_reflex.
  apply EqS_Snd_SC_TIMING.
  apply Is_Inv_P_Timing; try trivial.

  apply Invariant_Init_states_A.

  apply EqS_sym.
  apply Equiv_Struct_Beh_Arbitration.
  simpl in |- *; auto.

  rewrite Rewrite_Snd.
  rewrite Rewrite_Snd.
  apply Invariant_Init_states_a4.

  simpl in |- *.
  unfold R_Timing in |- *; auto.

  simpl in |- *.
  unfold R_Priority_Decode in |- *; auto.

  rewrite Rewrite_Snd; rewrite Rewrite_Fst; rewrite Rewrite_Snd;
   rewrite Rewrite_Fst.
  apply Inv_Init_states_t_a4.

  Qed.


End Struct_Beh_Arbitration.