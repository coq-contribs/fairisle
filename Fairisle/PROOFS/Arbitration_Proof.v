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
(*                           Arbitration_Proof.v                            *)
(****************************************************************************)

Require Import Arbitration_Specif.
Require Import Arbitration_beh_sc.
Require Export Timing_Arbiter.

Set Implicit Arguments.
Unset Strict Implicit.


Section Arbitration_Correctness.


  Let Input_type :=
    (bool * (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4)))%type.


(** Don't care values of registers **)

  Variable g11_0 g12_0 g21_0 g22_0 : bool * bool.  (* lasts *)
  Variable o_a4_0 : d_list bool 4.         (* outputDisables *)
  Variable p_0 : d_list (d_list bool 4) 4. (* ltReq *)


(** R_A is an invariant property **)

  Lemma Invariant_Init_states_A :
   R_A (WAIT_BEGIN_A, (List4 g11_0 g12_0 g21_0 g22_0, (o_a4_0, p_0)))
     (IDENTITY, (START_t, (START_p, p_0)),
     (WAIT_a4, (List4 g11_0 g12_0 g21_0 g22_0, o_a4_0))).
  unfold R_A in |- *; split; auto.
  Qed.



(** Invariant proof **)

  Lemma Invariant_relation_A :
   Inv_under_P Trans_Arbitration TransSC_Arbitration_beh P_A R_A.

  unfold Inv_under_P in |- *.
  intros i sA ssc.
  elim i.
  intros fs inp.
  elim inp; clear inp.
  intros act inp.
  elim inp; clear inp.
  intros pri route.
  elim sA; elim ssc; simpl in |- *.
  clear sA ssc.
  intros stpi sa4 sA oldA.
  elim stpi; elim sa4; clear stpi sa4.
  intros sa4 olda4 si stp.
  elim stp; clear stp; intros st sp.
  elim sp; clear sp; intros sp oldp.
  elim oldA; clear oldA; intros g oldA; elim oldA; clear oldA; intros o l.
  elim olda4; clear olda4; intros g_a4 o_a4.

  intros p_A H.
  elim H; clear H; intros H H'.
  elim H'; clear H'; intros H1 H'; elim H'; clear H'; intros H2 H3.
  unfold P_Timing in p_A.

  (** sA=WAIT_BEGIN_A /\ st=START_t /\ sa4=WAIT_a4 /\ sp=START_p **)

  elim H; clear H; intro H.
  elim H; clear H; intros H H'; elim H'; clear H'; intros H' H''; elim H'';
   clear H''; intros H'' H'''; rewrite H; rewrite H'; 
   rewrite H''; rewrite H'''; simpl in |- *.
  case fs; simpl in |- *.
  split; auto.
  right; right; left; auto.
  split; auto.
  right; auto.

  (** sA=WAIT_BEGIN_A /\ st=START_t /\ sa4=WAIT_a4 /\ sp=DECODE_p **)

  elim H; clear H; intro H.
  elim H; clear H; intros H H'; elim H'; clear H'; intros H' H''; elim H'';
   clear H''; intros H'' H'''; rewrite H; rewrite H'; 
   rewrite H''; rewrite H'''; simpl in |- *.
  case fs; simpl in |- *.
  split; auto.
  right; right; left; auto.
  split; auto.
  right; auto.

  (** sA=START_A /\ st=WAIT_t /\ sa4=START_a4 /\ sp=DECODE_p **)

  elim H; clear H; intro H.
  elim H; clear H; intros H H'; elim H'; clear H'; intros H' H''; elim H'';
   clear H''; intros H'' H'''; elim H'''; clear H'''; 
   intros H''' H_o; rewrite H; rewrite H'; rewrite H''; 
   rewrite H'''; rewrite H_o; simpl in |- *.
  case fs; case (Ackor act); simpl in |- *.
  split; auto.
  right; right; left; auto.
  split; auto.
  right; right; left; auto.
  split; auto.
  right; right; right; left; auto.
  split; auto.
  right; right; left; auto.

  (** sA=ACTIVE_A /\ st=ROUTE_t /\ sa4=START_a4 /\ sp=DECODE_p **)

  elim H; clear H; intro H.
  elim H; clear H; intros H H'; elim H'; clear H'; intros H' H''; elim H'';
   clear H''; intros H'' H'''; elim H'''; clear H'''; 
   intros H''' H_o; rewrite H; rewrite H'; rewrite H''; 
   rewrite H'''; rewrite H_o; simpl in |- *.
  elim (bool_dec fs); intro H_fs.
  generalize p_A; rewrite H_fs; simpl in |- *.
  rewrite H'; simpl in |- *; intro Abs.
  absurd (true = false); auto with bool.
  rewrite H_fs; simpl in |- *.
  rewrite H3.
  elim (Ackor (d_map (Ackor (n:=3)) oldp)); simpl in |- *.
  split; auto.
  right; right; right; right; right; auto.
  split; auto.
  rewrite H1; auto.
  split; auto.
  right; right; right; right; left; auto.

  (** sA=NOT_TRIGGER_A /\ st=START_t /\ sa4=START_a4 /\ sp=DECODE_p **)

  elim H; clear H; intro H.
  elim H; clear H; intros H H'; elim H'; clear H'; intros H' H''; elim H'';
   clear H''; intros H'' H'''; elim H'''; clear H'''; 
   intros H''' H_o; rewrite H; rewrite H'; rewrite H''; 
   simpl in |- *.
  case fs; simpl in |- *.
  split; auto.
  right; right; left; auto.
  split; auto.
  right; right; right; right; left; auto.

  (** sA=TRIGGER_A /\ st=START_t /\ sa4=AT_LEAST_ONE_IS_ACTIVE_a4 /\ sp=DECODE_p **)

  elim H; clear H; intros H H'; elim H'; clear H'; intros H' H''; elim H'';
   clear H''; intros H'' H'''; rewrite H; rewrite H'; 
   rewrite H''; rewrite H'''; simpl in |- *.
  case fs; simpl in |- *.
  split; auto.
  right; right; left; auto.
  split; auto.
  right; left; auto.

Qed.



(** Equality of the outputs **)


  Lemma Output_relation_A :
   Output_rel Out_Arbitration_Mealy OutSC_Arbitration_beh R_A.

  unfold Output_rel in |- *.
  intros i sA ssc.
  elim sA; elim ssc; simpl in |- *.
  clear sA ssc.
  intros stpi sa4 sA oldA.
  elim stpi; elim sa4; clear stpi sa4.
  intros sa4 olda4 si stp.
  elim stp; clear stp; intros st sp.
  elim sp; clear sp; intros sp oldp.
  elim oldA; clear oldA; intros g oldA; elim oldA; clear oldA; intros o l. 
  elim olda4; clear olda4; intros g_a4 o_a4 H.
  elim H; clear H; intros H H'; clear H.
  elim H'; clear H'; intros H1 H'; elim H'; clear H'; intros H2 H3.
  rewrite H1; rewrite H2; auto.
  Qed.



(** Correctness of the ARBITRATION unit **)


  Lemma Correct_ARBITRATION :
   forall (i : Stream Input_type) (sA : STATE_A)
     (stpia4 : state_id * (label_t * STATE_p) * STATE_a4),
   Inv P_A i (States_ARBITRATION i sA) (States_Beh_SC_ARBITRATION i stpia4) ->
   R_A sA stpia4 ->
   EqS (Behaviour_ARBITRATION i sA) (BehaviourSC_ARBITRATION i stpia4).

  intros i sA stpia4 HP HR.
  unfold Behaviour_ARBITRATION in |- *;
   unfold BehaviourSC_ARBITRATION in |- *.
  apply (Equiv_2_Mealy Invariant_relation_A Output_relation_A HP HR).

  Qed.


End Arbitration_Correctness.