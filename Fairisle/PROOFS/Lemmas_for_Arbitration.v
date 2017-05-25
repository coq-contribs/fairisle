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
(*                         Lemmas_for_Arbitration.v                         *)
(****************************************************************************)

Require Export Behaviour_Struct_lemmas.
Require Export Timing_Arbiter.
Require Export Arbitration_Proof.
Require Export Arbitration_Specif.
Require Export Arbitration_beh_sc.

Set Implicit Arguments.
Unset Strict Implicit.


Lemma Inv_P_Timing_Inv_A :
 forall
   (i : Stream
          (bool *
           (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4))))
   (sA : Stream STATE_A)
   (sitpa4 : Stream (state_id * (label_t * STATE_p) * STATE_a4)),
 Inv_P_Timing (S_map fstS i) (S_Snd_of_3 (S_map fstS sitpa4)) ->
 Inv P_A i sA sitpa4.
cofix.
intros i sA sitpa4 H_p.
inversion_clear H_p.
apply C_Inv.
unfold P_A in |- *; simpl in H.
generalize H; clear H.
elim (S_head sitpa4); intros itp sa4.
elim itp; intros si tp.
elim tp; intros t p.
simpl in |- *; try trivial.
elim (S_head i); simpl in |- *.
intros y y0; elim y0; simpl in |- *; auto.
apply Inv_P_Timing_Inv_A; try trivial.
Qed.


 Definition f_tpi
   (i : bool * (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4))) :=
   let (fs, t) := i in
   let (act, p) := t in
   let (pri, route) := p in (fs, (fs, (act, (pri, route)))).

 Definition f_tp
   (i : bool * (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4))) :=
   let (fs, t) := i in
   let (act, p) := t in
   let (pri, route) := p in (fs, act, (act, (pri, route))).


  Lemma S_Snd_S_f_tpi_simpl :
   forall
     i : Stream
           (bool *
            (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4))),
   EqS (S_map sndS (S_map f_tpi i)) i.
  cofix.
  intro i'.
  apply eqS; simpl in |- *.
  unfold f_tpi in |- *.
  elim (S_head i'); intros fs y.
  elim y; intros act y'.
  elim y'; intros pri route; auto.
  auto.
  Qed.

  Lemma S_Fst_S_f_tp_simpl :
   forall
     i : Stream
           (bool *
            (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4))),
   EqS (S_map fstS (S_map f_tp i))
     (Compact (S_map fstS i)
        (S_map fstS (S_map sndS i))).
  cofix.
  intro.
  apply eqS.
  simpl in |- *; auto.
  unfold f_tp in |- *; auto.
  elim (S_head i); intros y y0.
  elim y0; intros y1 y2.
  elim y2; intros y3 y4.
  auto.
  simpl in |- *; auto.
  Qed.


  Lemma EqS_Snd_SC_TIMING :
   forall
     (i : Stream
            (bool *
             (d_list bool 4 * (d_list bool 4 * d_list (d_list bool 2) 4))))
     (si : state_id) (st : label_t) (sp : STATE_p) 
     (sa4 : STATE_a4),
   EqS
     (S_Snd_of_3
        (S_map fstS (States_Beh_SC_ARBITRATION i (si, (st, sp), sa4))))
     (States_TIMING
        (Compact (S_map fstS i)
           (S_map fstS (S_map sndS i))) st).

  intros i si st sp sa4.
  unfold States_Beh_SC_ARBITRATION in |- *.
  apply
   EqS_trans with (S_Snd_of_3 (States_Beh_TIMINGPDECODE_ID i (si, (st, sp)))).
  apply EqS_S_Snd_of_3.
  unfold States_Beh_TIMINGPDECODE_ID in |- *; unfold States_PC in |- *;
   unfold Trans_TimingPDecode_Id in |- *.
  apply States_SC_simpl.
  unfold States_Beh_TIMINGPDECODE_ID in |- *.

  apply
   EqS_trans
    with
      (S_Snd_of_3
         (Compact (States_IDENTITY (S_map fstS (S_map f_tpi i)) si)
            (States_Beh_TIMING_PDECODE (S_map sndS (S_map f_tpi i))
               (st, sp)))).

  apply EqS_S_Snd_of_3.
  unfold States_IDENTITY in |- *; unfold States_Beh_TIMING_PDECODE in |- *;
   unfold States_PC at 2 in |- *.
  apply EqS_sym; apply Equiv_States_A1A2_PC.

  apply
   EqS_trans
    with
      (S_Snd_of_3
         (Compact (States_IDENTITY (S_map fstS (S_map f_tpi i)) si)
            (States_Beh_TIMING_PDECODE i (st, sp)))).

  apply EqS_S_Snd_of_3.
  apply EqS_Compact.
  apply EqS_reflex.
  unfold States_Beh_TIMING_PDECODE in |- *; apply Equiv_States_PC; auto.
  apply S_Snd_S_f_tpi_simpl.
  apply
   EqS_trans
    with
      (S_Snd_of_3
         (Compact (States_IDENTITY (S_map fstS (S_map f_tpi i)) si)
            (Compact (States_TIMING (S_map fstS (S_map f_tp i)) st)
               (States_PRIORITY_DECODE (S_map sndS (S_map f_tp i)) sp)))).
  apply EqS_S_Snd_of_3.
  apply EqS_Compact.
  apply EqS_reflex.
  unfold States_TIMING in |- *; unfold States_PRIORITY_DECODE in |- *;
   unfold States_Beh_TIMING_PDECODE in |- *.
  apply EqS_sym; apply Equiv_States_A1A2_PC.
  apply EqS_trans with (States_TIMING (S_map fstS (S_map f_tp i)) st).  apply S_Snd_of_3_Compact.
  unfold States_TIMING in |- *.
  apply EqS_States_Mealy.
  try trivial.
  apply S_Fst_S_f_tp_simpl.
  Qed.


