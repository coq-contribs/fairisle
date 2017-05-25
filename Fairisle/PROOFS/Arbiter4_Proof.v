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
(*                             Arbiter4_Proof.v                             *)
(****************************************************************************)
 

(** This is the proof of correctness of the parallel composition of **)
(** four ARBITER units **)


Require Export Arbiter4_Specif.
Require Export Lemmas_on_Basic_rules.
Require Export Invariant_a4_S.



Set Implicit Arguments.
Unset Strict Implicit.


Section Four_Arbiters_Proof_Correctness.

  Let Input_type := (bool * (bool * d_list (d_list bool 4) 4))%type.

  Let Reg_type :=
    (d_list bool 2 * bool * (d_list bool 2 * bool) *
     (d_list bool 2 * bool * (d_list bool 2 * bool)))%type.


(** Don't care values of registers **)

  Variable g11_0 g12_0 g21_0 g22_0 : bool * bool.    


(** R_a4 is an invariant property **)

  Lemma Invariant_Init_states_a4 :
   R_a4 (WAIT_a4, (List4 g11_0 g12_0 g21_0 g22_0, l4_ffff))
     (pdt_List2 g11_0, false, (pdt_List2 g12_0, false),
     (pdt_List2 g21_0, false, (pdt_List2 g22_0, false))).

  unfold R_a4 in |- *; split.
  do 6 right.
  split; auto.
  unfold At_least_one_of_2_active in |- *.
  right; right; left; auto.
  auto.
  Qed.



(** Invariant proof with the hypothesis that RouteE is low when we are    **)
(** in an active cycle (AT_LEAST_ONE_IS_ACTIVE_a2 or WAIT_a2) : see ArbiterTiming_Proof.v **)


  Lemma Invariant_relation_a4 :
   Inv_under_P Trans_Four_Arbiters Trans_Struct_four_arbiters P_a4 R_a4.

  unfold Inv_under_P in |- *.
  intros i sa4 old.
  elim i.
  intros fs inp.
  elim inp; clear inp.
  intros RouteE ltReq.
  elim sa4; elim old; simpl in |- *.
  clear sa4 old.
  intros old1 old2 sa4 old; elim old; intros g o.
  clear old; elim old1; elim old2; clear old1 old2; simpl in |- *.
  intros old1 old2 old3 old4.
  elim old1; elim old2; elim old3; elim old4; clear old1 old2 old3 old4.
  intros g12 o12 g11 o11 g22 o22 g21 o21.
  unfold R_a4 at 1 in |- *.
  intros pa4 H; simpl in pa4.
  elim H; clear H; intros H H'; simpl in H'.

  generalize (eq_pair H'); intro h; elim h; clear h; intros H1 H2.
  generalize (eq_pair H1); clear H1; intro H1; elim H1; clear H1;
   intros H11 H12.
  generalize (eq_pair H2); clear H2; intro H2; elim H2; clear H2;
   intros H21 H22.

  generalize (id_list3_fst H11); generalize (id_list3_scd H11);
   generalize (id_list3_thd H11); intros h11 h12 h13; 
   clear H11.
  generalize (id_list3_fst H12); generalize (id_list3_scd H12);
   generalize (id_list3_thd H12); intros h21 h22 h23; 
   clear H12.
  generalize (id_list3_fst H21); generalize (id_list3_scd H21);
   generalize (id_list3_thd H21); intros h31 h32 h33; 
   clear H21.
  generalize (id_list3_fst H22); generalize (id_list3_scd H22);
   generalize (id_list3_thd H22); intros h41 h42 h43; 
   clear H22.


  (** sa4=START_a4 /\ s2=START_a2 /\ s1=START_a2 **)

  elim H; clear H; intro H.
  generalize
   (Invariant_a4_SSS (fs:=fs) (RouteE:=RouteE) (ltReq:=ltReq) (sa4:=sa4)
      (g:=g) (o:=o) (old11:=(g11, o11)) (old12:=(g12, o12))
      (old21:=(g21, o21)) (old22:=(g22, o22)) H).
  intro I; apply I.
  auto.
  unfold R_a4 in |- *; unfold Out_Four_Arbiters in |- *; auto.


 (** sa4=AT_LEAST_ONE_IS_ACTIVE_a4 /\ s2=START_a2 /\ s1=AT_LEAST_ONE_IS_ACTIVE_a2 **)

  elim H; clear H; intro H.
  elim H; clear H; intros H H0.
  rewrite H; simpl in |- *.
  elim h11; elim h12; elim h13; elim h21; elim h22; elim h23; elim h31;
   elim h32; elim h33; elim h41; elim h42; elim h43; 
   auto. 
  case fs; rewrite pa4; simpl in |- *.
  split; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0; rewrite H0; simpl in |- *; auto.
  auto.
  split.
  right; right; right; right; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0; rewrite H0; simpl in |- *; auto.
  auto.


 (** sa4=AT_LEAST_ONE_IS_ACTIVE_a4 /\ s1=AT_LEAST_ONE_IS_ACTIVE_a2 /\ s1=START_a2 **)

  elim H; clear H; intro H.
  elim H; clear H; intros H H0.
  rewrite H; simpl in |- *.
  elim h11; elim h12; elim h13; elim h21; elim h22; elim h23; elim h31;
   elim h32; elim h33; elim h41; elim h42; elim h43; 
   auto. 
  case fs; rewrite pa4; simpl in |- *.
  split; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0; rewrite H0; simpl in |- *; auto.
  auto.
  split.
  right; right; right; right; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0; rewrite H0; simpl in |- *; auto.
  auto.


 (** sa4=AT_LEAST_ONE_IS_ACTIVE_a4 /\ s2=AT_LEAST_ONE_IS_ACTIVE_a2 /\ s1=AT_LEAST_ONE_IS_ACTIVE_a2 **)

  elim H; clear H; intro H.
  elim H; clear H; intros H H0.
  rewrite H; simpl in |- *.
  elim h11; elim h12; elim h13; elim h21; elim h22; elim h23; elim h31;
   elim h32; elim h33; elim h41; elim h42; elim h43; 
   auto. 
  case fs; rewrite pa4; simpl in |- *.
  split; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0; rewrite H0; simpl in |- *; auto.
  auto.
  split.
  right; right; right; right; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0; rewrite H0; simpl in |- *; auto.
  auto.


 (** sa4=WAIT_a4 /\ s2=START_a2 /\ s1=WAIT_a2 **)

  elim H; clear H; intro H.
  elim H; clear H; intros H H0.
  rewrite H; simpl in |- *.
  elim h11; elim h12; elim h13; elim h21; elim h22; elim h23; elim h31;
   elim h32; elim h33; elim h41; elim h42; elim h43; 
   auto. 
  case fs; rewrite pa4; simpl in |- *.
  split; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0; rewrite H0; simpl in |- *; auto.
  auto.
  split.
  right; right; right; right; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0; rewrite H0; simpl in |- *; auto.
  auto.


 (** sa4=WAIT_a4 /\ s2=WAIT_a2 /\ s1=START_a2 **)

  elim H; clear H; intro H.
  elim H; clear H; intros H H0.
  rewrite H; simpl in |- *.
  elim h11; elim h12; elim h13; elim h21; elim h22; elim h23; elim h31;
   elim h32; elim h33; elim h41; elim h42; elim h43; 
   auto. 
  case fs; rewrite pa4; simpl in |- *.
  split; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0; rewrite H0; simpl in |- *; auto.
  auto.
  split.
  right; right; right; right; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0; rewrite H0; simpl in |- *; auto.
  auto.


 (** sa4=WAIT_a4 /\ s2=WAIT_a2 /\ s1=WAIT_a2 **)

  elim H; clear H; intros H H0.
  rewrite H; simpl in |- *.
  elim h11; elim h12; elim h13; elim h21; elim h22; elim h23; elim h31;
   elim h32; elim h33; elim h41; elim h42; elim h43; 
   auto. 
  case fs; rewrite pa4; simpl in |- *.
  split; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0; rewrite H0; simpl in |- *; auto.
  auto.
  split.
  right; right; right; right; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0.
  rewrite H0; simpl in |- *; auto.
  elim H0; clear H0; intro H0; rewrite H0; simpl in |- *; auto.
  auto.

  Qed.



(** Equality of the outputs **)

  Lemma Output_relation_a4 :
   Output_rel Out_Four_Arbiters_Mealy Out_Struct_four_arbiters R_a4.

  unfold Output_rel in |- *.
  intros i sa4 old.
  elim sa4; elim old; simpl in |- *.
  clear sa4 old.
  intros old1 old2 sa4 old; elim old1; elim old2; clear old1 old2.
  intros old11 old12 old21 old22.
  elim old11; elim old12; elim old21; elim old22;
   clear old11 old12 old21 old22.
  intros g11 o11 g12 o12 g21 o21 g22 o22.
  elim old; clear old; intros g o.
  unfold output_four_arbiters in |- *; simpl in |- *.
  intro H; elim H; clear H; intros H1 H2.
  generalize (eq_pair H2).
  clear H2; intro H; elim H; clear H; intros H H'.
  generalize (eq_pair H).
  generalize (eq_pair H').
  clear H; intro H; elim H; clear H; intros H H0.
  clear H'; intro H'; elim H'; clear H'; intros H' H''.
  unfold Out_ArbiterXY in |- *; unfold Out_outdis in |- *.
  rewrite H; rewrite H0; rewrite H'; rewrite H''; auto.

  Qed.



(** Correctness of the FOUR_ARBITERS unit **)

  Definition Structure_States_FOUR_ARBITERS :=
    States_PC Trans_Struct_two_arbiters Trans_Struct_two_arbiters
      f_four_arbiters.



  Lemma Correct_FOUR_ARBITERS :
   forall (i : Stream Input_type) (sa4 : STATE_a4) (old : Reg_type),
   Inv P_a4 i (States_FOUR_ARBITERS i sa4)
     (Structure_States_FOUR_ARBITERS i old) ->
   R_a4 sa4 old ->
   EqS (Behaviour_FOUR_ARBITERS i sa4) (Structure_FOUR_ARBITERS i old).

  intros i sa4 old HP HR.
  unfold Behaviour_FOUR_ARBITERS in |- *;
   unfold Structure_FOUR_ARBITERS in |- *.
  apply (Equiv_2_Mealy Invariant_relation_a4 Output_relation_a4 HP HR).

  Qed.

  
End Four_Arbiters_Proof_Correctness.
