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
(*                          Lemmas_Comb_Behaviour.v                         *)
(****************************************************************************)


Require Export ElementComb_Behaviour.
Require Export SuccessfulInput.
Require Export Base_Struct.
Require Export Lemmas_on_fcts.
Require Export Lemmas_Struct.
Require Export ElementComb.

Set Implicit Arguments.
Unset Strict Implicit.


Definition Grant_for_Out (ltReq : d_list bool 4) (last : d_list bool 2) :=
  Convert_port_list2 (SuccessfulInput ltReq (Convert_list2_port last)).


Lemma Arbiter_last_tt :
 forall l : d_list bool 4,
 Ackor l = true ->
 Fst_of_l2 (Grant_for_Out l (List2 true true)) =
 Jk (Arb_xel (Scd_of_l4 l) true (Fth_of_l4 l) (Thd_of_l4 l))
   (Scd_of_l2 (Arbx true l)) true /\
 Scd_of_l2 (Grant_for_Out l (List2 true true)) =
 Jk (J_Arby true l) (Scd_of_l2 (Arby true l)) true.
intros l H.
unfold Grant_for_Out in |- *.
unfold SuccessfulInput in |- *.
rewrite RoundRobinArbiter_simpl.
unfold RoundRobin in |- *.
unfold Convert_list2_port in |- *; simpl in |- *.
elim
 (In_or_not eq_nat_dec
    (no_in (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4)))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intros H'.
unfold SUC_MODN in |- *;
 elim (less_or_eq (exist (fun p : nat => p < 4) 3 lt_3_4)); 
 simpl in |- *; auto.
intros Abs; absurd (4 < 4); auto with arith.
intros y'.
unfold Arbx in |- *.
unfold Arby in |- *.
unfold K_Arby in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; unfold Arb_xel in |- *;
 simpl in |- *.
unfold Arb_yel in |- *.
rewrite d_In_SUC_SSSO_l4.
unfold AO in |- *; simpl in |- *.
elim orb_sym; auto.
auto.
intro non.
unfold Arbx in |- *.
unfold Arby in |- *.
unfold K_Arby in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; unfold Arb_xel in |- *;
 simpl in |- *.
unfold Arb_yel in |- *.
rewrite not_d_In_SUC_SSSO_l4.
unfold AO in |- *; simpl in |- *.
elim orb_sym; simpl in |- *.
clear non.
elim
 (In_or_not eq_nat_dec
    (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4))))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intro H'.
unfold SUC_MODN in |- *;
 elim (less_or_eq (exist (fun p : nat => p < 4) 3 lt_3_4)); 
 simpl in |- *; auto.
intros Abs; absurd (4 < 4); auto with arith.
intro y'.
unfold SUC_MODN in |- *;
 elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y')));
 simpl in |- *; auto.
intro y''.
rewrite d_In_SUCSUC_SSSO_l4.
simpl in |- *; auto.
auto.
intro Abs; absurd (1 = 4); auto.
intro non.
rewrite not_d_In_SUCSUC_SSSO_l4.
clear non.
elim
 (In_or_not eq_nat_dec
    (no_in
       (SUC_MODN
          (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4)))))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intros H'.
unfold SUC_MODN at 3 6 in |- *;
 elim (less_or_eq (exist (fun p : nat => p < 4) 3 lt_3_4)); 
 simpl in |- *; auto.
intro Abs; absurd (4 < 4); auto with arith.
intro y'.
unfold SUC_MODN at 2 4 in |- *;
 elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y')));
 simpl in |- *; auto.
intro y''.
unfold SUC_MODN in |- *;
 elim (less_or_eq (exist (fun n : nat => n < 4) 1 y'')); 
 simpl in |- *; auto.
rewrite d_In_SUCSUCSUC_SSSO_l4.
intro y.
elim (less_or_eq (exist (fun p : nat => p < 4) 3 lt_3_4)); simpl in |- *.
intro Abs; absurd (4 < 4); auto with arith.
intro b.
elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen b)));
 simpl in |- *.
intro a; elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
trivial.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
intros.
rewrite not_d_In_SUCSUCSUC_SSSO_l4.
simpl in |- *.
elim
 (In_or_not eq_nat_dec
    (no_in
       (SUC_MODN
          (SUC_MODN
             (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4))))))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intros H'.
unfold Convert_port_list2 in |- *.
generalize eq_n_SM4_4_times; unfold SM4 in |- *; intros Sm4.
elim (Sm4 (exist (fun p : nat => p < 4) 3 lt_3_4)).
auto.
unfold SUC_MODN at 4 8 12 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 3 lt_3_4)); simpl in |- *.
intro Abs; absurd (4 < 4); auto with arith.
intro b0.
intro.
unfold SUC_MODN at 3 6 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen b0)));
 simpl in |- *.
intro a.
unfold SUC_MODN at 2 4 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
intro a0.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 2 a0)); simpl in |- *.
auto.
intro Abs; absurd (3 = 4); auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
auto.
auto.
auto.
auto.
Qed.




Lemma Arbiter_last_tf :
 forall l : d_list bool 4,
 Ackor l = true ->
 Fst_of_l2 (Grant_for_Out l (List2 true false)) =
 Jk (Arb_xel (Scd_of_l4 l) false (Fth_of_l4 l) (Thd_of_l4 l))
   (Scd_of_l2 (Arbx false l)) true /\
 Scd_of_l2 (Grant_for_Out l (List2 true false)) =
 Jk (J_Arby true l) (Scd_of_l2 (Arby true l)) false.
intros l H.
unfold Grant_for_Out in |- *.
unfold SuccessfulInput in |- *.
rewrite RoundRobinArbiter_simpl.
unfold RoundRobin in |- *.
unfold Convert_list2_port in |- *; simpl in |- *.
elim
 (In_or_not eq_nat_dec
    (no_in (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4)))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intro H'.
unfold SUC_MODN in |- *;
 elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); 
 simpl in |- *; auto.
intro y'.
  unfold Arbx in |- *; unfold J_Arby in |- *.
rewrite d_In_SUC_SSO_l4.
auto.
auto.
intro Abs; absurd (3 = 4); auto.
intro non.
  unfold Arbx in |- *; unfold J_Arby in |- *.
rewrite not_d_In_SUC_SSO_l4.
clear non.
elim
 (In_or_not eq_nat_dec
    (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4))))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intro H'.
unfold SUC_MODN at 2 4 in |- *;
 elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); 
 simpl in |- *; auto.
intro y'.
unfold SUC_MODN in |- *;
 elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); 
 simpl in |- *; auto.
intro a.
elim (less_or_eq (exist (fun n : nat => n < 4) 3 a)); simpl in |- *; auto.
intro Abs; absurd (4 < 4); auto with arith.
rewrite d_In_SUCSUC_SSO_l4; simpl in |- *; auto with arith.
intro b; absurd (3 = 4); auto with arith.
intro b; absurd (3 = 4); auto with arith.
intro b.
elim
 (In_or_not eq_nat_dec
    (no_in
       (SUC_MODN
          (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4)))))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intro H'.
unfold SUC_MODN at 3 6 in |- *;
 elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); 
 simpl in |- *; auto.
intro y'.
unfold SUC_MODN at 2 4 in |- *;
 elim (less_or_eq (exist (fun n : nat => n < 4) 3 y')); 
 simpl in |- *; auto.
intro Abs; absurd (4 < 4); auto with arith.
intro y''.
unfold SUC_MODN in |- *;
 elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y'')));
 simpl in |- *; auto.
clear y''; intro y''.
rewrite d_In_SUCSUCSUC_SSO_l4.
elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); simpl in |- *.
intro a.
elim (less_or_eq (exist (fun n : nat => n < 4) 3 a)); simpl in |- *.
intro Abs; absurd (4 < 4); auto with arith.
intro a'.
unfold SUC_MODN in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen a')));
 simpl in |- *.
intro a0.
rewrite not_d_In_SUCSUC_SSO_l4.  
auto.
auto.
intro Abs; absurd (1 = 4); auto.
intro Abs; absurd (3 = 4); auto.
auto.
intro Abs; absurd (1 = 4); auto.
intro Abs; absurd (3 = 4); auto.
intro H'.
rewrite not_d_In_SUCSUCSUC_SSO_l4. 
elim
 (In_or_not eq_nat_dec
    (no_in
       (SUC_MODN
          (SUC_MODN
             (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4))))))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l)))).
intro H''.
unfold Convert_port_list2 in |- *.
generalize eq_n_SM4_4_times; unfold SM4 in |- *; intros Sm4.
elim (Sm4 (exist (fun p : nat => p < 4) 2 lt_2_4)).
simpl in |- *.
rewrite not_d_In_SUCSUC_SSO_l4.
simpl in |- *; auto.
auto.
intro H''.
unfold SUC_MODN at 4 8 in |- *; simpl in |- *.
unfold Convert_port_list2 in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); simpl in |- *. 
intro a0.
unfold SUC_MODN at 3 6 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 3 a0)); simpl in |- *.
intro a1.
unfold SUC_MODN at 2 4 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 4 a1)); simpl in |- *.
intro Abs; absurd (5 < 4); auto with arith.
intro Abs; absurd (5 = 4); auto.
intro b0.
unfold SUC_MODN at 2 4 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen b0)));
 simpl in |- *.
unfold SUC_MODN at 1 2 in |- *; simpl in |- *.
intro a1.
elim (less_or_eq (exist (fun n : nat => n < 4) 1 a1)); simpl in |- *.
rewrite not_d_In_SUCSUC_SSO_l4.
auto.
auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
intro Abs; absurd (3 = 4); auto.
auto.
auto.
auto.
Qed.




Lemma Arbiter_last_ft :
 forall l : d_list bool 4,
 Ackor l = true ->
 Fst_of_l2 (Grant_for_Out l (List2 false true)) =
 Jk (Arb_xel (Scd_of_l4 l) true (Fth_of_l4 l) (Thd_of_l4 l))
   (Scd_of_l2 (Arbx true l)) false /\
 Scd_of_l2 (Grant_for_Out l (List2 false true)) =
 Jk (J_Arby false l) (Scd_of_l2 (Arby false l)) true.

intros l H.
unfold Grant_for_Out in |- *.
unfold SuccessfulInput in |- *.
rewrite RoundRobinArbiter_simpl.
unfold RoundRobin in |- *.
unfold Convert_list2_port in |- *; simpl in |- *.
elim
 (In_or_not eq_nat_dec
    (no_in (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4)))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intro H'.
unfold SUC_MODN in |- *;
 elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); 
 simpl in |- *; auto.
unfold Arby in |- *; unfold K_Arby in |- *.
rewrite d_In_SUC1_l4.
elim orb_sym; auto.
auto.
intro Abs; absurd (2 = 4); auto.
intro non.
unfold Arby in |- *; unfold K_Arby in |- *.
rewrite not_d_In_SUC1_l4.
clear non.
elim
 (In_or_not eq_nat_dec
    (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4))))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intro H'.
unfold SUC_MODN at 2 4 in |- *;
 elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); 
 simpl in |- *; auto.
intro y'.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *.
intro a; unfold SUC_MODN in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 2 a)); simpl in |- *.
intro a0.
rewrite d_In_SUCSUC1_l4.
auto.
auto.
intro Abs; absurd (3 = 4); auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (2 = 4); auto.
intro non.
rewrite not_d_In_SUCSUC1_l4.
elim
 (In_or_not eq_nat_dec
    (no_in
       (SUC_MODN
          (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4)))))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intro H'.
rewrite d_In_SUCSUCSUC_SO_l4.
auto.
unfold SUC_MODN at 3 6 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *.
intro a; unfold SUC_MODN at 2 4 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 2 a)); simpl in |- *.
unfold SUC_MODN in |- *; intro a0.
elim (less_or_eq (exist (fun n : nat => n < 4) 3 a0)); simpl in |- *.
intro Abs; absurd (4 < 4); auto with arith.
auto.
intro Abs; absurd (3 = 4); auto.
intro Abs; absurd (2 = 4); auto.
auto.
intro H'.
unfold Convert_port_list2 in |- *; simpl in |- *.
elim
 (In_or_not eq_nat_dec
    (no_in
       (SUC_MODN
          (SUC_MODN
             (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4))))))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intro H''.
simpl in |- *.
unfold SUC_MODN at 4 8 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *.
intro a.
unfold SUC_MODN at 3 6 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 2 a)); simpl in |- *.
intro a0.
unfold SUC_MODN at 2 4 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 3 a0)); simpl in |- *.
intro Abs; absurd (4 < 4); auto with arith.
intro b; unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen b)));
 simpl in |- *.
intro b0.
rewrite not_d_In_SUCSUCSUC_SO_l4.
auto.
auto.
intro Abs; absurd (1 = 4); auto.
intro Abs; absurd (3 = 4); auto.
intro Abs; absurd (2 = 4); auto.
intro H''.
unfold SUC_MODN at 4 8 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *.
intro a.
unfold SUC_MODN at 3 6 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 2 a)); simpl in |- *.
intro a0.
unfold SUC_MODN at 2 4 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 3 a0)); simpl in |- *.
intro Abs; absurd (4 < 4); auto with arith.
intro b; unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen b)));
 simpl in |- *.
intro b0.
rewrite not_d_In_SUCSUCSUC_SO_l4.
auto.
auto.
intro Abs; absurd (1 = 4); auto.
intro Abs; absurd (3 = 4); auto.
intro Abs; absurd (2 = 4); auto.
auto.
auto.
auto.
Qed.





Lemma Arbiter_last_ff :
 forall l : d_list bool 4,
 Ackor l = true ->
 Fst_of_l2 (Grant_for_Out l (List2 false false)) =
 Jk (Arb_xel (Scd_of_l4 l) false (Fth_of_l4 l) (Thd_of_l4 l))
   (Scd_of_l2 (Arbx false l)) false /\
 Scd_of_l2 (Grant_for_Out l (List2 false false)) =
 Jk (J_Arby false l) (Scd_of_l2 (Arby false l)) false.
intros l H.
unfold Grant_for_Out in |- *.
unfold SuccessfulInput in |- *.
rewrite RoundRobinArbiter_simpl.
unfold RoundRobin in |- *.
unfold Convert_list2_port in |- *; simpl in |- *.
elim
 (In_or_not eq_nat_dec
    (no_in (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4)))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intros H'.
unfold Convert_port_list2 in |- *.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))) with 1;
 simpl in |- *; auto.
unfold J_Arby in |- *.
rewrite d_In_SUC0_l2.
unfold Arb_yel in |- *; unfold Arb_xel in |- *; unfold AO in |- *;
 simpl in |- *.
elim orb_sym; auto.
auto.
unfold SUC_MODN in |- *;
 elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); 
 simpl in |- *; auto.
intros Abs; absurd (1 = 4); auto.
intro non.
unfold J_Arby in |- *.
rewrite not_d_In_SUC0_l2.
clear non.
elim
 (In_or_not eq_nat_dec
    (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intro H'.
unfold Convert_port_list2 in |- *.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))))
 with 2; simpl in |- *; auto.
rewrite d_In_SUC1_l3.
elim orb_sym; auto.
auto.
unfold SUC_MODN at 2 in |- *;
 elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); 
 simpl in |- *; auto.
intro y'.
unfold SUC_MODN in |- *;
 elim (less_or_eq (exist (fun n : nat => n < 4) 1 y')); 
 simpl in |- *; auto.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *.
intro a.
elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
auto.
intro Abs; absurd (2 = 4); auto with arith.
intro Abs; absurd (1 = 4); auto.
intro Abs; absurd (2 = 4); auto with arith.
intro Abs; absurd (1 = 4); auto.
intro non.
rewrite not_d_In_SUC1_l3.
clear non.
elim
 (In_or_not eq_nat_dec
    (no_in
       (SUC_MODN
          (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4)))))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intro H'.
unfold SUC_MODN at 3 6 in |- *;
 elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); 
 simpl in |- *; auto.
intro H0.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *.
intro a.
unfold SUC_MODN at 2 4 in |- *; simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
intro a0.
unfold SUC_MODN in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 2 a0)); simpl in |- *.
intro a1.
unfold Convert_port_list2 in |- *; simpl in |- *.
rewrite d_In_SUC2_l4.
auto.
auto.
intro Abs; absurd (3 = 4); auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
intro Abs; absurd (1 = 4); auto.
intro non.
elim
 (In_or_not eq_nat_dec
    (no_in
       (SUC_MODN
          (SUC_MODN
             (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))))))
    (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))));
 simpl in |- *.
intro H'.
unfold Convert_port_list2 in |- *.
generalize eq_n_SM4_4_times; unfold SM4 in |- *; intros Sm4.
unfold SUC_MODN at 4 8 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *.
intro a.
unfold SUC_MODN at 3 6 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
intro a0.
unfold SUC_MODN at 2 4 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 2 a0)); simpl in |- *.
intro a1.
unfold SUC_MODN in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 3 a1)); simpl in |- *.
intro Abs; absurd (4 < 4); auto with arith.
intro H0.
rewrite not_d_In_SUC2_l4.
auto.
auto.
intro Abs; absurd (3 = 4); auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
intro H'.
unfold Convert_port_list2 in |- *.
unfold SUC_MODN at 4 8 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *.
intro a.
unfold SUC_MODN at 3 6 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
intro a0.
unfold SUC_MODN at 2 4 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 2 a0)); simpl in |- *.
intro a1.
unfold SUC_MODN in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 3 a1)); simpl in |- *.
intro Abs; absurd (4 < 4); auto with arith.
intro H0.
rewrite not_d_In_SUC2_l4.
auto.
auto.
intro Abs; absurd (3 = 4); auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
auto.
auto.
auto.
Qed.



Lemma Arbiter_last :
 forall (l : d_list bool 4) (b1 b2 : bool),
 Ackor l = true ->
 Fst_of_l2 (Grant_for_Out l (List2 b1 b2)) =
 Jk (Arb_xel (Scd_of_l4 l) b2 (Fth_of_l4 l) (Thd_of_l4 l))
   (Scd_of_l2 (Arbx b2 l)) b1 /\
 Scd_of_l2 (Grant_for_Out l (List2 b1 b2)) =
 Jk (J_Arby b1 l) (Scd_of_l2 (Arby b1 l)) b2.
intros l b1 b2 H.
elim b1; elim b2.
apply Arbiter_last_tt; try trivial.
apply Arbiter_last_tf; try trivial.
apply Arbiter_last_ft; try trivial.
apply Arbiter_last_ff; try trivial.
Qed.




Lemma Ackor_ltReq_false :
 forall (l : d_list bool 4) (g1 g2 : bool),
 Ackor l = false ->
 Jk (Arb_xel (Scd_of_l4 l) g2 (Fth_of_l4 l) (Thd_of_l4 l))
   (Scd_of_l2 (Arbx g2 l)) g1 = g1 /\
 Jk (J_Arby g1 l) (Scd_of_l2 (Arby g1 l)) g2 = g2.
intros l g1 g2 H.
unfold Arbx in |- *; unfold Arby in |- *; unfold J_Arby in |- *;
 unfold Arb_xel in |- *; unfold Arb_yel in |- *; unfold K_Arby in |- *;
 unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold Arb_yel in |- *; unfold AO in |- *; unfold AND2 in |- *;
 unfold OR2 in |- *.
rewrite (Ackor_false_fst H).
rewrite (Ackor_false_scd H).
rewrite (Ackor_false_thd H).
rewrite (Ackor_false_fth H); simpl in |- *.
elim g1; elim g2; simpl in |- *; auto.
Qed.


Lemma Ackor_false :
 forall l : d_list bool 4,
 Ackor l = false ->
 Fst_of_l4 l = false /\
 Scd_of_l4 l = false /\ Thd_of_l4 l = false /\ Fth_of_l4 l = false.
intro l.
elim (non_empty l).
intros a H; elim H; clear H.
intros t H; rewrite H; simpl in |- *.
elim (non_empty t).
intros b H0; elim H0; clear H0.
intros t0 H0; rewrite H0; simpl in |- *.
elim (non_empty t0).
intros c H'; elim H'; clear H'.
intros t' H'; rewrite H'; simpl in |- *.
elim (non_empty t').
intros d H''; elim H''; clear H''.
intros t'' H''; rewrite H''; simpl in |- *.
replace t'' with (d_nil bool); auto.
unfold Ackor in |- *; simpl in |- *.
elim a; elim b; elim c; elim d; simpl in |- *; auto.
Qed.

