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
(*                             Invariant_a4_S.v                             *)
(****************************************************************************)
 

Require Export Arbiter4_Specif.
Require Export Product.
Require Export Arbitration.
Require Export Manip_BoolLists.
Require Export Lib_Bool.


Set Implicit Arguments.
Unset Strict Implicit.

  
Section For_ltReq.
   
 Variable g : d_list (bool * bool) 4.
 Variable o : d_list bool 4.
 Variable g11 g12 g21 g22 : d_list bool 2.
 Variable o11 o12 o21 o22 : bool.

 Hypothesis H1 : fst (Fst_of_l4 g) = Fst_of_l2 g11.
 Hypothesis H2 : snd (Fst_of_l4 g) = Scd_of_l2 g11.
 Hypothesis H3 : fst (Scd_of_l4 g) = Fst_of_l2 g12.
 Hypothesis H4 : snd (Scd_of_l4 g) = Scd_of_l2 g12.
 Hypothesis H5 : fst (Thd_of_l4 g) = Fst_of_l2 g21.
 Hypothesis H6 : snd (Thd_of_l4 g) = Scd_of_l2 g21.
 Hypothesis H7 : fst (Fth_of_l4 g) = Fst_of_l2 g22.
 Hypothesis H8 : snd (Fth_of_l4 g) = Scd_of_l2 g22.


Lemma ltReq_OOO1 :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = false /\
 Ackor (Scd_of_l4 ltReq) = false /\
 Ackor (Thd_of_l4 ltReq) = false /\ Ackor (Fth_of_l4 ltReq) = true ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
left.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.
unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G1; trivial; rewrite ltReq_false_G2; trivial;
 rewrite ltReq_false_G3; simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq1); intro A; elim A; clear A; intros A1 A; elim A;
 clear A; intros A2 A; elim A; clear A; intros A3 A4; 
 rewrite A1; rewrite A2; rewrite A3; rewrite A4; simpl in |- *.
specialize (Ackor_false Hreq2); intro B; elim B; clear B; intros B1 B; elim B;
 clear B; intros B2 B; elim B; clear B; intros B3 B4; 
 rewrite B1; rewrite B2; rewrite B3; rewrite B4; simpl in |- *.
specialize (Ackor_false Hreq3); intro C; elim C; clear C; intros C1 C; elim C;
 clear C; intros C2 C; elim C; clear C; intros C3 C4; 
 rewrite C1; rewrite C2; rewrite C3; rewrite C4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.
apply id_list3.

elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g11); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g11)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.
apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g12); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g12)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply pair_eq.
apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g21); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g21)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Fth_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g22) (Scd_of_l2 g22) Hreq4); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.
apply sym_equal; apply split_List4.
Qed.



Lemma ltReq_OO1O :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = false /\
 Ackor (Scd_of_l4 ltReq) = false /\
 Ackor (Thd_of_l4 ltReq) = true /\ Ackor (Fth_of_l4 ltReq) = false ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
right; left.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G1; trivial; rewrite ltReq_false_G2; trivial;
 rewrite ltReq_false_G4; simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq1); intro A; elim A; clear A; intros A1 A; elim A;
 clear A; intros A2 A; elim A; clear A; intros A3 A4; 
 rewrite A1; rewrite A2; rewrite A3; rewrite A4; simpl in |- *.
specialize (Ackor_false Hreq2); intro B; elim B; clear B; intros B1 B; elim B;
 clear B; intros B2 B; elim B; clear B; intros B3 B4; 
 rewrite B1; rewrite B2; rewrite B3; rewrite B4; simpl in |- *.
specialize (Ackor_false Hreq4); intro C; elim C; clear C; intros C1 C; elim C;
 clear C; intros C2 C; elim C; clear C; intros C3 C4; 
 rewrite C1; rewrite C2; rewrite C3; rewrite C4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.
apply id_list3.

elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g11); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g11)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.
apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g12); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g12)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply pair_eq.

   (** (Ackor (Thd_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g21) (Scd_of_l2 g21) Hreq3); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g22); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g22)); auto.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
apply id_list3; auto.
elim (d_Head (d_tl g22)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.

apply sym_equal; apply split_List4.

Qed.



Lemma ltReq_OO11 :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = false /\
 Ackor (Scd_of_l4 ltReq) = false /\
 Ackor (Thd_of_l4 ltReq) = true /\ Ackor (Fth_of_l4 ltReq) = true ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
right; right.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G1; trivial; rewrite ltReq_false_G2; trivial;
 simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq1); intro A; elim A; clear A; intros A1 A; elim A;
 clear A; intros A2 A; elim A; clear A; intros A3 A4; 
 rewrite A1; rewrite A2; rewrite A3; rewrite A4; simpl in |- *.
specialize (Ackor_false Hreq2); intro B; elim B; clear B; intros B1 B; elim B;
 clear B; intros B2 B; elim B; clear B; intros B3 B4; 
 rewrite B1; rewrite B2; rewrite B3; rewrite B4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.
apply id_list3.

elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g11); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g11)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g12); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g12)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply pair_eq.

   (** (Ackor (Thd_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g21) (Scd_of_l2 g21) Hreq3); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Fth_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g22) (Scd_of_l2 g22) Hreq4); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.

apply sym_equal; apply split_List4.

Qed.



Lemma ltReq_O1OO :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = false /\
 Ackor (Scd_of_l4 ltReq) = true /\
 Ackor (Thd_of_l4 ltReq) = false /\ Ackor (Fth_of_l4 ltReq) = false ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
left.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G1; trivial; rewrite ltReq_false_G3; trivial;
 rewrite ltReq_false_G4; trivial; simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq1); intro A; elim A; clear A; intros A1 A; elim A;
 clear A; intros A2 A; elim A; clear A; intros A3 A4; 
 rewrite A1; rewrite A2; rewrite A3; rewrite A4; simpl in |- *.
specialize (Ackor_false Hreq3); intro B; elim B; clear B; intros B1 B; elim B;
 clear B; intros B2 B; elim B; clear B; intros B3 B4; 
 rewrite B1; rewrite B2; rewrite B3; rewrite B4; simpl in |- *.
specialize (Ackor_false Hreq4); intro C; elim C; clear C; intros C1 C; elim C;
 clear C; intros C2 C; elim C; clear C; intros C3 C4; 
 rewrite C1; rewrite C2; rewrite C3; rewrite C4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.
apply id_list3.

elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g11); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g11)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Scd_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g12) (Scd_of_l2 g12) Hreq2); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply pair_eq.
apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g21); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g21)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g22); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g22)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.

apply sym_equal; apply split_List4.

Qed.


Lemma ltReq_O1O1 :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = false /\
 Ackor (Scd_of_l4 ltReq) = true /\
 Ackor (Thd_of_l4 ltReq) = false /\ Ackor (Fth_of_l4 ltReq) = true ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; right; right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
left.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G1; trivial; rewrite ltReq_false_G3; trivial;
 simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq1); intro A; elim A; clear A; intros A1 A; elim A;
 clear A; intros A2 A; elim A; clear A; intros A3 A4; 
 rewrite A1; rewrite A2; rewrite A3; rewrite A4; simpl in |- *.
specialize (Ackor_false Hreq3); intro B; elim B; clear B; intros B1 B; elim B;
 clear B; intros B2 B; elim B; clear B; intros B3 B4; 
 rewrite B1; rewrite B2; rewrite B3; rewrite B4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.
apply id_list3.

elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g11); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g11)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Scd_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g12) (Scd_of_l2 g12) Hreq2); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply pair_eq.
apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g21); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g21)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Fth_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g22) (Scd_of_l2 g22) Hreq4); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.

apply sym_equal; apply split_List4.

Qed.



Lemma ltReq_O11O :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = false /\
 Ackor (Scd_of_l4 ltReq) = true /\
 Ackor (Thd_of_l4 ltReq) = true /\ Ackor (Fth_of_l4 ltReq) = false ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; right; right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
right; right; right; left.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G1; trivial; rewrite ltReq_false_G4; trivial;
 simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq1); intro A; elim A; clear A; intros A1 A; elim A;
 clear A; intros A2 A; elim A; clear A; intros A3 A4; 
 rewrite A1; rewrite A2; rewrite A3; rewrite A4; simpl in |- *.
specialize (Ackor_false Hreq4); intro B; elim B; clear B; intros B1 B; elim B;
 clear B; intros B2 B; elim B; clear B; intros B3 B4; 
 rewrite B1; rewrite B2; rewrite B3; rewrite B4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.
apply id_list3.

elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g11); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g11)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Scd_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g12) (Scd_of_l2 g12) Hreq2); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Thd_of_l4 ltReq))=true **)
apply pair_eq.
specialize (Arbiter_last (Fst_of_l2 g21) (Scd_of_l2 g21) Hreq3); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g22); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g22)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.

apply sym_equal; apply split_List4.

Qed.


Lemma ltReq_O111 :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = false /\
 Ackor (Scd_of_l4 ltReq) = true /\
 Ackor (Thd_of_l4 ltReq) = true /\ Ackor (Fth_of_l4 ltReq) = true ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; right; right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
right; right; right; right; right; right; left.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G1; trivial; simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq1); intro A; elim A; clear A; intros A1 A; elim A;
 clear A; intros A2 A; elim A; clear A; intros A3 A4; 
 rewrite A1; rewrite A2; rewrite A3; rewrite A4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.
apply id_list3.

elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g11); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g11)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Scd_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g12) (Scd_of_l2 g12) Hreq2); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Thd_of_l4 ltReq))=true **)
apply pair_eq.
specialize (Arbiter_last (Fst_of_l2 g21) (Scd_of_l2 g21) Hreq3); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Fth_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g22) (Scd_of_l2 g22) Hreq4); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.

apply sym_equal; apply split_List4.

Qed.


Lemma ltReq_1OOO :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = true /\
 Ackor (Scd_of_l4 ltReq) = false /\
 Ackor (Thd_of_l4 ltReq) = false /\ Ackor (Fth_of_l4 ltReq) = false ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
right; left.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G2; trivial; rewrite ltReq_false_G3; trivial;
 rewrite ltReq_false_G4; simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq2); intro A; elim A; clear A; intros A1 A; elim A;
 clear A; intros A2 A; elim A; clear A; intros A3 A4; 
 rewrite A1; rewrite A2; rewrite A3; rewrite A4; simpl in |- *.
specialize (Ackor_false Hreq3); intro B; elim B; clear B; intros B1 B; elim B;
 clear B; intros B2 B; elim B; clear B; intros B3 B4; 
 rewrite B1; rewrite B2; rewrite B3; rewrite B4; simpl in |- *.
specialize (Ackor_false Hreq4); intro C; elim C; clear C; intros C1 C; elim C;
 clear C; intros C2 C; elim C; clear C; intros C3 C4; 
 rewrite C1; rewrite C2; rewrite C3; rewrite C4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.

   (** (Ackor (Fst_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g11) (Scd_of_l2 g11) Hreq1); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g12); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g12)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply pair_eq.
apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g21); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g21)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g22); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g22)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.
apply sym_equal; apply split_List4.
Qed.


Lemma ltReq_1OO1 :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = true /\
 Ackor (Scd_of_l4 ltReq) = false /\
 Ackor (Thd_of_l4 ltReq) = false /\ Ackor (Fth_of_l4 ltReq) = true ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; right; right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
right; right; right; right; left.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G2; trivial; rewrite ltReq_false_G3; trivial;
 simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq2); intro A; elim A; clear A; intros A1 A; elim A;
 clear A; intros A2 A; elim A; clear A; intros A3 A4; 
 rewrite A1; rewrite A2; rewrite A3; rewrite A4; simpl in |- *.
specialize (Ackor_false Hreq3); intro B; elim B; clear B; intros B1 B; elim B;
 clear B; intros B2 B; elim B; clear B; intros B3 B4; 
 rewrite B1; rewrite B2; rewrite B3; rewrite B4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.

   (** (Ackor (Fst_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g11) (Scd_of_l2 g11) Hreq1); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g12); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g12)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply pair_eq.
apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g21); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g21)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Fth_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g22) (Scd_of_l2 g22) Hreq4); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.
apply sym_equal; apply split_List4.
Qed.


Lemma ltReq_1O1O :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = true /\
 Ackor (Scd_of_l4 ltReq) = false /\
 Ackor (Thd_of_l4 ltReq) = true /\ Ackor (Fth_of_l4 ltReq) = false ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; right; right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
right; left.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G2; trivial; rewrite ltReq_false_G4; trivial;
 simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq2); intro A; elim A; clear A; intros A1 A; elim A;
 clear A; intros A2 A; elim A; clear A; intros A3 A4; 
 rewrite A1; rewrite A2; rewrite A3; rewrite A4; simpl in |- *.
specialize (Ackor_false Hreq4); intro B; elim B; clear B; intros B1 B; elim B;
 clear B; intros B2 B; elim B; clear B; intros B3 B4; 
 rewrite B1; rewrite B2; rewrite B3; rewrite B4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.

   (** (Ackor (Fst_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g11) (Scd_of_l2 g11) Hreq1); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g12); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g12)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Thd_of_l4 ltReq))=true **)
apply pair_eq.
specialize (Arbiter_last (Fst_of_l2 g21) (Scd_of_l2 g21) Hreq3); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g22); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g22)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.
apply sym_equal; apply split_List4.
Qed.


Lemma ltReq_1O11 :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = true /\
 Ackor (Scd_of_l4 ltReq) = false /\
 Ackor (Thd_of_l4 ltReq) = true /\ Ackor (Fth_of_l4 ltReq) = true ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; right; right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
right; right; right; right; right; right; right; right.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G2; trivial; simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq2); intro A; elim A; clear A; intros A1 A; elim A;
 clear A; intros A2 A; elim A; clear A; intros A3 A4; 
 rewrite A1; rewrite A2; rewrite A3; rewrite A4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.

   (** (Ackor (Fst_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g11) (Scd_of_l2 g11) Hreq1); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g12); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g12)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Thd_of_l4 ltReq))=true **)
apply pair_eq.
specialize (Arbiter_last (Fst_of_l2 g21) (Scd_of_l2 g21) Hreq3); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Fth_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g22) (Scd_of_l2 g22) Hreq4); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.
apply sym_equal; apply split_List4.
Qed.


Lemma ltReq_11OO :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = true /\
 Ackor (Scd_of_l4 ltReq) = true /\
 Ackor (Thd_of_l4 ltReq) = false /\ Ackor (Fth_of_l4 ltReq) = false ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
right; right.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G3; trivial; rewrite ltReq_false_G4; trivial;
 simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq3); intro A; elim A; clear A; intros A1 A; elim A;
 clear A; intros A2 A; elim A; clear A; intros A3 A4; 
 rewrite A1; rewrite A2; rewrite A3; rewrite A4; simpl in |- *.
specialize (Ackor_false Hreq4); intro B; elim B; clear B; intros B1 B; elim B;
 clear B; intros B2 B; elim B; clear B; intros B3 B4; 
 rewrite B1; rewrite B2; rewrite B3; rewrite B4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.

   (** (Ackor (Fst_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g11) (Scd_of_l2 g11) Hreq1); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Scd_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g12) (Scd_of_l2 g12) Hreq2); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply pair_eq.
apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g21); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g21)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g22); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g22)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.
apply sym_equal; apply split_List4.
Qed.


Lemma ltReq_11O1 :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = true /\
 Ackor (Scd_of_l4 ltReq) = true /\
 Ackor (Thd_of_l4 ltReq) = false /\ Ackor (Fth_of_l4 ltReq) = true ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; right; right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
do 7 right; left.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G3; trivial; simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq3); intro A; elim A; clear A; intros A1 A; elim A;
 clear A; intros A2 A; elim A; clear A; intros A3 A4; 
 rewrite A1; rewrite A2; rewrite A3; rewrite A4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.

   (** (Ackor (Fst_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g11) (Scd_of_l2 g11) Hreq1); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Scd_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g12) (Scd_of_l2 g12) Hreq2); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply pair_eq.
apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g21); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g21)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Fth_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g22) (Scd_of_l2 g22) Hreq4); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.
apply sym_equal; apply split_List4.
Qed.


Lemma ltReq_111O :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = true /\
 Ackor (Scd_of_l4 ltReq) = true /\
 Ackor (Thd_of_l4 ltReq) = true /\ Ackor (Fth_of_l4 ltReq) = false ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; right; right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
do 5 right; left.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).
rewrite ltReq_false_G4; trivial; simpl in |- *; trivial.
unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

specialize (Ackor_false Hreq4); intro B; elim B; clear B; intros B1 B; elim B;
 clear B; intros B2 B; elim B; clear B; intros B3 B4; 
 rewrite B1; rewrite B2; rewrite B3; rewrite B4; simpl in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.

   (** (Ackor (Fst_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g11) (Scd_of_l2 g11) Hreq1); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Scd_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g12) (Scd_of_l2 g12) Hreq2); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Thd_of_l4 ltReq))=true **)
apply pair_eq.
specialize (Arbiter_last (Fst_of_l2 g21) (Scd_of_l2 g21) Hreq3); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

apply id_list3.
elim andb_sym; simpl in |- *.
elim (Fst_of_l2 g22); auto.
unfold AO in |- *.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
elim (d_Head (d_tl g22)); auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.
apply sym_equal; apply split_List4.
Qed.


Lemma ltReq_1111 :
 forall (ltReq : d_list (d_list bool 4) 4) (fs : bool),
 Ackor (Fst_of_l4 ltReq) = true /\
 Ackor (Scd_of_l4 ltReq) = true /\
 Ackor (Thd_of_l4 ltReq) = true /\ Ackor (Fth_of_l4 ltReq) = true ->
 R_a4 (Trans_Four_Arbiters (fs, (true, ltReq)) (START_a4, (g, l4_tttt)))
   (Trans_Struct_four_arbiters (fs, (true, ltReq))
      (g11, true, (g12, true), (g21, true, (g22, true)))).

intros ltReq fs H0; elim H0; clear H0; intros Hreq1 H0; elim H0; clear H0;
 intros Hreq2 H0; elim H0; clear H0; intros Hreq3 Hreq4.
unfold R_a4 in |- *; unfold Trans_Four_Arbiters in |- *.
replace (Ackor (d_map (Ackor (n:=3)) ltReq)) with true.
split.
right; right; right; left.
split; auto.

unfold Output_requested in |- *.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
right; right; left.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; auto.
apply sym_equal; apply split_List4.

unfold Out_Four_Arbiters in |- *.
replace g with
 (List4 (Fst_of_l2 g11, Scd_of_l2 g11) (Fst_of_l2 g12, Scd_of_l2 g12)
    (Fst_of_l2 g21, Scd_of_l2 g21) (Fst_of_l2 g22, Scd_of_l2 g22)).

unfold Arb_xel in |- *; unfold Arbx in |- *; unfold Arb_xel in |- *.
unfold Two_Fst_of_l4' in |- *; unfold Two_last_of_l4' in |- *.
unfold Scd_of_l2 in |- *; unfold List2 in |- *; simpl in |- *.
unfold J_Arby in |- *; unfold K_Arby in |- *; unfold Arb_yel in |- *.

unfold Output_requested in |- *.

apply pair_eq.
apply pair_eq.

   (** (Ackor (Fst_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g11) (Scd_of_l2 g11) Hreq1); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Scd_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g12) (Scd_of_l2 g12) Hreq2); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Thd_of_l4 ltReq))=true **)
apply pair_eq.
specialize (Arbiter_last (Fst_of_l2 g21) (Scd_of_l2 g21) Hreq3); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

   (** (Ackor (Fth_of_l4 ltReq))=true **)
specialize (Arbiter_last (Fst_of_l2 g22) (Scd_of_l2 g22) Hreq4); intro A;
 elim A; clear A; intros A A'.
apply id_list3; auto.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *; auto.
apply sym_equal; apply split_List4.

elim H1; elim H2; elim H3; elim H4; elim H5; elim H6; elim H7; elim H8;
 simpl in |- *.
apply sym_equal; apply List4_of_pdt.
replace ltReq with
 (List4 (Fst_of_l4 ltReq) (Scd_of_l4 ltReq) (Thd_of_l4 ltReq)
    (Fth_of_l4 ltReq)); simpl in |- *.
rewrite Hreq1; rewrite Hreq2; rewrite Hreq3; rewrite Hreq4; simpl in |- *;
 auto.
apply sym_equal; apply split_List4.
Qed.



End For_ltReq.




Lemma Invariant_a4_SSS :
 forall (fs RouteE : bool) (ltReq : d_list (d_list bool 4) 4)
   (sa4 : label_a4) (g : d_list (bool * bool) 4) (o : d_list bool 4)
   (old11 old12 old21 old22 : d_list bool 2 * bool),
 sa4 = START_a4 /\ o = l4_tttt ->
 P_a4 (fs, (RouteE, ltReq)) (sa4, (g, o)) (old11, old12, (old21, old22)) ->
 R_a4 (sa4, (g, o)) (old11, old12, (old21, old22)) ->
 R_a4 (Trans_Four_Arbiters (fs, (RouteE, ltReq)) (sa4, (g, o)))
   (Trans_Struct_four_arbiters (fs, (RouteE, ltReq))
      (old11, old12, (old21, old22))).

intros fs RouteE ltReq sa4 g o old11 old12 old21 old22 H.
elim H; clear H; intros H H'; rewrite H; rewrite H'.
elim old11; elim old12; elim old21; elim old22; clear old11 old12 old21 old22;
 intros g22 o22 g21 o21 g12 o12 g11 o11.
unfold R_a4 at 1 in |- *.

intros p_a4 HR; simpl in HR; clear p_a4.
elim HR; clear HR.
intro Hr; clear Hr.
intro Hr.
specialize (eq_pair Hr).
clear Hr; intros Hr; elim Hr; clear Hr; intros H1 H2.
specialize (eq_pair H1); specialize (eq_pair H2); clear H1 H2.
intros H1 H2; elim H1; clear H1; elim H2; clear H2; intros H1 H2 H3 H4.
specialize (id_list3_fst H1); specialize (id_list3_scd H1); intros H11 H12.
specialize (id_list3_fst H2); specialize (id_list3_scd H2); intros H21 H22.
specialize (id_list3_fst H3); specialize (id_list3_scd H3); intros H31 H32.
specialize (id_list3_fst H4); specialize (id_list3_scd H4); intros H41 H42.
specialize (id_list3_thd H1); intro Ho1.
specialize (id_list3_thd H2); intro Ho2; unfold Scd_of_l4 in Ho2;
 simpl in Ho2.
specialize (id_list3_thd H3); intro Ho3; unfold Thd_of_l4 in Ho3;
 simpl in Ho3.
specialize (id_list3_thd H4); intro Ho4; unfold Fth_of_l4 in Ho4;
 simpl in Ho4.

replace o11 with true; trivial.
replace o12 with true; trivial.
replace o21 with true; trivial.
replace o22 with true; trivial.

case RouteE.
 
elim (bool_dec (Ackor (d_map (Ackor (n:=3)) ltReq))).
intro H_ltReq; elim (Ackor_dmap_true_4 H_ltReq).

 (** ltReq=0001 **)
intro H0.
apply ltReq_OOO1; try trivial.

 (** ltReq=0010 **)
intro H0; elim H0; clear H0; intro H0.
apply ltReq_OO1O; try trivial.

 (** ltReq=0011 **)
elim H0; clear H0; intro H0.
apply ltReq_OO11; try trivial.

 (** ltReq=O1OO **)
elim H0; clear H0; intro H0.
apply ltReq_O1OO; try trivial.

 (** ltReq=O1O1 **)
elim H0; clear H0; intro H0.
apply ltReq_O1O1; try trivial.

 (** ltReq=O11O **)
elim H0; clear H0; intro H0.
apply ltReq_O11O; try trivial.

 (** ltReq=O111 **)
elim H0; clear H0; intro H0.
apply ltReq_O111; try trivial.

 (** ltReq=1OOO **)
elim H0; clear H0; intro H0.
apply ltReq_1OOO; try trivial.

 (** ltReq=1OO1 **)
elim H0; clear H0; intro H0.
apply ltReq_1OO1; try trivial.

 (** ltReq=1O1O **)
elim H0; clear H0; intro H0.
apply ltReq_1O1O; try trivial.

 (** ltReq=1O11 **)
elim H0; clear H0; intro H0.
apply ltReq_1O11; try trivial.

 (** ltReq=11OO **)
elim H0; clear H0; intro H0.
apply ltReq_11OO; try trivial.

 (** ltReq=11O1 **)
elim H0; clear H0; intro H0.
apply ltReq_11O1; try trivial.

 (** ltReq=111O **)
elim H0; clear H0; intro H0.
apply ltReq_111O; try trivial.

 (** ltReq=1111 **)
apply ltReq_1111; try trivial.

intro H_ltReq.
elim (Ackor_dmap_false_4 H_ltReq).
intros Hreq1 H0; elim H0; clear H0; intros Hreq2 H0; elim H0; clear H0;
 intros Hreq3 Hreq4.
simpl in |- *.
rewrite H_ltReq; simpl in |- *.
unfold J_Arby in |- *; unfold Arby in |- *; unfold Arbx in |- *;
 unfold Arb_xel in |- *; unfold Scd_of_l2 in |- *; 
 unfold List2 in |- *; simpl in |- *.
unfold Arb_yel in |- *; unfold K_Arby in |- *.
specialize (Ackor_false Hreq1); specialize (Ackor_false Hreq2);
 specialize (Ackor_false Hreq3); specialize (Ackor_false Hreq4).
intros A B C D; elim A; clear A; intros A1 A; elim A; clear A; intros A2 A;
 elim A; clear A; intros A3 A4.
elim B; clear B; intros B1 B; elim B; clear B; intros B2 B; elim B; clear B;
 intros B3 B4.
elim C; clear C; intros C1 C; elim C; clear C; intros C2 C; elim C; clear C;
 intros C3 C4.
elim D; clear D; intros D1 D; elim D; clear D; intros D2 D; elim D; clear D;
 intros D3 D4.
rewrite A1; rewrite A2; rewrite A3; rewrite A4; rewrite B1; rewrite B2;
 rewrite B3; rewrite B4; rewrite C1; rewrite C2; rewrite C3; 
 rewrite C4; rewrite D1; rewrite D2; rewrite D3; rewrite D4; 
 simpl in |- *.
split.

auto.
unfold Arb_yel in |- *; unfold AO in |- *; simpl in |- *.
apply pair_eq.
apply pair_eq.
apply id_list3.
elim andb_sym; simpl in |- *.
rewrite H12; elim (Fst_of_l2 g11); auto.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
rewrite H11; unfold Scd_of_l2 in |- *; elim (d_Head (d_tl g11)); auto.
rewrite Hreq1; try trivial.

apply id_list3.
elim andb_sym; simpl in |- *.
rewrite H22; elim (Fst_of_l2 g12); auto.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
rewrite H21; unfold Scd_of_l2 in |- *; elim (d_Head (d_tl g12)); auto.
rewrite Hreq2; try trivial.

apply pair_eq.
apply id_list3.
elim andb_sym; simpl in |- *.
rewrite H32; elim (Fst_of_l2 g21); auto.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
rewrite H31; unfold Scd_of_l2 in |- *; elim (d_Head (d_tl g21)); auto.
rewrite Hreq3; try trivial.

apply id_list3.
elim andb_sym; simpl in |- *.
rewrite H42; elim (Fst_of_l2 g22); auto.
elim andb_sym; simpl in |- *.
elim andb_sym; simpl in |- *.
rewrite H41; unfold Scd_of_l2 in |- *; elim (d_Head (d_tl g22)); auto.
rewrite Hreq4; try trivial.

simpl in |- *.
split; auto.

elim H11; elim H12; elim H21; elim H22; elim H31; elim H32; elim H41;
 elim H42; auto.

Qed.