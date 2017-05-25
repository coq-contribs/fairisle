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
(*                         Arbiter4_Proof_lemmas.v                          *)
(****************************************************************************)
 

Require Export Lemmas_Comb_Behaviour.
Require Export Lemmas_Struct.

Set Implicit Arguments.
Unset Strict Implicit.

  
Definition d_Map_List4_pdt_Grant (l : d_list (d_list bool 4) 4)
  (g : d_list (bool * bool) 4) :=
  d_map (List2_pdt (A:=bool))
    (d_map2 Grant_for_Out l
       (List4 (List2 (fst (Fst_of_l4 g)) (snd (Fst_of_l4 g)))
          (List2 (fst (Scd_of_l4 g)) (snd (Scd_of_l4 g)))
          (List2 (fst (Thd_of_l4 g)) (snd (Thd_of_l4 g)))
          (List2 (fst (Fth_of_l4 g)) (snd (Fth_of_l4 g))))).



Lemma ltReq_false_G1 :
 forall (l : d_list (d_list bool 4) 4) (g1 g1' g2 g2' g3 g3' g4 g4' : bool),
 Ackor (Fst_of_l4 l) = false ->
 Fst_of_l4
   (d_Map_List4_pdt_Grant l (List4 (g1, g1') (g2, g2') (g3, g3') (g4, g4'))) =
 (g1, g1').
intros.
unfold d_Map_List4_pdt_Grant in |- *.
unfold Fst_of_l4 in |- *; simpl in |- *.
unfold Grant_for_Out in |- *; unfold SuccessfulInput in |- *;
 unfold RequestsToArbitrate in |- *.
replace (Fst_of_l4 (d_Head l)) with false.
replace (Scd_of_l4 (d_Head l)) with false.
replace (Thd_of_l4 (d_Head l)) with false.
replace (Fth_of_l4 (d_Head l)) with false; simpl in |- *.
replace (Convert_port_list2 (Convert_list2_port (List2 g1 g1'))) with
 (List2 g1 g1').
auto.
unfold Convert_list2_port in |- *; unfold Convert_port_list2 in |- *;
 simpl in |- *.
elim g1; elim g1'; simpl in |- *; auto.
apply sym_equal; apply Ackor_false_fth; auto.
apply sym_equal; apply Ackor_false_thd; auto.
apply sym_equal; apply Ackor_false_scd; auto.
apply sym_equal; apply Ackor_false_fst; auto.
Qed.



Lemma ltReq_false_G2 :
 forall (l : d_list (d_list bool 4) 4) (g1 g1' g2 g2' g3 g3' g4 g4' : bool),
 Ackor (Scd_of_l4 l) = false ->
 Scd_of_l4
   (d_Map_List4_pdt_Grant l (List4 (g1, g1') (g2, g2') (g3, g3') (g4, g4'))) =
 (g2, g2').
intros.
unfold d_Map_List4_pdt_Grant in |- *.
unfold Scd_of_l4 in |- *; simpl in |- *.
unfold Grant_for_Out in |- *; unfold SuccessfulInput in |- *;
 unfold RequestsToArbitrate in |- *.
replace (Fst_of_l4 (d_Head (d_tl l))) with false.
replace (Scd_of_l4 (d_Head (d_tl l))) with false.
replace (Thd_of_l4 (d_Head (d_tl l))) with false.
replace (Fth_of_l4 (d_Head (d_tl l))) with false; simpl in |- *.
replace (Convert_port_list2 (Convert_list2_port (List2 g2 g2'))) with
 (List2 g2 g2').
auto.
unfold Convert_list2_port in |- *; unfold Convert_port_list2 in |- *;
 simpl in |- *.
elim g2; elim g2'; simpl in |- *; auto.
apply sym_equal; apply Ackor_false_fth; auto.
apply sym_equal; apply Ackor_false_thd; auto.
apply sym_equal; apply Ackor_false_scd; auto.
apply sym_equal; apply Ackor_false_fst; auto.
Qed.



Lemma ltReq_false_G3 :
 forall (l : d_list (d_list bool 4) 4) (g1 g1' g2 g2' g3 g3' g4 g4' : bool),
 Ackor (Thd_of_l4 l) = false ->
 Thd_of_l4
   (d_Map_List4_pdt_Grant l (List4 (g1, g1') (g2, g2') (g3, g3') (g4, g4'))) =
 (g3, g3').
intros.
unfold d_Map_List4_pdt_Grant in |- *.
unfold Thd_of_l4 in |- *; simpl in |- *.
unfold Grant_for_Out in |- *; unfold SuccessfulInput in |- *;
 unfold RequestsToArbitrate in |- *.
generalize H; clear H.
elim (non_empty l).
intros x t; elim t; clear t; intros t H'.
rewrite H'; simpl in |- *; intro H.
replace (Fst_of_l4 (d_Head (d_tl t))) with false.
replace (Scd_of_l4 (d_Head (d_tl t))) with false.
replace (Thd_of_l4 (d_Head (d_tl t))) with false.
replace (Fth_of_l4 (d_Head (d_tl t))) with false; simpl in |- *.
replace (Convert_port_list2 (Convert_list2_port (List2 g3 g3'))) with
 (List2 g3 g3').
auto.
unfold Convert_list2_port in |- *; unfold Convert_port_list2 in |- *;
 simpl in |- *.
elim g3; elim g3'; simpl in |- *; auto.
apply sym_equal; apply Ackor_false_fth; auto.
apply sym_equal; apply Ackor_false_thd; auto.
apply sym_equal; apply Ackor_false_scd; auto.
apply sym_equal; apply Ackor_false_fst; auto.
Qed. 


Lemma ltReq_false_G4 :
 forall (l : d_list (d_list bool 4) 4) (g1 g1' g2 g2' g3 g3' g4 g4' : bool),
 Ackor (Fth_of_l4 l) = false ->
 Fth_of_l4
   (d_Map_List4_pdt_Grant l (List4 (g1, g1') (g2, g2') (g3, g3') (g4, g4'))) =
 (g4, g4').
intros.
unfold d_Map_List4_pdt_Grant in |- *.
unfold Fth_of_l4 in |- *; simpl in |- *.
unfold Grant_for_Out in |- *; unfold SuccessfulInput in |- *;
 unfold RequestsToArbitrate in |- *.
generalize H; clear H.
elim (non_empty l).
intros x t; elim t; clear t; intros t H'.
elim (non_empty t).
intros x' t'; elim t'; clear t'; intros t' H''.
rewrite H'; rewrite H''; simpl in |- *; intro H.
replace (Fst_of_l4 (d_Head (d_tl t'))) with false.
replace (Scd_of_l4 (d_Head (d_tl t'))) with false.
replace (Thd_of_l4 (d_Head (d_tl t'))) with false.
replace (Fth_of_l4 (d_Head (d_tl t'))) with false; simpl in |- *.
replace (Convert_port_list2 (Convert_list2_port (List2 g4 g4'))) with
 (List2 g4 g4').
auto.
unfold Convert_list2_port in |- *; unfold Convert_port_list2 in |- *;
 simpl in |- *.
elim g4; elim g4'; simpl in |- *; auto.
apply sym_equal; apply Ackor_false_fth; auto.
apply sym_equal; apply Ackor_false_thd; auto.
apply sym_equal; apply Ackor_false_scd; auto.
apply sym_equal; apply Ackor_false_fst; auto.
Qed. 
