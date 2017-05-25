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
(*                               Tools_Inf.v                                *)
(****************************************************************************)
 

Require Export Infinite_lists.
Require Import Syntactic_Def.
Require Import Base_Struct.
Require Import Proj_lists.

Set Implicit Arguments.
Unset Strict Implicit.


Definition S_Ackor (n : nat) := S_map (Ackor (n:=n)).



Definition active_bits :=
  S_list_of_nth (A:=bool) (i:=8) (n:=8) (m:=4) lt_O_8 le_8_8.

Definition priority_bits :=
  S_list_of_nth (A:=bool) (i:=7) (n:=8) (m:=4) lt_O_7 le_7_8.

Definition route_bits :=
  S_list_of_seg (A:=bool) (n:=5) (m:=6) (k:=8) (p:=4) lt_O_5 le_6_8 le_5_6.


Definition act_bits :=
  list_of_nth (A:=bool) (i:=8) (n:=8) lt_O_8 le_8_8 (n0:=4).
Definition pri_bits :=
  list_of_nth (A:=bool) (i:=7) (n:=8) lt_O_7 le_7_8 (n0:=4).
Definition rou_bits :=
  list_of_seg (A:=bool) (n:=5) (m:=6) (k:=8) lt_O_5 le_6_8 le_5_6 (n0:=4).


Definition All_Fst_of_l3 (l : d_list (d_list bool 3) 4) :=
  d_map (Fst_of_l3 (A:=bool)) l.
Definition x_Grant := S_map All_Fst_of_l3.

Definition All_Scd_of_l3 (l : d_list (d_list bool 3) 4) :=
  d_map (Scd_of_l3 (A:=bool)) l.
Definition y_Grant := S_map All_Scd_of_l3.

Definition All_Thd_of_l3 (l : d_list (d_list bool 3) 4) :=
  d_map (Thd_of_l3 (A:=bool)) l.
Definition OutputDisable := S_map All_Fst_of_l3.

Definition grant (l : d_list (d_list bool 3) 4) :=
  d_map (seg (A:=bool) (n:=1) (m:=2) (k:=3) lt_O_1 le_2_3 le_1_2) l.
Definition Grant := S_map grant.  


(*******************************************************************************)

Definition xGrant' :=
  d_map (S_Nth (A:=bool) (i:=1) (n:=3) lt_O_1 le_1_3) (n:=4).
 
Definition yGrant' :=
  d_map (S_Nth (A:=bool) (i:=2) (n:=3) lt_O_2 le_2_3) (n:=4).
 
Definition outputDisable' :=
  d_map (S_Nth (A:=bool) (i:=3) (n:=3) lt_O_3 le_3_3) (n:=4).
 

Definition x_Grant' (l : d_list (Stream (d_list bool 3)) 4) :=
  dlist_to_Stream (n:=4) (xGrant' l).

Definition y_Grant' (l : d_list (Stream (d_list bool 3)) 4) :=
  dlist_to_Stream (n:=4) (yGrant' l).

Definition OutputDisable' (l : d_list (Stream (d_list bool 3)) 4) :=
  dlist_to_Stream (n:=4) (outputDisable' l).


(** Returns the infinite list containing the two first infinite lists **)

Definition grant' :=
  d_map (S_Seg (A:=bool) (n:=1) (m:=2) (k:=3) lt_O_1 le_2_3 le_1_2) (n:=4).  

Definition Grant' (l : d_list (Stream (d_list bool 3)) 4) :=
  dlist_to_Stream (n:=4) (grant' l).  
