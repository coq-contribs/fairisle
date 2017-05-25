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
(*                               Proj_lists.v                               *)
(****************************************************************************)
 

Require Export Lists_of_lists.
Require Export Syntactic_Def.
Require Export Infinite_lists.

Set Implicit Arguments.
Unset Strict Implicit.


Section Projections_on_fixed_dlists.

  Variable A : Set.

  Definition Fst_of_l2 (l : d_list A 2) := d_Head l.
  Definition Scd_of_l2 (l : d_list A 2) := d_Head (d_tl l).

  Definition Fst_of_l3 (l : d_list A 3) := d_Head l.
  Definition Scd_of_l3 (l : d_list A 3) := d_Head (d_tl l).
  Definition Thd_of_l3 (l : d_list A 3) := d_Head (d_tl (d_tl l)).

  Definition Fst_of_l4 (l : d_list A 4) := d_Head l.
  Definition Scd_of_l4 (l : d_list A 4) := d_Head (d_tl l).
  Definition Thd_of_l4 (l : d_list A 4) := d_Head (d_tl (d_tl l)).
  Definition Fth_of_l4 (l : d_list A 4) := d_Head (d_tl (d_tl (d_tl l))).

  Definition List_of_fst_of_l2 := list_of_heads (A:=A) (i:=1) (n:=2). 
  Definition List_of_tails_of_l2 := list_of_tails (A:=A) (i:=2) (n:=2).
  Definition List_of_scd_of_l2 (l : d_list (d_list A 2) 2) :=
    list_of_heads (A:=A) (i:=0) (n:=2) (List_of_tails_of_l2 l).

  Definition three_fst_of_l4 (l : d_list A 4) :=
    Seg (A:=A) (n:=1) (m:=3) (k:=4) l lt_O_1 le_3_4 le_1_3.

  Definition two_fst_of_l3 (l : d_list A 3) :=
    Seg (A:=A) (n:=1) (m:=2) (k:=3) l lt_O_1 le_2_3 le_1_2.

  Definition Two_Fst_of_l4 (l : d_list A 4) :=
    Seg (A:=A) (n:=1) (m:=2) (k:=4) l lt_O_1 le_2_4 le_1_2.

  Definition Two_last_of_l4 (l : d_list A 4) :=
    Seg (A:=A) (n:=3) (m:=4) (k:=4) l lt_O_3 le_4_4 le_3_4.


  Definition S_Fst_of_l2 := S_map Fst_of_l2.
  Definition S_Scd_of_l2 := S_map Scd_of_l2.
  Definition S_Fst_of_l4 := S_map Fst_of_l4.
  Definition S_Scd_of_l4 := S_map Scd_of_l4.
  Definition S_Thd_of_l4 := S_map Thd_of_l4.
  Definition S_Fth_of_l4 := S_map Fth_of_l4.
  Definition S_List_of_fst_of_l2 := S_map List_of_fst_of_l2.
  Definition S_List_of_tails_of_l2 := S_map List_of_tails_of_l2.
  Definition S_List_of_scd_of_l2 := S_map List_of_scd_of_l2.

  Definition S_three_fst_of_l4 := S_map three_fst_of_l4.
  

End Projections_on_fixed_dlists.


Lemma EqS_S_Fst_of_l4 :
 forall (A : Set) (s1 s2 : Stream (d_list A 4)),
 EqS s1 s2 -> EqS (S_map (Fst_of_l4 (A:=A)) s1) (S_map (Fst_of_l4 (A:=A)) s2).
cofix.
intros A s1 s2 H.
inversion_clear H.
apply eqS; simpl in |- *.
elim H0; try trivial.
auto.
Qed.

Lemma EqS_S_Scd_of_l4 :
 forall (A : Set) (s1 s2 : Stream (d_list A 4)),
 EqS s1 s2 -> EqS (S_map (Scd_of_l4 (A:=A)) s1) (S_map (Scd_of_l4 (A:=A)) s2).
cofix.
intros A s1 s2 H.
inversion_clear H.
apply eqS; simpl in |- *.
elim H0; try trivial.
auto.
Qed.

Lemma EqS_S_Thd_of_l4 :
 forall (A : Set) (s1 s2 : Stream (d_list A 4)),
 EqS s1 s2 -> EqS (S_map (Thd_of_l4 (A:=A)) s1) (S_map (Thd_of_l4 (A:=A)) s2).
cofix.
intros A s1 s2 H.
inversion_clear H.
apply eqS; simpl in |- *.
elim H0; try trivial.
auto.
Qed.

Lemma EqS_S_Fth_of_l4 :
 forall (A : Set) (s1 s2 : Stream (d_list A 4)),
 EqS s1 s2 -> EqS (S_map (Fth_of_l4 (A:=A)) s1) (S_map (Fth_of_l4 (A:=A)) s2).
cofix.
intros A s1 s2 H.
inversion_clear H.
apply eqS; simpl in |- *.
elim H0; try trivial.
auto.
Qed.


