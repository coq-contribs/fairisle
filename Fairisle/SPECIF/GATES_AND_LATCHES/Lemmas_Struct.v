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
(*                             Lemmas_Struct.v                              *)
(****************************************************************************)
 

Require Export Base_Struct.
Require Export Proj_lists.
Require Export Bool_Compl.

Set Implicit Arguments.
Unset Strict Implicit.



Lemma Ackor_false_fst :
 forall l : d_list bool 4, Ackor l = false -> Fst_of_l4 l = false.
intros l; elim (non_empty l); intros x H; elim H; clear H; intros X H;
 rewrite H.
unfold Ackor in |- *; unfold Fold_with_f_S in |- *; simpl in |- *.
elim x; auto.
Qed.


Lemma Ackor_false_scd :
 forall l : d_list bool 4, Ackor l = false -> Scd_of_l4 l = false.
intros l; elim (non_empty l); intros x H; elim H; clear H; intros X H;
 rewrite H.
unfold Ackor in |- *; unfold Fold_with_f_S in |- *; simpl in |- *.
unfold Scd_of_l4 in |- *; simpl in |- *.
elim (d_Head X); auto.
simpl in |- *.
elim orb_sym; auto.
Qed.


Lemma Ackor_false_thd :
 forall l : d_list bool 4, Ackor l = false -> Thd_of_l4 l = false.
intros l; elim (non_empty l); intros x H; elim H; clear H; intros X H;
 rewrite H.
unfold Ackor in |- *; unfold Fold_with_f_S in |- *; simpl in |- *.
unfold Thd_of_l4 in |- *; simpl in |- *.
elim (d_Head (d_tl X)); auto.
simpl in |- *.
replace (OR2 (d_Head X) true) with (OR2 true (d_Head X)); simpl in |- *.
elim orb_sym; auto with bool.
auto with bool.
Qed.



Lemma Ackor_false_fth :
 forall l : d_list bool 4, Ackor l = false -> Fth_of_l4 l = false.
intros l; elim (non_empty l); intros x H; elim H; clear H; intros X H;
 rewrite H.
unfold Ackor in |- *; unfold Fold_with_f_S in |- *; simpl in |- *.
unfold Fth_of_l4 in |- *; simpl in |- *.
(** (Elim (d_Head (d_tl (d_tl X))); Auto) : NE FAIT RIEN ??? **)
elim (non_empty X); intros x' H'; elim H'; clear H'; intros X' H'; rewrite H';
 simpl in |- *.
elim (d_Head (d_tl X')); auto.
replace (OR2 (d_Head X') true) with (OR2 true (d_Head X')); simpl in |- *.
replace (OR2 x' true) with (true || x'); simpl in |- *.
elim orb_sym; auto.
auto with bool.
auto with bool.
Qed.


Lemma Ackor_dmap_true_2 :
 forall l : d_list (d_list bool 4) 2,
 Ackor (d_map (Ackor (n:=3)) l) = true ->
 Ackor (Fst_of_l2 l) = true /\ Ackor (Scd_of_l2 l) = true \/
 Ackor (Fst_of_l2 l) = true /\ Ackor (Scd_of_l2 l) = false \/
 Ackor (Fst_of_l2 l) = false /\ Ackor (Scd_of_l2 l) = true.
intro l.
elim (non_empty l).
intros x t; elim t; clear t.
intros t.
elim (non_empty t).
intros x' t'; elim t'; clear t'.
intros t'.
intros H1 H2.
rewrite H2; rewrite H1; simpl in |- *.
replace t' with (d_nil (d_list bool 4)); auto.
intros.
unfold Scd_of_l2 in |- *; simpl in |- *.
generalize H.
elim (Ackor x); elim (Ackor x'); simpl in |- *; auto.
Qed.


Lemma Ackor_dmap_false_2 :
 forall l : d_list (d_list bool 4) 2,
 Ackor (d_map (Ackor (n:=3)) l) = false ->
 Ackor (Fst_of_l2 l) = false /\ Ackor (Scd_of_l2 l) = false.
intro l.
elim (non_empty l).
intros x t; elim t; clear t.
intros t; elim (non_empty t).
intros x' t'; elim t'; clear t'.
intros t'.
replace t' with (d_nil (d_list bool 4)); auto.
intros H1 H2.
rewrite H2; rewrite H1; simpl in |- *.
unfold Scd_of_l2 in |- *; simpl in |- *.
elim (Ackor x); elim (Ackor x'); auto.
Qed.



Lemma Ackor_dmap_true_4 :
 forall l : d_list (d_list bool 4) 4,
 Ackor (d_map (Ackor (n:=3)) l) = true ->
 Ackor (Fst_of_l4 l) = false /\
 Ackor (Scd_of_l4 l) = false /\
 Ackor (Thd_of_l4 l) = false /\ Ackor (Fth_of_l4 l) = true \/
 Ackor (Fst_of_l4 l) = false /\
 Ackor (Scd_of_l4 l) = false /\
 Ackor (Thd_of_l4 l) = true /\ Ackor (Fth_of_l4 l) = false \/
 Ackor (Fst_of_l4 l) = false /\
 Ackor (Scd_of_l4 l) = false /\
 Ackor (Thd_of_l4 l) = true /\ Ackor (Fth_of_l4 l) = true \/
 Ackor (Fst_of_l4 l) = false /\
 Ackor (Scd_of_l4 l) = true /\
 Ackor (Thd_of_l4 l) = false /\ Ackor (Fth_of_l4 l) = false \/
 Ackor (Fst_of_l4 l) = false /\
 Ackor (Scd_of_l4 l) = true /\
 Ackor (Thd_of_l4 l) = false /\ Ackor (Fth_of_l4 l) = true \/
 Ackor (Fst_of_l4 l) = false /\
 Ackor (Scd_of_l4 l) = true /\
 Ackor (Thd_of_l4 l) = true /\ Ackor (Fth_of_l4 l) = false \/
 Ackor (Fst_of_l4 l) = false /\
 Ackor (Scd_of_l4 l) = true /\
 Ackor (Thd_of_l4 l) = true /\ Ackor (Fth_of_l4 l) = true \/
 Ackor (Fst_of_l4 l) = true /\
 Ackor (Scd_of_l4 l) = false /\
 Ackor (Thd_of_l4 l) = false /\ Ackor (Fth_of_l4 l) = false \/
 Ackor (Fst_of_l4 l) = true /\
 Ackor (Scd_of_l4 l) = false /\
 Ackor (Thd_of_l4 l) = false /\ Ackor (Fth_of_l4 l) = true \/
 Ackor (Fst_of_l4 l) = true /\
 Ackor (Scd_of_l4 l) = false /\
 Ackor (Thd_of_l4 l) = true /\ Ackor (Fth_of_l4 l) = false \/
 Ackor (Fst_of_l4 l) = true /\
 Ackor (Scd_of_l4 l) = false /\
 Ackor (Thd_of_l4 l) = true /\ Ackor (Fth_of_l4 l) = true \/
 Ackor (Fst_of_l4 l) = true /\
 Ackor (Scd_of_l4 l) = true /\
 Ackor (Thd_of_l4 l) = false /\ Ackor (Fth_of_l4 l) = false \/
 Ackor (Fst_of_l4 l) = true /\
 Ackor (Scd_of_l4 l) = true /\
 Ackor (Thd_of_l4 l) = false /\ Ackor (Fth_of_l4 l) = true \/
 Ackor (Fst_of_l4 l) = true /\
 Ackor (Scd_of_l4 l) = true /\
 Ackor (Thd_of_l4 l) = true /\ Ackor (Fth_of_l4 l) = false \/
 Ackor (Fst_of_l4 l) = true /\
 Ackor (Scd_of_l4 l) = true /\
 Ackor (Thd_of_l4 l) = true /\ Ackor (Fth_of_l4 l) = true.
intro l.
elim (non_empty l).
intros x t; elim t; clear t.
intro t.
elim (non_empty t).
intros x' t'; elim t'; clear t'.
intro t'.
elim (non_empty t').
intros x'' t''; elim t''; clear t''.
intro t''.
elim (non_empty t'').
intros x''' t'''; elim t'''; clear t'''.
intro t'''.
intros H1 H2 H3 H4.
rewrite H4; rewrite H3; rewrite H2; rewrite H1; simpl in |- *.
replace t''' with (d_nil (d_list bool 4)); auto.
intro H.
unfold Scd_of_l4 in |- *; unfold Thd_of_l4 in |- *; unfold Fth_of_l4 in |- *;
 simpl in |- *.
generalize H.
elim (Ackor x); elim (Ackor x'); elim (Ackor x''); elim (Ackor x''');
 simpl in |- *; clear H; intro H.
do 14 right; auto.
do 13 right; auto.
do 12 right; auto.
do 11 right; auto.
do 10 right; auto.
do 9 right; auto.
do 8 right; auto.
do 7 right; auto.
do 6 right; auto.
do 5 right; auto.
do 4 right; auto.
do 3 right; auto.
do 2 right; auto.
right; auto.
auto.
unfold Ackor in H; simpl in H.
absurd (false = true); auto.
Qed.


Lemma Ackor_dmap_false_4 :
 forall l : d_list (d_list bool 4) 4,
 Ackor (d_map (Ackor (n:=3)) l) = false ->
 Ackor (Fst_of_l4 l) = false /\
 Ackor (Scd_of_l4 l) = false /\
 Ackor (Thd_of_l4 l) = false /\ Ackor (Fth_of_l4 l) = false.
intro l.
elim (non_empty l).
intros x t; elim t; clear t.
intros t; elim (non_empty t).
intros x' t'; elim t'; clear t'.
intros t'.
elim (non_empty t').
intros x'' t''; elim t''; clear t''.
intro t''.
elim (non_empty t'').
intros x''' t'''; elim t'''; clear t'''.
intro t'''.
replace t''' with (d_nil (d_list bool 4)); auto.
intros H1 H2 H3 H4.
rewrite H4; rewrite H3; rewrite H2; rewrite H1; simpl in |- *.
unfold Scd_of_l4 in |- *; unfold Thd_of_l4 in |- *; unfold Fth_of_l4 in |- *;
 simpl in |- *.
elim (Ackor x); elim (Ackor x'); elim (Ackor x''); elim (Ackor x'''); auto.
Qed.
