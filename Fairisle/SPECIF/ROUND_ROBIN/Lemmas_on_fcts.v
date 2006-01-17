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
(*                             Lemmas_on_fcts.v                             *)
(****************************************************************************)
 

Require Import Bool_Compl.
Require Import SuccessfulInput.
Require Import Base_Struct.


Set Implicit Arguments.
Unset Strict Implicit.



Lemma Ackor_true_RequestsToArbitrate :
 forall l : d_list bool 4,
 Ackor l = true ->
 {b : T_Inportno 4 & 
 {l' : list (T_Inportno 4) | RequestsToArbitrate l = b :: l'}}.

intros l.
elim (non_empty l).
intros x0 X0; elim X0.
clear X0; intros X0 H0.
rewrite H0.
unfold Ackor in |- *; unfold RequestsToArbitrate in |- *.
unfold Fold_with_f_S in |- *; simpl in |- *.
case x0; simpl in |- *.
intros H; clear H.
exists (exist (fun p : nat => p < 4) 0 lt_O_4).
exists
 (test_port (Scd_of_l4 (d_cons true X0))
    (exist (fun p : nat => p < 4) 1 lt_1_4) ++
  test_port (Thd_of_l4 (d_cons true X0))
    (exist (fun p : nat => p < 4) 2 lt_2_4) ++
  test_port (Fth_of_l4 (d_cons true X0))
    (exist (fun p : nat => p < 4) 3 lt_3_4)); auto.
unfold Scd_of_l4 in |- *; simpl in |- *.
case (d_Head X0); simpl in |- *.
intro H; clear H.
exists (exist (fun p : nat => p < 4) 1 lt_1_4).
exists
 (test_port (Thd_of_l4 (d_cons false X0))
    (exist (fun p : nat => p < 4) 2 lt_2_4) ++
  test_port (Fth_of_l4 (d_cons false X0))
    (exist (fun p : nat => p < 4) 3 lt_3_4)); auto.
unfold Thd_of_l4 in |- *; simpl in |- *.
case (d_Head (d_tl X0)); simpl in |- *.
intro H; clear H.
exists (exist (fun p : nat => p < 4) 2 lt_2_4).
exists
 (test_port (Fth_of_l4 (d_cons false X0))
    (exist (fun p : nat => p < 4) 3 lt_3_4)); auto.
unfold Fth_of_l4 in |- *; simpl in |- *.
elim (non_empty X0).
intros x X; elim X; clear X.
intros X HX; rewrite HX; simpl in |- *.
case (d_Head (d_tl X)); simpl in |- *.
intros H; clear H.
exists (exist (fun p : nat => p < 4) 3 lt_3_4).
exists (nil (A:=T_Inportno 4)); auto.
intros Abs; absurd (false = true); auto.
Qed.



Lemma RoundRobinArbiter_simpl :
 forall l : d_list bool 4,
 Ackor l = true ->
 RoundRobinArbiter (list_dlist (RequestsToArbitrate l)) =
 RoundRobin 4 (list_dlist (RequestsToArbitrate l)).
intros l H.
elim (Ackor_true_RequestsToArbitrate H).
intros x H'; elim H'; clear H'.
intros X H'.
rewrite H'.
auto.
Qed.


(*****************************************************************************)


Definition SM4 := SUC_MODN (i:=4).

Lemma lt_4_4cases :
 forall n : nat, n < 4 -> {n = 0} + {n = 1} + {n = 2} + {n = 3}.
simple induction n; auto.
clear n; intros n H_rec H; elim H_rec.
intro H1; elim H1.
intro H2; elim H2.
auto.
auto.
auto.
intros H'; generalize H; rewrite H'.
intros Abs; absurd (4 < 4); auto with arith.
auto with arith.
Qed.


Lemma eq_n_SM4_4_times :
 forall n : T_Inportno 4, no_in n = no_in (SM4 (SM4 (SM4 (SM4 n)))).
simple destruct n.
clear n.
intros n lt_4.
generalize lt_4.
unfold SM4 in |- *; unfold SUC_MODN at 4 in |- *; simpl in |- *.
elim (lt_4_4cases (n:=n)).
intro H; elim H.
clear H; intro H; elim H.

       (** Port 0**)

clear H.
intro H.
rewrite H.
intro H'.
elim (less_or_eq (exist (fun x : nat => x < 4) 0 H')); simpl in |- *.
intro y.
unfold SUC_MODN at 3 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n0 : nat => n0 < 4) 1 y)); simpl in |- *.
intro y1.
unfold SUC_MODN at 2 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n0 : nat => n0 < 4) 2 y1)); simpl in |- *.
intro y2.
unfold SUC_MODN in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n0 : nat => n0 < 4) 3 y2)); simpl in |- *.
intro y'; absurd (4 < 4); auto with arith.
 intro y'.
auto.
intro y'; absurd (3 = 4); auto with arith.
intro y'; absurd (2 = 4); auto with arith.
intro y'; absurd (1 = 4); auto.


       (** Port 1**)

clear H.
intros H; rewrite H; intros H'.
elim (less_or_eq (exist (fun x : nat => x < 4) 1 H')); simpl in |- *.
intro y.
unfold SUC_MODN at 3 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n0 : nat => n0 < 4) 2 y)); simpl in |- *.
intro y1.
unfold SUC_MODN at 2 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n0 : nat => n0 < 4) 3 y1)); simpl in |- *.
intro y2; absurd (4 < 4); auto with arith.
intros y2.
unfold SUC_MODN in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n0 : nat => n0 < 4) 0 (Ex_n_lt_gen y2)));
 simpl in |- *.
auto.
intro y3; absurd (1 = 4); auto.
intro y1; absurd (3 = 4); auto.
intro y; absurd (2 = 4); auto.

       (** Port 2**)

clear H.
intros H; rewrite H; intros H'.
elim (less_or_eq (exist (fun x : nat => x < 4) 2 H')); simpl in |- *.
intro y.
unfold SUC_MODN at 3 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n0 : nat => n0 < 4) 3 y)); simpl in |- *.
intros y1; absurd (4 < 4); auto with arith.
intro y1.
unfold SUC_MODN at 2 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n0 : nat => n0 < 4) 0 (Ex_n_lt_gen y1)));
 simpl in |- *.
intro y2.
unfold SUC_MODN in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n : nat => n < 4) 1 y2)); simpl in |- *.
auto.
intro y3; absurd (2 = 4); auto.
intro y2; absurd (1 = 4); auto.
intro y; absurd (3 = 4); auto.

       (** Port 3**)

intro H; rewrite H; intro H'.
elim (less_or_eq (exist (fun x : nat => x < 4) 3 H')); simpl in |- *.
intro y.
absurd (4 < 4); auto with arith.
intro y.
unfold SUC_MODN at 3 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n0 : nat => n0 < 4) 0 (Ex_n_lt_gen y)));
 simpl in |- *.
intro y1.
unfold SUC_MODN at 2 in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n0 : nat => n0 < 4) 1 y1)); simpl in |- *.
intro y2.
unfold SUC_MODN in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun n0 : nat => n0 < 4) 2 y2)); simpl in |- *.
auto.
intro y3; absurd (3 = 4); auto.
intro y2; absurd (2 = 4); auto.
intro y1; absurd (1 = 4); auto.
trivial.
Qed.


(*****************************************************************************)


Lemma d_In_SUC0_l2 :
 forall l : d_list bool 4,
 d_In (no_in (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4)))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Scd_of_l4 l = true.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))) with 1.
intros l.
elim (non_empty l).
intros x0 X0; elim X0; clear X0.
intros X0 H.
elim (non_empty X0).
intros x1 X1; elim X1; clear X1.
intros X1 H1.
elim (non_empty X1).
intros x2 X2; elim X2; clear X2.
intros X2 H2.
elim (non_empty X2).
intros x3 X3; elim X3; clear X3.
intros X3 H3.
rewrite H; rewrite H1; rewrite H2; rewrite H3.
unfold Scd_of_l4 in |- *; simpl in |- *.
unfold RequestsToArbitrate in |- *.
unfold Fst_of_l4 in |- *; unfold Scd_of_l4 in |- *; unfold Thd_of_l4 in |- *;
 unfold Fth_of_l4 in |- *; simpl in |- *.
elim x1; simpl in |- *; auto.
elim x0; elim x2; elim x3; simpl in |- *.
intro H'.
elim H'; clear H'.
intros Abs.
absurd (0 = 1); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (2 = 1); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 1); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (0 = 1); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (2 = 1); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (0 = 1); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 1); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (0 = 1); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (2 = 1); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (2 = 1); auto.
absurd (3 = 1); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (2 = 1); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intro Abs; absurd (3 = 1); auto.
intros Abs; absurd False; auto.
intros Abs; absurd False; auto.
unfold SUC_MODN in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *;
 auto.
intros Abs; absurd (1 = 4); auto.
Qed.



Lemma not_d_In_SUC0_l2 :
 forall l : d_list bool 4,
 ~
 d_In (no_in (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4)))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Scd_of_l4 l = false.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))) with 1.
intros l.
elim (non_empty l).
intros x0 X0; elim X0; clear X0.
intros X0 H.
elim (non_empty X0).
intros x1 X1; elim X1; clear X1.
intros X1 H1.
elim (non_empty X1).
intros x2 X2; elim X2; clear X2.
intros X2 H2.
elim (non_empty X2).
intros x3 X3; elim X3; clear X3.
intros X3 H3.
rewrite H; rewrite H1; rewrite H2; rewrite H3.
unfold Scd_of_l4 in |- *; simpl in |- *.
unfold RequestsToArbitrate in |- *.
unfold Fst_of_l4 in |- *; unfold Scd_of_l4 in |- *; unfold Thd_of_l4 in |- *;
 unfold Fth_of_l4 in |- *; simpl in |- *.
elim x1; simpl in |- *; auto.
elim x0; elim x2; elim x3; simpl in |- *.
intro H'.
elim H'; clear H'.
right; auto.
intros H'; elim H'; clear H'.
right; auto.
intros H'; elim H'; clear H'.
right; auto.
intros H'; elim H'; clear H'.
right; auto.
intros H'; elim H'; clear H'.
auto.
intros H'; elim H'; clear H'.
auto.
intros H'; elim H'; clear H'.
auto.
intros H'; elim H'; clear H'.
auto.
unfold SUC_MODN in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *;
 auto.
intros Abs; absurd (1 = 4); auto.
Qed.



Lemma d_In_SUC1_l3 :
 forall l : d_list bool 4,
 d_In (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Thd_of_l4 l = true.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))))
 with 2.
intros l.
elim (non_empty l).
intros x0 X0; elim X0; clear X0.
intros X0 H.
elim (non_empty X0).
intros x1 X1; elim X1; clear X1.
intros X1 H1.
elim (non_empty X1).
intros x2 X2; elim X2; clear X2.
intros X2 H2.
elim (non_empty X2).
intros x3 X3; elim X3; clear X3.
intros X3 H3.
rewrite H; rewrite H1; rewrite H2; rewrite H3.
unfold Thd_of_l4 in |- *; simpl in |- *.
unfold RequestsToArbitrate in |- *.
unfold Fst_of_l4 in |- *; unfold Scd_of_l4 in |- *; unfold Thd_of_l4 in |- *;
 unfold Fth_of_l4 in |- *; simpl in |- *.
elim x2; simpl in |- *; auto.
elim x0; elim x1; elim x3; simpl in |- *.
intros H'; elim H'; clear H'.
intros Abs; absurd (0 = 2); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (2 = 1); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 1); auto.
absurd (3 = 2); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (0 = 1); auto.
absurd (0 = 2); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (2 = 1); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (0 = 2); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 2); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (0 = 2); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (2 = 1); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 2); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (2 = 1); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intro Abs; absurd (3 = 2); auto.
intros Abs; absurd False; auto.
intros Abs; absurd False; auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *.
intro a.
elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
auto.
intros Abs; absurd (2 = 4); auto.
intro b.
elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen b)));
 simpl in |- *.
absurd (1 = 4); auto.
absurd (1 = 4); auto.
Qed.



Lemma not_d_In_SUC1_l3 :
 forall l : d_list bool 4,
 ~
 d_In (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Thd_of_l4 l = false.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))))
 with 2.
intros l.
elim (non_empty l).
intros x0 X0; elim X0; clear X0.
intros X0 H.
elim (non_empty X0).
intros x1 X1; elim X1; clear X1.
intros X1 H1.
elim (non_empty X1).
intros x2 X2; elim X2; clear X2.
intros X2 H2.
elim (non_empty X2).
intros x3 X3; elim X3; clear X3.
intros X3 H3.
rewrite H; rewrite H1; rewrite H2; rewrite H3.
unfold Thd_of_l4 in |- *; simpl in |- *.
unfold RequestsToArbitrate in |- *.
unfold Fst_of_l4 in |- *; unfold Scd_of_l4 in |- *; unfold Thd_of_l4 in |- *;
 unfold Fth_of_l4 in |- *; simpl in |- *.
elim x2; simpl in |- *; auto.
elim x0; elim x1; elim x3; simpl in |- *.
intro H'.
elim H'; clear H'.
right; right; auto.
intros H'; elim H'; clear H'.
right; right; auto.
intros H'; elim H'; clear H'.
right; auto.
intros H'; elim H'; clear H'.
right; auto.
intros H'; elim H'; clear H'.
right; auto.
intros H'; elim H'; clear H'.
right; auto.
intros H'; elim H'; clear H'.
auto.
intros H'; elim H'; clear H'.
auto.
unfold SUC_MODN in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *.
intro a.
elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
auto.
intros Abs; absurd (2 = 4); auto.
intro b.
elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen b)));
 simpl in |- *.
absurd (1 = 4); auto.
absurd (1 = 4); auto.
Qed.



Lemma d_In_SUC2_l4 :
 forall l : d_list bool 4,
 d_In
   (no_in
      (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4)))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Fth_of_l4 l = true.
replace
 (no_in
    (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4)))))
 with 3.
intros l.
elim (non_empty l).
intros x0 X0; elim X0; clear X0.
intros X0 H.
elim (non_empty X0).
intros x1 X1; elim X1; clear X1.
intros X1 H1.
elim (non_empty X1).
intros x2 X2; elim X2; clear X2.
intros X2 H2.
elim (non_empty X2).
intros x3 X3; elim X3; clear X3.
intros X3 H3.
rewrite H; rewrite H1; rewrite H2; rewrite H3.
unfold Fth_of_l4 in |- *; simpl in |- *.
unfold RequestsToArbitrate in |- *.
unfold Fst_of_l4 in |- *; unfold Scd_of_l4 in |- *; unfold Thd_of_l4 in |- *;
 unfold Fth_of_l4 in |- *; simpl in |- *.
elim x3; simpl in |- *; auto.
elim x0; elim x1; elim x2; simpl in |- *.
intros H'; elim H'; clear H'.
intros Abs; absurd (0 = 3); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 1); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 2); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (0 = 3); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 1); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (0 = 3); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 2); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 2); auto.
elim Abs; clear Abs; intros Abs.
absurd (0 = 3); auto.
absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 1); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 2); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 1); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 2); auto.
intros Abs; absurd False; auto.
intros Abs; absurd False; auto.
unfold SUC_MODN in |- *; simpl in |- *.
 elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *.
intro a.
elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
intro a0; elim (less_or_eq (exist (fun n : nat => n < 4) 2 a0)).
simpl in |- *; auto.
simpl in |- *.
intros Abs; absurd (3 = 4); auto.
intro b.
elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen b)));
 simpl in |- *.
absurd (2 = 4); auto.
absurd (1 = 4); auto.
absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
Qed.




Lemma not_d_In_SUC2_l4 :
 forall l : d_list bool 4,
 ~
 d_In
   (no_in
      (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4)))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Fth_of_l4 l = false.
replace
 (no_in
    (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4)))))
 with 3.
intros l.
elim (non_empty l).
intros x0 X0; elim X0; clear X0.
intros X0 H.
elim (non_empty X0).
intros x1 X1; elim X1; clear X1.
intros X1 H1.
elim (non_empty X1).
intros x2 X2; elim X2; clear X2.
intros X2 H2.
elim (non_empty X2).
intros x3 X3; elim X3; clear X3.
intros X3 H3.
rewrite H; rewrite H1; rewrite H2; rewrite H3.
unfold Fth_of_l4 in |- *; simpl in |- *.
unfold RequestsToArbitrate in |- *.
unfold Fst_of_l4 in |- *; unfold Scd_of_l4 in |- *; unfold Thd_of_l4 in |- *;
 unfold Fth_of_l4 in |- *; simpl in |- *.
elim x3; simpl in |- *; auto.
elim x0; elim x1; elim x2; simpl in |- *.
intro H'; elim H'; clear H'.
right; right; auto.
intros H'; elim H'; clear H'.
right; right; auto.
intros H'; elim H'; clear H'.
right; right; auto.
intros H'; elim H'; clear H'.
right; auto.
intros H'; elim H'; clear H'.
right; right; auto.
intros H'; elim H'; clear H'.
right; auto.
intros H'; elim H'; clear H'.
right; auto.
intros H'; elim H'; clear H'.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *;
 auto.
intro a; elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
intro a0; elim (less_or_eq (exist (fun n : nat => n < 4) 2 a0));
 simpl in |- *; auto.
intro Abs; absurd (3 = 4); auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
Qed.
  



Lemma d_In_SUC1_l4 :
 forall l : d_list bool 4,
 d_In (no_in (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4)))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Thd_of_l4 l = true.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4))) with 2.
intros l H.
apply d_In_SUC1_l3.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))))
 with 2.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *.
intro a; elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
unfold SUC_MODN in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *;
 auto.
intros Abs; absurd (2 = 4); auto.
Qed.


Lemma not_d_In_SUC1_l4 :
 forall l : d_list bool 4,
 ~
 d_In (no_in (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4)))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Thd_of_l4 l = false.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4))) with 2.
intros l H.
apply not_d_In_SUC1_l3.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))))
 with 2.
auto.
unfold SUC_MODN in |- *; simpl in |- *.

elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *.
intro a; elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
unfold SUC_MODN in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *;
 auto.
intros Abs; absurd (2 = 4); auto.
Qed.




Lemma d_In_SUCSUC1_l4 :
 forall l : d_list bool 4,
 d_In (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Fth_of_l4 l = true.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4))))
 with 3.
intros l H.
apply d_In_SUC2_l4.
replace
 (no_in
    (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4)))))
 with 3.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *.
intro a; elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
intro a0; elim (less_or_eq (exist (fun n : nat => n < 4) 2 a0));
 simpl in |- *; auto.
intros Abs; absurd (3 = 4); auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
unfold SUC_MODN in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *;
 auto.
intro a; elim (less_or_eq (exist (fun n : nat => n < 4) 2 a)); simpl in |- *.
auto.
intros Abs; absurd (3 = 4); auto.
intros Abs; absurd (2 = 4); auto.
Qed.



Lemma not_d_In_SUCSUC1_l4 :
 forall l : d_list bool 4,
 ~
 d_In (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Fth_of_l4 l = false.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4))))
 with 3.
intros l H.
apply not_d_In_SUC2_l4.
replace
 (no_in
    (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4)))))
 with 3.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *.

intro a; elim (less_or_eq (exist (fun n : nat => n < 4) 1 a)); simpl in |- *.
intro a0; elim (less_or_eq (exist (fun n : nat => n < 4) 2 a0));
 simpl in |- *; auto.
intros Abs; absurd (3 = 4); auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
unfold SUC_MODN in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *;
 auto.
intro a; elim (less_or_eq (exist (fun n : nat => n < 4) 2 a)); simpl in |- *.
auto.
intros Abs; absurd (3 = 4); auto.
intros Abs; absurd (2 = 4); auto.
Qed.



Lemma d_In_SUC_SSO_l4 :
 forall l : d_list bool 4,
 d_In (no_in (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4)))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Fth_of_l4 l = true.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4))) with 3.
intros l H.
apply d_In_SUCSUC1_l4.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4))))
 with 3.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 2 y)); simpl in |- *;
 auto.
intros Abs; absurd (3 = 4); auto.
intros Abs; absurd (2 = 4); auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); simpl in |- *;
 auto.
intros Abs; absurd (3 = 4); auto.
Qed.



Lemma not_d_In_SUC_SSO_l4 :
 forall l : d_list bool 4,
 ~
 d_In (no_in (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4)))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Fth_of_l4 l = false.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4))) with 3.
intros l H.
apply not_d_In_SUCSUC1_l4.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4))))
 with 3.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 2 y)); simpl in |- *;
 auto.
intros Abs; absurd (3 = 4); auto.
intros Abs; absurd (2 = 4); auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); simpl in |- *;
 auto.
intros Abs; absurd (3 = 4); auto.
Qed.



Lemma d_In_SUCSUC_SSO_l4 :
 forall l : d_list bool 4,
 d_In (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Fst_of_l4 l = true.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4))))
 with 0.
intros l.
elim (non_empty l).
intros x0 X0; elim X0; clear X0.
intros X0 H.
elim (non_empty X0).
intros x1 X1; elim X1; clear X1.
intros X1 H1.
elim (non_empty X1).
intros x2 X2; elim X2; clear X2.
intros X2 H2.
elim (non_empty X2).
intros x3 X3; elim X3; clear X3.
intros X3 H3.
rewrite H; rewrite H1; rewrite H2; rewrite H3.
unfold Fst_of_l4 in |- *; simpl in |- *.
unfold RequestsToArbitrate in |- *.
unfold Fst_of_l4 in |- *; unfold Scd_of_l4 in |- *; unfold Thd_of_l4 in |- *;
 unfold Fth_of_l4 in |- *; simpl in |- *.
elim x0; simpl in |- *; auto.
elim x1; elim x2; elim x3; simpl in |- *.
intros H'.
elim H'; clear H'.
intros Abs.
absurd (1 = 0); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (2 = 0); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 0); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (1 = 0); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (2 = 0); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (1 = 0); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 0); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (1 = 0); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (2 = 0); auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (3 = 0); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intros Abs; absurd (2 = 0); auto.
intros Abs; absurd False; auto.
intros H'; elim H'; clear H'.
intro Abs; absurd (3 = 0); auto.
intros Abs; absurd False; auto.
intros Abs; absurd False; auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 3 y)); simpl in |- *;
 auto.
intro Abs; absurd (4 < 4); auto with arith.
intro Abs; absurd (3 = 4); auto.
Qed.



Lemma not_d_In_SUCSUC_SSO_l4 :
 forall l : d_list bool 4,
 ~
 d_In (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Fst_of_l4 l = false.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4))))
 with 0.
intro l.
elim (non_empty l).
intros x0 X0; elim X0; clear X0.
intros X0 H.
elim (non_empty X0).
intros x1 X1; elim X1; clear X1.
intros X1 H1.
elim (non_empty X1).
intros x2 X2; elim X2; clear X2.
intros X2 H2.
elim (non_empty X2).
intros x3 X3; elim X3; clear X3.
intros X3 H3.
rewrite H; rewrite H1; rewrite H2; rewrite H3.
unfold Fst_of_l4 in |- *; simpl in |- *.
unfold RequestsToArbitrate in |- *.
unfold Fst_of_l4 in |- *; unfold Scd_of_l4 in |- *; unfold Thd_of_l4 in |- *;
 unfold Fth_of_l4 in |- *; simpl in |- *.
elim x0; simpl in |- *; auto.
elim x1; elim x2; elim x3; simpl in |- *.
intro H'.
elim H'; clear H'.
auto.
intros H'; elim H'; clear H'.
auto.
intros H'; elim H'; clear H'.
auto.
intros H'; elim H'; clear H'.
auto.
intros H'; elim H'; clear H'.
auto.
intros H'; elim H'; clear H'.
auto.
intros H'; elim H'; clear H'.
auto.
intros H'; elim H'; clear H'.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 3 y)); simpl in |- *;
 auto. 
intro Abs; absurd (4 < 4); auto with arith.
intro Abs; absurd (3 = 4); auto.
Qed.



Lemma d_In_SUCSUCSUC_SSO_l4 :
 forall l : d_list bool 4,
 d_In
   (no_in
      (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4)))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Scd_of_l4 l = true.
replace
 (no_in
    (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4)))))
 with 1.
intros l H.
apply d_In_SUC0_l2.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))) with 1.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *;
 auto.
intros Abs; absurd (1 = 4); auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 3 y)); simpl in |- *;
 auto.
intro Abs; absurd (4 < 4); auto with arith.
intro y'; elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y')));
 simpl in |- *; auto.
intro Abs; absurd (1 = 4); auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y)));
 simpl in |- *; auto.
absurd (3 = 4); auto.
absurd (3 = 4); auto.
Qed.



Lemma not_d_In_SUCSUCSUC_SSO_l4 :
 forall l : d_list bool 4,
 ~
 d_In
   (no_in
      (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4)))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Scd_of_l4 l = false.
replace
 (no_in
    (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4)))))
 with 1.
intros l H.
apply not_d_In_SUC0_l2.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 0 lt_O_4))) with 1.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 0 lt_O_4)); simpl in |- *;
 auto.
intros Abs; absurd (1 = 4); auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 3 y)); simpl in |- *;
 auto.
intros Abs; absurd (4 < 4); auto with arith.
intro y'; elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y')));
 simpl in |- *; auto.
intro Abs; absurd (1 = 4); auto with arith.
intro Abs; absurd (3 = 4); auto with arith.
Qed.



Lemma d_In_SUC_SSSO_l4 :
 forall l : d_list bool 4,
 d_In (no_in (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4)))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Fst_of_l4 l = true.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4))) with 0.
intros l H.
apply d_In_SUCSUC_SSO_l4.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4))))
 with 0.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 3 y)); simpl in |- *;
 auto.
intro Abs; absurd (4 < 4); auto with arith.
intro Abs; absurd (3 = 4); auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 3 lt_3_4)); simpl in |- *;
 auto.
intros Abs; absurd (4 < 4); auto with arith.
Qed.


Lemma not_d_In_SUC_SSSO_l4 :
 forall l : d_list bool 4,
 ~
 d_In (no_in (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4)))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Fst_of_l4 l = false.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4))) with 0.
intros l H.
apply not_d_In_SUCSUC_SSO_l4.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4))))
 with 0.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 3 y)); simpl in |- *;
 auto.
intros Abs; absurd (4 < 4); auto with arith.
intros Abs; absurd (3 = 4); auto with arith.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 3 lt_3_4)); simpl in |- *;
 auto.
intros Abs; absurd (4 < 4); auto with arith.
Qed.



Lemma d_In_SUCSUC_SSSO_l4 :
 forall l : d_list bool 4,
 d_In (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Scd_of_l4 l = true.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4))))
 with 1.
intros l H.
apply d_In_SUCSUCSUC_SSO_l4.
replace
 (no_in
    (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4)))))
 with 1.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 3 y)); simpl in |- *;
 auto.
intros Abs; absurd (4 < 4); auto with arith.
intro y'; elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y')));
 simpl in |- *; auto.
intros Abs; absurd (1 = 4); auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y)));
 simpl in |- *; auto.
absurd (3 = 4); auto.
absurd (3 = 4); auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 3 lt_3_4)); simpl in |- *;
 auto.
intros Abs; absurd (4 < 4); auto with arith.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y)));
 simpl in |- *; auto.
intro Abs; absurd (1 = 4); auto.
Qed.


  
Lemma not_d_In_SUCSUC_SSSO_l4 :
 forall l : d_list bool 4,
 ~
 d_In (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Scd_of_l4 l = false.
replace (no_in (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4))))
 with 1.
intros l H.
apply not_d_In_SUCSUCSUC_SSO_l4.
replace
 (no_in
    (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 2 lt_2_4)))))
 with 1.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 2 lt_2_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 3 y)); simpl in |- *;
 auto.
intro Abs; absurd (4 < 4); auto with arith.
intro y'; elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y')));
 simpl in |- *; auto.
intro Abs; absurd (1 = 4); auto.
intro Abs; absurd (3 = 4); auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 3 lt_3_4)); simpl in |- *;
 auto.
intros Abs; absurd (4 < 4); auto with arith.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y)));
 simpl in |- *; auto.
intro Abs; absurd (1 = 4); auto.
Qed.



Lemma d_In_SUCSUCSUC_SO_l4 :
 forall l : d_list bool 4,
 d_In
   (no_in
      (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4)))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Fst_of_l4 l = true.
replace
 (no_in
    (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4)))))
 with 0.
intros l H.
apply d_In_SUC_SSSO_l4.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4))) with 0.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 3 lt_3_4)); simpl in |- *;
 auto.
intros Abs; absurd (4 < 4); auto with arith.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 2 y)); simpl in |- *;
 auto.
intro y'; elim (less_or_eq (exist (fun n : nat => n < 4) 3 y'));
 simpl in |- *; auto.
intros Abs; absurd (4 < 4); auto with arith.
intro Abs; absurd (3 = 4); auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y)));
 simpl in |- *; auto.
absurd (2 = 4); auto.
absurd (2 = 4); auto.
Qed.


Lemma not_d_In_SUCSUCSUC_SO_l4 :
 forall l : d_list bool 4,
 ~
 d_In
   (no_in
      (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4)))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Fst_of_l4 l = false.
replace
 (no_in
    (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4)))))
 with 0.
intros l H.
apply not_d_In_SUC_SSSO_l4.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4))) with 0.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 3 lt_3_4)); simpl in |- *;
 auto.
intros Abs; absurd (4 < 4); auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 2 y)); simpl in |- *;
 auto.
intro y'; elim (less_or_eq (exist (fun n : nat => n < 4) 3 y'));
 simpl in |- *; auto.
absurd (4 < 4); auto with arith.
absurd (4 < 4); auto with arith.
absurd (4 < 4); auto with arith.
absurd (4 < 4); auto with arith.
unfold SUC_MODN in |- *.
simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *;
 auto.
intro a; elim (less_or_eq (exist (fun n : nat => n < 4) 2 a)); simpl in |- *;
 auto.
intro a0; elim (less_or_eq (exist (fun n : nat => n < 4) 3 a0));
 simpl in |- *; auto.
intros Abs; absurd (4 < 4); auto.
absurd (4 < 4); auto with arith.
intro b; elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen b)));
 simpl in |- *; auto.
absurd (3 = 4); auto with arith.
intro Abs; absurd (2 = 4); auto.
Qed.



Lemma d_In_SUCSUCSUC_SSSO_l4 :
 forall l : d_list bool 4,
 d_In
   (no_in
      (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4)))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Thd_of_l4 l = true.
replace
 (no_in
    (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4)))))
 with 2.
intros l H.
apply d_In_SUC1_l4.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4))) with 2.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *;
 auto.
intros Abs; absurd (2 = 4); auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 3 lt_3_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 4 y)); simpl in |- *;
 auto.
absurd (4 < 4); auto with arith.
absurd (4 < 4); auto with arith.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y)));
 simpl in |- *; auto.
intro y'; elim (less_or_eq (exist (fun n : nat => n < 4) 1 y'));
 simpl in |- *; auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
Qed.



Lemma not_d_In_SUCSUCSUC_SSSO_l4 :
 forall l : d_list bool 4,
 ~
 d_In
   (no_in
      (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4)))))
   (d_map (no_in (i:=4)) (list_dlist (RequestsToArbitrate l))) ->
 Thd_of_l4 l = false.
replace
 (no_in
    (SUC_MODN (SUC_MODN (SUC_MODN (exist (fun p : nat => p < 4) 3 lt_3_4)))))
 with 2.
intros l H.
apply not_d_In_SUC1_l4.
replace (no_in (SUC_MODN (exist (fun p : nat => p < 4) 1 lt_1_4))) with 2.
auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 1 lt_1_4)); simpl in |- *;
 auto.
intros Abs; absurd (2 = 4); auto.
unfold SUC_MODN in |- *; simpl in |- *.
elim (less_or_eq (exist (fun p : nat => p < 4) 3 lt_3_4)); simpl in |- *;
 auto.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 4 y)); simpl in |- *;
 auto.
absurd (4 < 4); auto with arith.
absurd (4 < 4); auto with arith.
intro y; elim (less_or_eq (exist (fun n : nat => n < 4) 0 (Ex_n_lt_gen y)));
 simpl in |- *; auto.
intro y'; elim (less_or_eq (exist (fun n : nat => n < 4) 1 y'));
 simpl in |- *; auto.
intro Abs; absurd (2 = 4); auto.
intro Abs; absurd (1 = 4); auto.
Qed.