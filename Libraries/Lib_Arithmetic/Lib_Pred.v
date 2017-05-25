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
(*                                 Lib_Pred.v                               *)
(****************************************************************************)


Require Export Lib_Eq_Le_Lt.
Require Export Lib_Prop.


Lemma pred_diff_O : forall n : nat, n <> 0 -> n <> 1 -> pred n <> 0.
simple induction n; auto with arith.
Qed.
Hint Immediate pred_diff_O.



Lemma S_pred_n : forall n : nat, 1 <= n -> S (pred n) = n.
simple induction n; auto with arith.
Qed.
Hint Immediate S_pred_n.



Lemma eq_pred : forall n m : nat, n = m -> pred n = pred m.
intros n m H.
rewrite H; auto with arith.
Qed.
Hint Immediate eq_pred.



Lemma pred_diff_lt : forall n : nat, n <> 0 -> n <> 1 -> 0 < pred n.
intros; apply neq_O_lt.
apply sym_not_equal; auto.
Qed.
Hint Immediate pred_diff_lt.



Lemma pred_n_O : forall n : nat, pred n = 0 -> n = 0 \/ n = 1.
simple induction n; auto with arith.
Qed. 
Hint Immediate pred_n_O.



Lemma pred_O : forall n : nat, n = 0 -> pred n = 0.
intros.
rewrite H; auto with arith.
Qed.
Hint Immediate pred_O.


Lemma pred_no_O : forall n : nat, pred n <> 0 -> n <> 0.
simple induction n; auto with arith.
Qed.
Hint Immediate pred_no_O.



Lemma lt_pred : forall n : nat, 0 < n -> pred n < n.
simple induction n; auto with arith.
Qed.
Hint Immediate lt_pred.



Lemma dif_0_pred_eq_0_eq_1 : forall n : nat, n <> 0 -> pred n = 0 -> n = 1.
intros n H0 H1.
cut (n = 0 \/ n = 1).
intros H_Cut.
apply no_or_r with (n = 0); try trivial.
apply pred_n_O; try trivial.
Qed.



Lemma lt_le_pred : forall n m : nat, n < m -> n <= pred m.
simple induction n; simple induction m; auto with arith.
Qed.
Hint Immediate lt_le_pred.

