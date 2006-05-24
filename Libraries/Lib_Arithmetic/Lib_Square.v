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
(*                               Lib_Square.v                               *)
(****************************************************************************)

Require Export Lib_Exp.

Definition Square (n : nat) := n * n.

Lemma Square_exp_2 : forall n : nat, Square (exp_2 n) = exp_2 (2 * n).
intro.
unfold Square in |- *.
elim exp_2_n_plus_m.
rewrite plus_mult; reflexivity.
Qed.
Hint Immediate Square_exp_2.



Lemma eq_Square_exp_n : forall n : nat, Square n = exp_n n 2.
unfold Square in |- *.
simpl in |- *.
intro; elim (mult_comm 1 n); simpl in |- *; auto with arith.
Qed.
Hint Immediate eq_Square_exp_n.



Lemma Square_inc : forall n m : nat, n <= m -> Square n <= Square m.
intros.
unfold Square in |- *.
apply le_mult_csts; assumption.
Qed.
Hint Immediate Square_inc.



Lemma Square_strict_inc : forall n m : nat, n < m -> Square n < Square m.
intros.
unfold Square in |- *.
apply lt_mult_csts; assumption.
Qed.
Hint Immediate Square_strict_inc.



Lemma le_n_Square : forall n : nat, n <= Square n.
simple induction n; auto.
intros.
unfold Square in |- *.
simpl in |- *.
apply le_n_S.
elim mult_comm; simpl in |- *.
change (n0 <= n0 + (n0 + Square n0)) in |- *.
apply le_plus_l.
Qed.
Hint Immediate le_n_Square.
