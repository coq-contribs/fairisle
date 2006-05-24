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
(*                              Arith_Compl.v                               *)
(****************************************************************************)


Require Import Arith.
Require Import Lib_Minus.

Set Implicit Arguments.
Unset Strict Implicit.


Lemma Ex_n_lt_gen : forall n m : nat, S m = n -> 0 < n.
intros n m H; elim H; auto with arith.
Qed.

Lemma lt_S_le : forall n m : nat, S n <= m -> n < m.
auto with arith.
Qed.

Lemma lt_eq_lt : forall p q n : nat, p < n -> q = n -> p < q.
intros p q n H1 H2.
rewrite H2; try trivial.
Qed.

Lemma le_minusS : forall n m : nat, 0 < n -> n <= m -> S (m - n) <= m.
intros n m H1 H2.
apply lt_n_Sm_le.
auto with arith.
Qed.

Lemma le_le_Sminus : forall n m k : nat, m <= k -> S (m - n) <= S (k - n).
auto with arith.
Qed.

Lemma le_leS : forall n m : nat, n <= m -> n <= S m.
auto with arith.
Qed.

Lemma le_S_lt_O : forall n m : nat, S m <= n -> 0 < n.
intros n m H.
apply lt_le_trans with (S m); auto with arith.
Qed.


Lemma lt_le_pred : forall n m : nat, n < m -> n <= pred m.
simple induction n; simple induction m; auto with arith.
Qed.
Hint Immediate lt_le_pred.


Lemma le_Sn_le_n_pred : forall n m : nat, S n <= m -> n <= pred m.
auto with arith.
Qed.


Lemma le_mult_l : forall n m : nat, 0 < m -> n <= m * n.
intros.
rewrite (S_pred m 0); trivial.
simpl in |- *; auto with arith.
Qed.
Hint Immediate le_mult_l.


Lemma le_n_mult_S_n : forall n m : nat, n <= S m * n.
auto with arith.
Qed.


Lemma S_pred : forall n : nat, n <> 0 -> S (pred n) = n.
simple destruct n; simpl in |- *; trivial.
intro H; absurd (0 = 0); trivial.
Qed.


Lemma le_minusSS :
 forall n m k : nat, 0 < n -> m <= k -> n <= m -> S (k - n) <= k.
intros n m k H1 H2 H3.
apply lt_n_Sm_le.
apply lt_n_S.
apply lt_minus.
apply le_trans with m; auto with arith.
try trivial.
Qed.

