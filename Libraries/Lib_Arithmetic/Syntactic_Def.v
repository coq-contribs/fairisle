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
(*                              Syntactic_Def.v                             *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Le.

Notation one := 1 (only parsing).
Notation two := 2 (only parsing).
Notation three := 3 (only parsing).
Notation four := 4 (only parsing).
Notation five := 5 (only parsing).
Notation six := 6 (only parsing).
Notation seven := 7 (only parsing).
Notation eight := 8 (only parsing).

Require Export Lt.

Lemma lt_O_1 : 0 < 1.
auto with arith.
Qed.
Lemma lt_O_2 : 0 < 2.
auto with arith.
Qed.
Lemma lt_O_3 : 0 < 3.
auto with arith.
Qed.
Lemma lt_O_4 : 0 < 4.
auto with arith.
Qed.
Lemma lt_O_5 : 0 < 5.
auto with arith.
Qed.
Lemma lt_O_6 : 0 < 6.
auto with arith.
Qed.
Lemma lt_O_7 : 0 < 7.
auto with arith.
Qed.
Lemma lt_O_8 : 0 < 8.
auto with arith.
Qed.

Lemma lt_1_S4 : 1 < 5.
auto with arith.
Qed.
Lemma lt_2_S4 : 2 < 5.
auto with arith.
Qed.
Lemma lt_3_S4 : 3 < 5.
auto with arith.
Qed.
Lemma lt_4_S4 : 4 < 5.
auto with arith.
Qed.

Lemma lt_1_S2 : 1 < 3.
auto with arith.
Qed.
Lemma lt_2_S2 : 2 < 3.
auto with arith.
Qed.

Lemma lt_1_4 : 1 < 4.
auto with arith.
Qed.
Lemma lt_2_4 : 2 < 4.
auto with arith.
Qed.
Lemma lt_3_4 : 3 < 4.
auto with arith.
Qed.

Lemma lt_1_S3 : 1 < 4.
auto with arith.
Qed.
Lemma lt_2_S3 : 2 < 4.
auto with arith.
Qed.
Lemma lt_3_S3 : 3 < 4.
auto with arith.
Qed.
Lemma lt_7_S8 : 7 < 9.
auto with arith.
Qed.
Lemma lt_8_S8 : 8 < 9.
auto with arith.
Qed.

Lemma le_1_2 : 1 <= 2.
auto with arith.
Qed.
Lemma le_1_3 : 1 <= 3.
auto with arith.
Qed.
Lemma le_1_4 : 1 <= 4.
auto with arith.
Qed.
Lemma le_1_7 : 1 <= 7.
auto with arith.
Qed.

Lemma le_2_3 : 2 <= 3.
auto with arith.
Qed.
Lemma le_2_4 : 2 <= 4.
auto with arith.
Qed.

Lemma le_3_3 : 3 <= 3.
auto with arith.
Qed.
Lemma le_3_4 : 3 <= 4.
auto with arith.
Qed.
Lemma le_3_7 : 3 <= 7.
auto with arith.
Qed.

Lemma le_4_4 : 4 <= 4.
auto with arith.
Qed.
Lemma le_4_8 : 4 <= 8.
auto with arith.
Qed.

Lemma le_5_6 : 5 <= 6.
auto with arith.
Qed.
Lemma le_5_7 : 5 <= 7.
auto with arith.
Qed.
Lemma le_5_8 : 5 <= 8.
auto with arith.
Qed.

Lemma le_6_8 : 6 <= 8.
auto with arith.
Qed.

Lemma le_7_7 : 7 <= 7.
auto with arith.
Qed.
Lemma le_7_8 : 7 <= 8.
auto with arith.
Qed.


Lemma le_8_8 : 8 <= 8.
auto with arith.
Qed.

Lemma le8_lt7 : forall n : nat, 8 <= n -> 7 < S n.
auto with arith.
Qed.

Lemma le8_le6 : forall n : nat, 8 <= n -> 6 <= n.
intros.
apply le_trans with 8; auto with arith.
Qed.


Lemma not_lt_4 : forall n : nat, ~ S (S (S (S n))) < 4.
intro n.
apply le_not_lt.
repeat apply le_n_S; auto with arith.
Qed.


