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
(*                             Lib_Eq_Le_Lt.v                               *)
(****************************************************************************)


Require Export Arith.
Require Export Compare.


Lemma not_S_eq : forall n m : nat, S n <> S m -> n <> m.
auto with arith.
Qed.
Hint Immediate not_S_eq.


Lemma neq_O_le : forall n : nat, n <> 0 -> 1 <= n.
simple induction n; auto with arith.
Qed.
Hint Immediate neq_O_le.


Lemma lt_O : forall m n : nat, m < n -> 0 < n.
intros m n H.
apply le_lt_trans with m; auto with arith.
Qed.
Hint Immediate lt_O.


Lemma lt_Ex_n : forall n : nat, 0 < n -> exists n0 : nat, n = S n0.
intros.
elim H.
exists 0; try trivial.
intros; exists m; try trivial.
Qed.
Hint Immediate lt_Ex_n.


Lemma lt_m_neq : forall m n : nat, m < n -> n <> m.
simple induction m.
simple induction n; auto with arith.
clear m; intros m H_rec n H.
cut (exists p : nat, n = S p).
intros G; elim G; clear G.
intros p e.
rewrite e.
apply not_eq_S.
apply H_rec.
apply lt_S_n.
elim e; try trivial.
apply lt_Ex_n.
apply lt_O with (S m); try trivial.
Qed.
Hint Immediate lt_m_neq.

