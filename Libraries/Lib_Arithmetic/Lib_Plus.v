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
(*                               Lib_Plus.v                                 *)
(****************************************************************************)

Require Export Lib_Minus.


Lemma plus_opp : forall n m : nat, n + m - m = n.
intros n m; elim (plus_comm m n); apply minus_plus.
Qed.
Hint Immediate plus_opp.


Lemma S_plus : forall n : nat, S n = n + 1.
intro; elim plus_comm; auto with arith.
Qed.
Hint Immediate S_plus.


Lemma lt_plus : forall n m : nat, 0 < n -> m < n + m.
simple induction n; simple induction m; auto with arith.
intros.
simpl in |- *; apply lt_n_S.
elim plus_comm; simpl in |- *.
elim plus_comm; apply H0; auto with arith.
Qed.
Hint Immediate lt_plus.


Lemma le_minus_plus : forall n m : nat, n - m <= n + m.
simple induction n; auto with arith.
Qed.
Hint Immediate le_minus_plus.


Lemma le_le_assoc_plus_minus :
 forall n m p : nat, n <= m -> n <= p -> m - n + p = m + (p - n).
intros.
elim H.
elim minus_n_n; simpl in |- *; elim le_plus_minus; auto with arith.
intros.
elim minus_Sn_m; simpl in |- *.
apply eq_S; auto with arith.
assumption.
Qed.
Hint Immediate le_le_assoc_plus_minus.


Lemma le_lt_plus : forall n m p q : nat, n <= p -> m < q -> n + m < p + q.
intros.
apply lt_le_trans with (n + q).
apply plus_lt_compat_l; try trivial.
apply plus_le_compat_r; try trivial.
Qed.


Lemma plus_eq_zero : forall a b : nat, a + b = 0 -> a = 0 /\ b = 0.
intros a b H.
split; apply sym_equal; apply le_n_O_eq; elim H; auto with arith.
Qed.
Hint Immediate plus_eq_zero.


Lemma le_transp_l : forall n m p : nat, n + m <= p -> m <= p - n.
simple induction n; intros.
simpl in H; elim minus_n_O; assumption.
elim H0.
elim plus_comm; rewrite plus_opp; auto with arith.
intros.
simpl in |- *; apply H; auto with arith.
Qed.
Hint Immediate le_transp_l.


Lemma le_transp_r : forall n m p : nat, n + m <= p -> n <= p - m.
intros.
apply le_transp_l.
elim plus_comm; assumption.
Qed.
Hint Immediate le_transp_r.