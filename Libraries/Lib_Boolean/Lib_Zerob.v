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
(*                               Lib_Zerob.v                                *)
(****************************************************************************)

Require Export Lt.
Require Export Lib_Prop.
Require Export Lib_Set_Products.
Require Export Lib_Bool.


Lemma zerob_If :
 forall (b : bool) (x y : nat),
 zerob (if_bool (C:=nat) b x y) = true -> x <> 0 -> b = false.
simple induction b; simpl in |- *; intros; auto.
absurd (x <> 0).
apply no_no_A; apply zerob_true_elim; auto.
try trivial.
Qed.


Lemma lt_no_zerob : forall n : nat, 0 < n -> zerob n <> true.
simple induction n; auto. 
intros; elim (lt_irrefl 0); auto.
Qed.
Hint Immediate lt_no_zerob.


Lemma zerob_pred_no : forall n : nat, zerob (pred n) = false -> n <> 0.
simple induction n; auto.
simpl in |- *.
intro.
absurd (true = false); auto.
apply diff_true_false.
Qed.
Hint Immediate zerob_pred_no.


Lemma zerob_lt : forall n : nat, zerob n = false -> 0 < n.
simple induction n.
simpl in |- *; intro.
absurd (true = false); auto.
apply diff_true_false.
intros.
apply lt_O_Sn.
Qed.
Hint Immediate zerob_lt.


Lemma no_zerob_true : forall n : nat, n <> 0 -> zerob n <> true.
simple induction n; auto.
Qed.
Hint Immediate no_zerob_true.


Lemma x_1_or_y_0 :
 forall x y : nat,
 zerob (pred x) || zerob y = true -> x <> 0 -> x = 1 \/ y = 0.
simple induction x; simple induction y.
intros; right; try trivial.
intros.
absurd (0 <> 0); auto.
right; auto.
simpl in |- *.
elim orb_sym; simpl in |- *; intros.
left; replace n with 0.
try trivial.
apply sym_equal; apply zerob_true_elim; try trivial.
Qed.


Lemma zerob_pred_false :
 forall n : nat, zerob (pred n) = false -> zerob n = false.
simple induction n; auto.
Qed.
Hint Immediate zerob_pred_false.


