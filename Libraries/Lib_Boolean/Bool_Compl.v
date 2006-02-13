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
(*                               Bool_Compl.v                               *)
(****************************************************************************)

Require Export Bool.


Set Implicit Arguments.
Unset Strict Implicit.


Lemma false_orb_l : forall b b' : bool, false = b || b' -> b = false.
simple induction b; auto.
Qed.


Lemma false_orb_r : forall b b' : bool, false = b || b' -> b' = false.
simple induction b; auto.
simpl in |- *; intros.
absurd (false = true); auto.
Qed.


Lemma andb_sym : forall b b' : bool, b && b' = b' && b.
simple induction b; simple induction b'; auto.
Qed.


Lemma orb_sym : forall b b' : bool, b || b' = b' || b.
simple induction b; simple induction b'; auto.
Qed.


Lemma false_andb_b : forall b : bool, false = b && false.
intro; elim andb_sym; auto.
Qed.


Lemma false_neg_true : forall b : bool, b = false -> b <> true.
simple induction b; auto with bool. (* copy of no_true_false *)
Qed.


Lemma false_andb_true : forall b : bool, false = b && true -> b = false.
simple induction b; auto.
Qed.


Lemma orb_b_false : forall b : bool, b || false = b.
intro; elim orb_sym; auto.
Qed.


Lemma neg_neg : forall b : bool, b = negb (negb b).
simple induction b; auto.
Qed.


Lemma neg_andb_neg_orb :
 forall b1 b2 : bool, negb (b1 && b2) = negb b1 || negb b2.
simple induction b1; auto.
Qed.


Lemma neg_orb_neg_andb :
 forall b1 b2 : bool, negb (b1 || b2) = negb b1 && negb b2.
simple induction b1; auto.
Qed.


Lemma neg_b_true_b_false : forall b : bool, negb b = true -> b = false.
simple induction b; auto.
Qed.

