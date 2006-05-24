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
(*                            Manip_BoolLists.v                             *)
(****************************************************************************)
 

Require Export Dependent_lists.
Require Import Fixed_dLists.
Require Import Lib_Bool.


Set Implicit Arguments.
Unset Strict Implicit.

Fixpoint Exists1_atleast (P : bool -> Prop) (n : nat) 
 (l : d_list bool n) {struct l} : bool :=
  match l with
  | d_nil => false
  | d_cons _ a l' =>
      match a with
      | true => true
      | false => Exists1_atleast P l'
      end
  end.


Lemma Exists1_atleast_or_not :
 forall (P : bool -> Prop) (n : nat) (l : d_list bool n),
 {Exists1_atleast P l = true} + {Exists1_atleast P l = false}.
auto.
Qed.


Definition l4_ffff := List4 false false false false.
Definition l4_fftt := List4 false false true true.
Definition l4_ftft := List4 false true false true.
Definition l4_fttt := List4 false true true true.
Definition l4_tftf := List4 true false true false.
Definition l4_tftt := List4 true false true true.
Definition l4_ttff := List4 true true false false.
Definition l4_ttft := List4 true true false true.
Definition l4_tttf := List4 true true true false.
Definition l4_fttf := List4 false true true false.
Definition l4_tfft := List4 true false false true.
Definition l4_tttt := List4 true true true true.
Definition l4_ffft := List4 false false false true.
Definition l4_tfff := List4 true false false false.
Definition l4_fftf := List4 false false true false.
Definition l4_ftff := List4 false true false false.

Definition l2_ff := List2 false false.
Definition l2_ft := List2 false true.
Definition l2_tf := List2 true false.
Definition l2_tt := List2 true true.



Lemma List2Bool_dec :
 forall l : d_list bool 2,
 {l = l2_ff} + {l = l2_ft} + {l = l2_tf} + {l = l2_tt}.
intro l.
elim (non_empty l).
intros x1 H1; elim H1; clear H1; intro X; elim x1.
elim (non_empty X).
intros x2 H2; elim H2; clear H2; intro X2; elim x2.
replace X2 with (d_nil bool); auto.
intro HX; rewrite HX; intro H; rewrite H; auto.
replace X2 with (d_nil bool); auto.
intro HX; rewrite HX; intros H; rewrite H.
left; right; auto.
elim (non_empty X).
intros x2 H2; elim H2; clear H2; intro X2; elim x2.
replace X2 with (d_nil bool); auto.
intro HX; rewrite HX; intro H; rewrite H; auto.
replace X2 with (d_nil bool); auto.
intro HX; rewrite HX; intros H; rewrite H.
left; auto.
Qed.
