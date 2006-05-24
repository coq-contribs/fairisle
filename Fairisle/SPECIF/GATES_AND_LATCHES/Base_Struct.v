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
(*                              Base_Struct.v                               *)
(****************************************************************************)
 
Require Export Gates_Del.
Require Export dlist_Compl.
Require Import Syntactic_Def.

Set Implicit Arguments.
Unset Strict Implicit.


Definition IN_BUF := d_map IBUF.
Definition OUT_BUF := d_map OBUF.

Definition ILATCH := d_map2 INFFd.
Definition IN_LATCH (n : nat) := d_map2 (ILATCH (n:=n)).
Definition OLATCH := d_map2 OUTFFd.
Definition OUT_LATCH (n : nat) := d_map2 (OLATCH (n:=n)).
Definition LATCH := d_map2 DFFd.
Definition PAUSE (n : nat) := d_map2 (LATCH (n:=n)).

Definition Ackor (n : nat) := Fold_with_f_S (n:=n) OR2.

Definition NORL (n : nat) (H : 0 < n) := Fold_with_f (n:=n) NOR2 H.
Definition NORL3 := NORL (n:=3) lt_O_3.

Definition ANDL (n : nat) (H : 0 < n) := Fold_with_f (n:=n) AND2 H.
Definition ANDL4 := ANDL (n:=4) lt_O_4.
Definition ANDL3 := ANDL (n:=3) lt_O_3.

Definition AO (a b c d : bool) := a && b || c && d. 

Definition RLATCH (rd : Stream bool) := d_map2 (DFFRD rd).
