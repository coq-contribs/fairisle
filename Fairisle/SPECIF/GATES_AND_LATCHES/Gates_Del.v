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
(*                                Gates_Del.v                               *)
(****************************************************************************)
 

Require Export Gates.
Require Export Gen_Gates_Del.


Definition INFFd := Reg (A:=bool).
Definition OUTFFd := Reg (A:=bool).
Definition DFFd := Reg (A:=bool).

   
Definition JKFF_q (old : bool) (j k : Stream bool) := Loop2 old j k Jk.


Definition JKFF_qBar (old : bool) (j k : Stream bool) :=
  S_map negb (JKFF_q old j k).


Definition JKFFce (old_JkE : bool) (j k ce : Stream bool) :=
  Loop3_permut old_JkE j k ce JkE.


Definition DFFRD := Freg2 DFFrd.
