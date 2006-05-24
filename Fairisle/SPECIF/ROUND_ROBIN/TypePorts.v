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
(*                              TypePorts.v                                 *)
(****************************************************************************)
 

(* An input port number is a natural number less than the number of inputs   *)
(* An output port number is a natural number less than the number of outputs *)

Set Implicit Arguments.
Unset Strict Implicit.

Section Ports.

  Variable i o : nat. (* inputs and outputs numbers *)

  Definition T_Inportno := {x : nat | x < i}.
  Definition T_Outportno := {x : nat | x < o}.
 
End Ports.