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
(*                                  Gates.v                                 *)
(****************************************************************************)
 

Require Export Bool.

Definition Xor (a b : bool) := match a with
                               | true => negb b
                               | _ => b
                               end. 

Definition Xnor (a b : bool) := negb (Xor a b).

  (* Delayless wire - no effect *)
Definition Wire_bool (s : bool) := s.

 
Definition INV := negb.

Definition AND2 := andb.
Definition AND3 (a b c : bool) := AND2 a (AND2 b c).
Definition AND4 (a b c d : bool) := AND2 a (AND2 b (AND2 c d)).

Definition NAND2 (a b : bool) := INV (AND2 a b).
Definition NAND3 (a b c : bool) := INV (AND3 a b c).
Definition NAND4 (a b c d : bool) := INV (AND4 a b c d).

Definition OR2 := orb.
Definition OR3 (a b c : bool) := OR2 a (OR2 b c).
Definition OR4 (a b c d : bool) := OR2 a (OR2 b (OR2 c d)).

Definition NOR2 (a b : bool) := INV (OR2 a b).
Definition NOR3 (a b c : bool) := INV (OR3 a b c).
Definition NOR4 (a b c d : bool) := INV (OR4 a b c d).

Definition XOR2 := Xor.
Definition XOR3 (a b c : bool) := XOR2 a (XOR2 b c).
Definition XOR4 (a b c d : bool) := XOR2 a (XOR2 b (XOR2 c d)).

Definition NXOR2 (a b : bool) := INV (XOR2 a b).
Definition NXOR3 (a b c : bool) := INV (XOR3 a b c).
Definition NXOR4 (a b c d : bool) := INV (XOR4 a b c d).

Definition DFFrd (reset b : bool) :=
  match reset with
  | true => false
  | _ => b
  end.

       

Definition IBUF := Wire_bool.
Definition OBUF := Wire_bool.

Definition Jk (j k old : bool) :=
  match old with
  | true => negb k
  | _ => j
  end.

Definition JkE (j k old enable : bool) :=
  match enable with
  | true => Jk j k old
  | _ => old
  end.
