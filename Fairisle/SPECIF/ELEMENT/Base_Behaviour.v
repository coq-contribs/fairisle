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
(*                             Base_Behaviour.v                             *)
(****************************************************************************)

Require Export Gates_Del.
Require Export dlist_Compl.

Set Implicit Arguments.
Unset Strict Implicit.


Definition Wire (n : nat) (s : d_list bool n) := s.

Definition In_Buf := Wire.
Definition Out_Buf := Wire.

Definition Ilatch (n : nat) := Reg (A:=d_list bool n).
Definition Olatch (n : nat) := Reg (A:=d_list bool n).
Definition Latch (n : nat) := Reg (A:=d_list bool n).
Definition In_latch (m n : nat) := Reg (A:=d_list (d_list bool m) n).
Definition Out_latch (m n : nat) := Reg (A:=d_list (d_list bool m) n).
Definition Pause (m n : nat) := Reg (A:=d_list (d_list bool m) n).

Definition rlatch (n : nat) (disable : bool) (inp : d_list bool n) :=
  match disable with
  | true => make_list_of_v n false
  | _ => inp
  end.

Definition Rlatch (n : nat) (disable : Stream bool)
  (inp : Stream (d_list bool n)) (old : d_list bool n) :=
  Freg2 (rlatch (n:=n)) disable inp old.


 