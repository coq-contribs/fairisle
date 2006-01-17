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
(*                                NextPort.v                                *)
(****************************************************************************)


Require Export PortsCompl.
Require Import Arith_Compl.

Set Implicit Arguments.
Unset Strict Implicit.

Section Successor_Modulo_NbPorts.

  Variable i : nat. (* Number of input ports *)
  Let Inportno := T_Inportno i.
  Let no : Inportno -> nat := no_in (i:=i).
  Notation C_Inp := (exist (fun n : nat => n < i)) (only parsing).


 (** Returns the next successful input port according to the last successful one **)
 (** and according to the number of input ports                                  **)

 Definition SUC_MODN (last : Inportno) : Inportno :=
   match less_or_eq last with
   | left p => (* [p:(lt (S (no last)) i)] *)
       exist (fun n : nat => n < i) (S (no last)) p
   | right p => (* [p:(S (no last))=i] *) 
       exist (fun n : nat => n < i) 0 (Ex_n_lt_gen (n:=i) (m:=no last) p)
   end.


End Successor_Modulo_NbPorts.