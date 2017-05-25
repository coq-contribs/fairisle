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
(*                               RoundRobin.v                               *)
(****************************************************************************)


Require Export NextPort.

Set Implicit Arguments.
Unset Strict Implicit.

Section Round_Robin_function.

  Variable i o : nat. (* Number of inputs and outputs *)
  Let Inportno := T_Inportno i.
  Let Outportno := T_Outportno o.

  Variable k : nat. (* Length of the list containing the input ports to arbitrate *)

  (** Round robin function **)

 Fixpoint RoundRobin (n : nat) (requests_set : d_list Inportno k)
  (last : Inportno) {struct n} : Inportno :=
   match n with
   | O => last
   | S p =>
       match
         In_or_not eq_nat_dec (no_in (SUC_MODN last))
           (d_map (no_in (i:=i)) requests_set)
       with
       | left _ => SUC_MODN last
       | right _ => RoundRobin p requests_set (SUC_MODN last)
       end
   end.


 (** Arbitration on a Round Robin basis **)

  Definition RoundRobinArbiter (requests_set : d_list Inportno k)
    (last : Inportno) :=
    match requests_set with
    | d_nil => last
    | d_cons p _ _ => RoundRobin i requests_set last
    end.

End Round_Robin_function.