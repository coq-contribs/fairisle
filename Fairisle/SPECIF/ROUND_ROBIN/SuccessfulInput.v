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
(*                             SuccessfulInput.v                            *)
(****************************************************************************)

Require Export TypePorts.
Require Export Conversions.
Require Export Arith_Compl.
Require Export Bool.
Require Export RoundRobin.
Require Export PolyList_dlist.

Set Implicit Arguments.
Unset Strict Implicit.

Section Arbitration_between_several_inputs.

  Let Inportno := T_Inportno 4.

  Notation Exist := (exist (A:=_)) (only parsing).

  Variable requests : d_list bool 4.

  (** Constructs the list of input port numbers that must be arbitrated    **)
  (** If a boolean is equal to true at a given position then this position **)
  (** will be in the returned list                                         **)


  Definition test_port (b : bool) (n : Inportno) :=
    match b with
    | true => n :: nil
    | false => nil (A:=Inportno)
    end.


  Definition RequestsToArbitrate :=
    test_port (Fst_of_l4 requests) (exist (fun p : nat => p < 4) 0 lt_O_4) ++
    test_port (Scd_of_l4 requests) (exist (fun p : nat => p < 4) 1 lt_1_4) ++
    test_port (Thd_of_l4 requests) (exist (fun p : nat => p < 4) 2 lt_2_4) ++
    test_port (Fth_of_l4 requests) (exist (fun p : nat => p < 4) 3 lt_3_4).



 (** Chooses on a Round Robin basis the successful input port if any **)

  Definition SuccessfulInput (last : Inportno) :=
    RoundRobinArbiter (list_dlist RequestsToArbitrate) last. 



End Arbitration_between_several_inputs.


 