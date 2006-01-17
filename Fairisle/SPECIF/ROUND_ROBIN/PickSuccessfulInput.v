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
(*                           PickSuccessfulInput.v                          *)
(****************************************************************************)

Require Export SuccessfulInput.
Require Export Manip_BoolLists.

Set Implicit Arguments.
Unset Strict Implicit.

Section Filter_and_Pick.

  Let Inportno := T_Inportno 4.

  Variable actives priorities requests : d_list bool 4.

  Let d_map_andb := d_map2 andb (n:=4).
  Let eq_true (b : bool) := b = true :>bool.

 (* "and" between two bool lists *)
  Let and2 (l m : d_list bool 4) := d_map_andb l m.

 (* "and" between three bool lists *)
  Let and3 (l m n : d_list bool 4) := d_map_andb (and2 l m) n.


 (** Filters out low priority requests for an output and request signals from **)
 (** non-active inputs                                                        **)

  Definition PriorityRequests :=
    match
      Exists1_atleast_or_not eq_true (and3 actives priorities requests)
    with
    | left _ => and3 actives priorities requests
    | right _ => and2 actives requests
    end.

 
 (** Picks the successful input port **)

  Definition PickSuccessfulInput (last : Inportno) :=
    SuccessfulInput PriorityRequests last.


End Filter_and_Pick.