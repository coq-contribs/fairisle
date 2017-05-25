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
(*                       Derived_composition_rules.v                        *)
(****************************************************************************)
 
 
Require Export Basic_composition_rules.
Require Import Fixed_dLists.

Set Implicit Arguments.
Unset Strict Implicit.


(** Particular case of the PC rule : parallel composition of the same **)
(** Mealy automaton **)


Section Particular_Parallel_Composition.

  Variable
    Input_type_1 Input_type Output_type_1 Output_type State_type_1 : Set.

 (** Description of the automata to duplicate **)

  Variable Trans1 : Input_type_1 -> State_type_1 -> State_type_1.
  Variable Out1 : Input_type_1 -> State_type_1 -> Output_type_1.

  Let S1 := Mealy Trans1 Out1.
  Let S1' := Mealy Trans1 Out1.


  (** f will be used to dispath the input vector **)
  Variable f : Input_type -> Input_type_1 * Input_type_1.


  (** output will be used to construct the output of the parallel composition **)
  Variable output_part : d_list Output_type_1 2 -> Output_type.


 (** Explicit construction of the parallel composition *)

  Notation S1S1 :=
    (fun (i : Stream Input_type) (s1 s1' : State_type_1) =>
     S_map output_part
       (dlist_to_Stream
          (List2 (S1 (S_map fstS (S_map f i)) s1)
             (S1 (S_map sndS (S_map f i)) s1')))) 
    (only parsing).


 
 (** Description of the parallel composition PC of two Mealy automata S1 **)

  Definition Trans_PC_part (i : Input_type) (s : State_type_1 * State_type_1)
    : State_type_1 * State_type_1 := Trans_PC Trans1 Trans1 f i s.


  Definition Out_PC_part (i : Input_type) (s : State_type_1 * State_type_1) :
    Output_type :=
    let (s1, s1') := s in
    output_part (List2 (Out1 (fst (f i)) s1) (Out1 (snd (f i)) s1')).



  Definition PC_part :
    Stream Input_type -> State_type_1 * State_type_1 -> Stream Output_type :=
    Mealy Trans_PC_part Out_PC_part.


  Definition States_PC_part :
    Stream Input_type ->
    State_type_1 * State_type_1 -> Stream (State_type_1 * State_type_1) :=
    States_Mealy Trans_PC_part.


  (** Equivalence between S1S1 and PC_part **)

  Lemma Equiv_S1S1_PC_part :
   forall (i : Stream Input_type) (s1 s1' : State_type_1),
   EqS
     ((fun (i : Stream Input_type) (s1 s1' : State_type_1) =>
       S_map output_part
         (dlist_to_Stream
            (List2 (S1 (S_map fstS (S_map f i)) s1)
               (S1 (S_map sndS (S_map f i)) s1')))) i s1 s1')
     (PC_part i (s1, s1')).
  cofix.
  intros i s1 s1'.
  apply eqS.
  simpl in |- *; auto.
  rewrite S_tail_S_map; rewrite S_tail_dlist_to_Stream; rewrite tls_simpl.
  unfold S1 in |- *; unfold S1 in Equiv_S1S1_PC_part.
  rewrite S_tail_Mealy; rewrite S_tail_S_map; rewrite S_tail_S_map;
   rewrite S_tail_Mealy; rewrite S_tail_S_map; rewrite S_tail_S_map.
  unfold PC_part in |- *; unfold PC_part in Equiv_S1S1_PC_part.
  rewrite S_tail_Mealy.
  unfold Trans_PC_part in |- *; unfold Trans_PC_part in Equiv_S1S1_PC_part;
   unfold Trans_PC in |- *; auto.
  Qed.

End Particular_Parallel_Composition.
