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
(*                        Basic_composition_rules.v                         *)
(****************************************************************************)
 
Require Export Mealy.

Set Implicit Arguments.
Unset Strict Implicit.


(*************************************************************************)
(********************************* RULE 1 ********************************)
(*************************************************************************)

Section Parallel_Composition.

  Variable Input_type_1 Input_type_2 Input_type : Set.
  Variable Output_type_1 Output_type_2 Output_type : Set.
  Variable State_type_1 State_type_2 : Set.

 (** Description of the 2 automata to compose **)

  Variable Trans1 : Input_type_1 -> State_type_1 -> State_type_1.
  Variable Trans2 : Input_type_2 -> State_type_2 -> State_type_2.

  Variable Out1 : Input_type_1 -> State_type_1 -> Output_type_1.
  Variable Out2 : Input_type_2 -> State_type_2 -> Output_type_2.

  Let A1 := Mealy Trans1 Out1.
  Let A2 := Mealy Trans2 Out2.

  Let States_A1 := States_Mealy Trans1.
  Let States_A2 := States_Mealy Trans2.


  (** f will be used to dispath the input vector **)
  Variable f : Input_type -> Input_type_1 * Input_type_2.


  (** output will be used to construct the output of the parallel **)
  (** composition, given the outputs of A1 and A2 **)
  Variable output : Output_type_1 * Output_type_2 -> Output_type.


 (** Explicit construction of the parallel composition *)

  Notation A1A2 :=
    (fun (i : Stream Input_type) (s1 : State_type_1) (s2 : State_type_2) =>
     S_map output
       (Compact (A1 (S_map (fst (B:=_)) (S_map f i)) s1)
          (A2 (S_map (snd (B:=_)) (S_map f i)) s2))) 
    (only parsing).

 
 (** Description of the parallel composition PC of A1 and A2 **)

  Definition Trans_PC (i : Input_type) (s : State_type_1 * State_type_2) :
    State_type_1 * State_type_2 :=
    let (s1, s2) := s in (Trans1 (fst (f i)) s1, Trans2 (snd (f i)) s2).


  Definition Out_PC (i : Input_type) (s : State_type_1 * State_type_2) :
    Output_type :=
    let (s1, s2) := s in output (Out1 (fst (f i)) s1, Out2 (snd (f i)) s2).


  Definition PC :
    Stream Input_type -> State_type_1 * State_type_2 -> Stream Output_type :=
    Mealy Trans_PC Out_PC.


  Definition States_PC :
    Stream Input_type ->
    State_type_1 * State_type_2 -> Stream (State_type_1 * State_type_2) :=
    States_Mealy Trans_PC.


  (** Equivalence between A1A2 and PC **)

  Lemma Equiv_A1A2_PC :
   forall (i : Stream Input_type) (s1 : State_type_1) (s2 : State_type_2),
   EqS
     ((fun (i : Stream Input_type) (s1 : State_type_1) (s2 : State_type_2) =>
       S_map output
         (Compact (A1 (S_map fstS (S_map f i)) s1)
            (A2 (S_map sndS (S_map f i)) s2))) i s1 s2)
     (PC i (s1, s2)).
  Proof.
  cofix Equiv_A1A2_PC.
  intros i s1 s2.
  apply eqS; simpl in |- *; auto.
  Qed.


 (** Explicit construction of the parallel composition of the state streams *)

  Notation States_A1A2 :=
    (fun (i : Stream Input_type) (s1 : State_type_1) (s2 : State_type_2) =>
     Compact (States_A1 (S_map (fst (B:=_)) (S_map f i)) s1)
       (States_A2 (S_map (snd (B:=_)) (S_map f i)) s2)) 
    (only parsing).


  (** Equivalence between States_A1A2 and States_PC **)

  Lemma Equiv_States_A1A2_PC :
   forall (i : Stream Input_type) (s1 : State_type_1) (s2 : State_type_2),
   EqS
     ((fun (i : Stream Input_type) (s1 : State_type_1) (s2 : State_type_2) =>
       Compact (States_A1 (S_map fstS (S_map f i)) s1)
         (States_A2 (S_map sndS (S_map f i)) s2)) i s1 s2)
     (States_PC i (s1, s2)).
  Proof.
  cofix Equiv_States_A1A2_PC.
  intros i s1 s2.
  apply eqS; simpl in |- *; auto.
  Qed.


End Parallel_Composition.



(*************************************************************************)
(********************************* RULE 2 ********************************)
(*************************************************************************)

Section Series_Composition.

  Variable Input_type Output_type_1 Output_type_2 : Set.
  Variable State_type_1 State_type_2 : Set.

 (** Description of the 2 automata to compose **)

  Variable Trans1 : Input_type -> State_type_1 -> State_type_1.
  Variable Trans2 : Output_type_1 -> State_type_2 -> State_type_2.

  Variable Out1 : Input_type -> State_type_1 -> Output_type_1.
  Variable Out2 : Output_type_1 -> State_type_2 -> Output_type_2.

  Let A1 := Mealy Trans1 Out1.
  Let A2 := Mealy Trans2 Out2.

 (** The explicit construction of the composition consists to an application **)
 (** of A1 to A2 **)


 (** Description of the series composition SC of A1 and A2 **)

  Definition Trans_SC (i : Input_type) (s : State_type_1 * State_type_2) :
    State_type_1 * State_type_2 :=
    let (s1, s2) := s in (Trans1 i s1, Trans2 (Out1 i s1) s2).

  
  Definition Out_SC (i : Input_type) (s : State_type_1 * State_type_2) :
    Output_type_2 := let (s1, s2) := s in Out2 (Out1 i s1) s2.


  Definition SC :
    Stream Input_type -> State_type_1 * State_type_2 -> Stream Output_type_2 :=
    Mealy Trans_SC Out_SC.


  Definition States_SC :
    Stream Input_type ->
    State_type_1 * State_type_2 -> Stream (State_type_1 * State_type_2) :=
    States_Mealy Trans_SC.


 (** Equivalence between (A2(A1)) and SC **)

  Lemma Equiv_A1A2_SC :
   forall (s1 : State_type_1) (s2 : State_type_2) (i : Stream Input_type),
   EqS (A2 (A1 i s1) s2) (SC i (s1, s2)).
  Proof.
  cofix Equiv_A1A2_SC.
  intros s1 s2 i.
  apply eqS; simpl in |- *; auto.
  Qed.

End Series_Composition.



(*************************************************************************)
(********************************* RULE 3 ********************************)
(*************************************************************************)

Require Export Moore.

(** Hypothesis : A2 is a Moore machine (to have a stable solution) **)


Section Feedback_Composition.

  Variable Input_type Input_type_1 Output_type Output_type_2 : Set.
  Variable State_type_1 State_type_2 : Set.

 (** Description of the 2 automata to compose **)

  Variable Trans1 : Input_type_1 -> State_type_1 -> State_type_1.
  Variable Trans2 : Output_type -> State_type_2 -> State_type_2.

  Variable Out1 : Input_type_1 -> State_type_1 -> Output_type.
  Variable Out2 : State_type_2 -> Output_type_2.

  Let A1 := Mealy Trans1 Out1.
  Let A2 := Moore Trans2 Out2.


  (** input will be used to construct the input vector **)
  Variable input : Input_type * Output_type_2 -> Input_type_1.


  (** Explicit construction of the composition *)

  Let out (i : Input_type) (s1 : State_type_1) (s2 : State_type_2) :=
    Out1 (input (i, Out2 s2)) s1.
  
  Let upd_s1 (i : Input_type) (s1 : State_type_1) (s2 : State_type_2) :=
    Trans1 (input (i, Out2 s2)) s1.

  Let upd_s2 (i : Input_type) (s1 : State_type_1) (s2 : State_type_2) :=
    Trans2 (out i s1 s2) s2. 

  CoFixpoint A1A2 (i : Stream Input_type) (s1 : State_type_1)
   (s2 : State_type_2) : Stream Output_type :=
    S_cons (out (S_head i) s1 s2)
      (A1A2 (S_tail i) (upd_s1 (S_head i) s1 s2) (upd_s2 (S_head i) s1 s2)).



 (** Description of the feedback composition FC of A1 and A2 **)

  Definition Trans_FC (i : Input_type) (s : State_type_1 * State_type_2) :
    State_type_1 * State_type_2 :=
    let (s1, s2) := s in
    (Trans1 (input (i, Out2 s2)) s1,
    Trans2 (Out1 (input (i, Out2 s2)) s1) s2).

  
  Definition Out_FC (i : Input_type) (s : State_type_1 * State_type_2) :
    Output_type := let (s1, s2) := s in Out1 (input (i, Out2 s2)) s1.


  Definition FC :
    Stream Input_type -> State_type_1 * State_type_2 -> Stream Output_type :=
    Mealy Trans_FC Out_FC.


  Definition States_FC :
    Stream Input_type ->
    State_type_1 * State_type_2 -> Stream (State_type_1 * State_type_2) :=
    States_Mealy Trans_FC.



 (** Equivalence between A1A2 and FC **)

  Lemma Equiv_A1A2_FC :
   forall (s1 : State_type_1) (s2 : State_type_2) (i : Stream Input_type),
   EqS (A1A2 i s1 s2) (FC i (s1, s2)).
  Proof.
  cofix Equiv_A1A2_FC.
  intros s1 s2 i.
  apply eqS; simpl in |- *; auto.
  Qed.


End Feedback_Composition.

