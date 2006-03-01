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
(*                               Moore_Mealy.v                              *)
(****************************************************************************)
 
Require Export Mealy.
Require Export Moore.

Set Implicit Arguments.
Unset Strict Implicit.


           (** Equivalence between Moore and Mealy representation **)


 (** Construction of a Mealy automaton from a Moore automaton **)

Section Equivalence_Moore_to_Mealy1.

  Variable Input_type Output_type state_type : Set.
  Variable Trans_Moore : Input_type -> state_type -> state_type.
  Variable Out_Moore : state_type -> Output_type.
  Let A_Moore := Moore Trans_Moore Out_Moore.
 
  Let Trans_Mealy : Input_type -> state_type -> state_type := Trans_Moore.
    
  Definition Out_Mealy (_ : Input_type) (s_Mealy : state_type) :
    Output_type := Out_Moore s_Mealy.

  Let A_Mealy := Mealy Trans_Mealy Out_Mealy.


 (** Equivalence **)

  Lemma Equiv_Moore_Mealy :
   forall (i : Stream Input_type) (s : state_type),
   EqS (A_Moore i s) (A_Mealy i s).
  cofix.
  intros i s.
  apply eqS; simpl in |- *; auto.
  Qed.


End Equivalence_Moore_to_Mealy1.


 (** Construction of a Moore automaton from a Mealy automaton **)

Section Equivalence_Mealy_to_Moore1.

  Variable Input_type Output_type State_type_Mealy : Set.
  Variable Trans_Mealy : Input_type -> State_type_Mealy -> State_type_Mealy.
  Variable Out_Mealy : Input_type -> State_type_Mealy -> Output_type.
  Let A_Mealy := Mealy Trans_Mealy Out_Mealy.
 
  Let State_type_Moore := (State_type_Mealy * Output_type)%type.

  Let Trans_Moore (i : Input_type) (s_Moore : State_type_Moore) :
    State_type_Moore :=
    let (s, out) := s_Moore in (Trans_Mealy i s, Out_Mealy i s).

  Let Out_Moore (s_Moore : State_type_Moore) : Output_type :=
    let (_, out) := s_Moore in out.

  Let A_Moore := Moore Trans_Moore Out_Moore.

 (** Equivalence **)

  Lemma Equiv_Mealy_Moore :
   forall (i0 : Input_type) (i : Stream Input_type)
     (s_Mealy : State_type_Mealy),
   EqS (A_Moore i (Trans_Mealy i0 s_Mealy, Out_Mealy i0 s_Mealy))
     (A_Mealy (S_cons i0 i) s_Mealy).
intros i0 i s_Mealy.
apply eqS.
simpl in |- *; auto.
generalize i0 i s_Mealy.
clear i0 i s_Mealy.
cofix.
intros.
apply eqS.
simpl in |- *; auto.
simpl in |- *.
simpl in Equiv_Mealy_Moore.
apply Equiv_Mealy_Moore.
Qed.


Lemma EqS_const_stream :
 forall (A : Set) (i : Stream A), EqS (S_cons (S_head i) (S_tail i)) i.
cofix.
intros.
apply eqS; simpl in |- *; auto.
apply EqS_reflex.
Qed.


End Equivalence_Mealy_to_Moore1.  


(**** Another approach ****)


 (** Construction of a Mealy automaton from a Moore automaton **)

Section Equivalence_Moore_to_Mealy2.

  Variable Input_type Output_type State_type : Set.
  Variable Trans_Moore : Input_type -> State_type -> State_type.
  Variable Out_Moore : State_type -> Output_type.
  Let A_Moore := Moore Trans_Moore Out_Moore.
 
  Let Trans_Mealy : Input_type -> State_type -> State_type := Trans_Moore.
    
  Let Out_Mealy2 (_ : Input_type) (s_Mealy : State_type) : Output_type :=
    Out_Moore s_Mealy.

 (** Equivalence **)

  Lemma a_Mealy :
   forall (i : Stream Input_type) (s_Moore : State_type),
   {s_Mealy : State_type & 
   {Trans_Mealy : Input_type -> State_type -> State_type & 
   {Out_Mealy : Input_type -> State_type -> Output_type |
   EqS (A_Moore i s_Moore) (Mealy Trans_Mealy Out_Mealy i s_Mealy)}}}.
  intros i s_Moore.
  exists s_Moore.
  exists Trans_Mealy; exists Out_Mealy2.
  generalize i s_Moore.
  cofix.
  clear s_Moore i.
  intros i s_Moore.
  apply eqS; simpl in |- *; auto.
  Qed.
  
End Equivalence_Moore_to_Mealy2.


 (** Construction of a Moore automaton from a Mealy automaton **)

Section Equivalence_Mealy_to_Moore2.

  Variable Input_type Output_type State_type_Mealy : Set.
  Variable Trans_Mealy : Input_type -> State_type_Mealy -> State_type_Mealy.
  Variable Out_Mealy : Input_type -> State_type_Mealy -> Output_type.
  Let A_Mealy := Mealy Trans_Mealy Out_Mealy.
 
  Let State_type_Moore := (State_type_Mealy * Output_type)%type.

  Let Trans_Moore (i : Input_type) (s_Moore : State_type_Moore) :
    State_type_Moore :=
    let (s, out) := s_Moore in (Trans_Mealy i s, Out_Mealy i s).

  Let Out_Moore (s_Moore : State_type_Moore) : Output_type :=
    let (_, out) := s_Moore in out.


 (** Equivalence **)

 Lemma A_Moore :
  forall (i0 : Input_type) (i : Stream Input_type)
    (s_Mealy : State_type_Mealy),
  {s_Moore : State_type_Moore & 
  {Trans_Moore : Input_type -> State_type_Moore -> State_type_Moore & 
  {Out_Moore : State_type_Moore -> Output_type |
  EqS (Moore Trans_Moore Out_Moore i s_Moore) (A_Mealy (S_cons i0 i) s_Mealy)}}}.
 intros i0 i s_Mealy.
 exists (Trans_Mealy i0 s_Mealy, Out_Mealy i0 s_Mealy); exists Trans_Moore;
  exists Out_Moore.
 apply eqS.
 simpl in |- *; auto.
 generalize i0 i s_Mealy.
 clear i0 i s_Mealy.
 cofix.
 intros i0 i s_Mealy.
 apply eqS.
 simpl in |- *; auto.
 simpl in A_Moore.
 simpl in |- *.
 apply A_Moore.
Qed.


End Equivalence_Mealy_to_Moore2.


