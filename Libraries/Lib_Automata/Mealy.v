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
(*                                 Mealy.v                                  *)
(****************************************************************************)
 

Require Export Infinite_lists.


Set Implicit Arguments.
Unset Strict Implicit.


Section Mealy_Description.

  Variable Input_type Output_type State_type : Set.
  Variable Trans : Input_type -> State_type -> State_type.
  Variable Out : Input_type -> State_type -> Output_type.

  CoFixpoint Mealy (i : Stream Input_type) (s : State_type) :
   Stream Output_type :=
    S_cons (Out (S_head i) s) (Mealy (S_tail i) (Trans (S_head i) s)).


  CoFixpoint States_Mealy (i : Stream Input_type) (s : State_type) :
   Stream State_type :=
    S_cons s (States_Mealy (S_tail i) (Trans (S_head i) s)).
 
End Mealy_Description.


Section Equivalence_2_Mealy.

  Variable Input_type Output_type State_type_1 State_type_2 : Set.
  Variable Trans1 : Input_type -> State_type_1 -> State_type_1.
  Variable Trans2 : Input_type -> State_type_2 -> State_type_2.

  Variable Out1 : Input_type -> State_type_1 -> Output_type.
  Variable Out2 : Input_type -> State_type_2 -> Output_type.

  Let A1 := Mealy Trans1 Out1.
  Let A2 := Mealy Trans2 Out2.

  Let States_A1 := States_Mealy Trans1.
  Let States_A2 := States_Mealy Trans2.


 (** We can need a property on input signals or state_types or both **)

  Variable P : Input_type -> State_type_1 -> State_type_2 -> Prop.


 (** If we need P, P must be also defined on streams **)

  CoInductive Inv :
  Stream Input_type -> Stream State_type_1 -> Stream State_type_2 -> Prop :=
      C_Inv :
        forall (i : Stream Input_type) (s1 : Stream State_type_1)
          (s2 : Stream State_type_2),
        P (S_head i) (S_head s1) (S_head s2) ->
        Inv (S_tail i) (S_tail s1) (S_tail s2) -> Inv i s1 s2.


 (** If P is true everywhere, then it is verified on the streams **)

  Hypothesis
    P_is_true :
      forall (i : Input_type) (s1 : State_type_1) (s2 : State_type_2),
      P i s1 s2.

  Lemma Inv_Ok :
   forall (i : Stream Input_type) (s1 : Stream State_type_1)
     (s2 : Stream State_type_2), Inv i s1 s2.
  cofix.
  intros i s1 s2.
  apply C_Inv; auto.
  Qed.


  (** Relation R on the State_types **)

  Variable R : State_type_1 -> State_type_2 -> Prop.


   (* R is an invariant under P *)

  Definition Inv_under_P :=
    forall (i : Input_type) (s1 : State_type_1) (s2 : State_type_2),
    P i s1 s2 -> R s1 s2 -> R (Trans1 i s1) (Trans2 i s2). 


 (** R is an output relation **)

  Definition Output_rel :=
    forall (i : Input_type) (s1 : State_type_1) (s2 : State_type_2),
    R s1 s2 -> Out1 i s1 = Out2 i s2.


(** Equivalence proof between 2 Mealy automata **)

  Lemma Equiv_2_Mealy :
   Inv_under_P ->
   Output_rel ->
   forall (i : Stream Input_type) (s1 : State_type_1) (s2 : State_type_2),
   Inv i (States_A1 i s1) (States_A2 i s2) ->
   R s1 s2 -> EqS (A1 i s1) (A2 i s2).
  cofix.
  intros H_Inv_under_P H_Output_rel i s1 s2 H_Inv H_R.
  inversion_clear H_Inv.
  apply eqS; simpl in |- *.
  apply H_Output_rel; trivial.
  apply Equiv_2_Mealy; trivial.
  apply H_Inv_under_P; trivial.
  Qed.



 (** If no property is required P will be True **)

  Definition No_P (_ : Input_type) (_ : State_type_1) 
    (_ : State_type_2) := True.

 (** If no property is required Inv will be True', the same as True but of **)
 (** type Set **)

  Inductive True' : Set :=
      I' : True'.

  Definition No_Inv (_ : Stream Input_type) (p_ : Stream State_type_1)
    (_ : Stream State_type_2) := all_same I'.



End Equivalence_2_Mealy.


Lemma S_tail_Mealy :
 forall (Input_type o State_type : Set)
   (t : Input_type -> State_type -> State_type)
   (out : Input_type -> State_type -> o) (i : Stream Input_type)
   (s : State_type),
 S_tail (Mealy t out i s) = Mealy t out (S_tail i) (t (S_head i) s).
auto.
Qed.

Lemma S_tail_States_Mealy :
 forall (Input_type State_type : Set)
   (t : Input_type -> State_type -> State_type) (i : Stream Input_type)
   (s : State_type),
 S_tail (States_Mealy t i s) = States_Mealy t (S_tail i) (t (S_head i) s).
auto.
Qed.


Lemma S_head_States_Mealy :
 forall (Input_type State_type : Set)
   (t : Input_type -> State_type -> State_type) (i : Stream Input_type)
   (s : State_type), S_head (States_Mealy t i s) = s.
auto.
Qed.


Lemma EqS_Mealy :
 forall (Input_type Output_type State_type : Set)
   (t : Input_type -> State_type -> State_type)
   (out : Input_type -> State_type -> Output_type)
   (i1 i2 : Stream Input_type) (s1 s2 : State_type),
 s1 = s2 -> EqS i1 i2 -> EqS (Mealy t out i1 s1) (Mealy t out i2 s2).
cofix.
intros Input_type o State_type t out i1 i2 s1 s2 H1 H2.
inversion_clear H2.
apply eqS.
simpl in |- *; elim H; elim H1; auto.
rewrite S_tail_Mealy; rewrite S_tail_Mealy.
elim H; elim H1; auto.
Qed.


Lemma EqS_States_Mealy :
 forall (Input_type State_type : Set)
   (t : Input_type -> State_type -> State_type) (i1 i2 : Stream Input_type)
   (s1 s2 : State_type),
 s1 = s2 -> EqS i1 i2 -> EqS (States_Mealy t i1 s1) (States_Mealy t i2 s2).
cofix.
intros Input_type State_type t i1 i2 s1 s2 H1 H2.
inversion_clear H2.
apply eqS.
simpl in |- *; elim H; elim H1; auto.
rewrite S_tail_States_Mealy; rewrite S_tail_States_Mealy.
elim H; elim H1; auto.
Qed.



Section Equiv_about_P.
 
  Variable Input_type State_type_1 State_type_2 : Set.
  Variable P : Input_type -> State_type_1 -> State_type_2 -> Prop.

  Lemma eqS_about_P :
   forall (i i' : Stream Input_type) (s1 s1' : Stream State_type_1)
     (s2 s2' : Stream State_type_2),
   EqS i i' -> EqS s1 s1' -> EqS s2 s2' -> Inv P i' s1' s2' -> Inv P i s1 s2.
  cofix.
  intros i i' s1 s1' s2 s2' H_i H_s1 H_s2 H_P.
  inversion_clear H_i.
  inversion_clear H_s1.
  inversion_clear H_s2.
  inversion_clear H_P.
  apply C_Inv.
  rewrite H; rewrite H1; rewrite H3; try trivial.
  apply eqS_about_P with (S_tail i') (S_tail s1') (S_tail s2'); trivial.
  Qed.

End Equiv_about_P.


Section Tool_about_Equivalence_2_Mealy.

  Variable Input_type Output_type State_type_1 State_type_2 : Set.
  Variable Trans1 : Input_type -> State_type_1 -> State_type_1.
  Variable Trans2 : Input_type -> State_type_2 -> State_type_2.

  Variable Out1 : Input_type -> State_type_1 -> Output_type.
  Variable Out2 : Input_type -> State_type_2 -> Output_type.

  Let A1 := Mealy Trans1 Out1.
  Let A2 := Mealy Trans2 Out2.

  Lemma Equiv_2_Mealy_tool :
   forall (i i' : Stream Input_type) (s1 : State_type_1) (s2 : State_type_2),
   EqS (A1 i s1) (A2 i s2) -> EqS i i' -> EqS (A1 i s1) (A2 i' s2).
  cofix.
  intros i i' s1 s2 H0 H1.
  inversion_clear H0.
  inversion_clear H1.
  apply eqS; simpl in |- *.
  simpl in H.
  elim H0; try trivial.
  simpl in H2.
  apply Equiv_2_Mealy_tool; elim H0; try trivial.
  Qed.

End Tool_about_Equivalence_2_Mealy.
