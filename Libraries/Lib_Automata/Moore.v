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
(*                                 Moore.v                                  *)
(****************************************************************************)
 

Require Export Infinite_lists.


Set Implicit Arguments.
Unset Strict Implicit.


Section Moore_Description.

  Variable Input_type Output_type State_type : Set.
  Variable Trans : Input_type -> State_type -> State_type.
  Variable Out : State_type -> Output_type.

  CoFixpoint Moore (i : Stream Input_type) (s : State_type) :
   Stream Output_type :=
    S_cons (Out s) (Moore (S_tail i) (Trans (S_head i) s)).


End Moore_Description.

Lemma S_tail_Moore :
 forall (Input_type Output_type State_type : Set)
   (t : Input_type -> State_type -> State_type)
   (out : State_type -> Output_type) (i : Stream Input_type) 
   (s : State_type),
 S_tail (Moore t out i s) = Moore t out (S_tail i) (t (S_head i) s).
auto.
Qed.

Lemma S_head_Moore :
 forall (Input_type Output_type State_type : Set)
   (t : Input_type -> State_type -> State_type)
   (out : State_type -> Output_type) (i : Stream Input_type) 
   (s : State_type), S_head (Moore t out i s) = out s.
auto.
Qed.


Lemma EqS_Moore :
 forall (Input_type Output_type State_type : Set)
   (t : Input_type -> State_type -> State_type)
   (out : State_type -> Output_type) (i1 i2 : Stream Input_type)
   (s1 s2 : State_type),
 s1 = s2 -> EqS i1 i2 -> EqS (Moore t out i1 s1) (Moore t out i2 s2).
cofix.
intros Input_type o State_type t out i1 i2 s1 s2 H1 H2.
inversion_clear H2.
apply eqS.
simpl in |- *; elim H; elim H1; auto.
rewrite S_tail_Moore; rewrite S_tail_Moore.
elim H; elim H1; auto.
Qed.
