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
(*                            Tests_in_d_lists.v                            *)
(****************************************************************************)


Require Export Dependent_lists.

Set Implicit Arguments.
Unset Strict Implicit.


Section Tests_in_dlists.
  
  Variable A : Set.
  Variable P : A -> Prop.
  Hypothesis P_dec : forall a : A, {P a} + {~ P a}.
  Let d_List := d_list A.


(** Tests if neither of elements of a given list verifies P **)

  Fixpoint all_False (n : nat) (l : d_List n) {struct l} : Prop :=
    match l with
    | d_nil => True
    | d_cons p a l' =>
        match P_dec a with
        | left _ => False
        | right _ => all_False l'
        end
    end.


(** Tests if all the elements of a given list verify P **)

  Fixpoint all_True (n : nat) (l : d_List n) {struct l} : Prop :=
    match l with
    | d_nil => True
    | d_cons p a l' =>
        match P_dec a with
        | left _ => all_True l'
        | right _ => False
        end
    end.


(** Tests if it exists at least one element verifying P **)

  Fixpoint exists1_atleast (n : nat) (l : d_List n) {struct l} : Prop :=
    match l with
    | d_nil => False
    | d_cons p a l' =>
        match P_dec a with
        | left _ => True
        | right _ => exists1_atleast l'
        end
    end.
  

(** Tests if it exists exactly one element verifying P  **)

  Fixpoint exists1_exact (n : nat) (l : d_List n) {struct l} : Prop :=
    match l with
    | d_nil => False
    | d_cons p a l' =>
        match P_dec a with
        | left _ => all_False l'
        | right _ => exists1_exact l'
        end
    end.


(** Returns the number of elements verifying P **)

  Fixpoint number_P (n : nat) (l : d_List n) {struct l} : nat :=
    match l with
    | d_nil => 0
    | d_cons _ a l' =>
        match P_dec a with
        | left _ => S (number_P l')
        | right _ => number_P l'
        end
    end.


(** The number of elements verifying P in a length-n list is less than n **)

  Lemma le_number_P : forall (n : nat) (l : d_List n), number_P l <= n.
  simple induction l.
  simpl in |- *; auto.
  simpl in |- *; intros.
  elim (P_dec a); intro; auto with arith.
  Qed.


(** Tests if an element is in a list **)

  Fixpoint d_In (a : A) (n : nat) (l : d_List n) {struct l} : Prop :=
    match l with
    | d_nil => False
    | d_cons _ b l' => b = a \/ d_In a l'
    end.
 

End Tests_in_dlists.

Hint Immediate le_number_P.