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
(*                              Conversions.v                               *)
(****************************************************************************)


Require Export Lib_Exp. 
Require Export Fixed_dLists.


Set Implicit Arguments.
Unset Strict Implicit.


(** Conversion functions on booleans **)

Definition bool_nat (b : bool) : nat := match b with
                                        | true => 1
                                        | _ => 0
                                        end.


Definition nat_bool (n : nat) : bool :=
  match n with
  | O => false
  | _ => true
  end.


Fixpoint bool_to_nat (n : nat) (l : d_list bool n) {struct l} : nat :=
  match l with
  | d_nil => 0
  | d_cons p a l' => bool_nat a * exp_2 p + bool_to_nat l'
  end.


Lemma upper_bound_bool : forall b : bool, bool_nat b < 2.
simple induction b; auto.
Qed.

Lemma Upper_Bound_Bool :
 forall (n : nat) (l : d_list bool n), bool_to_nat l < exp_2 n.
simple induction l; auto.
intros; simpl in |- *.
elim plus_n_O.
apply le_lt_plus.
elim a; simpl in |- *.
elim plus_n_O; auto.
auto with arith.
auto.
Qed.



(** Converts a lenght-2 boolean list to the corresponding position vector **)

Definition Convert_list2 (l : d_list bool 2) :=
  match d_Head l with
  | true =>
      match d_Head (d_tl l) with
      | true => List4 false false false true
      | false => List4 false false true false
      end
  | false =>
      match d_Head (d_tl l) with
      | true => List4 false true false false
      | false => List4 true false false false
      end
  end.



(** Converts a lenght-2 boolean list to the corresponding natural number **)

Definition Convert_list2_nat (l : d_list bool 2) :=
  match d_Head l with
  | true => match d_Head (d_tl l) with
            | true => 3
            | false => 2
            end
  | false => match d_Head (d_tl l) with
             | true => 1
             | false => 0
             end
  end.
