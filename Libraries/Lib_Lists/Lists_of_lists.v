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
(*                           Lists_of_lists.v                               *)
(****************************************************************************)

Require Export Dependent_lists_Compl.

Set Implicit Arguments.
Unset Strict Implicit.


(** Takes as argument a list of non-empty lists and builds the list of **)
(** all the heads of the sub-lists **)

Definition list_of_heads (A : Set) (i : nat) := d_map (d_Head (A:=A) (n:=i)).


(** Takes as argument a list of lists and builds the list of all the tails **)
(** of the sub-lists **)

Definition list_of_tails (A : Set) (i : nat) := d_map (d_tl (A:=A) (n:=i)).


(** Takes as argument a list of lists and constructs the list of all the **)
(** ith elements of the sub-lists **)

Definition list_of_nth (A : Set) (i n : nat) (H : 0 < i) 
  (H' : i <= n) := d_map (nth (A:=A) (i:=i) (n:=n) H H').


(** Takes as argument a list of lists and constructs the list of **)
(** all the segments [n..m] of the sub-lists **)

Definition list_of_seg (A : Set) (n m k : nat) (H1 : 0 < n) 
  (H2 : m <= k) (H3 : n <= m) :=
  d_map (seg (A:=A) (n:=n) (m:=m) (k:=k) H1 H2 H3). 


(** Transposition of a matrix defined as a list of lists **)

Fixpoint merge (A : Set) (n m : nat) {struct n} :
 d_list (d_list A n) m -> d_list (d_list A m) n :=
  match n return (d_list (d_list A n) m -> d_list (d_list A m) n) with
  | O => fun l : d_list (d_list A 0) m => d_nil (d_list A m)
  | S p =>
      fun l : d_list (d_list A (S p)) m =>
      d_cons (list_of_heads l) (merge (list_of_tails l))
  end.