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
(*                              PolyList_dlist.v                            *)
(****************************************************************************)

Require Export List.
Require Export Dependent_lists.

Set Implicit Arguments.
Unset Strict Implicit.


Section Transformation.

  Variable A : Set.
  
  (** Conversion between dependent and non-dependent lists **) 

  Fixpoint List_dlist (l : list A) (n : nat) {struct n} :
   length l = n -> d_list A n :=
    match n return (length l = n -> d_list A n) with
    | O => fun _ : length l = 0 => d_nil A
    | S p =>
        match l return (length l = S p -> d_list A (S p)) with
        | nil => fun h : 0 = S p => False_rec (d_list A (S p)) (O_S p h)
        | a :: t =>
            fun h : S (length t) = S p =>
            d_cons a (List_dlist (eq_add_S (length t) p h))
        end
    end.

  
  (** A more easy to translate a list into a dependent list **)

   Fixpoint list_dlist (l : list A) : d_list A (length l) :=
     match l return (d_list A (length l)) with
     | nil => d_nil A
     | a :: l' => d_cons a (list_dlist l')
     end.



  Fixpoint dlist_List (n : nat) (l : d_list A n) {struct l} : 
   list A :=
    match l with
    | d_nil => nil (A:=A)
    | d_cons _ a t => a :: dlist_List t
    end.


End Transformation.


Lemma List_dlist_cons :
 forall (A : Set) (a : A) (l : list A),
 list_dlist (a :: l) = d_cons a (list_dlist l).
auto.
Qed.
