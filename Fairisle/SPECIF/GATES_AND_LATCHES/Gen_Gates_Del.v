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
(*                              Gen_Gates_Del.v                             *)
(****************************************************************************)
 

Require Export Infinite_lists.

Set Implicit Arguments.
Unset Strict Implicit.


(** Register **)

Definition Reg := S_cons.


(** Introducing a delay before a combinatorial part **)

CoFixpoint Regf (A B : Set) (old : A) (comb : A -> B) 
 (s : Stream A) : Stream B :=
  Reg (comb old) (Regf (S_head s) comb (S_tail s)).


(** Introducing a delay after a combinatorial part **)

Definition Freg (A B : Set) (comb : A -> B) (s : Stream A) 
  (init : B) := Reg init (S_map comb s).



Definition Freg2 (A B C : Set) (comb : A -> B -> C) 
  (s1 : Stream A) (s2 : Stream B) (init : C) := Reg init (S_map2 comb s1 s2).



(** Introducing a delay before a combinatorial part named f with a feedback loop **)

CoFixpoint Loop (A B : Set) (old : B) (s : Stream A) 
 (f : A -> B -> B) : Stream B :=
  Reg old (Loop (f (S_head s) old) (S_tail s) f).



CoFixpoint Loop2 (A B C : Set) (old : C) (s1 : Stream A) 
 (s2 : Stream B) (f : A -> B -> C -> C) : Stream C :=
  Reg old (Loop2 (f (S_head s1) (S_head s2) old) (S_tail s1) (S_tail s2) f).



CoFixpoint Loop3 (A B C D : Set) (old : D) (s1 : Stream A) 
 (s2 : Stream B) (s3 : Stream C) (f : A -> B -> C -> D -> D) : 
 Stream D :=
  Reg old
    (Loop3 (f (S_head s1) (S_head s2) (S_head s3) old) 
       (S_tail s1) (S_tail s2) (S_tail s3) f).



CoFixpoint Loop3_permut (A B C D : Set) (old : D) (s1 : Stream A)
 (s2 : Stream B) (s3 : Stream C) (f : A -> B -> D -> C -> D) : 
 Stream D :=
  Reg old
    (Loop3_permut (f (S_head s1) (S_head s2) old (S_head s3)) 
       (S_tail s1) (S_tail s2) (S_tail s3) f).


