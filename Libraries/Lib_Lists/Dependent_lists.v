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
(*                          Dependent_lists.v                               *)
(****************************************************************************)

Require Export Eqdep.
Require Export Arith.

Global Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.
  
Section Dependent_lists.

  Variable A : Set.

  Inductive d_list : nat -> Set :=
    | d_nil : d_list 0
    | d_cons : forall n : nat, A -> d_list n -> d_list (S n).

  Definition eq_d_list := eq_dep nat d_list.

  Definition d_hd (n : nat) (l : d_list n) : Exc A :=
    match l in (d_list m) return (Exc A) with
    | d_nil => error
    | d_cons p a l' => value a
    end.

  Definition d_head (n : nat) (l : d_list n) :=
    match l in (d_list p) return (0 < p -> A) with
    | d_nil =>
        (* d_nil*)	
        fun h : 0 < 0 => False_rec A (lt_irrefl 0 h)
        (* d_cons p a l' *)
    | d_cons p a l' => fun h : 0 < S p => a
    end.

                           
  Definition d_Head (n : nat) (l : d_list (S n)) := d_head l (lt_O_Sn n).

  Definition d_tl (n : nat) (l : d_list n) : d_list (pred n) :=
    match l in (d_list m) return (d_list (pred m)) with
    | d_nil => d_nil
    | d_cons p a l' => l'
    end.


  Lemma empty_dep :
   forall (n : nat) (l : d_list n), n = 0 -> eq_d_list d_nil l.
  unfold eq_d_list in |- *; intros n l.
  dependent inversion_clear l; auto.
  intros H; absurd (S n0 = 0); auto.
  Qed.

  Hint Immediate empty_dep.

  Lemma empty : forall l : d_list 0, d_nil = l.
  intros l.
  apply (eq_dep_eq nat d_list 0).
  apply empty_dep; auto.
  Qed.

  Hint Immediate empty.

  Remark non_empty_dep :
   forall n m : nat,
   m = S n ->
   forall l : d_list (S n),
   {h : A &  {t : d_list n | eq_d_list l (d_cons h t)}}.
  intros n m H l.
  generalize H; clear H.
  dependent inversion_clear l
   with
    (fun (n' : nat) (l : d_list n') =>
     m = n' -> {a : A &  {l' : d_list n | eq_d_list l (d_cons a l')}}).
  unfold eq_d_list in |- *.
  intros H; exists a; exists d; auto.
  Qed.


  Lemma non_empty :
   forall (n : nat) (l : d_list (S n)),
   {a : A &  {t : d_list n | l = d_cons a t}}. 
  intros n l.
  cut
   (sigS (fun a : A => sig (fun t : d_list n => eq_d_list l (d_cons a t)))).
  intros H; elim H; clear H.
  intros a H; elim H; clear H.
  intros t H.
  exists a; exists t.
  apply eq_dep_eq with (U := nat) (P := d_list) (p := S n).
  unfold eq_d_list in H; auto.
  apply (non_empty_dep (n:=n) (m:=S n)); auto.
  Qed.


  Lemma split_d_list :
   forall (n : nat) (l : d_list (S n)),
   l = d_cons (d_head l (lt_O_Sn n)) (d_tl l).
  intros n l.
  elim (non_empty l).
  intros h H; elim H; clear H.
  intros t e.
  rewrite e; simpl in |- *.
  auto.
  Qed.

  Definition d_Hd (n : nat) (l : d_list (S n)) :=
    let (a, P) return A := non_empty l in a.

  Lemma Non_empty_Hd :
   forall (n : nat) (a : A) (l : d_list n), d_Hd (d_cons a l) = a.
  intros n a l; unfold d_Hd in |- *.
  elim (non_empty (d_cons a l)).
  intros x H; elim H.
  clear H; intros X H.
  injection H; auto.
  Qed.

End Dependent_lists.

Hint Immediate empty_dep empty non_empty Non_empty_Hd.


(** Definitions of some usual mappings **)

  
Fixpoint d_map (A B : Set) (f : A -> B) (n : nat) (l : d_list A n) {struct l} 
   : d_list B n :=
  match l in (d_list _ x) return (d_list B x) with
  | d_nil =>
      (*(d_nil A)*)  d_nil B
      (*(d_cons A p a t*) 
  | d_cons p a t => d_cons (f a) (d_map f t)
  end.


Fixpoint d_map2 (A B C : Set) (f : A -> B -> C) (n : nat) {struct n} :
 d_list A n -> d_list B n -> d_list C n :=
  match n as x return (d_list A x -> d_list B x -> d_list C x) with
  | O => fun (_ : d_list A 0) (_ : d_list B 0) => d_nil C
  | S p =>
      fun (l1 : d_list A (S p)) (l2 : d_list B (S p)) =>
      d_cons (f (d_Head l1) (d_Head l2)) (d_map2 f (d_tl l1) (d_tl l2))
  end.



Fixpoint d_map3 (A B C D : Set) (f : A -> B -> C -> D) 
 (n : nat) {struct n} :
 d_list A n -> d_list B n -> d_list C n -> d_list D n :=
  match
    n as x return (d_list A x -> d_list B x -> d_list C x -> d_list D x)
  with
  | O => fun (_ : d_list A 0) (_ : d_list B 0) (_ : d_list C 0) => d_nil D
  | S p =>
      fun (l1 : d_list A (S p)) (l2 : d_list B (S p)) (l3 : d_list C (S p)) =>
      d_cons (f (d_Head l1) (d_Head l2) (d_Head l3))
        (d_map3 f (d_tl l1) (d_tl l2) (d_tl l3))
  end.


 
Fixpoint d_map4 (A B C D E : Set) (f : A -> B -> C -> D -> E) 
 (n : nat) {struct n} :
 d_list A n -> d_list B n -> d_list C n -> d_list D n -> d_list E n :=
  match
    n as x
    return
      (d_list A x -> d_list B x -> d_list C x -> d_list D x -> d_list E x)
  with
  | O =>
      fun (_ : d_list A 0) (_ : d_list B 0) (_ : d_list C 0) (_ : d_list D 0) =>
      d_nil E
  | S p =>
      fun (l1 : d_list A (S p)) (l2 : d_list B (S p)) 
        (l3 : d_list C (S p)) (l4 : d_list D (S p)) =>
      d_cons (f (d_Head l1) (d_Head l2) (d_Head l3) (d_Head l4))
        (d_map4 f (d_tl l1) (d_tl l2) (d_tl l3) (d_tl l4))
  end.