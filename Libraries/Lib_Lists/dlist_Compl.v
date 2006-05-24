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
(*                              dlist_Compl.v                               *)
(****************************************************************************)
  

Require Export Dependent_lists_Compl.
Require Export Tests_in_d_lists.
Require Export Arith_Compl.


Set Implicit Arguments.
Unset Strict Implicit.

Section Additional_Def_and_Lemmas.

  Variable A : Set.

(** Another way of computing a segment taken in a dlist **)
(** Returns the length-(S (minus m n)) list which elements are between **)
(** n and m position s (indexes) of a length-k list                                 **)

  Definition segment (n m k : nat) (l : d_list A k) 
    (H1 : 0 < n) (H2 : m <= k) (H3 : n <= m) :=
    construct_with_i_first
      (construct_with_i_last l (le_minusS H1 (le_trans n m k H3 H2)))
      (le_le_Sminus n H2).



(** The same as wseg with parameters order modified **)

  Definition Segment (n m k : nat) (H1 : 0 < n) (H2 : m <= k) 
    (H3 : n <= m) (l : d_list A k) := segment (n:=n) (m:=m) (k:=k) l H1 H2 H3.


(** The same as fold_with_f with parameters order modified **)

  Definition Fold_with_f (n : nat) (f : A -> A -> A) 
    (H : 0 < n) (l : d_list A n) := fold_with_f (n:=n) l f H.

(** The same as fold_with_f with a lenght-(n+1) list and a proof **)

  Definition Fold_with_f_S_p (n : nat) (f : A -> A -> A)
    (l : d_list A (S n)) := Fold_with_f f (lt_O_Sn n) l.


(** Another version of Fold_with_f_S without any proof **)

  Fixpoint Fold_with_f_S (n : nat) (f : A -> A -> A) {struct n} :
   d_list A (S n) -> A :=
    match n return (d_list A (S n) -> A) with
    | O => fun l : d_list A 1 => d_Head l
    | S p =>
        fun l : d_list A (S (S p)) => f (d_Head l) (Fold_with_f_S f (d_tl l))
    end.

 
(** Constructs a length-n list which all elements are equal to a given value v **)

  Fixpoint make_list_of_v (n : nat) (v : A) {struct n} : 
   d_list A n :=
    match n return (d_list A n) with
    | O => d_nil A
    | S p => d_cons v (make_list_of_v p v)
    end.


  Lemma eq_dlist_Head :
   forall (n : nat) (l l' : d_list A (S n)), l = l' -> d_Head l = d_Head l'.
  intros n l l' H; rewrite H; auto.
  Qed.


 (* Provided that A is a set on which the equality of two elements is decidable *)

  Hypothesis eq_dec : forall a b : A, {a = b} + {a <> b}.

  Lemma In_or_not :
   forall (a : A) (n : nat) (l : d_list A n), {d_In a l} + {~ d_In a l}.
  intro a.
  simple induction l.
  right; simpl in |- *; red in |- *; auto.
  intros n0 b d H.
  elim H; intro H'.
  left; simpl in |- *; auto.
  elim (eq_dec a b); intro dec.
  rewrite dec; left; simpl in |- *; auto.
  right.
  red in |- *; simpl in |- *.
  intro H0; elim H0; intro.
  red in dec; auto.
  red in H'; auto.
  Qed.


End Additional_Def_and_Lemmas.


Definition list_of_segment (A : Set) (n m k : nat) 
  (H1 : 0 < n) (H2 : m <= k) (H3 : n <= m) :=
  d_map (Segment (A:=A) (n:=n) (m:=m) (k:=k) H1 H2 H3). 



Lemma eqp1 :
 forall (A B : Set) (n : nat) (l : d_list A (S n)) (f : A -> B),
 d_Head (d_map f l) = f (d_Head l).
intros.
elim (non_empty l).
intros x p.
elim p; clear p; intros.
rewrite p; simpl in |- *; auto.
Qed.


Lemma eqp2 :
 forall (A B : Set) (n : nat) (l : d_list A (S n)) (f : A -> B),
 d_tl (d_map f l) = d_map f (d_tl l).
intros.
elim (non_empty l); intros x p.
elim p; clear p; intros.
rewrite p; simpl in |- *; auto.
Qed.

Lemma eqp3 :
 forall (A B : Set) (n : nat) (l : d_list A (S (S n))) (f : A -> B),
 d_Head (d_tl (d_map f l)) = f (d_Head (d_tl l)).
intros.
elim (non_empty l); intros x p.
elim p; clear p; intros.
rewrite p; simpl in |- *; auto.
rewrite eqp1.
auto.
Qed.


Lemma eqp4 :
 forall (A B : Set) (n : nat) (l : d_list A (S (S (S n)))) (f : A -> B),
 d_Head (d_tl (d_tl (d_map f l))) = f (d_Head (d_tl (d_tl l))).
intros.
elim (non_empty l); intros x p.
elim p; clear p; intros.
rewrite p; simpl in |- *; auto.
rewrite eqp3.
auto.
Qed.


Lemma eqp5 :
 forall (A B : Set) (n : nat) (l : d_list A (S (S (S (S n))))) (f : A -> B),
 d_Head (d_tl (d_tl (d_tl (d_map f l)))) = f (d_Head (d_tl (d_tl (d_tl l)))).
intros.
elim (non_empty l); intros x p.
elim p; clear p; intros.
rewrite p; simpl in |- *; auto.
elim (non_empty x0); intros x1 p0.
elim p0; clear p0; intros.
rewrite p0; simpl in |- *.
rewrite eqp3.
auto.
Qed.

