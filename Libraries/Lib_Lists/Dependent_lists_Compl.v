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
(*                          Dependent_lists_Compl.v                         *)
(****************************************************************************)
 

Require Export Dependent_lists.
Require Import Compare_dec.
Require Import Arith_Compl.

Set Implicit Arguments.
Unset Strict Implicit.

Section d_Lists_Compl.

  Variable A B C : Set.
  Let d_List := d_list A.

 (** Concatenation **)

  Fixpoint wcat (n m : nat) (l1 : d_List n) (l2 : d_List m) {struct l1} :
   d_List (n + m) :=
    match l1 in (d_list _ n) return (d_List (n + m)) with
    | d_nil => l2
    | d_cons _ a l1' => d_cons a (wcat l1' l2)
    end.


 (** Puts an element at the end of a list **)

  Fixpoint put_end (a : A) (n : nat) (l : d_List n) {struct l} :
   d_List (S n) :=
    match l in (d_list _ n) return (d_List (S n)) with
    | d_nil => d_cons a (d_nil A)
    | d_cons _ a' l' => d_cons a' (put_end a l')
    end.



 (** Converts a term of type (d_List n) to the same term of type (d_List m) given **)
 (** a proof that n=m **)

  Definition subst : forall n m : nat, n = m -> d_List n -> d_List m.
  simple destruct 1; trivial.
  Defined.


 (** Reverses a list **)

  Fixpoint Rev (n : nat) (l : d_List n) {struct l} : 
   d_List n :=
    match l in (d_list _ n) return (d_List n) with
    | d_nil => d_nil A
    | d_cons _ a l' => put_end a (Rev l')
    end.


 (** Constructs a length-i list taking the i first elements of a length-n **)
 (** list, under the hypothesis that i<=n                                 **)
 
  Fixpoint construct_with_i_first (n i : nat) (l : d_List n) {struct i} :
   i <= n -> d_List i :=
    match i as x return (x <= n -> d_List x) with
    | O => fun _ : 0 <= n => d_nil A
    | S p =>
        fun h : S p <= n =>
        d_cons (d_head l (le_S_lt_O h))
          (construct_with_i_first (d_tl l) (le_Sn_le_n_pred h))
    end.



 (** Constructs a length-i list taking the i last elements of a length-n list **)

  Definition construct_with_i_last (n i : nat) (l : d_List n) 
    (H : i <= n) : d_List i := Rev (construct_with_i_first (Rev l) H).




 (** Removes the ith first element(s) of a list **)

  Fixpoint strip_off_first (i n : nat) (l : d_List n) {struct l} :
   d_List (n - i) :=
    match l in (d_list _ n) return (d_List (n - i)) with
    | d_nil => d_nil A
    | d_cons p a t =>
        match i return (d_List (S p - i)) with
        | O => d_cons a t
        | S q => strip_off_first q t
        end
    end.


 (** Removes the ith last element(s) of a list **)

  Definition strip_off_last (i n : nat) (l : d_List n) :=
    Rev (strip_off_first i (Rev l)).



 (** Another way of returning the i first elements of a list **)

  Definition first_of_list (i n : nat) (l : d_List n) :=
    strip_off_last (n - i) l.


 (** Another way of returning the i last elements of a list **)
 
  Definition last_of_list (i n : nat) (l : d_List n) :=
    strip_off_first (n - i) l.


 (** Removes the ith element of a list **)

  Definition remove_i (i n : nat) (l : d_List n) :=
    wcat (first_of_list (pred i) l) (last_of_list (n - i) l).


 (** Another way of removing the ith element of a list **)
  
  Fixpoint Remove_i (i : nat) :
   0 < i -> forall n : nat, i <= n -> d_List (S n) -> d_List n :=
    match
      i return (0 < i -> forall n : nat, i <= n -> d_List (S n) -> d_List n)
    with
    | O =>
        fun (h : 0 < 0) (n : nat) (_ : 0 <= n) (l : d_List (S n)) =>
        False_rec (d_List n) (lt_irrefl 0 h)
    | S p =>
        fun (_ : 0 < S p) (n : nat) =>
        match zerop p return (S p <= n -> d_List (S n) -> d_List n) with
        | left _ => fun (_ : S p <= n) (l : d_List (S n)) => d_tl l
        | right h =>
            match n return (S p <= n -> d_List (S n) -> d_List n) with
            | O =>
                fun (h' : S p <= 0) (l : d_List 1) =>
                False_rec (d_List 0) (le_Sn_O p h')
            | S q =>
                fun (h' : S p <= S q) (l : d_List (S (S q))) =>
                d_cons (d_Head l) (Remove_i h (le_S_n p q h') (d_tl l))
            end
        end
    end.



 (** Returns the ith element of a length-n list **)

 Fixpoint Nth (i n : nat) (l : d_List n) {struct i} : 
  0 < i -> i <= n -> A :=
   match i as y return (0 < y -> y <= n -> A) with
   | O => fun (h : 0 < 0) (h' : 0 <= n) => False_rec A (lt_irrefl 0 h)
   | S p =>
       fun (_ : 0 < S p) (h' : S p <= n) =>
       match zerop p with
       | left _ => d_head l (le_S_lt_O h')
       | right h'' => Nth (d_tl l) h'' (le_Sn_le_n_pred h')
       end
   end.


 (** The same as Nth with parameter order modified **)

  Definition nth (i n : nat) (H : 0 < i) (H' : i <= n) 
    (l : d_List n) := Nth (i:=i) l H H'.


 (** Another way, using the Program tactic, of describing the nth function **)

  Inductive nth_spec : forall i n : nat, d_List n -> A -> Prop :=
    | nth_O :
        forall (a : A) (n : nat) (l : d_List n), nth_spec 1 (d_cons a l) a
    | nth_S :
        forall (i n : nat) (a b : A) (l : d_List n),
        nth_spec i l a -> nth_spec (S i) (d_cons b l) a.

  Fixpoint Nth_func (i n : nat) (l : d_List n) {struct l} : 
   Exc A :=
    match l with
    | d_nil => error (A:=A)
    | d_cons p a l' =>
        match i with
        | O => error (A:=A)
        | S q => match q with
                 | O => value a
                 | S q' => Nth_func (S q') l'
                 end
        end
    end.



 (** Returns the length-((minus m n)+1) list elements of which are between **)
 (** the n and m positions of a length-k list                              **)

  Definition Seg' (n m k : nat) (l : d_List k) (H1 : 0 < n) 
    (H2 : m <= k) (H3 : n <= m) :=
    first_of_list (S (m - n)) (last_of_list (S (k - n)) l).


 (** The same as Seg' with parameters order modified **)

  Definition seg' (n m k : nat) (H1 : 0 < n) (H2 : m <= k) 
    (H3 : n <= m) (l : d_List k) := Seg' l H1 H2 H3.


 (** The same as Seg' using other functions that returns a less complicated type **)

   Definition Seg (n m k : nat) (l : d_List k) (H1 : 0 < n) 
     (H2 : m <= k) (H3 : n <= m) :=
     construct_with_i_first (i:=S (m - n))
       (construct_with_i_last (i:=S (k - n)) l (le_minusSS H1 H2 H3))
       (le_le_Sminus n H2).

 (** The same as Seg with parameters order modified **)

   Definition seg (n m k : nat) (H1 : 0 < n) (H2 : m <= k) 
     (H3 : n <= m) (l : d_List k) := Seg l H1 H2 H3.


 (** Applies cumulatively a function f to a list (a1.a2....an) **)
 (** Returns (f a1 (f a2 ... an))                              **) 

  Fixpoint fold_with_f (n : nat) (l : d_List n) (f : A -> A -> A) {struct l} 
     : 0 < n -> A :=
    match l in (d_list _ n) return (0 < n -> A) with
    | d_nil => fun h : 0 < 0 => False_rec A (lt_irrefl 0 h)
    | d_cons p a t =>
        fun _ : 0 < S p =>
        match zerop p with
        | left _ => a
        | right h => f a (fold_with_f t f h)
        end
    end.
 

 (** Flattens / destructures a list **)

  Fixpoint Unfold_List (n m : nat) (l : d_list (d_List n) m) {struct l} :
   d_List (m * n) :=
    match l in (d_list _ m) return (d_List (m * n)) with
    | d_nil => d_nil A
    | d_cons p a t => wcat a (Unfold_List t)
    end.


 (** Introduces a level in a list (the reverse of Unfold_List) **)

  Fixpoint Fold_List (n m : nat) {struct m} :
   d_List (m * n) -> d_list (d_List n) m :=
    match m return (d_List (m * n) -> d_list (d_List n) m) with
    | O => fun l : d_List 0 => d_nil (d_List n)
    | S p =>
        fun l : d_List (S p * n) =>
        d_cons (construct_with_i_first (i:=n) l (le_n_mult_S_n n p))
          (Fold_List (subst (minus_plus n (p * n)) (strip_off_first n l)))
    end.


End d_Lists_Compl.