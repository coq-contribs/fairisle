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
(*                             Infinite_lists.v                             *)
(****************************************************************************)

Require Export Lists_of_lists.
Require Export Dependent_lists_Compl.


Set Implicit Arguments.
Unset Strict Implicit.


Section Infinite_List.

  Variable A B : Set.

  CoInductive Stream : Set :=
      S_cons : A -> Stream -> Stream.

  Definition S_head (l : Stream) : A := match l with
                                        | S_cons a _ => a
                                        end.

  Definition S_tail (l : Stream) : Stream :=
    match l with
    | S_cons _ tl => tl
    end.


  CoInductive EqS : Stream -> Stream -> Prop :=
      eqS :
        forall l l' : Stream,
        S_head l = S_head l' -> EqS (S_tail l) (S_tail l') -> EqS l l'.

End Infinite_List.


(* Some mappings on Streams **)

CoFixpoint S_map (A B : Set) (f : A -> B) (s : Stream A) : 
 Stream B := S_cons (f (S_head s)) (S_map f (S_tail s)).


CoFixpoint S_map2 (A B C : Set) (f : A -> B -> C) (l1 : Stream A)
 (l2 : Stream B) : Stream C :=
  S_cons (f (S_head l1) (S_head l2)) (S_map2 f (S_tail l1) (S_tail l2)).


CoFixpoint S_map3 (A B C D : Set) (f : A -> B -> C -> D) 
 (l1 : Stream A) (l2 : Stream B) (l3 : Stream C) : 
 Stream D :=
  S_cons (f (S_head l1) (S_head l2) (S_head l3))
    (S_map3 f (S_tail l1) (S_tail l2) (S_tail l3)).


CoFixpoint S_map4 (A B C D E : Set) (f : A -> B -> C -> D -> E)
 (l1 : Stream A) (l2 : Stream B) (l3 : Stream C) (l4 : Stream D) :
 Stream E :=
  S_cons (f (S_head l1) (S_head l2) (S_head l3) (S_head l4))
    (S_map4 f (S_tail l1) (S_tail l2) (S_tail l3) (S_tail l4)).


(** Infinite lists which all elements are the same **)

CoFixpoint all_same (A : Set) (v : A) : Stream A := S_cons v (all_same v).


(** A stream of 0 **)

Definition zeros : Stream nat := all_same 0.

(** A stream of false and a stream of true values **)

Definition sig_false : Stream bool := all_same false.

Definition sig_true : Stream bool := all_same true.


(** All heads of a dlist of streams **)
Definition hds (A : Set) := d_map (S_head (A:=A)).

(** All tails of a dlist of streams **)
Definition tls (A : Set) := d_map (S_tail (A:=A)).


(** All heads of a stream of dlist **)

Definition S_hds (A : Set) (n : nat) := S_map (d_Head (A:=A) (n:=n)).

(** All tails of a stream of dlist **)

Definition S_tls (A : Set) (n : nat) := S_map (d_tl (A:=A) (n:=n)).


(** Applies a function g to an infinite dlist taking all heads, **)
(** heads of tail... (g h0 h1...hn) **)

CoFixpoint MAP_g (A B : Set) (n : nat) (g : d_list A n -> B)
 (l : d_list (Stream A) n) : Stream B := S_cons (g (hds l)) (MAP_g g (tls l)).


(** Applies a function g to each element of heads, heads of tail... **)
(** ((g h0).(g h1).....(g hn)) **)

CoFixpoint MAP_map_g (A B : Set) (n m : nat) (g : d_list A n -> B)
 (l : d_list (Stream (d_list A n)) m) : Stream (d_list B m) :=
  S_cons (d_map g (hds l)) (MAP_map_g g (tls l)).


(** Transforms a dlist of streams in a stream of dlists **)

CoFixpoint dlist_to_Stream (A : Set) (n : nat) (l : d_list (Stream A) n) :
 Stream (d_list A n) := S_cons (hds l) (dlist_to_Stream (tls l)).


(** Transforms a stream of dlists in a dlist of streams **)

Fixpoint Stream_to_dlist (A : Set) (n : nat) {struct n} :
 Stream (d_list A n) -> d_list (Stream A) n :=
  match n return (Stream (d_list A n) -> d_list (Stream A) n) with
  | O => fun _ : Stream (d_list A 0) => d_nil (Stream A)
  | S p =>
      fun s : Stream (d_list A (S p)) =>
      d_cons (S_hds s) (Stream_to_dlist (S_tls s))
  end.
 

(** Transforms a dlist of dlists of streams in a dlist of streams of dlists **)

Definition dmap_dlist_to_Stream (A : Set) (n : nat) :=
  d_map (dlist_to_Stream (A:=A) (n:=n)).


(** Transforms a dlist of streams of dlists in a dlist of dlist of streams **)

Definition dmap_Stream_to_dlist (A : Set) (n : nat) :=
  d_map (Stream_to_dlist (A:=A) (n:=n)).


Lemma EqS_trans :
 forall (A : Set) (s1 s2 s3 : Stream A), EqS s1 s2 -> EqS s2 s3 -> EqS s1 s3.
cofix u.
intros.
apply eqS.
transitivity (S_head s2).
case H.
intros.
assumption. 
case H0.
intros.
assumption.
apply (u A (S_tail s1) (S_tail s2) (S_tail s3)).
case H.
intros.
assumption.
case H0.
intros.
assumption.
Qed.


Lemma EqS_reflex : forall (A : Set) (s : Stream A), EqS s s.
cofix u.
intros.
apply eqS.
trivial.
apply u.
Qed. 


Lemma EqS_sym : forall (A : Set) (s s' : Stream A), EqS s s' -> EqS s' s.
cofix u.
intros.
case H.
intros.
apply eqS.
symmetry  in |- *.
assumption.
apply u.
assumption.
Qed.


Lemma S_map_id :
 forall (A : Set) (id : A -> A) (s : Stream A),
 (forall a : A, id a = a) -> EqS s (S_map id s).
cofix.
intros A id s H.
apply eqS; simpl in |- *; auto.
Qed.


Lemma S_map_f :
 forall (A B : Set) (f : A -> B) (s s' : Stream A),
 EqS s s' -> EqS (S_map f s) (S_map f s').
cofix.
intros A B f s s' H.
inversion_clear H.
apply eqS; simpl in |- *.
elim H0; auto.
auto.
Qed.


(** Definition of an equality for dlists of streams **)

Inductive eq_dlist_of_Stream (A : Set) :
forall n : nat, d_list (Stream A) n -> d_list (Stream A) n -> Prop :=
  | eq4_LSO : forall l l' : d_list (Stream A) 0, eq_dlist_of_Stream l l'
  | eq4_LS1 :
      forall (n : nat) (l l' : d_list (Stream A) (S n)),
      EqS (d_Head l) (d_Head l') ->
      eq_dlist_of_Stream (d_tl l) (d_tl l') -> eq_dlist_of_Stream l l'.


(** Tools over streams of dlists **)

(** Returns a stream containing all the ith elements **)

Definition S_Nth (A : Set) (i n : nat) (H : 0 < i) 
  (H' : i <= n) := S_map (nth (A:=A) (i:=i) (n:=n) H H').


(** Returns a stream containing all the specified segments **)

Definition S_Seg (A : Set) (n m k : nat) (H : 0 < n) 
  (H' : m <= k) (H'' : n <= m) :=
  S_map (seg (A:=A) (n:=n) (m:=m) (k:=k) H H' H'').


(** Returns a stream containing the dlists with the ith element removed **)
  
Definition S_Remove_i (A : Set) (n i : nat) (H : 0 < i) 
  (H' : i <= n) := S_map (Remove_i (A:=A) (i:=i) H (n:=n) H').


(** Returns a stream containing the dlists flattened **)

Definition S_Unfold_List (A : Set) (n m : nat) :=
  S_map (Unfold_List (A:=A) (n:=n) (m:=m)).


(** Returns a stream containing the dlists structured **) 

Definition S_Fold_List (A : Set) (n m : nat) :=
  S_map (Fold_List (A:=A) (n:=n) (m:=m)).


(** Returns a stream containing all the nth elements of the sublists **)

Definition S_list_of_nth (A : Set) (i n m : nat) (H : 0 < i) 
  (H' : i <= n) := S_map (list_of_nth (A:=A) (i:=i) (n:=n) H H' (n0:=m)).


(** Returns a stream containing all the specified segments of the sublists **)

Definition S_list_of_seg (A : Set) (n m k p : nat) 
  (H : 0 < n) (H' : m <= k) (H'' : n <= m) :=
  S_map (list_of_seg (A:=A) (n:=n) (m:=m) (k:=k) H H' H'' (n0:=p)).



(** Tools over streams of products **)

Definition fstS {A B : Set} : prod A B -> A := fst.
Definition sndS {A B : Set} : prod A B -> B := snd.

Notation S_Fst := (S_map (fstS (B:=_))) (only parsing).
Notation S_Snd := (S_map (sndS (B:=_))) (only parsing).

Definition S_Snd_of_3 (A B C : Set) (s : Stream (A * (B * C))) :=
  S_map fstS (S_map sndS s).
Definition S_Thd_of_3 (A B C : Set) (s : Stream (A * (B * C))) :=
  S_map sndS (S_map sndS s).
Definition S_Snd_of_4 (A B C D : Set) (s : Stream (A * (B * (C * D)))) :=
  S_map fstS (S_map sndS s).
Definition S_Thd_of_4 (A B C D : Set) (s : Stream (A * (B * (C * D)))) :=
  S_map fstS (S_map sndS (S_map sndS s)).
Definition S_Fth_of_4 (A B C D : Set) (s : Stream (A * (B * (C * D)))) :=
  S_map sndS (S_map sndS (S_map sndS s)).

Lemma EqS_S_Thd_of_3 :
 forall (A B C : Set) (s s' : Stream (A * (B * C))),
 EqS s s' -> EqS (S_Thd_of_3 s) (S_Thd_of_3 s').
cofix.
intros.
inversion_clear H.
apply eqS; simpl in |- *.
rewrite H0; auto.
unfold S_Thd_of_3 in EqS_S_Thd_of_3; auto.
Qed.

Lemma EqS_S_Snd_of_3 :
 forall (A B C : Set) (s s' : Stream (A * (B * C))),
 EqS s s' -> EqS (S_Snd_of_3 s) (S_Snd_of_3 s').
cofix.
intros.
inversion_clear H.
apply eqS; simpl in |- *.
rewrite H0; auto.
unfold S_Snd_of_3 in EqS_S_Snd_of_3; auto.
Qed.



CoFixpoint Compact (A B : Set) (s1 : Stream A) (s2 : Stream B) :
 Stream (A * B) :=
  S_cons (S_head s1, S_head s2) (Compact (S_tail s1) (S_tail s2)).


CoFixpoint S_Fst_pdt (A B : Set) (s : Stream (A * B)) : 
 Stream A := S_cons (fst (S_head s)) (S_Fst_pdt (S_tail s)).


CoFixpoint S_Snd_pdt (A B : Set) (s : Stream (A * B)) : 
 Stream B := S_cons (snd (S_head s)) (S_Snd_pdt (S_tail s)).


Definition UnCompact (A B : Set) (s : Stream (A * B)) :
  Stream A * Stream B := (S_Fst_pdt s, S_Snd_pdt s).


Definition S_Two_Fst (A B C : Set) (s : Stream (A * (B * C))) :
  Stream (A * B) := Compact (S_Fst_pdt s) (S_Fst_pdt (S_Snd_pdt s)).


Lemma EqS_Compact :
 forall (A B : Set) (s1 s1' : Stream A) (s2 s2' : Stream B),
 EqS s1 s1' -> EqS s2 s2' -> EqS (Compact s1 s2) (Compact s1' s2').
cofix.
intros A B s1 s1' s2 s2' H1 H2.
inversion_clear H1; inversion_clear H2.
apply eqS; simpl in |- *.
elim H; elim H1; auto.
apply EqS_Compact; auto.
Qed.


Lemma Fst_Compact :
 forall (A B : Set) (s1 : Stream A) (s2 : Stream B),
 EqS (S_map fstS (Compact s1 s2)) s1.
cofix.
intros A B s1 s2.
apply eqS; simpl in |- *; auto.
Qed.

Lemma Snd_Compact :
 forall (A B : Set) (s1 : Stream A) (s2 : Stream B),
 EqS (S_map sndS (Compact s1 s2)) s2.
cofix.
intros A B s1 s2.
apply eqS; simpl in |- *; auto.
Qed.

Lemma S_Snd_of_3_Compact :
 forall (A B C : Set) (s1 : Stream A) (s2 : Stream B) (s3 : Stream C),
 EqS (S_Snd_of_3 (Compact s1 (Compact s2 s3))) s2.
cofix.
intros A B C s1 s2 s3.
apply eqS; simpl in |- *; auto.
unfold S_Snd_of_3 in S_Snd_of_3_Compact; auto.
Qed.

Lemma S_Thd_of_3_Compact :
 forall (A B C : Set) (s1 : Stream A) (s2 : Stream B) (s3 : Stream C),
 EqS (S_Thd_of_3 (Compact s1 (Compact s2 s3))) s3.
cofix.
intros A B C s1 s2 s3.
apply eqS; simpl in |- *; auto.
unfold S_Thd_of_3 in S_Thd_of_3_Compact; auto.
Qed.


(** Some convenient lemmas to avoid a complete simplication (with Simpl) **)
(** during proofs **)

Lemma S_tail_S_map :
 forall (A B : Set) (f : A -> B) (s : Stream A),
 S_tail (S_map f s) = S_map f (S_tail s).
auto.
Qed.

Lemma S_head_S_map :
 forall (A B : Set) (f : A -> B) (s : Stream A),
 S_head (S_map f s) = f (S_head s).
auto.
Qed.


Lemma S_tail_dlist_to_Stream :
 forall (A : Set) (n : nat) (l : d_list (Stream A) n),
 S_tail (dlist_to_Stream l) = dlist_to_Stream (tls l).
auto.
Qed.

Lemma S_tail_Compact :
 forall (A B : Set) (s1 : Stream A) (s2 : Stream B),
 S_tail (Compact s1 s2) = Compact (S_tail s1) (S_tail s2).
auto.
Qed.

Lemma S_head_Compact :
 forall (A B : Set) (s1 : Stream A) (s2 : Stream B),
 S_head (Compact s1 s2) = (S_head s1, S_head s2).
auto.
Qed.

