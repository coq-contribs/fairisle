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
(*                             Fixed_dLists.v                               *)
(****************************************************************************)

Require Export dlist_Compl.
Require Export Syntactic_Def.
Require Export Proj_lists.


Set Implicit Arguments.
Unset Strict Implicit.


Section fixed_lists.

  Variable A : Set.

 (** Construction of fixed length lists **)

  Definition List2 (e1 e2 : A) := d_cons e1 (d_cons e2 (d_nil A)).

  Definition List3 (e1 e2 e3 : A) :=
    d_cons e1 (d_cons e2 (d_cons e3 (d_nil A))).

  Definition List4 (e1 e2 e3 e4 : A) :=
    d_cons e1 (d_cons e2 (d_cons e3 (d_cons e4 (d_nil A)))).



 (** Some (convenient) lemmas about fixed lenght lists **)

  Lemma id_list :
   forall e1 e2 e3 e4 e1' e2' e3' e4' : A,
   e1 = e1' ->
   e2 = e2' ->
   e3 = e3' -> e4 = e4' -> List4 e1 e2 e3 e4 = List4 e1' e2' e3' e4'.
  intros e1 e2 e3 e4 e1' e2' e3' e4' H0 H1 H2 H3.
  rewrite H0; rewrite H1; rewrite H2; rewrite H3; auto.
  Qed.

  Lemma id_list3 :
   forall e1 e2 e3 e1' e2' e3' : A,
   e1 = e1' -> e2 = e2' -> e3 = e3' -> List3 e1 e2 e3 = List3 e1' e2' e3'.
  intros e1 e2 e3 e1' e2' e3' H0 H1 H2.
  rewrite H0; rewrite H1; rewrite H2; auto.
  Qed.

  Lemma id_list3_fst :
   forall e1 e2 e3 e1' e2' e3' : A,
   List3 e1 e2 e3 = List3 e1' e2' e3' -> e1 = e1'.
  intros e1 e2 e3 e1' e2' e3' H; inversion H; try trivial.
  Qed.

  Lemma id_list3_scd :
   forall e1 e2 e3 e1' e2' e3' : A,
   List3 e1 e2 e3 = List3 e1' e2' e3' -> e2 = e2'.
  intros e1 e2 e3 e1' e2' e3' H; inversion H; try trivial.
  Qed.

  Lemma id_list3_thd :
   forall e1 e2 e3 e1' e2' e3' : A,
   List3 e1 e2 e3 = List3 e1' e2' e3' -> e3 = e3'.
  intros e1 e2 e3 e1' e2' e3' H; inversion H; try trivial.
  Qed.


  Lemma id_list' :
   forall e1 e2 e3 e4 e1' e2' e3' e4' : A,
   e1 = e1' ->
   e2 = e2' ->
   e3 = e3' ->
   e4 = e4' ->
   d_cons e1 (d_cons e2 (d_cons e3 (d_cons e4 (d_nil A)))) =
   d_cons e1' (d_cons e2' (d_cons e3' (d_cons e4' (d_nil A)))).
  intros e1 e2 e3 e4 e1' e2' e3' e4' H0 H1 H2 H3.
  rewrite H0; rewrite H1; rewrite H2; rewrite H3; auto.
  Qed.


  Lemma split_List2 :
   forall l : d_list A 2, l = List2 (Fst_of_l2 l) (Scd_of_l2 l).
  intro l.
  elim (non_empty l).
  intros x1 X1; elim X1; clear X1.
  intros x H.
  rewrite H.
  unfold List2 in |- *; unfold Fst_of_l2 in |- *; unfold Scd_of_l2 in |- *;
   unfold d_Head in |- *.
  simpl in |- *.
  rewrite (split_d_list x).
  simpl in |- *.
  replace (d_tl x) with (d_nil A); auto.
  Qed.
					
 
  Lemma fst_list2 : forall a b : A, a = Fst_of_l2 (List2 a b).
  auto.
  Qed.

  Lemma scd_list2 : forall a b : A, b = Scd_of_l2 (List2 a b).
  auto.
  Qed.
    
  Lemma List2_access :
   forall a b c d : A, List2 a b = List2 c d -> a = c /\ b = d.
  unfold List2 in |- *; intros a b c d H; split.
  replace a with (d_Head (d_cons a (d_cons b (d_nil A)))); auto.
  replace c with (d_Head (d_cons c (d_cons d (d_nil A)))); auto.
  rewrite H; auto.
  replace b with (d_Head (d_tl (d_cons a (d_cons b (d_nil A))))); auto.
  replace d with (d_Head (d_tl (d_cons c (d_cons d (d_nil A))))); auto.
  rewrite H; auto.
  Qed.


  Lemma split_List3 :
   forall l : d_list A 3, l = List3 (Fst_of_l3 l) (Scd_of_l3 l) (Thd_of_l3 l).
  intro l; elim (non_empty l).
  intros x1 X1; elim X1; clear X1.
  intros X1; elim (non_empty X1).
  intros x2 X2; elim X2; clear X2.
  intros X2; elim (non_empty X2).
  intros x3 X3; elim X3; clear X3.
  intros X3; replace X3 with (d_nil A); auto.
  intros H; rewrite H; clear H; intros H; rewrite H; clear H; intros H;
   rewrite H; auto.
  Qed.

  Lemma split_List4 :
   forall l : d_list A 4,
   l = List4 (Fst_of_l4 l) (Scd_of_l4 l) (Thd_of_l4 l) (Fth_of_l4 l).
  intro l.
  unfold List4 in |- *; unfold Fst_of_l3 in |- *; unfold Scd_of_l3 in |- *;
   unfold Thd_of_l3 in |- *; unfold Fth_of_l4 in |- *; 
   unfold d_Head in |- *.
  elim (non_empty l).
  intros x p.
  elim p; clear p; intros x0 p.
  rewrite p.
  simpl in |- *.
  elim (non_empty x0); intros x1 p0.
  elim p0; clear p0; intros x2 p0.
  rewrite p0; simpl in |- *.
  elim (non_empty x2); intros x3 p1.
  elim p1; clear p1; intros x4 p1.
  rewrite p1; simpl in |- *.
  elim (non_empty x4); intros x5 p2.
  elim p2; clear p2; intros x6 p2.
  rewrite p2; simpl in |- *.
  replace x6 with (d_nil A); auto.
  Qed.

End fixed_lists.


  Lemma List4_of_pdt :
   forall (A B : Set) (l : d_list (A * B) 4),
   l =
   List4 (fst (Fst_of_l4 l), snd (Fst_of_l4 l))
     (fst (Scd_of_l4 l), snd (Scd_of_l4 l))
     (fst (Thd_of_l4 l), snd (Thd_of_l4 l))
     (fst (Fth_of_l4 l), snd (Fth_of_l4 l)).
  intros A B l.
  elim (non_empty l).
  intros x t; elim t; clear t.
  intros t H.
  elim (non_empty t).
  intros x' H'; elim H'; clear H'.
  intros t' H'.
  elim (non_empty t').
  intros x'' H''; elim H''; clear H''.
  intros t'' H''.
  elim (non_empty t'').
  intros x''' H'''; elim H'''; clear H'''.
  intros t''' H'''.
  rewrite H; rewrite H'; rewrite H''; rewrite H'''; simpl in |- *.
  replace t''' with (d_nil (A * B)); auto.
  unfold Scd_of_l4 in |- *; unfold Thd_of_l4 in |- *;
   unfold Fth_of_l4 in |- *; unfold List4 in |- *; 
   simpl in |- *.
  elim x; elim x'; elim x''; elim x'''; simpl in |- *; auto.
  Qed.


Definition List2_pdt (A : Set) (l : d_list A 2) := (Fst_of_l2 l, Scd_of_l2 l).

Definition pdt_List2 (A : Set) (p : A * A) := List2 (fst p) (snd p).


 CoFixpoint Compact_dlist (A : Set) (s1 s2 : Stream A) :
  Stream (d_list A 2) :=
   S_cons (List2 (S_head s1) (S_head s2))
     (Compact_dlist (S_tail s1) (S_tail s2)).


Lemma List4_map :
 forall (A B : Set) (l : d_list A 4) (f : A -> B),
 List4 (f (d_Head l)) (f (d_Head (d_tl l))) (f (d_Head (d_tl (d_tl l))))
   (f (d_Head (d_tl (d_tl (d_tl l))))) = d_map f l.
  intros A B l f.
  elim (non_empty l).
  intros x0 H0; elim H0; clear H0.
  intros X0 XH0; rewrite XH0; clear XH0.
  elim (non_empty X0).
  intros x1 H1; elim H1; clear H1.
  intros X1 XH1; rewrite XH1; clear XH1.
  elim (non_empty X1).
  intros x2 H2; elim H2; clear H2.
  intros X2 XH2; rewrite XH2; clear XH2.
  elim (non_empty X2).
  intros x3 H3; elim H3; clear H3.
  intros X3 XH3; rewrite XH3; clear XH3.
  unfold List4 in |- *; simpl in |- *.
  replace X3 with (d_nil A); auto.
  Qed.


Lemma eq_List4_map :
 forall (A B : Set) (l k : d_list A 4) (f g : A -> B),
 List4 (f (d_Head l)) (f (d_Head (d_tl l))) (f (d_Head (d_tl (d_tl l))))
   (f (d_Head (d_tl (d_tl (d_tl l))))) =
 List4 (g (d_Head k)) (g (d_Head (d_tl k))) (g (d_Head (d_tl (d_tl k))))
   (g (d_Head (d_tl (d_tl (d_tl k))))) -> d_map f l = d_map g k.
  intros A B l k f g.
  rewrite List4_map; rewrite List4_map; auto.
  Qed.


Lemma tls_simpl :
 forall (A : Set) (a b : Stream A),
 tls (List2 a b) = List2 (S_tail a) (S_tail b).
auto.
Qed.


Lemma Eq_dlist_to_Stream_List4 :
 forall (A : Set) (s1 s1' s2 s2' s3 s3' s4 s4' : Stream A),
 EqS s1 s1' ->
 EqS s2 s2' ->
 EqS s3 s3' ->
 EqS s4 s4' ->
 EqS (dlist_to_Stream (List4 s1 s2 s3 s4))
   (dlist_to_Stream (List4 s1' s2' s3' s4')).
 cofix.
 intros A s1 s1' s2 s2' s3 s3' s4 s4' H1 H2 H3 H4.
 inversion_clear H1; inversion_clear H2; inversion_clear H3;
  inversion_clear H4.
 apply eqS; simpl in |- *.
 unfold hds in |- *; simpl in |- *.
 elim H; elim H1; elim H2; elim H3; try trivial.
 unfold tls in |- *; simpl in |- *.
 unfold List4 in Eq_dlist_to_Stream_List4; apply Eq_dlist_to_Stream_List4;
  auto.
 Qed.


Lemma S_map_Fst_of_l4 :
 forall (A : Set) (s1 s2 s3 s4 : Stream A),
 EqS (S_map (Fst_of_l4 (A:=A)) (dlist_to_Stream (List4 s1 s2 s3 s4))) s1.
cofix.
intros A s1 s2 s3 s4.
apply eqS; simpl in |- *; auto.
unfold tls in |- *; simpl in |- *.
unfold List4 in S_map_Fst_of_l4; auto.
Qed.

Lemma S_map_Scd_of_l4 :
 forall (A : Set) (s1 s2 s3 s4 : Stream A),
 EqS (S_map (Scd_of_l4 (A:=A)) (dlist_to_Stream (List4 s1 s2 s3 s4))) s2.
cofix.
intros A s1 s2 s3 s4.
apply eqS; simpl in |- *; auto.
unfold tls in |- *; simpl in |- *.
unfold List4 in S_map_Scd_of_l4; auto.
Qed.

Lemma S_map_Thd_of_l4 :
 forall (A : Set) (s1 s2 s3 s4 : Stream A),
 EqS (S_map (Thd_of_l4 (A:=A)) (dlist_to_Stream (List4 s1 s2 s3 s4))) s3.
cofix.
intros A s1 s2 s3 s4.
apply eqS; simpl in |- *; auto.
unfold tls in |- *; simpl in |- *.
unfold List4 in S_map_Thd_of_l4; auto.
Qed.

Lemma S_map_Fth_of_l4 :
 forall (A : Set) (s1 s2 s3 s4 : Stream A),
 EqS (S_map (Fth_of_l4 (A:=A)) (dlist_to_Stream (List4 s1 s2 s3 s4))) s4.
cofix.
intros A s1 s2 s3 s4.
apply eqS; simpl in |- *; auto.
unfold tls in |- *; simpl in |- *.
unfold List4 in S_map_Fth_of_l4; auto.
Qed.

Lemma simplification1 :
 forall (A : Set) (s1 s2 s3 : Stream (d_list A 2)),
 hds (tls (List3 (S_Fst_of_l2 s1) (S_Scd_of_l2 s2) (S_Fst_of_l2 s3))) =
 List3 (Fst_of_l2 (S_head (S_tail s1))) (Scd_of_l2 (S_head (S_tail s2)))
   (Fst_of_l2 (S_head (S_tail s3))).
auto.
Qed.


Lemma simplification2 :
 forall (A : Set) (s1 s2 s3 s4 : Stream (d_list A 2)),
 three_fst_of_l4
   (hds
      (tls
         (List4 (S_Fst_of_l2 s1) (S_Scd_of_l2 s2) (S_Fst_of_l2 s3)
            (S_Scd_of_l2 s4)))) =
 List3 (Fst_of_l2 (S_head (S_tail s1))) (Scd_of_l2 (S_head (S_tail s2)))
   (Fst_of_l2 (S_head (S_tail s3))).
auto.
Qed.


Lemma simplification3 :
 forall (A : Set) (s1 s2 s3 : Stream (d_list A 2)),
 tls (tls (List3 (S_Fst_of_l2 s1) (S_Scd_of_l2 s2) (S_Fst_of_l2 s3))) =
 List3 (S_Fst_of_l2 (S_tail (S_tail s1))) (S_Scd_of_l2 (S_tail (S_tail s2)))
   (S_Fst_of_l2 (S_tail (S_tail s3))).
auto.
Qed.


Lemma Unfold_tls_4 :
 forall (A : Set) (a b c d : Stream A),
 tls (d_cons a (d_cons b (d_cons c (d_cons d (d_nil (Stream A)))))) =
 d_cons (S_tail a)
   (d_cons (S_tail b)
      (d_cons (S_tail c) (d_cons (S_tail d) (d_nil (Stream A))))).
 unfold tls in |- *; simpl in |- *; auto.
 Qed.



Definition transf (A : Set) (s : Stream (d_list A 4)) :=
  Compact (Compact (S_map (Fst_of_l4 (A:=A)) s) (S_map (Scd_of_l4 (A:=A)) s))
    (Compact (S_map (Thd_of_l4 (A:=A)) s) (S_map (Fth_of_l4 (A:=A)) s)).


Lemma transf_simpl :
 forall (A : Set) (s1 s2 s3 s4 : Stream A),
 EqS (transf (dlist_to_Stream (List4 s1 s2 s3 s4)))
   (Compact (Compact s1 s2) (Compact s3 s4)).
cofix.
intros A s1 s2 s3 s4.
apply eqS; simpl in |- *.
unfold hds in |- *; simpl in |- *.
unfold Scd_of_l4 in |- *; unfold Thd_of_l4 in |- *; unfold Fth_of_l4 in |- *;
 simpl in |- *; auto.
unfold tls in |- *; simpl in |- *.
unfold List4 in transf_simpl; unfold transf in transf_simpl.
auto.
Qed.


Lemma EqS_transf :
 forall (A : Set) (s1 s2 : Stream (d_list A 4)),
 EqS s1 s2 -> EqS (transf s1) (transf s2).
cofix.
intros A s1 s2 H.
inversion_clear H.
apply eqS; simpl in |- *.
elim H0; auto.
unfold transf in EqS_transf; auto.
Qed.


(* Because of the ways of giving the initial values of the registers and of *)
(* defining initial states are different *)
Definition transf1 (A : Set) (p : d_list (A * A) 4 * d_list A 4) :=
  let (g, o) := p in
  List4 (List3 (fst (Fst_of_l4 g)) (snd (Fst_of_l4 g)) (Fst_of_l4 o))
    (List3 (fst (Scd_of_l4 g)) (snd (Scd_of_l4 g)) (Scd_of_l4 o))
    (List3 (fst (Thd_of_l4 g)) (snd (Thd_of_l4 g)) (Thd_of_l4 o))
    (List3 (fst (Fth_of_l4 g)) (snd (Fth_of_l4 g)) (Fth_of_l4 o)).


(* Because of the type of the structural representation *)
Definition transf2 (A : Set) (q : A * (A * (A * A))) :=
  let (q1, t) := q in
  let (q2, p) := t in let (q3, q4) := p in List4 q1 q2 q3 q4.


(* Because of the parallel composition of TWO_ARBITERS, we have a term of *)
(* type (A*B)*(C*D) but we need of a term of type A*B*C*D *)
Definition transf3 (A B C D : Set) (l : Stream (A * B * (C * D))) :=
  Compact (S_map fstS (S_map fstS l))
    (Compact (S_map sndS (S_map fstS l))
       (Compact (S_map fstS (S_map sndS l))
          (S_map sndS (S_map sndS l)))).
  

Lemma equiv1 :
 forall
   l
    l' : Stream
           (d_list bool 3 * d_list bool 3 * (d_list bool 3 * d_list bool 3)),
 EqS l l' ->
 EqS (S_map (transf2 (A:=d_list bool 3)) (transf3 l'))
   (S_map (transf2 (A:=d_list bool 3)) (transf3 l)).
  cofix.
  intros.
  apply eqS; simpl in |- *.
  inversion_clear H.
  elim H0; try trivial.
  unfold transf3 in equiv1.
  apply equiv1.
  inversion_clear H; try trivial.
  Qed.
 


Definition transf4 (A : Set) (p : A * A * (A * A)) : 
  d_list A 4 :=
  let (a1, a2) := p in
  let (a11, a12) := a1 in let (a21, a22) := a2 in List4 a11 a12 a21 a22.


Lemma equiv2 :
 forall (A : Set) (s1 s1' s2 s2' s3 s3' s4 s4' : Stream A),
 EqS s1 s1' ->
 EqS s2 s2' ->
 EqS s3 s3' ->
 EqS s4 s4' ->
 EqS (dlist_to_Stream (List4 s1 s2 s3 s4))
   (dlist_to_Stream (List4 s1' s2' s3' s4')).
 cofix.
 intros A s1 s1' s2 s2' s3 s3' s4 s4' H1 H2 H3 H4.
 inversion_clear H1; inversion_clear H2; inversion_clear H3;
  inversion_clear H4.
 apply eqS; simpl in |- *.
 unfold hds in |- *; simpl in |- *.
 elim H; elim H1; elim H2; elim H3; try trivial.
 unfold tls in |- *; simpl in |- *.
 unfold List4 in equiv2; apply equiv2; auto.
 Qed.


Definition Two_Fst_of_l4' (A : Set) (l : d_list A 4) :=
  List2 (Fst_of_l4 l) (Scd_of_l4 l).

Definition Two_last_of_l4' (A : Set) (l : d_list A 4) :=
  List2 (Thd_of_l4 l) (Fth_of_l4 l).

Definition Two_fst_of_l3 (A : Set) (l : d_list A 3) :=
  List2 (Fst_of_l3 l) (Scd_of_l3 l).

Definition Two_last_of_l3 (A : Set) (l : d_list A 3) :=
  List2 (Scd_of_l3 l) (Thd_of_l3 l).


Notation Two_List2_List4 :=
  (fun (A : Set) (l1 l2 : d_list A 2) =>
   List4 (Fst_of_l2 l1) (Scd_of_l2 l1) (Fst_of_l2 l2) (Scd_of_l2 l2))
  (only parsing).


Definition Pdt_List4_List3 (A : Set) (a1 a2 a3 a4 : A * A) 
  (a : A) :=
  List4 (List3 (fst a1) (snd a1) a) (List3 (fst a2) (snd a2) a)
    (List3 (fst a3) (snd a3) a) (List3 (fst a4) (snd a4) a).


Definition List4_transf (A : Set) (a : d_list (A * A) 4) :=
  Pdt_List4_List3 (Fst_of_l4 a) (Scd_of_l4 a) (Thd_of_l4 a) (Fth_of_l4 a).


Definition transf_List4_List3 (A : Set) (a1 a2 : d_list (A * A) 2) 
  (a : A) :=
  List4 (List3 (fst (Fst_of_l2 a1)) (snd (Fst_of_l2 a1)) a)
    (List3 (fst (Scd_of_l2 a1)) (snd (Scd_of_l2 a1)) a)
    (List3 (fst (Fst_of_l2 a2)) (snd (Fst_of_l2 a2)) a)
    (List3 (fst (Scd_of_l2 a2)) (snd (Scd_of_l2 a2)) a).