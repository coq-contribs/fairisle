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
(*                                Product.v                                 *)
(****************************************************************************)


Set Implicit Arguments.
Unset Strict Implicit.


Lemma pair_eq :
 forall (A B : Set) (p1 p1' : A) (p2 p2' : B),
 p1 = p1' -> p2 = p2' -> (p1, p2) = (p1', p2').
intros A B p1 p1' p2 p2' H1 H2; rewrite H1; rewrite H2; auto.
Qed.

Lemma eq_pair :
 forall (A B : Set) (p1 p1' : A) (p2 p2' : B),
 (p1, p2) = (p1', p2') -> p1 = p1' /\ p2 = p2'.
intros A B p1 p1' p2 p2' H; inversion H; auto.
Qed.


Lemma triplet_simpl :
 forall (A B C : Set) (x : A * (B * C)) (P : B -> Prop),
 P (fst (snd x)) ->
 let (_, p) return Prop := x in let (b, _) return Prop := p in P b.
intros A B C x P.
elim x.
intros y y0; elim y0; auto.
Qed.

Lemma Rewrite_Fst : forall (A B : Set) (a : A) (b : B), fst (a, b) = a.
auto.
Qed.

Lemma Rewrite_Snd : forall (A B : Set) (a : A) (b : B), snd (a, b) = b.
auto.
Qed.
