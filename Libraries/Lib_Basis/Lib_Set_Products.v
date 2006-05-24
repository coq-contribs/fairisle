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
(*                           Lib_Set_Products.v                             *)
(****************************************************************************)


Lemma pair_fst_snd : forall (A B : Set) (c : A * B), (fst c, snd c) = c.
intros.
pattern c in |- *; elim c; auto.
Qed.


Inductive prod_3 (A B C : Set) : Set :=
    triplet : A -> B -> C -> prod_3 A B C.

Section programming_3.
        
Variable A B C : Set.

Lemma fst_3 : prod_3 A B C -> A.
simple induction 1; try trivial.
Defined.
Transparent fst_3.

Lemma snd_3 : prod_3 A B C -> B.
simple induction 1; try trivial.
Defined.
Transparent snd_3.

Lemma thd_3 : prod_3 A B C -> C.
simple induction 1; try trivial.
Defined.
Transparent thd_3.

End programming_3.

Notation Fst_3 := (fst_3 _ _ _) (only parsing).
Notation Snd_3 := (snd_3 _ _ _) (only parsing).
Notation Thd_3 := (thd_3 _ _ _) (only parsing).
Notation Triplet := (triplet _ _ _) (only parsing).



Lemma triplet_fst_snd_thd :
 forall (A B C : Set) (c : prod_3 A B C),
 triplet _ _ _ (fst_3 _ _ _ c) (snd_3 _ _ _ c) (thd_3 _ _ _ c) = c.
intros.
pattern c in |- *; elim c; auto.
Qed.


Definition ifProp (C : Type) (b : bool) (x y : C) : C :=
  match b return C with
  | true => x
  | false => y
  end.

Lemma ifProp_or : forall (b : bool) (P Q : Prop), ifProp Prop b P Q -> P \/ Q.
simple induction b; auto.
Qed.
