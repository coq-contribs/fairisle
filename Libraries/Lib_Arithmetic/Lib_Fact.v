(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                Solange Coupet-Grimal & Line Jakubiec-Jamet               *)
(*                                                                          *)
(*                                                                          *)
(*             Laboratoire d'Informatique Fondamentale de Marseille         *)
(*                   CMI et Facult� des Sciences de Luminy                  *)
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
(*                                Lib_Fact.v                                *)
(****************************************************************************)

Require Export Arith.


Fixpoint factorial (n : nat) : nat :=
  match n return nat with
  | O => 1
  | S p => S p * factorial p
  end.



Lemma fact_pred :
 forall n : nat, 0 < n -> factorial n = n * factorial (pred n).
simple induction n; auto with arith.
Qed.
Hint Immediate fact_pred.