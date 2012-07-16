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
(*                              Injections.v                                *)
(****************************************************************************)


Global Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.

Definition Inj1 (A : Set) (P : A -> Prop) (e : {x : A | P x}) :=
  match e with
  | exist a _ => a
  end.

Definition Inj2 (A : Set) (P : A -> Prop) (e : {x : A | P x}) :=
  let (a, _) return Prop := e in P a.