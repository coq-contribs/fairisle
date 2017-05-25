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
(*                               PortsCompl.v                               *)
(****************************************************************************)

Require Export Injections.
Require Export TypePorts.
Require Export Lib_Dec.
Require Export Syntactic_Def.
Require Export Fixed_dLists.


Set Implicit Arguments.
Unset Strict Implicit.

Section Definitions_and_lemmas_about_ports.

  Variable i o : nat. (* Number of inputs and outputs *)

  Let Inportno := T_Inportno i.
  Let Outportno := T_Outportno o. 

  Definition no_out : Outportno -> nat :=
    Inj1 (A:=nat) (P:=fun p : nat => p < o).
  Definition no_in : Inportno -> nat :=
    Inj1 (A:=nat) (P:=fun p : nat => p < i).
  Definition proof_out : Outportno -> Prop :=
    Inj2 (A:=nat) (P:=fun n : nat => n < o).
  Definition proof_in : Inportno -> Prop :=
    Inj2 (A:=nat) (P:=fun n : nat => n < i).
  
  Lemma lt_no_in_i : forall x : Inportno, no_in x < i.
  simple induction x; simpl in |- *; auto.
  Qed.
  Hint Immediate lt_no_in_i.

  Lemma lt_no_out_o : forall x : Outportno, no_out x < o.
  simple induction x; simpl in |- *; auto.
  Qed.

  Lemma proof_inportno : forall x : Inportno, proof_in x.
  simple induction x; simpl in |- *; auto.
  Qed.

  Lemma proof_outportno : forall x : Outportno, proof_out x.
  simple induction x; simpl in |- *; auto.
  Qed.

  Lemma less_or_eq :
   forall inp : Inportno, {S (no_in inp) < i} + {S (no_in inp) = i}.
  intros inp.
  apply le_lt_eq_dec; auto with arith.
  Qed.
  

End Definitions_and_lemmas_about_ports.


(** Translates a port number to its corresponding encoding as a length-2 list **)

Definition Convert_port_list2 (no : T_Inportno 4) :=
  match no_in no with
  | O => List2 false false
  | S p =>
      match p with
      | O => List2 false true
      | S q =>
          match q with
          | O => List2 true false
          | _ => List2 true true
          end
      end
  end.


Definition Convert_port_list2_bis (no : T_Inportno 4) :=
  let (n, P) return (d_list bool 2) := no in
  match n with
  | O => List2 false false
  | S p =>
      match p with
      | O => List2 false true
      | S q =>
          match q with
          | O => List2 true false
          | _ => List2 true true
          end
      end
  end.


(** The same as above but more precisely (and more complicated) **)

Definition Convert_port_list2_ter (p : T_Inportno 4) :=
  let (n, x) return (d_list bool 2) := p in
  match n return (n < 4 -> d_list bool 2) with
  | O => fun _ : 0 < 4 => List2 false false
  | S q =>
      match q return (S q < 4 -> d_list bool 2) with
      | O => fun _ : 1 < 4 => List2 false true
      | S r =>
          match r return (S (S r) < 4 -> d_list bool 2) with
          | O => fun _ : 2 < 4 => List2 true false
          | S s =>
              match s return (S (S (S s)) < 4 -> d_list bool 2) with
              | O => fun _ : 3 < 4 => List2 true true
              | S t =>
                  fun h : S (S (S (S t))) < 4 =>
                  False_rec (d_list bool 2) (not_lt_4 h)
              end
          end
      end
  end x.


(** Translates a length-2 list to its corresponding encoding as a port number  **)

Definition Convert_list2_port (l : d_list bool 2) :=
  match d_Head l return (T_Inportno 4) with
  | true =>
      match d_Head (d_tl l) with
      | true => exist (fun p : nat => p < 4) 3 lt_3_4
      | false => exist (fun p : nat => p < 4) 2 lt_2_4
      end
  | false =>
      match d_Head (d_tl l) with
      | true => exist (fun p : nat => p < 4) 1 lt_1_4
      | false => exist (fun p : nat => p < 4) 0 lt_O_4
      end
  end.



(** Translates a port numbers less than 4 list to the corresponding **)
(** list of length 4 containing length-2 boolean lists              **)

Definition list_no_port_bool (l : d_list (T_Inportno 4) 4) :
  d_list (d_list bool 2) 4 := d_map Convert_port_list2 l.


