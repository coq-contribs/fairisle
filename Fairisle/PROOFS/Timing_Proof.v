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
(*                              Timing_Proof.v                              *)
(****************************************************************************)


Require Export Arbitration.
Require Export Bool_Compl.
Require Export Moore_Mealy.


Set Implicit Arguments.
Unset Strict Implicit.


Section Timing_Correctness.

  Let Input_type := (bool * d_list bool 4)%type.

  Let Output_type := bool.


(** The automaton describing the behaviour of TIMING has 3 states **)

  Inductive label_t : Set :=
    | START_t : label_t
    | WAIT_t : label_t
    | ROUTE_t : label_t. 



(** Automaton describing the transitions from a state to another **)

  Definition Trans_Timing (i : Input_type) (s : label_t) : label_t :=
    let (fs, act) := i in
    match s with
    | START_t => match fs with
                 | true => WAIT_t
                 | false => START_t
                 end
    | WAIT_t =>
        match Ackor act with
        | true => match fs with
                  | true => WAIT_t
                  | false => ROUTE_t
                  end
        | false => WAIT_t
        end
    | ROUTE_t => match fs with
                 | true => WAIT_t
                 | false => START_t
                 end
    end.


(** Each label_t corresponds to a result **)

  Definition Out_Timing (s : label_t) : Output_type :=
    match s with
    | START_t => false
    | WAIT_t => false
    | ROUTE_t => true
    end.



(** States stream **)

  Definition States_TIMING := States_Mealy Trans_Timing.


(** Intented behaviour **)

  Definition Behaviour_TIMING := Moore Trans_Timing Out_Timing.



(** Transformation of Behaviour_TIMING to a Mealy automaton **)

  Definition Out_Timing_Mealy :=
    Out_Mealy (Input_type:=Input_type) Out_Timing.

  Lemma equiv_out_Timing :
   forall (i : Input_type) (s : label_t), Out_Timing s = Out_Timing_Mealy i s.
  auto.
  Qed.


  Lemma Equiv_Timing_Moore_Mealy :
   forall (s : label_t) (i : Stream Input_type),
   EqS (Behaviour_TIMING i s) (Mealy Trans_Timing Out_Timing_Mealy i s).
  intros s i.
  unfold Behaviour_TIMING in |- *; unfold Out_Timing_Mealy in |- *;
   apply Equiv_Moore_Mealy.
  Qed.



(** Stream of states for Structure_TIMING **)

  Definition States_Structure_TIMING := States_Mealy Timing_Aux.


(** No invariant property *)

  Let Reg_type := d_list bool 2. (* Type of the registers of TIMING *)

  Let Cst_True (i : Input_type) (s : label_t) (b : Reg_type) := True.


(** Output relation **)

  Definition R_Timing (s : label_t) (l : Reg_type) :=
    Fst_of_l2 l = Out_Timing s /\
    (s = START_t /\ Scd_of_l2 l = false \/
     s = WAIT_t /\ Scd_of_l2 l = true \/ s = ROUTE_t /\ Scd_of_l2 l = true).


(** Proof : correctness of the TIMING UNIT **)


  Lemma Cst_True_inv_t :
   forall (i : Stream Input_type) (s : label_t) (l : Reg_type),
   Inv Cst_True i (States_TIMING i s) (States_Structure_TIMING i l).

  cofix.
  intros i s l.
  apply Inv_Ok.
  unfold Cst_True in |- *; auto.
  Qed.



 (* Combinational proof *)

  Lemma Invariant_relation_t :
   Inv_under_P Trans_Timing Timing_Aux Cst_True R_Timing.

  unfold Inv_under_P in |- *; unfold R_Timing in |- *.
  intros i s l H_True R; clear H_True; elim i; intros fs act.
  elim R; clear R.
  intros H1 H2.

 (* s=START_t /\ (Scd_of_l2 l)=false *)
  elim H2; clear H2; intros H2.
  elim H2; clear H2; intros H2 H3.
  unfold Timing_Aux in |- *; unfold Timing in |- *; simpl in |- *.
  generalize H1; clear H1; rewrite H2; simpl in |- *.
  intros H1; rewrite H1; rewrite H3; simpl in |- *.
  case fs; simpl in |- *.
  split; auto.
  unfold AND4 in |- *; unfold AND2 in |- *; simpl in |- *.
  elim andb_sym; simpl in |- *; auto.
  split; auto.
  unfold AND4 in |- *; unfold AND2 in |- *; simpl in |- *.
  elim andb_sym; simpl in |- *; auto.

 (* s=WAIT_t /\ (Scd_of_l2 l)=true *)
  elim H2; clear H2; intros H2.
  elim H2; clear H2; intros H2 H3.
  unfold Timing_Aux in |- *; unfold Timing in |- *; simpl in |- *.
  generalize H1; clear H1; rewrite H2; simpl in |- *.
  intros H1; rewrite H1; rewrite H3; simpl in |- *.
  case (Ackor act); simpl in |- *; auto.
  case fs; simpl in |- *; auto.
  split; auto.
  right; left; auto.
  split; auto.
  unfold List2 in |- *; unfold Scd_of_l2 in |- *; simpl in |- *;
   auto with bool.

 (* s=ROUTE_t /\ (Scd_of_l2 l)=true *)
  elim H2; clear H2; intros H2 H3.
  unfold Timing_Aux in |- *; unfold Timing in |- *; simpl in |- *.
  generalize H1; clear H1; rewrite H2; simpl in |- *.
  intros H1; rewrite H1; rewrite H3; simpl in |- *.
  case fs; simpl in |- *; auto.
  split; auto.
  unfold AND4 in |- *; unfold AND2 in |- *; simpl in |- *.
  elim andb_sym; simpl in |- *; auto.
  split; auto.
  unfold AND4 in |- *; unfold AND2 in |- *; simpl in |- *.
  elim andb_sym; simpl in |- *; auto.
  Qed.


 (* R_Timing is an output relation *)

  Lemma Output_relation_t :
   Output_rel Out_Timing_Mealy Out_Struct_Timing R_Timing.

  unfold Output_rel in |- *; unfold R_Timing in |- *; intros i s l H.
  elim H; clear H.
  intros H1 H2.
  elim H2; clear H2; intro H2.
  elim H2; clear H2; intros H2 H3.
  generalize H1; clear H1; unfold Fst_of_l2 in |- *; rewrite H2;
   simpl in |- *; intro H; auto.
  elim H2; clear H2; intros H2.
  elim H2; clear H2; intros H2 H3.
  generalize H1; clear H1; unfold Fst_of_l2 in |- *; rewrite H2;
   simpl in |- *; intro H; auto.
  elim H2; clear H2; intros H2 H3.
  generalize H1; clear H1; unfold Fst_of_l2 in |- *; rewrite H2;
   simpl in |- *; intro H; auto.
  Qed.


 (* Temporal proof *)

  Lemma Correct_TIMING :
   forall (i : Stream Input_type) (l : Reg_type) (s : label_t),
   R_Timing s l -> EqS (Behaviour_TIMING i s) (Structure_TIMING i l).

  intros i l s HR.
  unfold Behaviour_TIMING in |- *; unfold Structure_TIMING in |- *.
  apply
   (Equiv_2_Mealy Invariant_relation_t Output_relation_t
      (Cst_True_inv_t i s l) HR).

  Qed.


End Timing_Correctness.