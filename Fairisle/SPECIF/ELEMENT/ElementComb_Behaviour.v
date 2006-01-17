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
(*                          ElementComb_Behaviour.v                         *)
(****************************************************************************)


Require Export Conversions.
Require Export Bool.
Require Import Lib_Dec.
Require Import PortsCompl.
Require Export Manip_BoolLists.


(** List of all the 4 (input or output) ports **)

Definition All_Ports :=
  List4 (exist (fun p : nat => p < 4) 0 lt_O_4)
    (exist (fun p : nat => p < 4) 1 lt_1_4)
    (exist (fun p : nat => p < 4) 2 lt_2_4)
    (exist (fun p : nat => p < 4) 3 lt_3_4).



(** Behavioural description of the Ackgen unit **)

Definition Ackgen_Behaviour (ackIn disabled : bool)
  (grant : d_list bool 2) :=
  match ackIn && negb disabled with
  | true => Convert_list2 grant
  | false => List4 false false false false
  end.



(** Behavioural description of the Ack unit **)

Definition ack_behaviour (inp : T_Inportno 4) (a d : bool)
  (g : d_list bool 2) :=
  match eq_or_not_bis (Convert_list2_nat g) (no_in inp) with
  | left _ => a && negb d
  | right _ => false
  end.


Definition Ack_behaviour (ackIn disabled : d_list bool 4)
  (grant : d_list (d_list bool 2) 4) (inp : T_Inportno 4) :=
  Exists1_atleast (fun b : bool => b = true)
    (d_map3 (ack_behaviour inp) ackIn disabled grant).


Definition Ack_Behaviour (ackIn disabled : d_list bool 4)
  (grant : d_list (d_list bool 2) 4) :=
  d_map (Ack_behaviour ackIn disabled grant) All_Ports.


(****************************************************************************)

(** Pause_DataSwitch Unit **)

Lemma le_S_bool_nat : forall b : bool, S (bool_nat b) <= 4.
simple induction b; auto.
Qed.

Lemma le_SSS_bool_nat : forall b : bool, S (S (S (bool_nat b))) <= 4.
simple induction b; auto.
Qed.


Definition Dmux4t2ffc_Behaviour' (d : d_list bool 4)
  (outputDisable y : bool) :=
  match outputDisable with
  | true => List2 false false
  | false =>
      List2
        (Nth (i:=S (bool_nat y)) d (lt_O_Sn (bool_nat y)) (le_S_bool_nat y))
        (Nth (i:=S (S (S (bool_nat y)))) d (lt_O_Sn (S (S (bool_nat y))))
           (le_SSS_bool_nat y))
  end.


(** A simplier way for writing Dmux4t2ffc_Behaviour **)

Definition Dmux4t2ffc_Behaviour (d : d_list bool 4)
  (outputDisable y : bool) :=
  match outputDisable with
  | true => List2 false false
  | false =>
      match y with
      | true => List2 (Scd_of_l4 d) (Fth_of_l4 d)
      | false => List2 (Fst_of_l4 d) (Thd_of_l4 d)
      end
  end.


(****************************************************************************)

(** Arbitration Unit **)

(** Behavioural description of the Arbiter_XY unit **)
(** Arbiter_XY computes the two bits of the grant signal **)
(** x and y stand for x_grant and y_grant **)

Definition Arbiter_X_behaviour (ltReq : d_list bool 4) 
  (RouteE x y : bool) :=
  match RouteE with
  | true =>
      match x with
      | true =>
          negb y && Fth_of_l4 ltReq
          || negb (Fst_of_l4 ltReq) && negb (Scd_of_l4 ltReq)
      | false =>
          (y || negb (Scd_of_l4 ltReq)) &&
          (Fth_of_l4 ltReq || Thd_of_l4 ltReq)
      end
  | false => x
  end.
 


Definition Arbiter_Y_behaviour (ltReq : d_list bool 4) 
  (RouteE x y : bool) :=
  match RouteE with
  | true =>
      match y with
      | true =>
          (x && Scd_of_l4 ltReq || negb (Thd_of_l4 ltReq)) &&
          (negb x && Fth_of_l4 ltReq || negb (Fst_of_l4 ltReq))
      | false =>
          (x || negb (Thd_of_l4 ltReq)) && Fth_of_l4 ltReq
          || (negb x || negb (Fst_of_l4 ltReq)) && Scd_of_l4 ltReq
      end
  | false => y
  end.


(** Behavioural description of the Outdis unit **)

Definition Outdis_behaviour (ltReq RouteE fs old : bool) :=
  match old with
  | true => negb (RouteE && ltReq)
  | false => fs
  end.
 

