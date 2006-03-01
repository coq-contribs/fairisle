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
(*                          ElementTemp_Behaviour.v                         *)
(****************************************************************************)


Require Import ElementComb_Behaviour.
Require Import Base_Struct.


(** For the PAUSE_DATASWITCH unit **)

CoFixpoint DMUX4T2FFC_Behaviour (old : d_list bool two)
 (d : Stream (d_list bool four)) (outputDisable y : Stream bool) :
 Stream (d_list bool 2) :=
  S_cons old
    (DMUX4T2FFC_Behaviour
       (Dmux4t2ffc_Behaviour (S_head d) (S_head outputDisable) (S_head y))
       (S_tail d) (S_tail outputDisable) (S_tail y)).




(** For the ARBITRATION unit **)

CoFixpoint ARBITER_XY_Behaviour (last : d_list bool two)
 (ltReq : Stream (d_list bool four)) (RouteE : Stream bool) :
 Stream (d_list bool 2) :=
  S_cons last
    (ARBITER_XY_Behaviour
       (List2
          (Arbiter_X_behaviour (S_head ltReq) (S_head RouteE)
             (Fst_of_l2 last) (Scd_of_l2 last))
          (Arbiter_Y_behaviour (S_head ltReq) (S_head RouteE)
             (Fst_of_l2 last) (Scd_of_l2 last))) (S_tail ltReq)
       (S_tail RouteE)).



CoFixpoint OUTDIS_Behaviour (old : bool) (ltReq : Stream (d_list bool four))
 (RouteE fs : Stream bool) : Stream (d_list bool 2) :=
  S_cons (List2 old (negb old))
    (OUTDIS_Behaviour
       (Outdis_behaviour (Ackor (S_head ltReq)) (S_head RouteE) 
          (S_head fs) old) (S_tail ltReq) (S_tail RouteE) 
       (S_tail fs)).