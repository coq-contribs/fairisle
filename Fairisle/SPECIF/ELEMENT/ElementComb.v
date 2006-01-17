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
(*                              ElementComb.v                               *)
(****************************************************************************)
 

Require Export Proj_lists.
Require Export Fixed_dLists.
Require Export Base_Struct.

Set Implicit Arguments.
Unset Strict Implicit.


(** Describes the combinational parts of the circuit **)


Definition ackgen (a b c d : bool) := NOR2 (NAND3 a b c) d. 


(** Ackgen unit : generates the acknowledgement signals for a single output port **)

Definition Ackgen (ackIn x y disabled : bool) : d_list bool 4 :=
  List4 (ackgen (INV x) (INV y) ackIn disabled)
    (ackgen (INV x) y ackIn disabled) (ackgen x (INV y) ackIn disabled)
    (ackgen x y ackIn disabled).


(** Ackor unit : combines into a boolean the n+1 acknowledgements for a single input port **)

Definition Ackor_n (n m : nat) (l : d_list (d_list bool n) (S m)) :=
  d_map (Ackor (n:=m)) (merge l).

Definition Ackor_4 (ackTerm : d_list (d_list bool 4) 4) := Ackor_n ackTerm.


Definition Ackgen_n := d_map4 Ackgen. 

Definition Ackgen_4 := Ackgen_n (n:=4).


Definition Ack (ackIn xgrant ygrant outputDisable : d_list bool 4) :=
  Ackor_4 (Ackgen_4 ackIn xgrant ygrant outputDisable).
 



Definition dmux4t2ffc (y : bool) (d : d_list bool 4) :=
  List2 (AO (Fst_of_l4 d) (INV y) (Scd_of_l4 d) y)
    (AO (Thd_of_l4 d) (INV y) (Fth_of_l4 d) y).

  

Definition Dmux4t2 (x : bool) (d : d_list (d_list bool 2) 2) :=
  List2
    (AO (Fst_of_l2 (List_of_fst_of_l2 d)) (INV x)
       (Fst_of_l2 (List_of_scd_of_l2 d)) x)
    (AO (Scd_of_l2 (List_of_fst_of_l2 d)) (INV x)
       (Scd_of_l2 (List_of_scd_of_l2 d)) x).



Definition Timing (frameStart : bool) (active : d_list bool 4)
  (old_timing : d_list bool 2) :=
  List2
    (AND4 (Ackor active) (Scd_of_l2 old_timing) (INV frameStart)
       (INV (Fst_of_l2 old_timing)))
    (OR2 frameStart
       (AND2 (INV (Fst_of_l2 old_timing)) (Scd_of_l2 old_timing))).



Definition Prifilunit (hiOtherR : d_list bool 3) (genR hiR : bool) :=
  OR2 hiR (AND2 genR (NORL3 hiOtherR)).



Definition Prifil4clb (hiR genR : d_list bool 4) :=
  List4 (Prifilunit (remove_i 1 hiR) (Fst_of_l4 genR) (Fst_of_l4 hiR))
    (Prifilunit (remove_i 2 hiR) (Scd_of_l4 genR) (Scd_of_l4 hiR))
    (Prifilunit (remove_i 3 hiR) (Thd_of_l4 genR) (Thd_of_l4 hiR))
    (Prifilunit (remove_i 4 hiR) (Fth_of_l4 genR) (Fth_of_l4 hiR)).


Definition Priority_4 (hiR genR : d_list (d_list bool 4) 4) :=
  merge (d_map2 Prifil4clb hiR genR).

 
Definition Hireq (act pri r1 r2 r1Bar r2Bar : bool) :=
  d_map ANDL4
    (List4 (List4 act pri r1Bar r2Bar) (List4 act pri r1Bar r2)
       (List4 act pri r1 r2Bar) (List4 act pri r1 r2)).
       

Definition Genreq (act r1 r2 r1Bar r2Bar : bool) :=
  d_map ANDL3
    (List4 (List3 act r1Bar r2Bar) (List3 act r1Bar r2) 
       (List3 act r1 r2Bar) (List3 act r1 r2)).
        

Definition Decode (route : d_list bool 2) (act pri : bool) :=
  List2
    (Hireq act pri (Scd_of_l2 route) (INV (Scd_of_l2 route))
       (INV (Fst_of_l2 route)) (Fst_of_l2 route))
    (Genreq act (INV (Scd_of_l2 route)) (Scd_of_l2 route)
       (INV (Fst_of_l2 route)) (Fst_of_l2 route)).


Definition Decode_n := d_map3 Decode.

Definition Decode_4 := Decode_n (n:=4).


Definition Arb_yel (x xBar reqA reqB reqC reqD : bool) :=
  AO (OR2 x (INV reqB)) reqC (OR2 xBar (INV reqA)) reqD.
   

Definition Arb_xel (reqA y reqB reqC : bool) :=
  AND2 (OR2 y (INV reqA)) (OR2 reqB reqC).


Definition K_Arby (x : bool) (req : d_list bool 4) :=
  Arb_yel (INV x) x (Fth_of_l4 req) (Scd_of_l4 req) 
    (Thd_of_l4 req) (Fst_of_l4 req).


Definition J_Arby (x : bool) (req : d_list bool 4) :=
  Arb_yel x (INV x) (Fst_of_l4 req) (Thd_of_l4 req) 
    (Fth_of_l4 req) (Scd_of_l4 req).
  

Definition Arby (x : bool) (req : d_list bool 4) :=
  List2 (J_Arby x req) (K_Arby x req).


Definition Arbx (y : bool) (req : d_list bool 4) :=
  List2 (Arb_xel (Scd_of_l4 req) y (Fth_of_l4 req) (Thd_of_l4 req))
    (Arb_xel (Fth_of_l4 req) y (Fst_of_l4 req) (Scd_of_l4 req)).
  
 
Definition outdis (req : d_list bool 4) (routeEnable : bool) :=
  AND2 routeEnable (Ackor req).


Definition hiReq := d_map (Fst_of_l2 (A:=d_list bool 4)) (n:=4).
  
Definition genReq := d_map (Scd_of_l2 (A:=d_list bool 4)) (n:=4).


Definition Priority_Decode_Less_Pause (active priority : d_list bool 4)
  (route : d_list (d_list bool 2) 4) :=
  Priority_4 (hiReq (Decode_4 route active priority))
    (genReq (Decode_4 route active priority)).